import Submission.BoundaryFinal
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Function.L2Space

open Complex Filter MeasureTheory Metric Real Set Topology
open scoped LSeries.notation

namespace Submission.BoundaryTauberian

open Submission.Analytic Submission.BoundaryFinal Submission.BoundaryOscillation
open Submission.Endpoint Submission.FejerLaplace Submission.Helpers
open Submission.PrimeSeries Submission.ResidueCertificate Submission.SignChange
open Submission.ZeroMass

private lemma tendsto_div_atTop_of_deriv_tendsto_zero
    {f f' : ℝ → ℂ}
    (hf : ∀ x, 1 ≤ x → HasDerivAt f (f' x) x)
    (hf' : Filter.Tendsto f' atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ)⁻¹ * f x) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp hf') (ε / 2) hhalf
  let B : ℝ := max 1 A
  let N : ℝ := max B (2 * ‖f B‖ / ε + 1)
  refine ⟨N, fun x hx => ?_⟩
  have hNB : B ≤ N := le_max_left _ _
  have hBx : B ≤ x := hNB.trans hx
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBA : A ≤ B := le_max_right _ _
  have hxpos : 0 < x := zero_lt_one.trans_le (hB1.trans hBx)
  have hderiv : ∀ y ∈ Icc B x, HasDerivWithinAt f (f' y) (Icc B x) y := by
    intro y hy
    exact (hf y (hB1.trans hy.1)).hasDerivWithinAt
  have hbound : ∀ y ∈ Icc B x, ‖f' y‖ ≤ ε / 2 := by
    intro y hy
    have := hA y (hBA.trans hy.1)
    simpa [Real.dist_eq] using this.le
  have hmv := (convex_Icc B x).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound ⟨le_rfl, hBx⟩ ⟨hBx, le_rfl⟩
  have hfx : ‖f x‖ ≤ ‖f B‖ + (ε / 2) * x := by
    calc
      ‖f x‖ ≤ ‖f x - f B‖ + ‖f B‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f x - f B) (f B)
      _ ≤ (ε / 2) * ‖x - B‖ + ‖f B‖ := by
        simpa only [add_comm] using add_le_add_right hmv ‖f B‖
      _ ≤ (ε / 2) * x + ‖f B‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hBx)]
        nlinarith
      _ = _ := by ring
  have hNlarge : 2 * ‖f B‖ / ε + 1 ≤ x :=
    (le_max_right B _).trans hx
  have hsmall : ‖f B‖ / x < ε / 2 := by
    apply (div_lt_iff₀ hxpos).2
    have hεne : ε ≠ 0 := hε.ne'
    have : 2 * ‖f B‖ / ε < x := lt_of_lt_of_le (lt_add_one _) hNlarge
    field_simp [hεne] at this ⊢
    nlinarith
  rw [dist_zero_right, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hxpos]
  calc
    x⁻¹ * ‖f x‖ = ‖f x‖ / x := by rw [inv_mul_eq_div]
    _ ≤ (‖f B‖ + (ε / 2) * x) / x :=
      div_le_div_of_nonneg_right hfx hxpos.le
    _ = ‖f B‖ / x + ε / 2 := by field_simp [hxpos.ne']
    _ < ε := by linarith

private lemma tendsto_mul_self_of_scaled_deriv
    {f f' : ℝ → ℂ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    {c : ℂ}
    (hf' : Filter.Tendsto (fun x : ℝ => (x : ℂ) * f' x)
      (nhdsWithin 0 (Ioi 0)) (nhds c)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let F : ℝ → ℂ := fun y => f y⁻¹
  let F' : ℝ → ℂ := fun y => -(f' y⁻¹) / (y : ℂ) ^ 2
  have hF (y : ℝ) (hy : 1 ≤ y) : HasDerivAt F (F' y) y := by
    have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
    dsimp [F, F']
    have hcomp := HasDerivAt.scomp y
      (hf y⁻¹ (inv_pos.mpr (zero_lt_one.trans_le hy))) (hasDerivAt_inv hy0)
    simpa [Function.comp_def, div_eq_mul_inv, smul_eq_mul, mul_comm] using hcomp
  have hinv : Filter.Tendsto (fun y : ℝ => y⁻¹) atTop
      (nhdsWithin 0 (Ioi 0)) := tendsto_inv_atTop_nhdsGT_zero
  have hscaled := hf'.comp hinv
  have hF' : Filter.Tendsto F' atTop (nhds 0) := by
    have hone : Filter.Tendsto (fun y : ℝ => (y : ℂ)⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.ofReal :
        Filter.Tendsto (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) atTop (nhds 0))
    have hprod : Filter.Tendsto
        (fun y : ℝ => -(((y⁻¹ : ℝ) : ℂ) * f' y⁻¹) * (y : ℂ)⁻¹)
        atTop (nhds 0) := by
      simpa using hscaled.neg.mul hone
    refine (tendsto_congr' ?_).2 hprod
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
    dsimp [F']
    push_cast
    field_simp [hy]
  have hquot := tendsto_div_atTop_of_deriv_tendsto_zero hF hF'
  have hcomp := hquot.comp tendsto_inv_nhdsGT_zero
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  dsimp [F]
  push_cast
  field_simp [hx0]

private lemma tendsto_difference_of_scaled_deriv
    {f f' : ℝ → ℂ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    {c : ℂ}
    (hf' : Filter.Tendsto (fun x : ℝ => (x : ℂ) * f' x)
      (nhdsWithin 0 (Ioi 0)) (nhds c)) :
    Filter.Tendsto (fun x : ℝ => f x - f (2 * x))
      (nhdsWithin 0 (Ioi 0)) (nhds (-((Real.log 2 : ℝ) : ℂ) * c)) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf' ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨η, hη, hres⟩ := hf' (ε / 2) hhalf
  let radius : ℝ := min (η / 2) 1
  have hradius : 0 < radius := by
    dsimp [radius]
    exact lt_min_iff.mpr ⟨by positivity, zero_lt_one⟩
  refine ⟨radius, hradius, ?_⟩
  intro x hx hxdist
  have hxpos : 0 < x := hx
  have hxltRadius : x < radius := by
    simpa [Real.dist_eq, abs_of_pos hxpos] using hxdist
  have htwoEta : 2 * x < η := by
    have : x < η / 2 := hxltRadius.trans_le (min_le_left _ _)
    linarith
  let g : ℝ → ℂ := fun y => f y - ((Real.log y : ℝ) : ℂ) * c
  let g' : ℝ → ℂ := fun y => f' y - (((y⁻¹ : ℝ) : ℂ) * c)
  have hg (y : ℝ) (hy : 0 < y) : HasDerivAt g (g' y) y := by
    have hlog : HasDerivAt
        (fun z : ℝ => ((Real.log z : ℝ) : ℂ) * c)
        (((y⁻¹ : ℝ) : ℂ) * c) y := by
      simpa using
        (Complex.ofRealCLM.hasDerivAt.scomp y
          (Real.hasDerivAt_log hy.ne')).mul_const c
    exact (hf y hy).sub hlog
  have hbound : ∀ y ∈ Icc x (2 * x), ‖g' y‖ ≤ ε / (2 * x) := by
    intro y hy
    have hypos : 0 < y := hxpos.trans_le hy.1
    have hyeta : dist y 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hypos]
      exact hy.2.trans_lt htwoEta
    have hry := hres hypos hyeta
    have hry' : ‖(y : ℂ) * f' y - c‖ < ε / 2 := by
      simpa [Complex.dist_eq] using hry
    have hgeq : g' y = ((y : ℂ) * f' y - c) / (y : ℂ) := by
      dsimp [g']
      push_cast
      field_simp [hypos.ne']
    rw [hgeq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
    calc
      ‖(y : ℂ) * f' y - c‖ / y ≤ (ε / 2) / y :=
        div_le_div_of_nonneg_right hry'.le hypos.le
      _ ≤ (ε / 2) / x := by
        exact div_le_div_of_nonneg_left hhalf.le hxpos hy.1
      _ = ε / (2 * x) := by ring
  have hmv := (convex_Icc x (2 * x)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hg y (hxpos.trans_le hy.1)).hasDerivWithinAt)
    hbound ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  have hmv' : ‖g (2 * x) - g x‖ ≤ ε / 2 := by
    calc
      ‖g (2 * x) - g x‖ ≤ (ε / (2 * x)) * ‖(2 * x) - x‖ := hmv
      _ = ε / 2 := by
        rw [show (2 * x) - x = x by ring, Real.norm_eq_abs, abs_of_pos hxpos]
        field_simp [hxpos.ne']
  have halg :
      (f x - f (2 * x)) - (-((Real.log 2 : ℝ) : ℂ) * c) =
        -(g (2 * x) - g x) := by
    dsimp [g]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
    push_cast
    ring
  rw [Complex.dist_eq, halg, norm_neg]
  exact hmv'.trans_lt (by linarith)

noncomputable def boundaryPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * I

noncomputable def boundaryResidueMass (t : ℝ) : ℂ :=
  if t = 0 then (1 / 2 : ℂ)
  else (chiFourZeroMultiplicity (boundaryPoint t) : ℂ)

lemma boundaryPoint_re (t : ℝ) : (boundaryPoint t).re = 1 / 2 := by
  simp [boundaryPoint]

lemma boundaryPoint_im (t : ℝ) : (boundaryPoint t).im = t := by
  simp [boundaryPoint]

lemma boundaryPoint_ne_zero (t : ℝ) : boundaryPoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [boundaryPoint] at hre

private lemma tendsto_boundaryPath_nhds (t : ℝ) :
    Filter.Tendsto (fun r : ℝ => boundaryPoint t + (r : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhds (boundaryPoint t)) := by
  have hr : Filter.Tendsto (fun r : ℝ => (r : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (Complex.ofRealCLM.continuous.tendsto 0).comp
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa using tendsto_const_nhds.add hr

private lemma tendsto_boundaryPath_nhdsNE (t : ℝ) :
    Filter.Tendsto (fun r : ℝ => boundaryPoint t + (r : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin (boundaryPoint t) {boundaryPoint t}ᶜ) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_boundaryPath_nhds t) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have hre := congrArg Complex.re h
  simp [boundaryPoint] at hre
  exact (ne_of_gt hr) hre

private lemma twistedPrimeLogContinuation_analyticAt_boundaryPoint_of_L_ne
    {t : ℝ} (ht : t ≠ 0)
    (hL : DirichletCharacter.LFunction chiFour (boundaryPoint t) ≠ 0) :
    AnalyticAt ℂ twistedPrimeLogContinuation (boundaryPoint t) := by
  have hLAn : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) (boundaryPoint t) :=
    differentiable_chiFour_LFunction.analyticAt _
  have hlog : AnalyticAt ℂ chiFourNegLogDerivative (boundaryPoint t) := by
    change AnalyticAt ℂ
      (fun s => -(deriv (DirichletCharacter.LFunction chiFour) s /
        DirichletCharacter.LFunction chiFour s)) (boundaryPoint t)
    exact (hLAn.deriv.div hLAn hL).neg
  have hsquare : AnalyticAt ℂ squarePrimePowerContinuation (boundaryPoint t) :=
    squarePrimePowerContinuation_analyticAt_of_half_le_re_of_im_ne_zero
      (by rw [boundaryPoint_re]) (by simpa [boundaryPoint_im] using ht)
  have hhigher : AnalyticAt ℂ (L higherExponentPrimePowerCoeff) (boundaryPoint t) :=
    higherExponentPrimePowerCoeff_LSeries_analyticOnNhd _ (by
      change (2 / 5 : ℝ) < (boundaryPoint t).re
      rw [boundaryPoint_re]
      norm_num)
  unfold twistedPrimeLogContinuation
  exact hlog.sub hsquare |>.sub hhigher

private lemma tendsto_scaled_deriv_adjustedPrimeDirichlet_neg_one
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) (t : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => (r : ℂ) *
        deriv (adjustedPrimeDirichlet (-1) C) (boundaryPoint t + (r : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds (-boundaryResidueMass t)) := by
  have hbeta : mellinAbscissa (-1) C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone (by norm_num)
  have hLpath : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0),
      DirichletCharacter.LFunction chiFour (boundaryPoint t + (r : ℂ)) ≠ 0 := by
    by_cases hL : DirichletCharacter.LFunction chiFour (boundaryPoint t) = 0
    · exact (tendsto_boundaryPath_nhdsNE t).eventually
        (eventually_chiFour_LFunction_ne_zero_nhdsNE hL)
    · have hne : ∀ᶠ z in nhds (boundaryPoint t),
          DirichletCharacter.LFunction chiFour z ≠ 0 :=
        differentiable_chiFour_LFunction.continuous.continuousAt.preimage_mem_nhds
          (compl_singleton_mem_nhds_iff.mpr hL)
      exact (tendsto_boundaryPath_nhds t).eventually hne
  have hderivEq :
      (fun r : ℝ => (r : ℂ) *
        deriv (adjustedPrimeDirichlet (-1) C) (boundaryPoint t + (r : ℂ)))
        =ᶠ[nhdsWithin 0 (Ioi 0)]
      fun r : ℝ =>
        ((boundaryPoint t + (r : ℂ)) - boundaryPoint t) *
          twistedPrimeLogContinuation (boundaryPoint t + (r : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin, hLpath] with r hr hL
    have hs : max (mellinAbscissa (-1) C) (1 / 2 : ℝ) <
        (boundaryPoint t + (r : ℂ)).re := by
      rw [hbeta, max_self, Complex.add_re, boundaryPoint_re]
      simp
      exact hr
    rw [deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_ne_zero
      hone hs hL]
    norm_num
  apply (tendsto_congr' hderivEq).2
  by_cases ht : t = 0
  · subst t
    have hpath : (fun r : ℝ => boundaryPoint 0 + (r : ℂ)) =
        fun r : ℝ => (1 / 2 : ℂ) + (r : ℂ) := by
      funext r
      simp [boundaryPoint]
    have hp : Filter.Tendsto (fun r : ℝ => boundaryPoint 0 + (r : ℂ))
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin (1 / 2 : ℂ) {(1 / 2 : ℂ)}ᶜ) := by
      simpa [boundaryPoint] using tendsto_boundaryPath_nhdsNE 0
    have hres := tendsto_twistedPrimeLogContinuation_central.comp hp
    rw [Submission.Central.chiFourCentralMultiplicity_eq_zero] at hres
    simpa [Function.comp_def, boundaryResidueMass, hpath, boundaryPoint] using hres
  · by_cases hL : DirichletCharacter.LFunction chiFour (boundaryPoint t) = 0
    · have hres := tendsto_twistedPrimeLogContinuation_nonreal_zero hL
        (by rw [boundaryPoint_re]) (by simpa [boundaryPoint_im] using ht)
      have hcomp := hres.comp (tendsto_boundaryPath_nhdsNE t)
      simpa [Function.comp_def, boundaryResidueMass, ht] using hcomp
    · have hAn :=
        twistedPrimeLogContinuation_analyticAt_boundaryPoint_of_L_ne ht hL
      have hmult : chiFourZeroMultiplicity (boundaryPoint t) = 0 := by
        unfold chiFourZeroMultiplicity analyticOrderNatAt
        rw [(differentiable_chiFour_LFunction.analyticAt _).analyticOrderAt_eq_zero.mpr hL]
        rfl
      have hsub : Filter.Tendsto
          (fun r : ℝ => (boundaryPoint t + (r : ℂ)) - boundaryPoint t)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa using (tendsto_boundaryPath_nhds t).sub_const (boundaryPoint t)
      have hprod := hsub.mul
        (hAn.continuousAt.tendsto.comp (tendsto_boundaryPath_nhds t))
      simpa [boundaryResidueMass, ht, hmult] using hprod

private lemma hasDerivAt_radial_adjustedPrimeMellin
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun x : ℝ => adjustedPrimeMellin (-1) C (boundaryPoint t + (x : ℂ)))
      (deriv (adjustedPrimeMellin (-1) C) (boundaryPoint t + (r : ℂ))) r := by
  have hbeta : mellinAbscissa (-1) C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone (by norm_num)
  have hs : mellinAbscissa (-1) C < (boundaryPoint t + (r : ℂ)).re := by
    rw [hbeta, Complex.add_re, boundaryPoint_re]
    simp
    exact hr
  have hM := analyticAt_adjustedPrimeMellin hone hs
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    Function.comp_apply] using!
    HasDerivAt.scomp r hM.differentiableAt.hasDerivAt
      (Complex.ofRealCLM.hasDerivAt.const_add (boundaryPoint t))

private lemma hasDerivAt_radial_adjustedPrimeDirichlet
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun x : ℝ => adjustedPrimeDirichlet (-1) C (boundaryPoint t + (x : ℂ)))
      (deriv (adjustedPrimeDirichlet (-1) C) (boundaryPoint t + (r : ℂ))) r := by
  have hbeta : mellinAbscissa (-1) C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone (by norm_num)
  have hs : mellinAbscissa (-1) C < (boundaryPoint t + (r : ℂ)).re := by
    rw [hbeta, Complex.add_re, boundaryPoint_re]
    simp
    exact hr
  have hM := analyticAt_adjustedPrimeMellin hone hs
  have hA : AnalyticAt ℂ (adjustedPrimeDirichlet (-1) C)
      (boundaryPoint t + (r : ℂ)) := by
    unfold adjustedPrimeDirichlet
    exact analyticAt_id.mul hM
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    Function.comp_apply] using!
    HasDerivAt.scomp r hA.differentiableAt.hasDerivAt
      (Complex.ofRealCLM.hasDerivAt.const_add (boundaryPoint t))

private lemma tendsto_scaled_adjustedPrimeMellin_neg_one
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) (t : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => (r : ℂ) *
        adjustedPrimeMellin (-1) C (boundaryPoint t + (r : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hscaledA := tendsto_mul_self_of_scaled_deriv
    (fun x hx => hasDerivAt_radial_adjustedPrimeDirichlet hone t (r := x) hx)
    (tendsto_scaled_deriv_adjustedPrimeDirichlet_neg_one hone t)
  have hpath := tendsto_boundaryPath_nhds t
  have hdiv := hscaledA.div hpath (boundaryPoint_ne_zero t)
  simp only [zero_div] at hdiv
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  have hs0 : boundaryPoint t + (r : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    rw [Complex.add_re, boundaryPoint_re]
    simp
    linarith
  unfold adjustedPrimeDirichlet
  change ((r : ℂ) * ((boundaryPoint t + (r : ℂ)) *
      adjustedPrimeMellin (-1) C (boundaryPoint t + (r : ℂ)))) /
      (boundaryPoint t + (r : ℂ)) =
    (r : ℂ) * adjustedPrimeMellin (-1) C (boundaryPoint t + (r : ℂ))
  field_simp [hs0]

private lemma tendsto_scaled_deriv_adjustedPrimeMellin_neg_one
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) (t : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => (r : ℂ) *
        deriv (adjustedPrimeMellin (-1) C) (boundaryPoint t + (r : ℂ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((-boundaryResidueMass t) / boundaryPoint t)) := by
  have hA := tendsto_scaled_deriv_adjustedPrimeDirichlet_neg_one hone t
  have hM := tendsto_scaled_adjustedPrimeMellin_neg_one hone t
  have hpath := tendsto_boundaryPath_nhds t
  have hlim := (hA.sub hM).div hpath (boundaryPoint_ne_zero t)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  let s : ℂ := boundaryPoint t + (r : ℂ)
  have hbeta : mellinAbscissa (-1) C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone (by norm_num)
  have hs : mellinAbscissa (-1) C < s.re := by
    dsimp [s]
    rw [hbeta, boundaryPoint_re]
    simp
    exact hr
  have hMan := analyticAt_adjustedPrimeMellin hone hs
  have hprod := (hasDerivAt_id s).mul hMan.differentiableAt.hasDerivAt
  have hderiv : deriv (adjustedPrimeDirichlet (-1) C) s =
      adjustedPrimeMellin (-1) C s +
        s * deriv (adjustedPrimeMellin (-1) C) s := by
    unfold adjustedPrimeDirichlet
    change deriv (id * adjustedPrimeMellin (-1) C) s = _
    simpa only [id_eq, one_mul] using hprod.deriv
  dsimp [s] at hderiv ⊢
  rw [hderiv]
  have hs0 : boundaryPoint t + (r : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    rw [Complex.add_re, boundaryPoint_re]
    simp
    linarith
  field_simp [hs0]
  ring

lemma tendsto_adjustedPrimeMellin_dyadicDifference
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) (t : ℝ) :
    Filter.Tendsto
      (fun r : ℝ =>
        adjustedPrimeMellin (-1) C (boundaryPoint t + (r : ℂ)) -
          adjustedPrimeMellin (-1) C (boundaryPoint t + ((2 * r : ℝ) : ℂ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((Real.log 2 : ℝ) : ℂ) * boundaryResidueMass t /
        boundaryPoint t)) := by
  have h := tendsto_difference_of_scaled_deriv
    (fun x hx => hasDerivAt_radial_adjustedPrimeMellin hone t (r := x) hx)
    (tendsto_scaled_deriv_adjustedPrimeMellin_neg_one hone t)
  convert h using 1
  · congr 1
    ring

end Submission.BoundaryTauberian
