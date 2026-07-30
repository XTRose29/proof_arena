import Submission.StrictFary

open LeanEval.Geometry.FaryMilnorProblem
open MeasureTheory
open ProbabilityTheory
open Set
open Filter
open scoped ContDiff
open scoped ENNReal
open scoped Real
open scoped RealInnerProductSpace
open scoped Topology
open WithLp

namespace Submission.Helpers

noncomputable def tangentBinormalRaw (r : ℝ → Space) (t : ℝ) : Space :=
  toLp 2 (crossProduct (ofLp (unitTangent r t))
    (ofLp (deriv (unitTangent r) t)))

noncomputable def tangentTripleProduct (r : ℝ → Space) (t : ℝ) : ℝ :=
  inner ℝ (tangentBinormalRaw r t) (deriv (deriv (unitTangent r)) t)

noncomputable def tangentBinormal (r : ℝ → Space) (t : ℝ) : Space :=
  normalizedDirection (tangentBinormalRaw r t)

theorem contDiff_deriv_unitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (deriv (unitTangent r)) := by
  exact ContDiff.deriv' (n := ⊤) (contDiff_unitTangent hknot)

theorem contDiff_deriv_deriv_unitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (deriv (deriv (unitTangent r))) := by
  exact ContDiff.deriv' (n := ⊤) (contDiff_deriv_unitTangent hknot)

theorem contDiff_tangentBinormalRaw {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (tangentBinormalRaw r) := by
  have hT := (contDiff_euclidean.mp (contDiff_unitTangent hknot))
  have hV := (contDiff_euclidean.mp (contDiff_deriv_unitTangent hknot))
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [tangentBinormalRaw, cross_apply] using
      ((hT 1).mul (hV 2)).sub ((hT 2).mul (hV 1))
  · simpa [tangentBinormalRaw, cross_apply] using
      ((hT 2).mul (hV 0)).sub ((hT 0).mul (hV 2))
  · simpa [tangentBinormalRaw, cross_apply] using
      ((hT 0).mul (hV 1)).sub ((hT 1).mul (hV 0))

theorem contDiff_tangentTripleProduct {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (tangentTripleProduct r) := by
  exact (contDiff_tangentBinormalRaw hknot).inner ℝ
    (contDiff_deriv_deriv_unitTangent hknot)

theorem inner_tangentBinormalRaw_unitTangent {r : ℝ → Space}
    (t : ℝ) :
    inner ℝ (tangentBinormalRaw r t) (unitTangent r t) = 0 := by
  simp [tangentBinormalRaw, EuclideanSpace.inner_eq_star_dotProduct]

theorem inner_tangentBinormalRaw_deriv_unitTangent {r : ℝ → Space}
    (t : ℝ) :
    inner ℝ (tangentBinormalRaw r t) (deriv (unitTangent r) t) = 0 := by
  simp [tangentBinormalRaw, EuclideanSpace.inner_eq_star_dotProduct]

theorem tangentBinormalRaw_ne_zero_of_triple_ne_zero {r : ℝ → Space}
    {t : ℝ} (htriple : tangentTripleProduct r t ≠ 0) :
    tangentBinormalRaw r t ≠ 0 := by
  intro hzero
  apply htriple
  simp [tangentTripleProduct, hzero]

theorem norm_tangentBinormal_of_triple_ne_zero {r : ℝ → Space}
    {t : ℝ} (htriple : tangentTripleProduct r t ≠ 0) :
    ‖tangentBinormal r t‖ = 1 := by
  exact norm_normalizedDirection
    (tangentBinormalRaw_ne_zero_of_triple_ne_zero htriple)

theorem directionalUnitTangent_tangentBinormal {r : ℝ → Space}
    (t : ℝ) :
    directionalUnitTangent r (tangentBinormal r t) t = 0 := by
  simp [directionalUnitTangent, tangentBinormal, normalizedDirection,
    real_inner_smul_left, inner_tangentBinormalRaw_unitTangent]

theorem inner_tangentBinormal_deriv_unitTangent {r : ℝ → Space}
    (t : ℝ) :
    inner ℝ (tangentBinormal r t) (deriv (unitTangent r) t) = 0 := by
  simp [tangentBinormal, normalizedDirection, real_inner_smul_left,
    inner_tangentBinormalRaw_deriv_unitTangent]

theorem hasDerivAt_tangentBinormalRaw {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt (tangentBinormalRaw r)
      (toLp 2 (crossProduct (ofLp (unitTangent r t))
        (ofLp (deriv (deriv (unitTangent r)) t)))) t := by
  let T := unitTangent r
  let V := deriv T
  let A := deriv V
  have hT : HasDerivAt T (V t) t :=
    ((contDiff_unitTangent hknot).differentiable (by simp)).differentiableAt.hasDerivAt
  have hV : HasDerivAt V (A t) t :=
    ((contDiff_deriv_unitTangent hknot).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hTi (i : Fin 3) : HasDerivAt (fun x => ofLp (T x) i) (ofLp (V t) i) t := by
    simpa using (hasDerivAt_pi.mp
      ((PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (T t)).comp_hasDerivAt t hT)) i
  have hVi (i : Fin 3) : HasDerivAt (fun x => ofLp (V x) i) (ofLp (A t) i) t := by
    simpa using (hasDerivAt_pi.mp
      ((PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (V t)).comp_hasDerivAt t hV)) i
  have hcross : HasDerivAt
      (fun x => crossProduct (ofLp (T x)) (ofLp (V x)))
      (crossProduct (ofLp (T t)) (ofLp (A t))) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · convert ((hTi 1).mul (hVi 2)).sub ((hTi 2).mul (hVi 1)) using 1
      · ext x
        rfl
      · simp [cross_apply]
        ring
    · convert ((hTi 2).mul (hVi 0)).sub ((hTi 0).mul (hVi 2)) using 1
      · ext x
        rfl
      · simp [cross_apply]
        ring
    · convert ((hTi 0).mul (hVi 1)).sub ((hTi 1).mul (hVi 0)) using 1
      · ext x
        rfl
      · simp [cross_apply]
        ring
  have htoLp := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (crossProduct (ofLp (T t)) (ofLp (V t)))).comp_hasDerivAt t hcross
  change HasDerivAt
    (fun x => toLp 2 (crossProduct (ofLp (unitTangent r x))
      (ofLp (deriv (unitTangent r) x))))
    (toLp 2 (crossProduct (ofLp (unitTangent r t))
      (ofLp (deriv (deriv (unitTangent r)) t)))) t
  simpa [T, V, A, Function.comp_def] using htoLp

theorem inner_unitTangent_deriv_unitTangent_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (t : ℝ) :
    inner ℝ (unitTangent r t) (deriv (unitTangent r) t) = 0 := by
  have hT : HasDerivAt (unitTangent r) (deriv (unitTangent r) t) t :=
    ((contDiff_unitTangent hknot).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hnorm := hT.norm_sq
  have hconst : (fun x => ‖unitTangent r x‖ ^ 2) = fun _ => (1 : ℝ) := by
    funext x
    rw [norm_unitTangent hknot x]
    norm_num
  have hzero : deriv (fun x => ‖unitTangent r x‖ ^ 2) t = 0 := by
    rw [hconst]
    simp
  have heq := hnorm.deriv
  rw [hzero] at heq
  linarith

theorem tangentBinormalRaw_ne_zero_of_deriv_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {t : ℝ}
    (hderiv : deriv (unitTangent r) t ≠ 0) :
    tangentBinormalRaw r t ≠ 0 := by
  intro hzero
  have hcross : crossProduct (ofLp (unitTangent r t))
      (ofLp (deriv (unitTangent r) t)) = 0 := by
    have := congrArg ofLp hzero
    simpa [tangentBinormalRaw] using this
  have hnotLI : ¬ LinearIndependent ℝ
      ![ofLp (unitTangent r t), ofLp (deriv (unitTangent r) t)] := by
    rwa [← crossProduct_ne_zero_iff_linearIndependent, not_not]
  have hTraw : ofLp (unitTangent r t) ≠ 0 := by
    intro h
    have : unitTangent r t = 0 := by
      apply ofLp_injective
      simpa using h
    have hnorm := norm_unitTangent hknot t
    rw [this, norm_zero] at hnorm
    norm_num at hnorm
  rw [LinearIndependent.pair_iff' hTraw] at hnotLI
  push Not at hnotLI
  obtain ⟨c, hc⟩ := hnotLI
  have hcSpace : c • unitTangent r t = deriv (unitTangent r) t := by
    apply ofLp_injective
    simpa using hc
  have hinner := congrArg (fun w : Space => inner ℝ (unitTangent r t) w) hcSpace
  rw [inner_unitTangent_deriv_unitTangent_eq_zero hknot t,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_unitTangent hknot t] at hinner
  norm_num at hinner
  apply hderiv
  rw [← hcSpace, hinner, zero_smul]

theorem cross_cross_common_left (T V A : Fin 3 → ℝ) :
    crossProduct (crossProduct T V) (crossProduct T A) =
      (A ⬝ᵥ crossProduct T V) • T := by
  ext i
  fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_three] <;> ring

theorem tangentBinormalRaw_deriv_smul_of_triple_eq_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {t : ℝ}
    (hderiv : deriv (unitTangent r) t ≠ 0)
    (htriple : tangentTripleProduct r t = 0) :
    ∃ c : ℝ,
      toLp 2 (crossProduct (ofLp (unitTangent r t))
        (ofLp (deriv (deriv (unitTangent r)) t))) =
          c • tangentBinormalRaw r t := by
  let T := ofLp (unitTangent r t)
  let V := ofLp (deriv (unitTangent r) t)
  let A := ofLp (deriv (deriv (unitTangent r)) t)
  let N := crossProduct T V
  let N' := crossProduct T A
  have hN : N ≠ 0 := by
    intro hzero
    apply tangentBinormalRaw_ne_zero_of_deriv_ne_zero hknot hderiv
    apply ofLp_injective
    simpa [tangentBinormalRaw, N, T, V] using hzero
  have hcross : crossProduct N N' = 0 := by
    rw [cross_cross_common_left]
    have hscalar : A ⬝ᵥ crossProduct T V = 0 := by
      simpa [tangentTripleProduct, tangentBinormalRaw,
        EuclideanSpace.inner_eq_star_dotProduct, star_trivial, T, V, A]
        using htriple
    rw [hscalar, zero_smul]
  have hnotLI : ¬ LinearIndependent ℝ ![N, N'] := by
    rwa [← crossProduct_ne_zero_iff_linearIndependent, not_not]
  rw [LinearIndependent.pair_iff' hN] at hnotLI
  push Not at hnotLI
  obtain ⟨c, hc⟩ := hnotLI
  refine ⟨c, ?_⟩
  apply ofLp_injective
  simpa [tangentBinormalRaw, N, N', T, V, A] using hc.symm

noncomputable def tangentBinormalChart (r : ℝ → Space) (i : Fin 3)
    (t : ℝ) : Space :=
  (ofLp (tangentBinormalRaw r t) i)⁻¹ • tangentBinormalRaw r t

theorem hasDerivAt_tangentBinormalChart_zero_of_triple_eq_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (i : Fin 3) {t : ℝ}
    (hcoord : ofLp (tangentBinormalRaw r t) i ≠ 0)
    (hderiv : deriv (unitTangent r) t ≠ 0)
    (htriple : tangentTripleProduct r t = 0) :
    HasDerivAt (tangentBinormalChart r i) 0 t := by
  obtain ⟨c, hc⟩ := tangentBinormalRaw_deriv_smul_of_triple_eq_zero
    hknot hderiv htriple
  have hraw : HasDerivAt (tangentBinormalRaw r)
      (c • tangentBinormalRaw r t) t := by
    rw [← hc]
    exact hasDerivAt_tangentBinormalRaw hknot t
  have hcoordDeriv : HasDerivAt
      (fun x => ofLp (tangentBinormalRaw r x) i)
      (ofLp (c • tangentBinormalRaw r t) i) t := by
    simpa using (hasDerivAt_pi.mp
      ((PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2
        (tangentBinormalRaw r t)).comp_hasDerivAt t hraw)) i
  have hinv := hcoordDeriv.inv hcoord
  have hchart := hinv.smul hraw
  change HasDerivAt
    (fun x => (ofLp (tangentBinormalRaw r x) i)⁻¹ •
      tangentBinormalRaw r x) 0 t
  apply hchart.congr_deriv
  ext j
  simp
  field_simp [hcoord]
  ring

theorem exists_deriv_unitTangent_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    ∃ t : ℝ, deriv (unitTangent r) t ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hconst : ∀ x y : ℝ, unitTangent r x = unitTangent r y :=
    is_const_of_deriv_eq_zero
      ((contDiff_unitTangent hknot).differentiable (by simp)) hnone
  let u := unitTangent r 0
  have hdir : ∀ t : ℝ, directionalUnitTangent r u t = 1 := by
    intro t
    rw [directionalUnitTangent, hconst t 0,
      real_inner_self_eq_norm_sq, norm_unitTangent hknot 0]
    norm_num
  have hmono : StrictMonoOn (height r u) (Icc (0 : ℝ) period) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) period)
      (continuous_height hknot u).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t, hdir]
    simpa using speed_pos hknot t
  have hlt := hmono (left_mem_Icc.mpr period_pos.le)
    (right_mem_Icc.mpr period_pos.le) period_pos
  have hperiod : height r u period = height r u 0 := by
    simpa using periodic_height hknot u 0
  rw [hperiod] at hlt
  exact (lt_irrefl _ hlt)

theorem exists_unit_directionalUnitTangent_eq_zero_of_triple_eq_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (htriple : ∀ t : ℝ, tangentTripleProduct r t = 0) :
    ∃ u : Space, ‖u‖ = 1 ∧ directionalUnitTangent r u = 0 := by
  obtain ⟨t₀, ht₀⟩ := exists_deriv_unitTangent_ne_zero hknot
  have hraw₀ : tangentBinormalRaw r t₀ ≠ 0 :=
    tangentBinormalRaw_ne_zero_of_deriv_ne_zero hknot ht₀
  have hcoordExists : ∃ i : Fin 3,
      ofLp (tangentBinormalRaw r t₀) i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hraw₀
    apply ofLp_injective
    ext i
    simpa using hnone i
  obtain ⟨i, hi⟩ := hcoordExists
  let U : Set ℝ := {t | ofLp (tangentBinormalRaw r t) i ≠ 0}
  have hcoordCont : Continuous (fun t => ofLp (tangentBinormalRaw r t) i) :=
    (contDiff_euclidean.mp (contDiff_tangentBinormalRaw hknot) i).continuous
  have hUopen : IsOpen U := by
    exact isOpen_ne.preimage hcoordCont
  have ht₀U : t₀ ∈ U := hi
  obtain ⟨a, b, ht₀ab, habU⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hUopen.mem_nhds ht₀U)
  have hchartDeriv : ∀ t ∈ Ioo a b,
      HasDerivAt (tangentBinormalChart r i) 0 t := by
    intro t ht
    have hcoord : ofLp (tangentBinormalRaw r t) i ≠ 0 := habU ht
    have hderiv : deriv (unitTangent r) t ≠ 0 := by
      intro hzero
      apply hcoord
      simp [tangentBinormalRaw, hzero]
    exact hasDerivAt_tangentBinormalChart_zero_of_triple_eq_zero
      hknot i hcoord hderiv (htriple t)
  have hchartDiff : DifferentiableOn ℝ (tangentBinormalChart r i) (Ioo a b) := by
    intro t ht
    exact (hchartDeriv t ht).differentiableAt.differentiableWithinAt
  have hchartZero : EqOn (deriv (tangentBinormalChart r i)) 0 (Ioo a b) := by
    intro t ht
    exact (hchartDeriv t ht).deriv
  have hchartConst : ∀ t ∈ Ioo a b,
      tangentBinormalChart r i t = tangentBinormalChart r i t₀ := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hchartDiff hchartZero ht ht₀ab
  let u₀ := tangentBinormalChart r i t₀
  have hu₀ : u₀ ≠ 0 := by
    dsimp [u₀, tangentBinormalChart]
    exact smul_ne_zero (inv_ne_zero hi) hraw₀
  let u := normalizedDirection u₀
  have hu : ‖u‖ = 1 := norm_normalizedDirection hu₀
  have hlocal : ∀ t ∈ Ioo a b, directionalUnitTangent r u t = 0 := by
    intro t ht
    have horth : inner ℝ u₀ (unitTangent r t) = 0 := by
      dsimp [u₀]
      rw [← hchartConst t ht]
      simp [tangentBinormalChart, real_inner_smul_left,
        inner_tangentBinormalRaw_unitTangent]
    simp [u, normalizedDirection, directionalUnitTangent,
      real_inner_smul_left, horth]
  have hevent : directionalUnitTangent r u =ᶠ[nhds t₀] 0 := by
    filter_upwards [Ioo_mem_nhds ht₀ab.1 ht₀ab.2] with t ht
    exact hlocal t ht
  have hglobal : directionalUnitTangent r u = 0 :=
    (contDiff_directionalUnitTangent hknot u).analyticOnNhd.eq_of_eventuallyEq
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ))).analyticOnNhd
      hevent
  exact ⟨u, hu, hglobal⟩

theorem isUnknotted_of_tangentTripleProduct_eq_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (htriple : ∀ t : ℝ, tangentTripleProduct r t = 0) :
    IsUnknotted r := by
  obtain ⟨u, hu, hzero⟩ :=
    exists_unit_directionalUnitTangent_eq_zero_of_triple_eq_zero hknot htriple
  apply isUnknotted_of_not_hasFourAlternatingSigns hknot hu
  simp [HasFourAlternatingSigns, hzero]

theorem periodic_deriv_deriv_unitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    Function.Periodic (deriv (deriv (unitTangent r))) period :=
  periodic_deriv (periodic_deriv (periodic_unitTangent hknot))

theorem periodic_tangentBinormalRaw {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    Function.Periodic (tangentBinormalRaw r) period := by
  intro t
  simp [tangentBinormalRaw, periodic_unitTangent hknot t,
    periodic_deriv (periodic_unitTangent hknot) t]

theorem periodic_tangentTripleProduct {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    Function.Periodic (tangentTripleProduct r) period := by
  intro t
  simp [tangentTripleProduct, periodic_tangentBinormalRaw hknot t,
    periodic_deriv_deriv_unitTangent hknot t]

theorem exists_mem_Ioo_tangentTripleProduct_ne_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hne : ¬ ∀ t : ℝ, tangentTripleProduct r t = 0) :
    ∃ t ∈ Ioo (0 : ℝ) period, tangentTripleProduct r t ≠ 0 := by
  push Not at hne
  obtain ⟨t, ht⟩ := hne
  obtain ⟨s, hs, hst⟩ :=
    (periodic_tangentTripleProduct hknot).exists_mem_Ico₀ period_pos t
  have hsne : tangentTripleProduct r s ≠ 0 := by
    rw [← hst]
    exact ht
  rcases hs.1.eq_or_lt with rfl | hspos
  · rcases lt_or_gt_of_ne hsne with hneg | hpos
    · obtain ⟨z, hz, hzne⟩ := exists_right_lt_zero
        (contDiff_tangentTripleProduct hknot).continuous.continuousAt
        hneg period_pos
      exact ⟨z, hz, hzne.ne⟩
    · obtain ⟨z, hz, hzne⟩ := exists_right_pos
        (contDiff_tangentTripleProduct hknot).continuous.continuousAt
        hpos period_pos
      exact ⟨z, hz, hzne.ne'⟩
  · exact ⟨s, ⟨hspos, hs.2⟩, hsne⟩

theorem hasDerivAt_deriv_directionalUnitTangent
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) (t : ℝ) :
    HasDerivAt (deriv (directionalUnitTangent r u))
      (inner ℝ u (deriv (deriv (unitTangent r)) t)) t := by
  have heq : deriv (directionalUnitTangent r u) =
      fun x => inner ℝ u (deriv (unitTangent r) x) := by
    funext x
    exact (hasDerivAt_directionalUnitTangent hknot u x).deriv
  rw [heq]
  have hV : HasDerivAt (deriv (unitTangent r))
      (deriv (deriv (unitTangent r)) t) t :=
    ((contDiff_deriv_unitTangent hknot).differentiable
      (by simp)).differentiableAt.hasDerivAt
  exact (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t hV

theorem deriv_deriv_directionalUnitTangent_tangentBinormal_ne_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {t : ℝ}
    (htriple : tangentTripleProduct r t ≠ 0) :
    deriv (deriv (directionalUnitTangent r (tangentBinormal r t))) t ≠ 0 := by
  rw [(hasDerivAt_deriv_directionalUnitTangent hknot
    (tangentBinormal r t) t).deriv]
  have hraw := tangentBinormalRaw_ne_zero_of_triple_ne_zero htriple
  simp only [tangentBinormal, normalizedDirection, real_inner_smul_left]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hraw)) htriple

theorem exists_same_sign_around_quadratic_zero
    {f : ℝ → ℝ} {L t R : ℝ} (hf : ContDiff ℝ ⊤ f)
    (hLt : L < t) (htR : t < R) (hf0 : f t = 0)
    (hdf0 : deriv f t = 0) (hddf : deriv (deriv f) t ≠ 0) :
    ∃ x y : ℝ, L < x ∧ x < t ∧ t < y ∧ y < R ∧ 0 < f x * f y := by
  have hpunct : ∀ᶠ z in nhdsWithin t ({t}ᶜ : Set ℝ), f z ≠ 0 := by
    rcases hf.contDiffAt.analyticAt.eventually_eq_zero_or_eventually_ne_zero with
      heq | hne
    · exfalso
      have heq' : f =ᶠ[nhds t] fun _ => (0 : ℝ) := heq
      have hsecond := heq'.deriv.deriv_eq
      simp at hsecond
      exact hddf hsecond
    · exact hne
  rcases lt_or_gt_of_ne hddf with hneg | hpos
  · have hlocal := isLocalMax_of_deriv_deriv_neg hneg hdf0 hf.continuous.continuousAt
    have hleft : ∀ᶠ x in nhdsWithin t (Iio t),
        f x ≠ 0 ∧ f x ≤ 0 ∧ L < x ∧ x < t := by
      filter_upwards [hpunct.filter_mono (nhdsLT_le_nhdsNE t),
        hlocal.filter_mono nhdsWithin_le_nhds,
        (eventually_gt_nhds hLt).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with x hxne hxle hLx hxt
      exact ⟨hxne, by simpa [hf0] using hxle, hLx, hxt⟩
    have hright : ∀ᶠ y in nhdsWithin t (Ioi t),
        f y ≠ 0 ∧ f y ≤ 0 ∧ t < y ∧ y < R := by
      filter_upwards [hpunct.filter_mono (nhdsGT_le_nhdsNE t),
        hlocal.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin,
        (eventually_lt_nhds htR).filter_mono nhdsWithin_le_nhds]
        with y hyne hyle hty hyR
      exact ⟨hyne, by simpa [hf0] using hyle, hty, hyR⟩
    obtain ⟨x, hxne, hxle, hLx, hxt⟩ := hleft.exists
    obtain ⟨y, hyne, hyle, hty, hyR⟩ := hright.exists
    exact ⟨x, y, hLx, hxt, hty, hyR,
      mul_pos_of_neg_of_neg (lt_of_le_of_ne hxle hxne)
        (lt_of_le_of_ne hyle hyne)⟩
  · have hlocal := isLocalMin_of_deriv_deriv_pos hpos hdf0 hf.continuous.continuousAt
    have hleft : ∀ᶠ x in nhdsWithin t (Iio t),
        f x ≠ 0 ∧ 0 ≤ f x ∧ L < x ∧ x < t := by
      filter_upwards [hpunct.filter_mono (nhdsLT_le_nhdsNE t),
        hlocal.filter_mono nhdsWithin_le_nhds,
        (eventually_gt_nhds hLt).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with x hxne hxge hLx hxt
      exact ⟨hxne, by simpa [hf0] using hxge, hLx, hxt⟩
    have hright : ∀ᶠ y in nhdsWithin t (Ioi t),
        f y ≠ 0 ∧ 0 ≤ f y ∧ t < y ∧ y < R := by
      filter_upwards [hpunct.filter_mono (nhdsGT_le_nhdsNE t),
        hlocal.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin,
        (eventually_lt_nhds htR).filter_mono nhdsWithin_le_nhds]
        with y hyne hyge hty hyR
      exact ⟨hyne, by simpa [hf0] using hyge, hty, hyR⟩
    obtain ⟨x, hxne, hxge, hLx, hxt⟩ := hleft.exists
    obtain ⟨y, hyne, hyge, hty, hyR⟩ := hright.exists
    exact ⟨x, y, hLx, hxt, hty, hyR,
      mul_pos (lt_of_le_of_ne hxge (Ne.symm hxne))
        (lt_of_le_of_ne hyge (Ne.symm hyne))⟩

def HasSixAlternatingSigns (r : ℝ → Space) (u : Space) : Prop :=
  ∃ t₀ t₁ t₂ t₃ t₄ t₅ : ℝ,
    0 < t₀ ∧ t₀ < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧
    t₃ < t₄ ∧ t₄ < t₅ ∧ t₅ < period ∧
    directionalUnitTangent r u t₀ * directionalUnitTangent r u t₁ < 0 ∧
    directionalUnitTangent r u t₁ * directionalUnitTangent r u t₂ < 0 ∧
    directionalUnitTangent r u t₂ * directionalUnitTangent r u t₃ < 0 ∧
    directionalUnitTangent r u t₃ * directionalUnitTangent r u t₄ < 0 ∧
    directionalUnitTangent r u t₄ * directionalUnitTangent r u t₅ < 0 ∧
    directionalUnitTangent r u t₅ * directionalUnitTangent r u t₀ < 0

def BirthGap (q₀ q₁ q₂ q₃ x y : ℝ) : Prop :=
  (0 < x ∧ y < q₀) ∨
  (q₀ < x ∧ y < q₁) ∨
  (q₁ < x ∧ y < q₂) ∨
  (q₂ < x ∧ y < q₃) ∨
  (q₃ < x ∧ y < period)

theorem mul_pos_trans {a b c : ℝ} (hab : 0 < a * b) (hbc : 0 < b * c) :
    0 < a * c := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases mul_pos_iff.mp hbc with ⟨hb', hc⟩ | ⟨hb', hc⟩
  · exact mul_pos ha hc
  · linarith
  · linarith
  · exact mul_pos_of_neg_of_neg ha hc

theorem mul_neg_trans_right {a b c : ℝ}
    (hab : 0 < a * b) (hbc : b * c < 0) : a * c < 0 := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases mul_neg_iff.mp hbc with ⟨hb', hc⟩ | ⟨hb', hc⟩
  · exact mul_neg_of_pos_of_neg ha hc
  · linarith
  · linarith
  · exact mul_neg_of_neg_of_pos ha hc

theorem mul_pos_of_two_mul_neg {a b c : ℝ}
    (hab : a * b < 0) (hbc : b * c < 0) : 0 < a * c := by
  rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases mul_neg_iff.mp hbc with ⟨hb', hc⟩ | ⟨hb', hc⟩
  · linarith
  · exact mul_pos ha hc
  · exact mul_pos_of_neg_of_neg ha hc
  · linarith

theorem alternating_insert_signs {a b x z y : ℝ}
    (hab : a * b < 0) (hxy : 0 < x * y)
    (hxz : x * z < 0) (_hzy : z * y < 0) :
    (a * x < 0 ∧ z * b < 0) ∨ (a * z < 0 ∧ y * b < 0) := by
  by_cases hax : 0 < a * x
  · right
    have haz : a * z < 0 := mul_neg_trans_right hax hxz
    have hay : 0 < a * y := mul_pos_trans hax hxy
    have hya : 0 < y * a := by simpa [mul_comm] using hay
    exact ⟨haz, mul_neg_trans_right hya hab⟩
  · left
    have ha : a ≠ 0 := left_ne_zero_of_mul hab.ne
    have hx : x ≠ 0 := left_ne_zero_of_mul hxy.ne'
    have haxneg : a * x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hax) (mul_ne_zero ha hx)
    have haz : 0 < a * z := mul_pos_of_two_mul_neg haxneg hxz
    have hza : 0 < z * a := by simpa [mul_comm] using haz
    exact ⟨haxneg, mul_neg_trans_right hza hab⟩

theorem hasSixAlternatingSigns_of_four_birth
    {r : ℝ → Space} {u : Space}
    {q₀ q₁ q₂ q₃ x z y : ℝ}
    (hq₀ : 0 < q₀) (hq₀₁ : q₀ < q₁) (hq₁₂ : q₁ < q₂)
    (hq₂₃ : q₂ < q₃) (hq₃ : q₃ < period)
    (h₀₁ : directionalUnitTangent r u q₀ * directionalUnitTangent r u q₁ < 0)
    (h₁₂ : directionalUnitTangent r u q₁ * directionalUnitTangent r u q₂ < 0)
    (h₂₃ : directionalUnitTangent r u q₂ * directionalUnitTangent r u q₃ < 0)
    (h₃₀ : directionalUnitTangent r u q₃ * directionalUnitTangent r u q₀ < 0)
    (hxzOrder : x < z) (hzyOrder : z < y)
    (hgap : BirthGap q₀ q₁ q₂ q₃ x y)
    (hxy : 0 < directionalUnitTangent r u x * directionalUnitTangent r u y)
    (hxz : directionalUnitTangent r u x * directionalUnitTangent r u z < 0)
    (hzy : directionalUnitTangent r u z * directionalUnitTangent r u y < 0) :
    HasSixAlternatingSigns r u := by
  rcases hgap with hgap | hgap | hgap | hgap | hgap
  · rcases alternating_insert_signs h₃₀ hxy hxz hzy with h | h
    · exact ⟨x, z, q₀, q₁, q₂, q₃, hgap.1, hxzOrder,
        hzyOrder.trans hgap.2, hq₀₁, hq₁₂, hq₂₃, hq₃,
        hxz, h.2, h₀₁, h₁₂, h₂₃, h.1⟩
    · exact ⟨z, y, q₀, q₁, q₂, q₃,
        hgap.1.trans hxzOrder, hzyOrder, hgap.2, hq₀₁,
        hq₁₂, hq₂₃, hq₃, hzy, h.2, h₀₁, h₁₂, h₂₃, h.1⟩
  · rcases alternating_insert_signs h₀₁ hxy hxz hzy with h | h
    · exact ⟨q₀, x, z, q₁, q₂, q₃, hq₀, hgap.1, hxzOrder,
        hzyOrder.trans hgap.2, hq₁₂, hq₂₃, hq₃,
        h.1, hxz, h.2, h₁₂, h₂₃, h₃₀⟩
    · exact ⟨q₀, z, y, q₁, q₂, q₃, hq₀,
        hgap.1.trans hxzOrder, hzyOrder, hgap.2, hq₁₂, hq₂₃,
        hq₃, h.1, hzy, h.2, h₁₂, h₂₃, h₃₀⟩
  · rcases alternating_insert_signs h₁₂ hxy hxz hzy with h | h
    · exact ⟨q₀, q₁, x, z, q₂, q₃, hq₀, hq₀₁,
        hgap.1, hxzOrder, hzyOrder.trans hgap.2, hq₂₃, hq₃,
        h₀₁, h.1, hxz, h.2, h₂₃, h₃₀⟩
    · exact ⟨q₀, q₁, z, y, q₂, q₃, hq₀, hq₀₁,
        hgap.1.trans hxzOrder, hzyOrder, hgap.2, hq₂₃, hq₃,
        h₀₁, h.1, hzy, h.2, h₂₃, h₃₀⟩
  · rcases alternating_insert_signs h₂₃ hxy hxz hzy with h | h
    · exact ⟨q₀, q₁, q₂, x, z, q₃, hq₀, hq₀₁,
        hq₁₂, hgap.1, hxzOrder, hzyOrder.trans hgap.2, hq₃,
        h₀₁, h₁₂, h.1, hxz, h.2, h₃₀⟩
    · exact ⟨q₀, q₁, q₂, z, y, q₃, hq₀, hq₀₁,
        hq₁₂, hgap.1.trans hxzOrder, hzyOrder, hgap.2, hq₃,
        h₀₁, h₁₂, h.1, hzy, h.2, h₃₀⟩
  · rcases alternating_insert_signs h₃₀ hxy hxz hzy with h | h
    · exact ⟨q₀, q₁, q₂, q₃, x, z, hq₀, hq₀₁,
        hq₁₂, hq₂₃, hgap.1, hxzOrder, hzyOrder.trans hgap.2,
        h₀₁, h₁₂, h₂₃, h.1, hxz, h.2⟩
    · exact ⟨q₀, q₁, q₂, q₃, z, y, hq₀, hq₀₁,
        hq₁₂, hq₂₃, hgap.1.trans hxzOrder, hzyOrder, hgap.2,
        h₀₁, h₁₂, h₂₃, h.1, hzy, h.2⟩

theorem exists_same_sign_in_birth_gap
    {f : ℝ → ℝ} {q₀ q₁ q₂ q₃ z : ℝ}
    (hf : ContDiff ℝ ⊤ f)
    (_hq₀ : 0 < q₀) (_hq₀₁ : q₀ < q₁) (_hq₁₂ : q₁ < q₂)
    (_hq₂₃ : q₂ < q₃) (_hq₃ : q₃ < period)
    (hz : z ∈ Ioo (0 : ℝ) period) (hfz : f z = 0)
    (hfq₀ : f q₀ ≠ 0) (hfq₁ : f q₁ ≠ 0)
    (hfq₂ : f q₂ ≠ 0) (hfq₃ : f q₃ ≠ 0)
    (hdfz : deriv f z = 0) (hddfz : deriv (deriv f) z ≠ 0) :
    ∃ x y : ℝ, x < z ∧ z < y ∧ BirthGap q₀ q₁ q₂ q₃ x y ∧
      0 < f x * f y := by
  have hzq₀ : z ≠ q₀ := by intro h; subst z; exact hfq₀ hfz
  have hzq₁ : z ≠ q₁ := by intro h; subst z; exact hfq₁ hfz
  have hzq₂ : z ≠ q₂ := by intro h; subst z; exact hfq₂ hfz
  have hzq₃ : z ≠ q₃ := by intro h; subst z; exact hfq₃ hfz
  by_cases hz0 : z < q₀
  · obtain ⟨x, y, hx0, hxz, hzy, hyq, hxy⟩ :=
      exists_same_sign_around_quadratic_zero hf hz.1 hz0 hfz hdfz hddfz
    exact ⟨x, y, hxz, hzy, Or.inl ⟨hx0, hyq⟩, hxy⟩
  have hq₀z : q₀ < z := lt_of_le_of_ne (le_of_not_gt hz0) (Ne.symm hzq₀)
  by_cases hz1 : z < q₁
  · obtain ⟨x, y, hxq, hxz, hzy, hyq, hxy⟩ :=
      exists_same_sign_around_quadratic_zero hf hq₀z hz1 hfz hdfz hddfz
    exact ⟨x, y, hxz, hzy, Or.inr (Or.inl ⟨hxq, hyq⟩), hxy⟩
  have hq₁z : q₁ < z := lt_of_le_of_ne (le_of_not_gt hz1) (Ne.symm hzq₁)
  by_cases hz2 : z < q₂
  · obtain ⟨x, y, hxq, hxz, hzy, hyq, hxy⟩ :=
      exists_same_sign_around_quadratic_zero hf hq₁z hz2 hfz hdfz hddfz
    exact ⟨x, y, hxz, hzy, Or.inr (Or.inr (Or.inl ⟨hxq, hyq⟩)), hxy⟩
  have hq₂z : q₂ < z := lt_of_le_of_ne (le_of_not_gt hz2) (Ne.symm hzq₂)
  by_cases hz3 : z < q₃
  · obtain ⟨x, y, hxq, hxz, hzy, hyq, hxy⟩ :=
      exists_same_sign_around_quadratic_zero hf hq₂z hz3 hfz hdfz hddfz
    exact ⟨x, y, hxz, hzy,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨hxq, hyq⟩))), hxy⟩
  have hq₃z : q₃ < z := lt_of_le_of_ne (le_of_not_gt hz3) (Ne.symm hzq₃)
  obtain ⟨x, y, hxq, hxz, hzy, hyP, hxy⟩ :=
    exists_same_sign_around_quadratic_zero hf hq₃z hz.2 hfz hdfz hddfz
  exact ⟨x, y, hxz, hzy,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨hxq, hyP⟩))), hxy⟩

noncomputable def tangentDirectionPerturb (r : ℝ → Space)
    (u : Space) (z e : ℝ) : Space :=
  u + e • unitTangent r z

theorem directionalUnitTangent_tangentDirectionPerturb
    (r : ℝ → Space) (u : Space) (z e t : ℝ) :
    directionalUnitTangent r (tangentDirectionPerturb r u z e) t =
      directionalUnitTangent r u t +
        e * inner ℝ (unitTangent r z) (unitTangent r t) := by
  simp [tangentDirectionPerturb, directionalUnitTangent,
    inner_add_left, real_inner_smul_left]

theorem exists_hasSixAlternatingSigns_of_triple_ne_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hnot : ¬ IsUnknotted r) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) period)
    (htriple : tangentTripleProduct r z ≠ 0) :
    ∃ v : Space, HasSixAlternatingSigns r v := by
  let u := tangentBinormal r z
  have hu : ‖u‖ = 1 := norm_tangentBinormal_of_triple_ne_zero htriple
  have hfour : HasFourAlternatingSigns r u := by
    by_contra hno
    exact hnot (isUnknotted_of_not_hasFourAlternatingSigns hknot hu hno)
  rcases hfour with ⟨q₀, q₁, q₂, q₃, hq₀, hq₀₁, hq₁₂, hq₂₃,
    hq₃, h₀₁, h₁₂, h₂₃, h₃₀⟩
  let f := directionalUnitTangent r u
  have hf : ContDiff ℝ ⊤ f := contDiff_directionalUnitTangent hknot u
  have hfz : f z = 0 := by
    exact directionalUnitTangent_tangentBinormal z
  have hdfz : deriv f z = 0 := by
    rw [(hasDerivAt_directionalUnitTangent hknot u z).deriv]
    exact inner_tangentBinormal_deriv_unitTangent z
  have hddfz : deriv (deriv f) z ≠ 0 := by
    exact deriv_deriv_directionalUnitTangent_tangentBinormal_ne_zero hknot htriple
  have hfq₀ : f q₀ ≠ 0 := left_ne_zero_of_mul h₀₁.ne
  have hfq₁ : f q₁ ≠ 0 := right_ne_zero_of_mul h₀₁.ne
  have hfq₂ : f q₂ ≠ 0 := right_ne_zero_of_mul h₁₂.ne
  have hfq₃ : f q₃ ≠ 0 := right_ne_zero_of_mul h₂₃.ne
  obtain ⟨x, y, hxz, hzy, hgap, hxy⟩ := exists_same_sign_in_birth_gap
    hf hq₀ hq₀₁ hq₁₂ hq₂₃ hq₃ hz hfz hfq₀ hfq₁ hfq₂ hfq₃
      hdfz hddfz
  let v : ℝ → Space := fun e => tangentDirectionPerturb r u z e
  let g : ℝ → ℝ → ℝ := fun e t => directionalUnitTangent r (v e) t
  have hg (e t : ℝ) : g e t = f t +
      e * inner ℝ (unitTangent r z) (unitTangent r t) := by
    exact directionalUnitTangent_tangentDirectionPerturb r u z e t
  have hgcont (t : ℝ) : Continuous (fun e => g e t) := by
    rw [show (fun e => g e t) = fun e =>
      f t + e * inner ℝ (unitTangent r z) (unitTangent r t) by
        funext e
        exact hg e t]
    fun_prop
  have eventually_neg {a b : ℝ} (hab : f a * f b < 0) :
      ∀ᶠ e in nhds (0 : ℝ), g e a * g e b < 0 := by
    have hcont := (hgcont a).mul (hgcont b)
    apply hcont.continuousAt.eventually_lt continuousAt_const
    simpa [hg] using hab
  have eventually_same (t : ℝ) (ht : f t ≠ 0) :
      ∀ᶠ e in nhds (0 : ℝ), 0 < f t * g e t := by
    have hcont :=
      (continuous_const : Continuous (fun _ : ℝ => f t)).mul (hgcont t)
    apply continuousAt_const.eventually_lt hcont.continuousAt
    simpa [hg] using ht
  have hxne : f x ≠ 0 := left_ne_zero_of_mul hxy.ne'
  have hyne : f y ≠ 0 := right_ne_zero_of_mul hxy.ne'
  have hgood : ∀ᶠ e in nhds (0 : ℝ),
      g e q₀ * g e q₁ < 0 ∧ g e q₁ * g e q₂ < 0 ∧
      g e q₂ * g e q₃ < 0 ∧ g e q₃ * g e q₀ < 0 ∧
      0 < f x * g e x ∧ 0 < f y * g e y := by
    filter_upwards [eventually_neg h₀₁, eventually_neg h₁₂,
      eventually_neg h₂₃, eventually_neg h₃₀,
      eventually_same x hxne, eventually_same y hyne]
      with e he₀₁ he₁₂ he₂₃ he₃₀ hex hey
    exact ⟨he₀₁, he₁₂, he₂₃, he₃₀, hex, hey⟩
  obtain ⟨delta, hdelta, hdeltaGood⟩ := Metric.eventually_nhds_iff.mp hgood
  have hgz (e : ℝ) : g e z = e := by
    rw [hg, hfz, real_inner_self_eq_norm_sq, norm_unitTangent hknot z]
    ring
  rcases mul_pos_iff.mp hxy with ⟨hfx, hfy⟩ | ⟨hfx, hfy⟩
  · let e := -delta / 2
    have heNeg : e < 0 := by dsimp [e]; linarith
    have heClose : dist e (0 : ℝ) < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_neg heNeg]
      dsimp [e]
      linarith
    obtain ⟨he₀₁, he₁₂, he₂₃, he₃₀, hex, hey⟩ := hdeltaGood heClose
    have hgx : 0 < g e x := pos_of_mul_pos_right hex hfx.le
    have hgy : 0 < g e y := pos_of_mul_pos_right hey hfy.le
    have hxze : g e x * g e z < 0 := by
      rw [hgz]
      exact mul_neg_of_pos_of_neg hgx heNeg
    have hzye : g e z * g e y < 0 := by
      rw [hgz]
      exact mul_neg_of_neg_of_pos heNeg hgy
    refine ⟨v e, ?_⟩
    exact hasSixAlternatingSigns_of_four_birth hq₀ hq₀₁ hq₁₂ hq₂₃ hq₃
      he₀₁ he₁₂ he₂₃ he₃₀ hxz hzy hgap
      (mul_pos hgx hgy) hxze hzye
  · let e := delta / 2
    have hePos : 0 < e := by dsimp [e]; linarith
    have heClose : dist e (0 : ℝ) < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hePos]
      dsimp [e]
      linarith
    obtain ⟨he₀₁, he₁₂, he₂₃, he₃₀, hex, hey⟩ := hdeltaGood heClose
    have hgx : g e x < 0 := neg_of_mul_pos_right hex hfx.le
    have hgy : g e y < 0 := neg_of_mul_pos_right hey hfy.le
    have hxze : g e x * g e z < 0 := by
      rw [hgz]
      exact mul_neg_of_neg_of_pos hgx hePos
    have hzye : g e z * g e y < 0 := by
      rw [hgz]
      exact mul_neg_of_pos_of_neg hePos hgy
    refine ⟨v e, ?_⟩
    exact hasSixAlternatingSigns_of_four_birth hq₀ hq₀₁ hq₁₂ hq₂₃ hq₃
      he₀₁ he₁₂ he₂₃ he₃₀ hxz hzy hgap
      (mul_pos_of_neg_of_neg hgx hgy) hxze hzye

def HasFourAlternatingDyadicSignsAt (r : ℝ → Space) (n : ℕ)
    (u : Space) : Prop :=
  ∃ i₀ i₁ i₂ i₃ : ℕ,
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < 2 ^ (n + 1) ∧
    inner ℝ u (dyadicTangentSample r n i₀) *
      inner ℝ u (dyadicTangentSample r n i₁) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₁) *
      inner ℝ u (dyadicTangentSample r n i₂) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₂) *
      inner ℝ u (dyadicTangentSample r n i₃) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₃) *
      inner ℝ u (dyadicTangentSample r n i₀) < 0

def HasSixAlternatingDyadicSignsAt (r : ℝ → Space) (n : ℕ)
    (u : Space) : Prop :=
  ∃ i₀ i₁ i₂ i₃ i₄ i₅ : ℕ,
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧
    i₄ < i₅ ∧ i₅ < 2 ^ (n + 1) ∧
    inner ℝ u (dyadicTangentSample r n i₀) *
      inner ℝ u (dyadicTangentSample r n i₁) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₁) *
      inner ℝ u (dyadicTangentSample r n i₂) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₂) *
      inner ℝ u (dyadicTangentSample r n i₃) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₃) *
      inner ℝ u (dyadicTangentSample r n i₄) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₄) *
      inner ℝ u (dyadicTangentSample r n i₅) < 0 ∧
    inner ℝ u (dyadicTangentSample r n i₅) *
      inner ℝ u (dyadicTangentSample r n i₀) < 0

theorem hasFourAlternatingDyadicSigns_iff_exists_at
    (r : ℝ → Space) (u : Space) :
    HasFourAlternatingDyadicSigns r u ↔
      ∃ n, HasFourAlternatingDyadicSignsAt r n u := by
  rfl

theorem HasFourAlternatingDyadicSignsAt.refine
    {r : ℝ → Space} {m n : ℕ} {u : Space}
    (h : HasFourAlternatingDyadicSignsAt r m u) (hmn : m ≤ n) :
    HasFourAlternatingDyadicSignsAt r n u := by
  rcases h with ⟨i₀, i₁, i₂, i₃, hi₀₁, hi₁₂, hi₂₃, hi₃N,
    h₀₁, h₁₂, h₂₃, h₃₀⟩
  let c : ℕ := 2 ^ (n - m)
  let j₀ := c * i₀
  let j₁ := c * i₁
  let j₂ := c * i₂
  let j₃ := c * i₃
  have hc : 0 < c := by dsimp [c]; positivity
  have hj₀₁ : j₀ < j₁ := by
    exact (Nat.mul_lt_mul_left hc).2 hi₀₁
  have hj₁₂ : j₁ < j₂ := by
    exact (Nat.mul_lt_mul_left hc).2 hi₁₂
  have hj₂₃ : j₂ < j₃ := by
    exact (Nat.mul_lt_mul_left hc).2 hi₂₃
  have hpow : c * 2 ^ (m + 1) = 2 ^ (n + 1) := by
    dsimp [c]
    rw [← pow_add]
    congr 1
    omega
  have hj₃N : j₃ < 2 ^ (n + 1) := by
    calc
      j₃ < c * 2 ^ (m + 1) := (Nat.mul_lt_mul_left hc).2 hi₃N
      _ = 2 ^ (n + 1) := hpow
  have hs₀ : dyadicTangentSample r n j₀ = dyadicTangentSample r m i₀ := by
    exact dyadicTangentSample_refine_of_le r hmn
  have hs₁ : dyadicTangentSample r n j₁ = dyadicTangentSample r m i₁ := by
    exact dyadicTangentSample_refine_of_le r hmn
  have hs₂ : dyadicTangentSample r n j₂ = dyadicTangentSample r m i₂ := by
    exact dyadicTangentSample_refine_of_le r hmn
  have hs₃ : dyadicTangentSample r n j₃ = dyadicTangentSample r m i₃ := by
    exact dyadicTangentSample_refine_of_le r hmn
  exact ⟨j₀, j₁, j₂, j₃, hj₀₁, hj₁₂, hj₂₃, hj₃N,
    by simpa [hs₀, hs₁] using h₀₁,
    by simpa [hs₁, hs₂] using h₁₂,
    by simpa [hs₂, hs₃] using h₂₃,
    by simpa [hs₃, hs₀] using h₃₀⟩

theorem HasSixAlternatingDyadicSignsAt.refine
    {r : ℝ → Space} {m n : ℕ} {u : Space}
    (h : HasSixAlternatingDyadicSignsAt r m u) (hmn : m ≤ n) :
    HasSixAlternatingDyadicSignsAt r n u := by
  rcases h with ⟨i₀, i₁, i₂, i₃, i₄, i₅, hi₀₁, hi₁₂, hi₂₃,
    hi₃₄, hi₄₅, hi₅N, h₀₁, h₁₂, h₂₃, h₃₄, h₄₅, h₅₀⟩
  let c : ℕ := 2 ^ (n - m)
  let j₀ := c * i₀
  let j₁ := c * i₁
  let j₂ := c * i₂
  let j₃ := c * i₃
  let j₄ := c * i₄
  let j₅ := c * i₅
  have hc : 0 < c := by dsimp [c]; positivity
  have hpow : c * 2 ^ (m + 1) = 2 ^ (n + 1) := by
    dsimp [c]
    rw [← pow_add]
    congr 1
    omega
  have hs (i : ℕ) : dyadicTangentSample r n (c * i) =
      dyadicTangentSample r m i := dyadicTangentSample_refine_of_le r hmn
  refine ⟨j₀, j₁, j₂, j₃, j₄, j₅,
    (Nat.mul_lt_mul_left hc).2 hi₀₁,
    (Nat.mul_lt_mul_left hc).2 hi₁₂,
    (Nat.mul_lt_mul_left hc).2 hi₂₃,
    (Nat.mul_lt_mul_left hc).2 hi₃₄,
    (Nat.mul_lt_mul_left hc).2 hi₄₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      j₅ < c * 2 ^ (m + 1) := (Nat.mul_lt_mul_left hc).2 hi₅N
      _ = 2 ^ (n + 1) := hpow
  · simpa [j₀, j₁, hs] using h₀₁
  · simpa [j₁, j₂, hs] using h₁₂
  · simpa [j₂, j₃, hs] using h₂₃
  · simpa [j₃, j₄, hs] using h₃₄
  · simpa [j₄, j₅, hs] using h₄₅
  · simpa [j₅, j₀, hs] using h₅₀

theorem exists_level_forall_unit_hasFourAlternatingDyadicSignsAt
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hall : ∀ u : Space, ‖u‖ = 1 → HasFourAlternatingSigns r u) :
    ∃ m : ℕ, ∀ u : Space, ‖u‖ = 1 →
      HasFourAlternatingDyadicSignsAt r m u := by
  classical
  by_contra hnone
  push Not at hnone
  choose u hunorm huno using hnone
  have huSphere : ∀ n, u n ∈ Metric.sphere (0 : Space) 1 := by
    intro n
    simpa [Metric.mem_sphere, dist_eq_norm] using hunorm n
  obtain ⟨v, hvSphere, phi, hphi, hconv⟩ :=
    (isCompact_sphere (0 : Space) 1).tendsto_subseq huSphere
  have hvnorm : ‖v‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hvSphere
  have hvFourDyadic : HasFourAlternatingDyadicSigns r v :=
    hasFourAlternatingDyadicSigns_of_hasFourAlternatingSigns hknot
      (hall v hvnorm)
  rw [hasFourAlternatingDyadicSigns_iff_exists_at] at hvFourDyadic
  obtain ⟨m, i₀, i₁, i₂, i₃, hi₀₁, hi₁₂, hi₂₃, hi₃N,
    h₀₁, h₁₂, h₂₃, h₃₀⟩ := hvFourDyadic
  let x₀ := dyadicTangentSample r m i₀
  let x₁ := dyadicTangentSample r m i₁
  let x₂ := dyadicTangentSample r m i₂
  let x₃ := dyadicTangentSample r m i₃
  have hinner (x : Space) :
      Tendsto (fun k => inner ℝ (u (phi k)) x) atTop
        (nhds (inner ℝ v x)) := by
    have hc : Continuous (fun w : Space => inner ℝ w x) :=
      continuous_id.inner continuous_const
    change Tendsto ((fun w : Space => inner ℝ w x) ∘ (u ∘ phi)) atTop
      (nhds (inner ℝ v x))
    exact hc.continuousAt.tendsto.comp hconv
  have he₀₁ : ∀ᶠ k in atTop,
      inner ℝ (u (phi k)) x₀ * inner ℝ (u (phi k)) x₁ < 0 := by
    exact (tendsto_order.1 ((hinner x₀).mul (hinner x₁))).2 0
      (by simpa [x₀, x₁] using h₀₁)
  have he₁₂ : ∀ᶠ k in atTop,
      inner ℝ (u (phi k)) x₁ * inner ℝ (u (phi k)) x₂ < 0 := by
    exact (tendsto_order.1 ((hinner x₁).mul (hinner x₂))).2 0
      (by simpa [x₁, x₂] using h₁₂)
  have he₂₃ : ∀ᶠ k in atTop,
      inner ℝ (u (phi k)) x₂ * inner ℝ (u (phi k)) x₃ < 0 := by
    exact (tendsto_order.1 ((hinner x₂).mul (hinner x₃))).2 0
      (by simpa [x₂, x₃] using h₂₃)
  have he₃₀ : ∀ᶠ k in atTop,
      inner ℝ (u (phi k)) x₃ * inner ℝ (u (phi k)) x₀ < 0 := by
    exact (tendsto_order.1 ((hinner x₃).mul (hinner x₀))).2 0
      (by simpa [x₃, x₀] using h₃₀)
  have hphiTop : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have hem : ∀ᶠ k in atTop, m ≤ phi k :=
    hphiTop.eventually (eventually_ge_atTop m)
  obtain ⟨k, hk₀₁, hk₁₂, hk₂₃, hk₃₀, hmk⟩ :=
    (he₀₁.and (he₁₂.and (he₂₃.and (he₃₀.and hem)))).exists
  have hat : HasFourAlternatingDyadicSignsAt r m (u (phi k)) :=
    ⟨i₀, i₁, i₂, i₃, hi₀₁, hi₁₂, hi₂₃, hi₃N,
      by simpa [x₀, x₁] using hk₀₁,
      by simpa [x₁, x₂] using hk₁₂,
      by simpa [x₂, x₃] using hk₂₃,
      by simpa [x₃, x₀] using hk₃₀⟩
  exact huno (phi k) (hat.refine hmk)

theorem exists_hasSixAlternatingDyadicSignsAt_of_hasSixAlternatingSigns
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space}
    (h : HasSixAlternatingSigns r u) :
    ∃ n : ℕ, HasSixAlternatingDyadicSignsAt r n u := by
  rcases h with ⟨t₀, t₁, t₂, t₃, t₄, t₅, ht₀, ht₀₁, ht₁₂, ht₂₃,
    ht₃₄, ht₄₅, ht₅P, h₀₁, h₁₂, h₂₃, h₃₄, h₄₅, h₅₀⟩
  have ht₀ne : directionalUnitTangent r u t₀ ≠ 0 :=
    left_ne_zero_of_mul h₀₁.ne
  have ht₁ne : directionalUnitTangent r u t₁ ≠ 0 :=
    right_ne_zero_of_mul h₀₁.ne
  have ht₂ne : directionalUnitTangent r u t₂ ≠ 0 :=
    right_ne_zero_of_mul h₁₂.ne
  have ht₃ne : directionalUnitTangent r u t₃ ≠ 0 :=
    right_ne_zero_of_mul h₂₃.ne
  have ht₄ne : directionalUnitTangent r u t₄ ≠ 0 :=
    right_ne_zero_of_mul h₃₄.ne
  have ht₅ne : directionalUnitTangent r u t₅ ≠ 0 :=
    right_ne_zero_of_mul h₄₅.ne
  let q₀₁ := (t₀ + t₁) / 2
  let q₁₂ := (t₁ + t₂) / 2
  let q₂₃ := (t₂ + t₃) / 2
  let q₃₄ := (t₃ + t₄) / 2
  let q₄₅ := (t₄ + t₅) / 2
  have hq₀₁P : q₀₁ ≤ period := by dsimp [q₀₁]; linarith
  have hq₁₂P : q₁₂ ≤ period := by dsimp [q₁₂]; linarith
  have hq₂₃P : q₂₃ ≤ period := by dsimp [q₂₃]; linarith
  have hq₃₄P : q₃₄ ≤ period := by dsimp [q₃₄]; linarith
  have hq₄₅P : q₄₅ ≤ period := by dsimp [q₄₅]; linarith
  have he₀ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := 0) (t := t₀) (R := q₀₁) le_rfl ht₀
      (by dsimp [q₀₁]; linarith) hq₀₁P ht₀ne
  have he₁ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₀₁) (t := t₁) (R := q₁₂)
      (by dsimp [q₀₁]; linarith) (by dsimp [q₀₁]; linarith)
      (by dsimp [q₁₂]; linarith) hq₁₂P ht₁ne
  have he₂ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₁₂) (t := t₂) (R := q₂₃)
      (by dsimp [q₁₂]; linarith) (by dsimp [q₁₂]; linarith)
      (by dsimp [q₂₃]; linarith) hq₂₃P ht₂ne
  have he₃ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₂₃) (t := t₃) (R := q₃₄)
      (by dsimp [q₂₃]; linarith) (by dsimp [q₂₃]; linarith)
      (by dsimp [q₃₄]; linarith) hq₃₄P ht₃ne
  have he₄ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₃₄) (t := t₄) (R := q₄₅)
      (by dsimp [q₃₄]; linarith) (by dsimp [q₃₄]; linarith)
      (by dsimp [q₄₅]; linarith) hq₄₅P ht₄ne
  have he₅ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₄₅) (t := t₅) (R := period)
      (by dsimp [q₄₅]; linarith) (by dsimp [q₄₅]; linarith)
      ht₅P le_rfl ht₅ne
  obtain ⟨n, hn₀, hn₁, hn₂, hn₃, hn₄, hn₅⟩ :=
    (he₀.and (he₁.and (he₂.and (he₃.and (he₄.and he₅))))).exists
  obtain ⟨i₀, hi₀N, hi₀band, hi₀sign⟩ := hn₀
  obtain ⟨i₁, hi₁N, hi₁band, hi₁sign⟩ := hn₁
  obtain ⟨i₂, hi₂N, hi₂band, hi₂sign⟩ := hn₂
  obtain ⟨i₃, hi₃N, hi₃band, hi₃sign⟩ := hn₃
  obtain ⟨i₄, hi₄N, hi₄band, hi₄sign⟩ := hn₄
  obtain ⟨i₅, hi₅N, hi₅band, hi₅sign⟩ := hn₅
  have hi₀₁ : i₀ < i₁ := dyadic_index_lt_of_parameter_lt
    (hi₀band.2.trans hi₁band.1)
  have hi₁₂ : i₁ < i₂ := dyadic_index_lt_of_parameter_lt
    (hi₁band.2.trans hi₂band.1)
  have hi₂₃ : i₂ < i₃ := dyadic_index_lt_of_parameter_lt
    (hi₂band.2.trans hi₃band.1)
  have hi₃₄ : i₃ < i₄ := dyadic_index_lt_of_parameter_lt
    (hi₃band.2.trans hi₄band.1)
  have hi₄₅ : i₄ < i₅ := dyadic_index_lt_of_parameter_lt
    (hi₄band.2.trans hi₅band.1)
  refine ⟨n, i₀, i₁, i₂, i₃, i₄, i₅, hi₀₁, hi₁₂, hi₂₃,
    hi₃₄, hi₄₅, hi₅N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₀sign hi₁sign h₀₁
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₁sign hi₂sign h₁₂
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₂sign hi₃sign h₂₃
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₃sign hi₄sign h₃₄
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₄sign hi₅sign h₄₅
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₅sign hi₀sign h₅₀

theorem six_le_card_of_six_mem {s : Finset ℕ} {k₀ k₁ k₂ k₃ k₄ k₅ : ℕ}
    (h₀ : k₀ ∈ s) (h₁ : k₁ ∈ s) (h₂ : k₂ ∈ s) (h₃ : k₃ ∈ s)
    (h₄ : k₄ ∈ s) (h₅ : k₅ ∈ s)
    (h₀₁ : k₀ ≠ k₁) (h₀₂ : k₀ ≠ k₂) (h₀₃ : k₀ ≠ k₃)
    (h₀₄ : k₀ ≠ k₄) (h₀₅ : k₀ ≠ k₅) (h₁₂ : k₁ ≠ k₂)
    (h₁₃ : k₁ ≠ k₃) (h₁₄ : k₁ ≠ k₄) (h₁₅ : k₁ ≠ k₅)
    (h₂₃ : k₂ ≠ k₃) (h₂₄ : k₂ ≠ k₄) (h₂₅ : k₂ ≠ k₅)
    (h₃₄ : k₃ ≠ k₄) (h₃₅ : k₃ ≠ k₅) (h₄₅ : k₄ ≠ k₅) :
    6 ≤ s.card := by
  have hsub : ({k₀, k₁, k₂, k₃, k₄, k₅} : Finset ℕ) ⊆ s := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
    · exact h₅
  have hcard := Finset.card_le_card hsub
  have hsix : ({k₀, k₁, k₂, k₃, k₄, k₅} : Finset ℕ).card = 6 := by
    simp [h₀₁, h₀₂, h₀₃, h₀₄, h₀₅, h₁₂, h₁₃, h₁₄,
      h₁₅, h₂₃, h₂₄, h₂₅, h₃₄, h₃₅, h₄₅]
  omega

theorem six_le_card_cyclic_bool_transitions (b : ℕ → Bool) {N : ℕ}
    {i₀ i₁ i₂ i₃ i₄ i₅ : ℕ}
    (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃)
    (hi₃₄ : i₃ < i₄) (hi₄₅ : i₄ < i₅) (hi₅N : i₅ < N)
    (hcycle : b N = b 0)
    (h₀₁ : b i₀ ≠ b i₁) (h₁₂ : b i₁ ≠ b i₂) (h₂₃ : b i₂ ≠ b i₃)
    (h₃₄ : b i₃ ≠ b i₄) (h₄₅ : b i₄ ≠ b i₅) (h₅₀ : b i₅ ≠ b i₀) :
    6 ≤ ((Finset.range N).filter fun i => b i ≠ b (i + 1)).card := by
  obtain ⟨k₀, hi₀k₀, hk₀i₁, hk₀⟩ := exists_bool_transition_between b hi₀₁ h₀₁
  obtain ⟨k₁, hi₁k₁, hk₁i₂, hk₁⟩ := exists_bool_transition_between b hi₁₂ h₁₂
  obtain ⟨k₂, hi₂k₂, hk₂i₃, hk₂⟩ := exists_bool_transition_between b hi₂₃ h₂₃
  obtain ⟨k₃, hi₃k₃, hk₃i₄, hk₃⟩ := exists_bool_transition_between b hi₃₄ h₃₄
  obtain ⟨k₄, hi₄k₄, hk₄i₅, hk₄⟩ := exists_bool_transition_between b hi₄₅ h₄₅
  have hk₀mem : k₀ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (hk₀i₁.trans (hi₁₂.trans (hi₂₃.trans (hi₃₄.trans (hi₄₅.trans hi₅N))))), hk₀⟩
  have hk₁mem : k₁ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (hk₁i₂.trans (hi₂₃.trans (hi₃₄.trans (hi₄₅.trans hi₅N)))), hk₁⟩
  have hk₂mem : k₂ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (hk₂i₃.trans (hi₃₄.trans (hi₄₅.trans hi₅N))), hk₂⟩
  have hk₃mem : k₃ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (hk₃i₄.trans (hi₄₅.trans hi₅N)), hk₃⟩
  have hk₄mem : k₄ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hk₄i₅.trans hi₅N), hk₄⟩
  by_cases h₅N : b i₅ ≠ b N
  · obtain ⟨k₅, hi₅k₅, hk₅N, hk₅⟩ := exists_bool_transition_between b hi₅N h₅N
    have hk₅mem : k₅ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk₅N, hk₅⟩
    apply six_le_card_of_six_mem hk₀mem hk₁mem hk₂mem hk₃mem hk₄mem hk₅mem
    all_goals omega
  · have hNi₅ : b N = b i₅ := (not_ne_iff.mp h₅N).symm
    have h0i₀ : b 0 ≠ b i₀ := by
      rw [← hcycle, hNi₅]
      exact h₅₀
    have hi₀pos : 0 < i₀ := by
      by_contra hi₀zero
      have hi₀eq : i₀ = 0 := Nat.eq_zero_of_not_pos hi₀zero
      subst i₀
      exact h0i₀ rfl
    obtain ⟨k₅, _hzero, hk₅i₀, hk₅⟩ := exists_bool_transition_between b hi₀pos h0i₀
    have hk₅mem : k₅ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (hk₅i₀.trans (hi₀₁.trans (hi₁₂.trans (hi₂₃.trans
          (hi₃₄.trans (hi₄₅.trans hi₅N)))))), hk₅⟩
    apply six_le_card_of_six_mem hk₀mem hk₁mem hk₂mem hk₃mem hk₄mem hk₅mem
    all_goals omega

theorem six_le_dyadicSignChangeIndices_card_of_alternating
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {n : ℕ} {u : Space}
    (hreg : IsDyadicRegular r n u)
    (h : HasSixAlternatingDyadicSignsAt r n u) :
    6 ≤ (dyadicSignChangeIndices r n u).card := by
  rcases h with ⟨i₀, i₁, i₂, i₃, i₄, i₅, hi₀₁, hi₁₂, hi₂₃,
    hi₃₄, hi₄₅, hi₅N, h₀₁, h₁₂, h₂₃, h₃₄, h₄₅, h₅₀⟩
  let N : ℕ := 2 ^ (n + 1)
  let b : ℕ → Bool := fun i => decide (0 < inner ℝ u (dyadicTangentSample r n i))
  have hi₀N : i₀ < N := hi₀₁.trans (hi₁₂.trans (hi₂₃.trans
    (hi₃₄.trans (hi₄₅.trans hi₅N))))
  have hi₁N : i₁ < N := hi₁₂.trans (hi₂₃.trans (hi₃₄.trans (hi₄₅.trans hi₅N)))
  have hi₂N : i₂ < N := hi₂₃.trans (hi₃₄.trans (hi₄₅.trans hi₅N))
  have hi₃N : i₃ < N := hi₃₄.trans (hi₄₅.trans hi₅N)
  have hi₄N : i₄ < N := hi₄₅.trans hi₅N
  have hcycle : b N = b 0 := by
    dsimp [b, N]
    rw [dyadicTangentSample_last hknot n]
  have hb₀₁ : b i₀ ≠ b i₁ :=
    (decide_pos_ne_iff_mul_neg (hreg i₀ (Finset.mem_range.mpr hi₀N))
      (hreg i₁ (Finset.mem_range.mpr hi₁N))).2 h₀₁
  have hb₁₂ : b i₁ ≠ b i₂ :=
    (decide_pos_ne_iff_mul_neg (hreg i₁ (Finset.mem_range.mpr hi₁N))
      (hreg i₂ (Finset.mem_range.mpr hi₂N))).2 h₁₂
  have hb₂₃ : b i₂ ≠ b i₃ :=
    (decide_pos_ne_iff_mul_neg (hreg i₂ (Finset.mem_range.mpr hi₂N))
      (hreg i₃ (Finset.mem_range.mpr hi₃N))).2 h₂₃
  have hb₃₄ : b i₃ ≠ b i₄ :=
    (decide_pos_ne_iff_mul_neg (hreg i₃ (Finset.mem_range.mpr hi₃N))
      (hreg i₄ (Finset.mem_range.mpr hi₄N))).2 h₃₄
  have hb₄₅ : b i₄ ≠ b i₅ :=
    (decide_pos_ne_iff_mul_neg (hreg i₄ (Finset.mem_range.mpr hi₄N))
      (hreg i₅ (Finset.mem_range.mpr hi₅N))).2 h₄₅
  have hb₅₀ : b i₅ ≠ b i₀ :=
    (decide_pos_ne_iff_mul_neg (hreg i₅ (Finset.mem_range.mpr hi₅N))
      (hreg i₀ (Finset.mem_range.mpr hi₀N))).2 h₅₀
  have hsix := six_le_card_cyclic_bool_transitions b hi₀₁ hi₁₂ hi₂₃
    hi₃₄ hi₄₅ hi₅N hcycle hb₀₁ hb₁₂ hb₂₃ hb₃₄ hb₄₅ hb₅₀
  have hfilter : ((Finset.range N).filter fun i => b i ≠ b (i + 1)) =
      dyadicSignChangeIndices r n u := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, dyadicSignChangeIndices]
    constructor
    · rintro ⟨hi, hchange⟩
      refine ⟨hi, ?_⟩
      exact (decide_pos_ne_iff_mul_neg (hreg i (Finset.mem_range.mpr hi))
        (isDyadicRegular_next hknot hreg hi)).1 hchange
    · rintro ⟨hi, hchange⟩
      refine ⟨hi, ?_⟩
      exact (decide_pos_ne_iff_mul_neg (hreg i (Finset.mem_range.mpr hi))
        (isDyadicRegular_next hknot hreg hi)).2 hchange
  rw [hfilter] at hsix
  exact hsix

theorem four_le_dyadicSignChangeIndices_card_of_at
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {n : ℕ} {u : Space}
    (hreg : IsDyadicRegular r n u)
    (h : HasFourAlternatingDyadicSignsAt r n u) :
    4 ≤ (dyadicSignChangeIndices r n u).card := by
  rcases h with ⟨i₀, i₁, i₂, i₃, hi₀₁, hi₁₂, hi₂₃, hi₃N,
    h₀₁, h₁₂, h₂₃, h₃₀⟩
  exact four_le_dyadicSignChangeIndices_card_of_alternating hknot hreg
    hi₀₁ hi₁₂ hi₂₃ hi₃N h₀₁ h₁₂ h₂₃ h₃₀

theorem isOpen_gaussianSeparatingDirections (x y : Space) :
    IsOpen (gaussianSeparatingDirections x y) := by
  unfold gaussianSeparatingDirections
  exact isOpen_lt
    ((continuous_id.inner continuous_const).mul
      (continuous_id.inner continuous_const)) continuous_const

theorem isOpenPosMeasure_stdGaussianSpace :
    (stdGaussian Space).IsOpenPosMeasure := by
  letI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
  rw [← map_pi_eq_stdGaussian]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).isOpenPosMeasure_map
    (toLp_surjective 2)

theorem dyadicSphericalLength_gt_four_pi_of_four_and_six
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (n : ℕ)
    (hfour : ∀ u : Space, ‖u‖ = 1 →
      HasFourAlternatingDyadicSignsAt r n u)
    {v : Space} (hsix : HasSixAlternatingDyadicSignsAt r n v) :
    4 * Real.pi < dyadicSphericalLength r n := by
  classical
  rcases hsix with ⟨i₀, i₁, i₂, i₃, i₄, i₅, hi₀₁, hi₁₂, hi₂₃,
    hi₃₄, hi₄₅, hi₅N, h₀₁, h₁₂, h₂₃, h₃₄, h₄₅, h₅₀⟩
  let x₀ := dyadicTangentSample r n i₀
  let x₁ := dyadicTangentSample r n i₁
  let x₂ := dyadicTangentSample r n i₂
  let x₃ := dyadicTangentSample r n i₃
  let x₄ := dyadicTangentSample r n i₄
  let x₅ := dyadicTangentSample r n i₅
  let O : Set Space :=
    gaussianSeparatingDirections x₀ x₁ ∩
    gaussianSeparatingDirections x₁ x₂ ∩
    gaussianSeparatingDirections x₂ x₃ ∩
    gaussianSeparatingDirections x₃ x₄ ∩
    gaussianSeparatingDirections x₄ x₅ ∩
    gaussianSeparatingDirections x₅ x₀
  have hOopen : IsOpen O := by
    exact (((((isOpen_gaussianSeparatingDirections x₀ x₁).inter
      (isOpen_gaussianSeparatingDirections x₁ x₂)).inter
      (isOpen_gaussianSeparatingDirections x₂ x₃)).inter
      (isOpen_gaussianSeparatingDirections x₃ x₄)).inter
      (isOpen_gaussianSeparatingDirections x₄ x₅)).inter
      (isOpen_gaussianSeparatingDirections x₅ x₀)
  have hvO : v ∈ O := by
    exact ⟨⟨⟨⟨⟨by simpa [x₀, x₁, gaussianSeparatingDirections] using h₀₁,
      by simpa [x₁, x₂, gaussianSeparatingDirections] using h₁₂⟩,
      by simpa [x₂, x₃, gaussianSeparatingDirections] using h₂₃⟩,
      by simpa [x₃, x₄, gaussianSeparatingDirections] using h₃₄⟩,
      by simpa [x₄, x₅, gaussianSeparatingDirections] using h₄₅⟩,
      by simpa [x₅, x₀, gaussianSeparatingDirections] using h₅₀⟩
  letI : (stdGaussian Space).IsOpenPosMeasure := isOpenPosMeasure_stdGaussianSpace
  have hOpos : 0 < stdGaussian Space O :=
    hOopen.measure_pos (stdGaussian Space) ⟨v, hvO⟩
  have haeNe : ∀ᵐ u ∂stdGaussian Space, u ≠ 0 := by
    rw [ae_iff]
    simpa using stdGaussian_singleton_zero hknot
  have haeLower : ∀ᵐ u ∂stdGaussian Space,
      (4 : ℝ≥0∞) + O.indicator (fun _ => (2 : ℝ≥0∞)) u ≤
        dyadicSignChangeCount r n u := by
    filter_upwards [haeNe, ae_isDyadicRegular hknot n] with u hu hreg
    have hregNorm := isDyadicRegular_normalizedDirection r n hu hreg
    have hcardFour := four_le_dyadicSignChangeIndices_card_of_at hknot hregNorm
      (hfour (normalizedDirection u) (norm_normalizedDirection hu))
    have hcountFour : (4 : ℝ≥0∞) ≤
        dyadicSignChangeCount r n (normalizedDirection u) := by
      rw [dyadicSignChangeCount_eq_card]
      exact_mod_cast hcardFour
    rw [dyadicSignChangeCount_normalizedDirection r n hu] at hcountFour
    by_cases huO : u ∈ O
    · have hsixU : HasSixAlternatingDyadicSignsAt r n u := by
        rcases huO with ⟨⟨⟨⟨⟨hu₀₁, hu₁₂⟩, hu₂₃⟩, hu₃₄⟩, hu₄₅⟩, hu₅₀⟩
        exact ⟨i₀, i₁, i₂, i₃, i₄, i₅, hi₀₁, hi₁₂, hi₂₃,
          hi₃₄, hi₄₅, hi₅N,
          by simpa [x₀, x₁, gaussianSeparatingDirections] using hu₀₁,
          by simpa [x₁, x₂, gaussianSeparatingDirections] using hu₁₂,
          by simpa [x₂, x₃, gaussianSeparatingDirections] using hu₂₃,
          by simpa [x₃, x₄, gaussianSeparatingDirections] using hu₃₄,
          by simpa [x₄, x₅, gaussianSeparatingDirections] using hu₄₅,
          by simpa [x₅, x₀, gaussianSeparatingDirections] using hu₅₀⟩
      have hcardSix := six_le_dyadicSignChangeIndices_card_of_alternating hknot hreg hsixU
      have hcountSix : (6 : ℝ≥0∞) ≤ dyadicSignChangeCount r n u := by
        rw [dyadicSignChangeCount_eq_card]
        exact_mod_cast hcardSix
      rw [Set.indicator_of_mem huO]
      norm_num
      exact hcountSix
    · rw [Set.indicator_apply, if_neg huO, add_zero]
      exact hcountFour
  have hlower :
      (∫⁻ u, (4 : ℝ≥0∞) + O.indicator (fun _ => (2 : ℝ≥0∞)) u
        ∂stdGaussian Space) ≤
        ∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space :=
    lintegral_mono_ae haeLower
  have hcalc :
      (∫⁻ u, (4 : ℝ≥0∞) + O.indicator (fun _ => (2 : ℝ≥0∞)) u
        ∂stdGaussian Space) = 4 + 2 * stdGaussian Space O := by
    rw [lintegral_add_left measurable_const]
    rw [lintegral_indicator hOopen.measurableSet, setLIntegral_const]
    simp
  have hextra : (0 : ℝ≥0∞) < 2 * stdGaussian Space O :=
    ENNReal.mul_pos (by norm_num) hOpos.ne'
  have hfourStrict : (4 : ℝ≥0∞) < 4 + 2 * stdGaussian Space O := by
    have h := ENNReal.add_lt_add_left (a := (4 : ℝ≥0∞))
      (b := 0) (c := 2 * stdGaussian Space O) (by norm_num) hextra
    simpa using h
  have hintegral : (4 : ℝ≥0∞) <
      ∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space := by
    rw [← hcalc] at hfourStrict
    exact hfourStrict.trans_le hlower
  rw [lintegral_dyadicSignChangeCount hknot n] at hintegral
  let L : ℝ := dyadicSphericalLength r n / Real.pi
  have hintegralL : (4 : ℝ≥0∞) < ENNReal.ofReal L := by
    simpa [L] using hintegral
  have hLpos : 0 < L := by
    by_contra hnonpos
    have hzero : ENNReal.ofReal L = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hnonpos)
    rw [hzero] at hintegralL
    norm_num at hintegralL
  have hreal : (4 : ℝ) < L := by
    apply (ENNReal.ofReal_lt_ofReal_iff hLpos).mp
    simpa using hintegralL
  dsimp [L] at hreal
  exact (lt_div_iff₀ Real.pi_pos).mp hreal

theorem totalCurvature_gt_four_pi_of_not_unknotted
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hnot : ¬ IsUnknotted r) :
    4 * Real.pi < totalCurvature r := by
  have hall : ∀ u : Space, ‖u‖ = 1 → HasFourAlternatingSigns r u := by
    intro u hu
    by_contra hno
    exact hnot (isUnknotted_of_not_hasFourAlternatingSigns hknot hu hno)
  obtain ⟨m, hm⟩ :=
    exists_level_forall_unit_hasFourAlternatingDyadicSignsAt hknot hall
  have htriple : ¬ ∀ t : ℝ, tangentTripleProduct r t = 0 := by
    intro hzero
    exact hnot (isUnknotted_of_tangentTripleProduct_eq_zero hknot hzero)
  obtain ⟨z, hz, hztriple⟩ :=
    exists_mem_Ioo_tangentTripleProduct_ne_zero hknot htriple
  obtain ⟨v, hvSix⟩ :=
    exists_hasSixAlternatingSigns_of_triple_ne_zero hknot hnot hz hztriple
  obtain ⟨n, hn⟩ :=
    exists_hasSixAlternatingDyadicSignsAt_of_hasSixAlternatingSigns hknot hvSix
  let N := max m n
  have hmN : m ≤ N := le_max_left _ _
  have hnN : n ≤ N := le_max_right _ _
  have hfourN : ∀ u : Space, ‖u‖ = 1 →
      HasFourAlternatingDyadicSignsAt r N u := by
    intro u hu
    exact (hm u hu).refine hmN
  have hsixN : HasSixAlternatingDyadicSignsAt r N v := hn.refine hnN
  exact (dyadicSphericalLength_gt_four_pi_of_four_and_six hknot N hfourN hsixN).trans_le
    (dyadicSphericalLength_le_totalCurvature hknot N)

end Submission.Helpers
