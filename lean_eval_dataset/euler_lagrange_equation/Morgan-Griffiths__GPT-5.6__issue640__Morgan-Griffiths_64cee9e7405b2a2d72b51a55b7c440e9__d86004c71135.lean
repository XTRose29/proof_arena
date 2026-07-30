import Mathlib

namespace Submission

namespace LeanEval
namespace Analysis

/-!
# Euler–Lagrange equation

§44 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (the additional
statement of the calculus-of-variations section). A sufficiently regular
stationary path `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt` satisfies
the Euler–Lagrange equation `∂L/∂x = (d/dt)(∂L/∂x')` pointwise on `(a, b)`.

mathlib has the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and neighbours), but it
has no notion of a variational extremum of an action functional and no
Euler–Lagrange theorem (`grep -i 'euler.*lagrange'` in mathlib finds nothing in
the analytic sense). Here a path is a variational extremum when the first
variation of the action vanishes against every smooth compactly supported
perturbation, and the conclusion is the classical pointwise equation for `C²`
data.
-/

open MeasureTheory Set
open scoped ContDiff

/-- `∂L/∂x` along the path `x` at time `t`: the derivative of the partial map
`y ↦ L t y (x' t)` at `y = x t`. -/
noncomputable def lagrangianPartialX
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t)) (x t)

/-- `∂L/∂x'` along the path `x` at time `t`: the derivative of the partial map
`z ↦ L t (x t) z` at `z = x' t`. -/
noncomputable def lagrangianPartialV
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun z => L t (x t) z) (deriv x t)

/-- A `C¹` path `x : ℝ → ℝ` is a **variational extremum** of the action
`I(y) := ∫_a^b L(t, y(t), y'(t)) dt` on `(a, b)` if for every smooth compactly
supported variation `h` with `tsupport h ⊆ (a, b)`, the first variation
`d/dε|_{ε=0} ∫_a^b L(t, x(t) + ε h(t), x'(t) + ε h'(t)) dt` vanishes. -/
def IsVariationalExtremum
    (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 x ∧
  ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
    tsupport h ⊆ Set.Ioo a b →
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0 = 0



end Analysis
end LeanEval

open LeanEval.Analysis
open MeasureTheory Set
open scoped ContDiff
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

private abbrev ELFun (L : ℝ → ℝ → ℝ → ℝ) : (ℝ × ℝ × ℝ) → ℝ :=
  fun p => L p.1 p.2.1 p.2.2

private lemma el_partialX_fderiv {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (ELFun L)) (t : ℝ) :
    lagrangianPartialX L x t =
      (fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (1, 0)) := by
  have hdiff : Differentiable ℝ (ELFun L) := hL.differentiable (by norm_num)
  have hi : HasFDerivAt (fun y : ℝ => (t, (y, deriv x t)))
        ((0 : ℝ →L[ℝ] ℝ).prod
          ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))) (x t) := by
    exact (hasFDerivAt_const (x := (x t)) t).prodMk
      ((hasFDerivAt_id (𝕜:=ℝ) (x t)).prodMk (hasFDerivAt_const (x := (x t)) (deriv x t)))
  have ho := (hdiff (t, (x t, deriv x t))).hasFDerivAt.comp (x t) hi
  have hd : HasDerivAt (fun y : ℝ => ELFun L (t, (y, deriv x t)))
      ((fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (1, 0))) (x t) := by
    simpa [Function.comp_def] using ho.hasDerivAt
  exact hd.deriv

private lemma el_partialV_fderiv {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (ELFun L)) (t : ℝ) :
    lagrangianPartialV L x t =
      (fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (0, 1)) := by
  have hdiff : Differentiable ℝ (ELFun L) := hL.differentiable (by norm_num)
  have hi : HasFDerivAt (fun z : ℝ => (t, (x t, z)))
        ((0 : ℝ →L[ℝ] ℝ).prod
          ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ))) (deriv x t) := by
    exact (hasFDerivAt_const (x := (deriv x t)) t).prodMk
      ((hasFDerivAt_const (x := (deriv x t)) (x t)).prodMk (hasFDerivAt_id (𝕜:=ℝ) (deriv x t)))
  have ho := (hdiff (t, (x t, deriv x t))).hasFDerivAt.comp (deriv x t) hi
  have hd : HasDerivAt (fun z : ℝ => ELFun L (t, (x t, z)))
      ((fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (0, 1))) (deriv x t) := by
    simpa [Function.comp_def] using ho.hasDerivAt
  exact hd.deriv


private lemma el_contDiff_partials {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (ELFun L)) (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (lagrangianPartialX L x) ∧
      ContDiff ℝ 1 (lagrangianPartialV L x) := by
  have hdx : ContDiff ℝ 1 (deriv x) := by
    convert (ContDiff.deriv' (n:= (1 : ℕ∞ω)) hx) using 1 <;> norm_num
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hp : ContDiff ℝ 1 (fun t : ℝ => (t, (x t, deriv x t))) :=
    contDiff_id.prodMk (hx1.prodMk hdx)
  have hdf : ContDiff ℝ 1 (fderiv ℝ (ELFun L)) :=
    hL.fderiv_right (m:= (1 : ℕ∞ω)) (by norm_num)
  constructor
  · have H : ContDiff ℝ 1 (fun t : ℝ =>
          (fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (1, 0))) := by
        exact (hdf.comp hp).clm_apply contDiff_const
    rw [show lagrangianPartialX L x = (fun t : ℝ =>
          (fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (1, 0)))
          from funext (el_partialX_fderiv hL)]
    exact H
  · have H : ContDiff ℝ 1 (fun t : ℝ =>
          (fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (0, 1))) := by
        exact (hdf.comp hp).clm_apply contDiff_const
    rw [show lagrangianPartialV L x = (fun t : ℝ =>
          (fderiv ℝ (ELFun L) (t, (x t, deriv x t))) (0, (0, 1)))
          from funext (el_partialV_fderiv hL)]
    exact H


private noncomputable def ELPhi (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (e t : ℝ) : ℝ :=
  L t (x t + e * h t) (deriv x t + e * deriv h t)
private noncomputable def ELD (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (e t : ℝ) : ℝ :=
  (fderiv ℝ (ELFun L)
    (t, (x t + e * h t, deriv x t + e * deriv h t))) (0, (h t, deriv h t))

private lemma el_phi_deriv {L : ℝ → ℝ → ℝ → ℝ} {x h : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (ELFun L)) (e t : ℝ) :
    HasDerivAt (fun u : ℝ => ELPhi L x h u t) (ELD L x h e t) e := by
  have hf : Differentiable ℝ (ELFun L) := hL.differentiable (by norm_num)
  have hy : HasDerivAt (fun u : ℝ => x t + u * h t) (h t) e := by
    convert (hasDerivAt_const (x := e) (x t)).add ((hasDerivAt_id e).mul_const (h t)) using 1 <;>
      first | rfl | (ext z; rfl) | simp [id, Pi.add_apply]
  have hz : HasDerivAt (fun u : ℝ => deriv x t + u * deriv h t) (deriv h t) e := by
    convert (hasDerivAt_const (x := e) (deriv x t)).add ((hasDerivAt_id e).mul_const (deriv h t)) using 1 <;>
      first | rfl | (ext z; rfl) | simp [id, Pi.add_apply]
  have hp : HasDerivAt (fun u : ℝ =>
        (t, (x t + u * h t, deriv x t + u * deriv h t)))
        (0, (h t, deriv h t)) e :=
    (hasDerivAt_const (x := e) t).prodMk (hy.prodMk hz)
  have hh := (hf (t, (x t + e * h t, deriv x t + e * deriv h t))).hasFDerivAt.comp_hasDerivAt e hp
  simpa [ELPhi, ELD, Function.comp_def] using hh

private lemma el_D_zero {L : ℝ → ℝ → ℝ → ℝ} {x h : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (ELFun L)) (t : ℝ) :
    ELD L x h 0 t =
      lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t := by
  rw [el_partialX_fderiv hL t, el_partialV_fderiv hL t]
  simp [ELD]
  -- linearity in the two variation directions
  let A := fderiv ℝ (ELFun L) (t, (x t, deriv x t))
  let v : ℝ × ℝ × ℝ := (0, (1, 0))
  let w : ℝ × ℝ × ℝ := (0, (0, 1))
  change A (0, (h t, deriv h t)) = A v * h t + A w * deriv h t
  calc
    A (0, (h t, deriv h t)) = A ((h t) • v + (deriv h t) • w) := by
      congr 1
      ext <;> simp [v, w]
    _ = A ((h t) • v) + A ((deriv h t) • w) := by
      rw [map_add]
    _ = A v * h t + A w * deriv h t := by
      rw [map_smul, map_smul]
      simp [smul_eq_mul, mul_comm]



private lemma integral_mul_deriv_compact_Ioo {a b : ℝ} (hab : a < b)
    {q h : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    (hh : ContDiff ℝ ∞ h) (hs : tsupport h ⊆ Ioo a b) :
    (∫ t in Ioo a b, q t * deriv h t) =
      - (∫ t in Ioo a b, deriv q t * h t) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  have hcq : Continuous q := hq.continuous
  have hch : Continuous h := hh1.continuous
  have hdq : Continuous (deriv q) := hq.continuous_deriv_one
  have hdh : Continuous (deriv h) := hh1.continuous_deriv_one
  have ha0 : h a = 0 := by
    by_contra hn
    have ha : a ∈ tsupport h := subset_tsupport h hn
    exact (not_lt_of_ge le_rfl) (hs ha).1
  have hb0 : h b = 0 := by
    by_contra hn
    have hb : b ∈ tsupport h := subset_tsupport h hn
    exact (not_lt_of_ge le_rfl) (hs hb).2
  have ib := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a:=a) (b:=b) (u:=q) (v:=h) (u':=deriv q) (v':=deriv h)
    hcq.continuousOn hch.continuousOn
    (fun z _ => (hq.differentiable (by norm_num) z).hasDerivAt)
    (fun z _ => (hh1.differentiable (by norm_num) z).hasDerivAt)
    (hdq.intervalIntegrable a b) (hdh.intervalIntegrable a b)
  have ib' : (∫ t in a..b, q t * deriv h t) =
       - (∫ t in a..b, deriv q t * h t) := by
    rw [ib, ha0, hb0]
    ring
  simpa [intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo] using ib'


private lemma el_first_variation {a b : ℝ} (hab : a < b)
    {L : ℝ → ℝ → ℝ → ℝ} {x h : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (ELFun L)) (hx : ContDiff ℝ 2 x)
    (hh : ContDiff ℝ ∞ h) :
    deriv (fun e : ℝ => ∫ t in Ioo a b, ELPhi L x h e t) 0 =
      ∫ t in Ioo a b, (lagrangianPartialX L x t * h t +
        lagrangianPartialV L x t * deriv h t) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  have hdh : Continuous (deriv h) := hh1.continuous_deriv_one
  have hdx : Continuous (deriv x) := (hx.of_le (by norm_num : (1:ℕ∞ω) ≤ 2)).continuous_deriv_one
  have cp : Continuous (fun p : ℝ × ℝ => ELPhi L x h p.1 p.2) := by
    unfold ELPhi
    exact hL.continuous.comp (continuous_snd.prodMk
      (((hx.continuous.comp continuous_snd).add (continuous_fst.mul (hh.continuous.comp continuous_snd))).prodMk
        ((hdx.comp continuous_snd).add (continuous_fst.mul (hdh.comp continuous_snd)))))
  have cd : Continuous (fun p : ℝ × ℝ => ELD L x h p.1 p.2) := by
    unfold ELD
    have cf : Continuous (fderiv ℝ (ELFun L)) :=
      (hL.fderiv_right (m:=(0:ℕ∞ω)) (by norm_num)).continuous
    exact (cf.comp (continuous_snd.prodMk
      (((hx.continuous.comp continuous_snd).add (continuous_fst.mul (hh.continuous.comp continuous_snd))).prodMk
        ((hdx.comp continuous_snd).add (continuous_fst.mul (hdh.comp continuous_snd)))))).clm_apply
          (continuous_const.prodMk ((hh.continuous.comp continuous_snd).prodMk (hdh.comp continuous_snd)))
  let K : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc a b
  have Kc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have bd : BddAbove ((fun p : ℝ × ℝ => ‖ELD L x h p.1 p.2‖) '' K) :=
    Kc.bddAbove_image cd.norm.continuousOn
  rcases bd with ⟨C, hC⟩
  have boundall : ∀ e ∈ Icc (-1:ℝ) 1, ∀ t ∈ Icc a b,
       ‖ELD L x h e t‖ ≤ C := by
    intro e he t ht
    exact hC ⟨(e,t), ⟨he,ht⟩, rfl⟩
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hfin : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  letI : IsFiniteMeasure μ := hfin
  have mea_phi : ∀ᶠ e in nhds (0:ℝ), AEStronglyMeasurable (fun t => ELPhi L x h e t) μ :=
    Filter.Eventually.of_forall (fun e => (cp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  have int_phi : Integrable (fun t => ELPhi L x h 0 t) μ :=
    (cp.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact isCompact_Icc
  have dm : AEStronglyMeasurable (fun t => ELD L x h 0 t) μ :=
    (cd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbnd : ∀ᵐ t ∂μ, ∀ e ∈ Icc (-1:ℝ) 1, ‖ELD L x h e t‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc (μ:= (volume : Measure ℝ))] with t ht
    intro e he; exact boundall e he t ht
  have hdif : ∀ᵐ t ∂μ, ∀ e ∈ Icc (-1:ℝ) 1,
      HasDerivAt (fun e => ELPhi L x h e t) (ELD L x h e t) e :=
    Filter.Eventually.of_forall (fun t e he => el_phi_deriv hL e t)
  obtain ⟨_, key⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=fun e t => ELPhi L x h e t)
    (F':=fun e t => ELD L x h e t) (bound:= fun _ : ℝ => C)
    (Icc_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))
    mea_phi int_phi dm hbnd (integrable_const C) hdif
  have kk := key.deriv
  dsimp [μ] at kk
  simp_rw [integral_Icc_eq_integral_Ioo] at kk
  rw [kk]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact el_D_zero hL t

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem euler_lagrange_equation {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (_hab : a < b)
    (_hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (_hx : ContDiff ℝ 2 x)
    (_hxe : IsVariationalExtremum a b L x) :
    ∀ t ∈ Set.Ioo a b,
      lagrangianPartialX L x t = deriv (lagrangianPartialV L x) t :=
/-ResultProofBegin-/by
  have parts := el_contDiff_partials (L:=L) (x:=x) _hL _hx
  let f : ℝ → ℝ := fun t => lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t
  have cf : Continuous f := parts.1.continuous.sub parts.2.continuous_deriv_one
  have loc : LocallyIntegrableOn f (Ioo a b) :=
    cf.continuousOn.locallyIntegrableOn measurableSet_Ioo
  have ae0 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → f t = 0 := by
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo loc
    intro h hh hc hs
    have sta := _hxe.2 h hh hc hs
    have fv := el_first_variation _hab _hL _hx hh
    change deriv (fun e : ℝ => ∫ t in Ioo a b, ELPhi L x h e t) 0 = 0 at sta
    rw [fv] at sta
    have ib := integral_mul_deriv_compact_Ioo _hab parts.2 hh hs
    -- arithmetic of the two integrals on the interval
    have intA : Integrable (fun t : ℝ => lagrangianPartialX L x t * h t)
        ((volume : Measure ℝ).restrict (Ioo a b)) := by
      have ht : IntegrableOn (fun t : ℝ => lagrangianPartialX L x t * h t)
          (Icc a b) (volume : Measure ℝ) := by
        have hc : Continuous (fun t : ℝ => lagrangianPartialX L x t * h t) :=
          parts.1.continuous.mul hh.continuous
        exact hc.integrableOn_Icc
      exact ht.mono_set Ioo_subset_Icc_self
    have intB : Integrable (fun t : ℝ => lagrangianPartialV L x t * deriv h t)
        ((volume : Measure ℝ).restrict (Ioo a b)) := by
      have ht : IntegrableOn (fun t : ℝ => lagrangianPartialV L x t * deriv h t)
          (Icc a b) (volume : Measure ℝ) := by
        have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
        have hc : Continuous (fun t : ℝ => lagrangianPartialV L x t * deriv h t) :=
          parts.2.continuous.mul hh1.continuous_deriv_one
        exact hc.integrableOn_Icc
      exact ht.mono_set Ioo_subset_Icc_self
    rw [integral_add intA intB] at sta
    rw [ib] at sta
    have intC : Integrable
        (fun t : ℝ => deriv (lagrangianPartialV L x) t * h t)
        ((volume : Measure ℝ).restrict (Ioo a b)) := by
      have ht : IntegrableOn
          (fun t : ℝ => deriv (lagrangianPartialV L x) t * h t)
          (Icc a b) (volume : Measure ℝ) := by
        have hc' : Continuous
            (fun t : ℝ => deriv (lagrangianPartialV L x) t * h t) :=
          parts.2.continuous_deriv_one.mul hh.continuous
        exact hc'.integrableOn_Icc
      exact ht.mono_set Ioo_subset_Icc_self
    have staI : (∫ t in Ioo a b, h t * f t) = 0 := by
      calc
        (∫ t in Ioo a b, h t * f t) =
            ∫ t in Ioo a b,
              (lagrangianPartialX L x t * h t -
                deriv (lagrangianPartialV L x) t * h t) := by
                  apply setIntegral_congr_fun measurableSet_Ioo
                  intro z hz
                  dsimp [f]
                  ring
        _ = (∫ t in Ioo a b, lagrangianPartialX L x t * h t) -
              (∫ t in Ioo a b, deriv (lagrangianPartialV L x) t * h t) := by
                  exact integral_sub intA intC
        _ = (∫ t in Ioo a b, lagrangianPartialX L x t * h t) +
              -(∫ t in Ioo a b, deriv (lagrangianPartialV L x) t * h t) := by
                  ring
        _ = 0 := sta
    -- Since the multiplier `h` is supported inside the interval, its
    -- integral over the whole line is the same interval integral.
    have hzout : ∀ z : ℝ, z ∉ Ioo a b → h z = 0 := by
      intro z hz
      by_contra hn
      have zt : z ∈ tsupport h := subset_tsupport h hn
      exact hz (hs zt)
    let g : ℝ → ℝ := fun z => h z * f z
    have ind : g = (Ioo a b).indicator g := by
      funext z
      by_cases hz : z ∈ Ioo a b
      · simp [indicator_of_mem hz]
      · have hzero : h z = 0 := hzout z hz
        -- both sides are zero off the interval
        simp [g, indicator_of_notMem hz, hzero]
    have glob : (∫ z : ℝ, g z) = (∫ z in Ioo a b, g z) := by
      -- replace the compactly supported function by its indicator
      conv_lhs => rw [ind]
      exact integral_indicator measurableSet_Ioo
    change (∫ z : ℝ, g z) = 0
    rw [glob]
    exact staI
  have rr : (f =ᵐ[(volume : Measure ℝ).restrict (Ioo a b)] (fun _ => 0)) :=
    (ae_restrict_iff' measurableSet_Ioo).2 ae0
  have eqn := Measure.eqOn_open_of_ae_eq rr isOpen_Ioo cf.continuousOn continuous_const.continuousOn
  intro t ht
  have z := eqn ht
  dsimp [f] at z
  linarith
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
