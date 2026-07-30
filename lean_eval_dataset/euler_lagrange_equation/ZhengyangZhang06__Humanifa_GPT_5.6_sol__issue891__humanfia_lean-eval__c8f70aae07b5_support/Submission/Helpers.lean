import ChallengeDeps

open LeanEval.Analysis
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Interval

namespace Submission.Helpers

set_option autoImplicit false

private abbrev Point := ℝ × ℝ × ℝ

lemma partialX_eq_fderiv
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2)) (t : ℝ) :
    lagrangianPartialX L x t =
      fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
        (t, x t, deriv x t) (0, 1, 0) := by
  rw [lagrangianPartialX]
  have hline : HasDerivAt (fun y : ℝ => (t, y, deriv x t)) (0, 1, 0) (x t) := by
    simpa only [id_eq] using
      (hasDerivAt_const (x t) t).prodMk
        ((hasDerivAt_id (𝕜 := ℝ) (x t)).prodMk (hasDerivAt_const (x t) (deriv x t)))
  have hcomp := ((hL.differentiable (by norm_num)) _).hasFDerivAt.comp (x t) hline.hasFDerivAt
  change deriv ((fun p : Point => L p.1 p.2.1 p.2.2) ∘
    fun y : ℝ => (t, y, deriv x t)) (x t) = _
  simpa using hcomp.hasDerivAt.deriv

lemma partialV_eq_fderiv
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2)) (t : ℝ) :
    lagrangianPartialV L x t =
      fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
        (t, x t, deriv x t) (0, 0, 1) := by
  rw [lagrangianPartialV]
  have hline : HasDerivAt (fun z : ℝ => (t, x t, z)) (0, 0, 1) (deriv x t) := by
    simpa only [id_eq] using
      (hasDerivAt_const (deriv x t) t).prodMk
        ((hasDerivAt_const (deriv x t) (x t)).prodMk
          (hasDerivAt_id (𝕜 := ℝ) (deriv x t)))
  have hcomp := ((hL.differentiable (by norm_num)) _).hasFDerivAt.comp
    (deriv x t) hline.hasFDerivAt
  change deriv ((fun p : Point => L p.1 p.2.1 p.2.2) ∘
    fun z : ℝ => (t, x t, z)) (deriv x t) = _
  simpa using hcomp.hasDerivAt.deriv

lemma contDiff_partialX
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (lagrangianPartialX L x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := by
    simpa using (hx.deriv' : ContDiff ℝ 1 (deriv x))
  have hcurve : ContDiff ℝ 1 (fun t : ℝ => (t, x t, deriv x t)) :=
    contDiff_id.prodMk (hx1.prodMk hdx)
  have hpartial : ContDiff ℝ 1 (fun t : ℝ =>
      fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
        (t, x t, deriv x t) (0, 1, 0)) :=
    (hL.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
      (hcurve.prodMk contDiff_const)
  have heq : lagrangianPartialX L x = fun t : ℝ =>
      fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
        (t, x t, deriv x t) (0, 1, 0) := by
    funext t
    exact partialX_eq_fderiv L x hL t
  rwa [heq]

lemma contDiff_partialV
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (lagrangianPartialV L x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := by
    simpa using (hx.deriv' : ContDiff ℝ 1 (deriv x))
  have hcurve : ContDiff ℝ 1 (fun t : ℝ => (t, x t, deriv x t)) :=
    contDiff_id.prodMk (hx1.prodMk hdx)
  have hpartial : ContDiff ℝ 1 (fun t : ℝ =>
      fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
        (t, x t, deriv x t) (0, 0, 1)) :=
    (hL.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
      (hcurve.prodMk contDiff_const)
  have heq : lagrangianPartialV L x = fun t : ℝ =>
      fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
        (t, x t, deriv x t) (0, 0, 1) := by
    funext t
    exact partialV_eq_fderiv L x hL t
  rwa [heq]

private noncomputable def variationIntegrand
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  L t (x t + ε * h t) (deriv x t + ε * deriv h t)

private noncomputable def variationDerivative
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  fderiv ℝ (fun p : Point => L p.1 p.2.1 p.2.2)
    (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, h t, deriv h t)

lemma hasDerivAt_variationIntegrand
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2)) (ε t : ℝ) :
    HasDerivAt (fun δ => variationIntegrand L x h δ t)
      (variationDerivative L x h ε t) ε := by
  have hsecond : HasDerivAt (fun δ : ℝ => x t + δ * h t) (h t) ε := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) ε).mul_const (h t)).const_add (x t)
  have hthird : HasDerivAt (fun δ : ℝ => deriv x t + δ * deriv h t) (deriv h t) ε := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) ε).mul_const (deriv h t)).const_add (deriv x t)
  have hline : HasDerivAt
      (fun δ : ℝ => (t, x t + δ * h t, deriv x t + δ * deriv h t))
      (0, h t, deriv h t) ε :=
    (hasDerivAt_const ε t).prodMk (hsecond.prodMk hthird)
  have hcomp := ((hL.differentiable (by norm_num)) _).hasFDerivAt.comp ε hline.hasFDerivAt
  change HasDerivAt
    ((fun p : Point => L p.1 p.2.1 p.2.2) ∘
      fun δ : ℝ => (t, x t + δ * h t, deriv x t + δ * deriv h t))
    (variationDerivative L x h ε t) ε
  simpa [variationDerivative] using hcomp.hasDerivAt

lemma variationDerivative_zero
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2)) (t : ℝ) :
    variationDerivative L x h 0 t =
      lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t := by
  rw [partialX_eq_fderiv L x hL t, partialV_eq_fderiv L x hL t]
  simp only [variationDerivative, zero_mul, add_zero]
  have hv : ((0, h t, deriv h t) : Point) =
      h t • ((0, 1, 0) : Point) + deriv h t • ((0, 0, 1) : Point) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

lemma continuous_variationDerivative_uncurry
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) :
    Continuous (Function.uncurry (variationDerivative L x h)) := by
  have hdx : Continuous (deriv x) := hx.continuous_deriv (by norm_num)
  have hdh : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have hcurve : Continuous (fun p : ℝ × ℝ =>
      ((p.2, x p.2 + p.1 * h p.2,
        deriv x p.2 + p.1 * deriv h p.2) : Point)) :=
    continuous_snd.prodMk
      (((hx.continuous.comp continuous_snd).add
        (continuous_fst.mul (hh.continuous.comp continuous_snd))).prodMk
      ((hdx.comp continuous_snd).add
        (continuous_fst.mul (hdh.comp continuous_snd))))
  have hdirection : Continuous (fun p : ℝ × ℝ =>
      ((0, h p.2, deriv h p.2) : Point)) :=
    continuous_const.prodMk
      ((hh.continuous.comp continuous_snd).prodMk (hdh.comp continuous_snd))
  have houter : Continuous (fun p : Point × Point =>
      fderiv ℝ (fun q : Point => L q.1 q.2.1 q.2.2) p.1 p.2) :=
    (hL.contDiff_fderiv_apply (m := 0) (by norm_num)).continuous
  exact houter.comp (hcurve.prodMk hdirection)

lemma continuous_variationIntegrand
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (ε : ℝ) :
    Continuous (variationIntegrand L x h ε) := by
  have hdx : Continuous (deriv x) := hx.continuous_deriv (by norm_num)
  have hdh : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have hcurve : Continuous (fun t : ℝ =>
      ((t, x t + ε * h t, deriv x t + ε * deriv h t) : Point)) :=
    continuous_id.prodMk
      ((hx.continuous.add (continuous_const.mul hh.continuous)).prodMk
        (hdx.add (continuous_const.mul hdh)))
  exact hL.continuous.comp hcurve

lemma firstVariation_eq_zero
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (hsupport : tsupport h ⊆ Ioo a b) :
    ∫ t in Ioo a b,
      (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) = 0 := by
  have hD := continuous_variationDerivative_uncurry L x h hL hx hh
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hnorm : ContinuousOn
      (fun p : ℝ × ℝ => ‖variationDerivative L x h p.1 p.2‖)
      (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := hD.norm.continuousOn
  obtain ⟨C, hC⟩ := bddAbove_def.mp (hK.bddAbove_image hnorm)
  have hbound_point (ε t : ℝ) (hε : ε ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc a b) :
      ‖variationDerivative L x h ε t‖ ≤ C :=
    hC _ ⟨(ε, t), ⟨hε, ht⟩, rfl⟩
  have hD0 : Continuous (variationDerivative L x h 0) := by
    simpa [Function.comp_def, Function.uncurry] using
      hD.comp (continuous_const.prodMk continuous_id)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo a b))
    (F := variationIntegrand L x h) (F' := variationDerivative L x h)
    (bound := fun _ => C) (x₀ := (0 : ℝ)) (s := Icc (-1 : ℝ) 1)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun ε =>
      (continuous_variationIntegrand L x h hL hx hh ε).aestronglyMeasurable)
    ((continuous_variationIntegrand L x h hL hx hh 0).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
    hD0.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      intro ε hε
      exact hbound_point ε t hε (Ioo_subset_Icc_self ht))
    (integrableOn_const (measure_Ioo_lt_top.ne))
    (Filter.Eventually.of_forall fun t ε _ => hasDerivAt_variationIntegrand L x h hL ε t)
  have hzeroD : ∫ t in Ioo a b, variationDerivative L x h 0 t = 0 := by
    rw [← hparam.2.deriv]
    simpa [variationIntegrand] using hxe.2 h hh hcompact hsupport
  calc
    ∫ t in Ioo a b,
        (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) =
        ∫ t in Ioo a b, variationDerivative L x h 0 t := by
          apply integral_congr_ae
          filter_upwards with t
          exact (variationDerivative_zero L x h hL t).symm
    _ = 0 := hzeroD

lemma weakEuler_setIntegral_eq_zero
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (hab : a < b)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (hsupport : tsupport h ⊆ Ioo a b) :
    ∫ t in Ioo a b,
      (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) * h t = 0 := by
  have hA := contDiff_partialX L x hL hx
  have hB := contDiff_partialV L x hL hx
  have ha0 : h a = 0 := by
    by_contra ha
    exact (lt_irrefl a) (hsupport (subset_tsupport h ha)).1
  have hb0 : h b = 0 := by
    by_contra hb
    exact (lt_irrefl b) (hsupport (subset_tsupport h hb)).2
  have hibp' : ∫ t in Ioo a b, lagrangianPartialV L x t * deriv h t =
      -∫ t in Ioo a b, deriv (lagrangianPartialV L x) t * h t := by
    simpa only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
      ha0, hb0, mul_zero, sub_zero, zero_sub] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := lagrangianPartialV L x) (v := h)
        (u' := deriv (lagrangianPartialV L x)) (v' := deriv h)
        (fun t _ => ((hB.differentiable one_ne_zero) t).hasDerivAt)
        (fun t _ => ((hh.differentiable (by simp)) t).hasDerivAt)
        (hB.continuous_deriv_one.intervalIntegrable a b)
        ((hh.continuous_deriv (by simp)).intervalIntegrable a b))
  have hfirst := firstVariation_eq_zero L x hL hx hxe h hh hcompact hsupport
  have hAint : IntegrableOn (fun t => lagrangianPartialX L x t * h t) (Ioo a b) :=
    (hA.continuous.mul hh.continuous).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hBdhint : IntegrableOn (fun t => lagrangianPartialV L x t * deriv h t) (Ioo a b) :=
    (hB.continuous.mul (hh.continuous_deriv (by simp))).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hdBhint : IntegrableOn
      (fun t => deriv (lagrangianPartialV L x) t * h t) (Ioo a b) :=
    (hB.continuous_deriv_one.mul hh.continuous).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [integral_add hAint hBdhint, hibp'] at hfirst
  simp_rw [sub_mul]
  rw [integral_sub hAint hdBhint]
  simpa [sub_eq_add_neg] using hfirst

lemma weakEuler_integral_eq_zero
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (hab : a < b)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (hsupport : tsupport h ⊆ Ioo a b) :
    ∫ t, h t •
      (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) = 0 := by
  calc
    ∫ t, h t • (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) =
        ∫ t, (Ioo a b).indicator (fun s =>
          (lagrangianPartialX L x s - deriv (lagrangianPartialV L x) s) * h s) t := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioo a b
      · simp [ht, smul_eq_mul, mul_comm]
      · have hzero : h t = 0 := by
          by_contra hn
          exact ht (hsupport (subset_tsupport h hn))
        simp [ht, hzero]
    _ = ∫ t in Ioo a b,
        (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) * h t :=
      integral_indicator measurableSet_Ioo
    _ = 0 := weakEuler_setIntegral_eq_zero L x hab hL hx hxe h hh hcompact hsupport

theorem euler_lagrange_equation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (hab : a < b)
    (hL : ContDiff ℝ 2 (fun p : Point => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x) :
    ∀ t ∈ Ioo a b,
      lagrangianPartialX L x t = deriv (lagrangianPartialV L x) t := by
  let E : ℝ → ℝ := fun t =>
    lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t
  have hA := contDiff_partialX L x hL hx
  have hB := contDiff_partialV L x hL hx
  have hE : Continuous E := hA.continuous.sub hB.continuous_deriv_one
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hE.locallyIntegrable.locallyIntegrableOn (Ioo a b))
    (fun h hh hcompact hsupport =>
      weakEuler_integral_eq_zero L x hab hL hx hxe h hh hcompact hsupport)
  have hae' : E =ᵐ[volume.restrict (Ioo a b)] (fun _ => 0) := by
    change ∀ᵐ t ∂volume.restrict (Ioo a b), E t = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hae
  have hpoint := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hE.continuousOn
    continuous_const.continuousOn
  intro t ht
  exact sub_eq_zero.mp (hpoint ht)

end Submission.Helpers
