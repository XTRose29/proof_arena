import Submission.Helpers
import Submission.Winding

open LeanEval.Geometry.HopfUmlaufsatz

namespace Submission.Orientation

open Set MeasureTheory
open Submission.Helpers
open Submission.Winding

noncomputable section

/-- The closed curve as a continuous map on the standard unit circle. -/
def curveCircle (r : ℝ → Plane) (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    C(Circle, ℂ) := by
  let f : Circle → ℂ := fun z => planeToComplex (r (Complex.arg (z : ℂ)))
  have hf_exp (t : ℝ) : f (Circle.exp t) = planeToComplex (r t) := by
    have hexp : Circle.exp (Complex.arg ((Circle.exp t : Circle) : ℂ)) =
        Circle.exp t := Circle.exp_arg _
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
    have hrarg : r (Complex.arg ((Circle.exp t : Circle) : ℂ)) = r t := by
      rw [hn]
      simpa only [period, mul_assoc] using hr.periodic.int_mul n t
    exact congrArg planeToComplex hrarg
  refine ⟨f, ?_⟩
  have hcomp : Continuous (f ∘ Circle.exp) := by
    rw [show f ∘ Circle.exp = fun t => planeToComplex (r t) by
      funext t
      exact hf_exp t]
    exact planeToComplex.continuous.comp hr.smooth.continuous
  exact continuous_of_comp_circleExp hcomp

@[simp]
theorem curveCircle_exp (r : ℝ → Plane)
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (t : ℝ) :
    curveCircle r hr (Circle.exp t) = planeToComplex (r t) := by
  simp only [curveCircle]
  have hexp : Circle.exp (Complex.arg ((Circle.exp t : Circle) : ℂ)) =
      Circle.exp t := Circle.exp_arg _
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hrarg : r (Complex.arg ((Circle.exp t : Circle) : ℂ)) = r t := by
    rw [hn]
    simpa only [period, mul_assoc] using hr.periodic.int_mul n t
  exact congrArg planeToComplex hrarg

theorem range_curveCircle (r : ℝ → Plane)
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Set.range (curveCircle r hr) = Set.range (fun t => planeToComplex (r t)) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Complex.arg (u : ℂ), rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp t, curveCircle_exp r hr t⟩

theorem curveCircle_injective (r : ℝ → Plane)
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Function.Injective (curveCircle r hr) := by
  intro x y hxy
  obtain ⟨sx, hsx⟩ := Circle.exp_surjective x
  obtain ⟨sy, hsy⟩ := Circle.exp_surjective y
  subst x
  subst y
  rw [curveCircle_exp, curveCircle_exp] at hxy
  have hrxy : r sx = r sy := planeToComplex.injective hxy
  letI : Fact (0 < period) := ⟨period_pos⟩
  have hclasses : (sx : AddCircle period) = (sy : AddCircle period) := by
    apply periodicLift_injective hr
    simpa only [hr.periodic.lift_coe] using hrxy
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at hclasses
  obtain ⟨n, hn⟩ := hclasses
  apply Circle.exp_eq_exp.mpr
  refine ⟨n, ?_⟩
  simp only [period, zsmul_eq_mul] at hn
  linarith

/-- The nonnegative scalar relating the extended secant to the actual chord. -/
noncomputable def chordScale (δ : ℝ) : ℝ :=
  if δ ≤ period / 2 then δ else period - δ

theorem chordScale_continuous : Continuous chordScale := by
  unfold chordScale
  refine Continuous.if_le continuous_id (continuous_const.sub continuous_id)
    continuous_id continuous_const ?_
  intro x hx
  rw [hx]
  ring

@[simp]
theorem chordScale_zero : chordScale 0 = 0 := by
  simp [chordScale, (half_pos period_pos).le]

@[simp]
theorem chordScale_period : chordScale period = 0 := by
  simp [chordScale, not_le.mpr (half_lt_self period_pos)]

theorem chordScale_nonneg {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) period) :
    0 ≤ chordScale δ := by
  rw [chordScale]
  split_ifs with h
  · exact hδ.1
  · exact sub_nonneg.mpr hδ.2

theorem chordScale_pos {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) period) :
    0 < chordScale δ := by
  rw [chordScale]
  split_ifs
  · exact hδ.1
  · exact sub_pos.mpr hδ.2

theorem chordScale_smul_extendedSecant_eq_sub {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ) :
    chordScale δ • extendedSecant r s δ = r (s + δ) - r s := by
  rw [chordScale]
  split_ifs with hhalf
  · rw [extendedSecant, if_pos hhalf]
    exact smul_averageVelocity_eq_sub hr s δ
  · exact subperiod_smul_extendedSecant_eq_sub hr s δ hhalf

theorem complex_chord_factor {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ) :
    planeToComplex (r (s + δ) - r s) =
      (chordScale δ : ℂ) * planeToComplex (extendedSecant r s δ) := by
  rw [← chordScale_smul_extendedSecant_eq_sub hr s δ, map_smul]
  rfl

/-- A closest parameter exists because one period is compact. -/
theorem exists_nearest_parameter {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (x : ℂ) :
    ∃ a : ℝ, ∀ t : ℝ,
      ‖planeToComplex (r a) - x‖ ≤ ‖planeToComplex (r t) - x‖ := by
  have hc : Continuous (fun t : ℝ => ‖planeToComplex (r t) - x‖) :=
    ((planeToComplex.continuous.comp hr.smooth.continuous).sub
      continuous_const).norm
  obtain ⟨a, _, ha⟩ := isCompact_Icc.exists_isMinOn
    ⟨(0 : ℝ), by exact ⟨le_rfl, period_pos.le⟩⟩ hc.continuousOn
  refine ⟨a, fun t => ?_⟩
  letI : Fact (0 < period) := ⟨period_pos⟩
  let t₀ := AddCircle.equivIco period 0 (t : AddCircle period)
  have ht₀ : (t₀ : ℝ) ∈ Ico (0 : ℝ) period := by
    simpa [t₀] using t₀.2
  have hclass : ((t₀ : ℝ) : AddCircle period) = (t : AddCircle period) :=
    AddCircle.coe_equivIco (p := period) (a := 0) (y := (t : AddCircle period))
  have hrt : r t₀ = r t := by
    have h := congrArg hr.periodic.lift hclass
    simpa [t₀] using h
  rw [← hrt]
  exact ha (Ico_subset_Icc_self ht₀)

theorem hasDerivAt_complexCurve {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (t : ℝ) :
    HasDerivAt (fun s : ℝ => planeToComplex (r s))
      (planeToComplex (velocity r t)) t := by
  have hdr : HasDerivAt r (velocity r t) t := by
    simpa [velocity] using
      ((hr.smooth.differentiable (by norm_num)) t).hasDerivAt
  exact planeToComplex.hasFDerivAt.comp_hasDerivAt t hdr

/-- At a closest point, the displacement to the external point is normal to
the tangent. -/
theorem nearest_inner_velocity_eq_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (x : ℂ) (a : ℝ)
    (ha : ∀ t : ℝ,
      ‖planeToComplex (r a) - x‖ ≤ ‖planeToComplex (r t) - x‖) :
    @inner ℝ ℂ _ (planeToComplex (r a) - x)
      (planeToComplex (velocity r a)) = 0 := by
  let z : ℝ → ℂ := fun t => planeToComplex (r t) - x
  have hz : HasDerivAt z (planeToComplex (velocity r a)) a := by
    exact (hasDerivAt_complexCurve hr a).sub_const x
  have hmin : IsLocalMin (fun t => ‖z t‖ ^ 2) a := by
    apply Filter.Eventually.of_forall
    intro t
    have h := ha t
    dsimp [z]
    nlinarith [norm_nonneg (planeToComplex (r a) - x),
      norm_nonneg (planeToComplex (r t) - x)]
  have hzero := hmin.hasDerivAt_eq_zero hz.norm_sq
  dsimp [z] at hzero
  simpa using (show
    (2 : ℝ) * @inner ℝ ℂ _ (planeToComplex (r a) - x)
      (planeToComplex (velocity r a)) = 0 by exact hzero)

/-- The elementary scalar inequality behind the nearest-point winding
calculation. -/
theorem scalar_re_nonneg_of_nearest (l : ℝ) (hl : 0 < l)
    (e w : ℂ) (he : e ≠ 0)
    (hnear : ‖w‖ ≤ ‖(l : ℂ) * e - w‖) :
    0 ≤ ((l : ℂ) - w / e).re := by
  have hsq : Complex.normSq w ≤ Complex.normSq ((l : ℂ) * e - w) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w, norm_nonneg ((l : ℂ) * e - w)]
  have hden : 0 < Complex.normSq e := Complex.normSq_pos.mpr he
  change 0 ≤ l - (w / e).re
  rw [Complex.div_re]
  rw [sub_nonneg, ← add_div, div_le_iff₀ hden]
  rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal] at hsq
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add] at hsq
  have hdot :
      2 * l * (w.re * e.re + w.im * e.im) ≤
        l ^ 2 * Complex.normSq e := by
    nlinarith
  nlinarith

theorem div_re_eq_inner_div_normSq (w e : ℂ) :
    (w / e).re = (@inner ℝ ℂ _ w e) / Complex.normSq e := by
  rw [Complex.div_re, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add]
  ring

/-- The scalar left after factoring a translated chord through the extended
secant field. -/
noncomputable def nearestScalar (r : ℝ → Plane) (a : ℝ) (x : ℂ) (δ : ℝ) : ℂ :=
  (chordScale δ : ℂ) -
    (x - planeToComplex (r a)) / planeToComplex (extendedSecant r a δ)

theorem nearestScalar_continuous {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) (x : ℂ) :
    Continuous (fun δ : Icc (0 : ℝ) period => nearestScalar r a x δ) := by
  have hecont : Continuous (fun δ => planeToComplex (extendedSecant r a δ)) :=
    planeToComplex.continuous.comp
      ((extendedSecant_continuous hr).comp (continuous_const.prodMk continuous_id))
  have he : ∀ δ : Icc (0 : ℝ) period,
      planeToComplex (extendedSecant r a δ) ≠ 0 := by
    intro δ hzero
    apply extendedSecant_ne_zero hr a δ δ.property
    apply planeToComplex.injective
    simpa using hzero
  exact ((RCLike.continuous_ofReal.comp chordScale_continuous).comp
      continuous_subtype_val).sub
    (continuous_const.div₀ (hecont.comp continuous_subtype_val) he)

theorem nearestScalar_factor {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) (x : ℂ) (δ : ℝ)
    (hδ : δ ∈ Icc (0 : ℝ) period) :
    planeToComplex (extendedSecant r a δ) * nearestScalar r a x δ =
      planeToComplex (r (a + δ)) - x := by
  have he : planeToComplex (extendedSecant r a δ) ≠ 0 := by
    intro hzero
    apply extendedSecant_ne_zero hr a δ hδ
    apply planeToComplex.injective
    simpa using hzero
  rw [nearestScalar, mul_sub, mul_div_cancel₀ _ he,
    mul_comm (planeToComplex (extendedSecant r a δ)),
    ← complex_chord_factor hr a δ]
  simp only [map_sub]
  ring

theorem nearestScalar_ne_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) (x : ℂ)
    (hx : x ∉ Set.range (curveCircle r hr)) (δ : ℝ)
    (hδ : δ ∈ Icc (0 : ℝ) period) :
    nearestScalar r a x δ ≠ 0 := by
  intro hzero
  have hfactor := nearestScalar_factor hr a x δ hδ
  rw [hzero, mul_zero] at hfactor
  apply hx
  refine ⟨Circle.exp (a + δ), ?_⟩
  rw [curveCircle_exp]
  exact sub_eq_zero.mp hfactor.symm

theorem nearest_displacement_inner_velocity_eq_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (x : ℂ) (a : ℝ)
    (ha : ∀ t : ℝ,
      ‖planeToComplex (r a) - x‖ ≤ ‖planeToComplex (r t) - x‖) :
    @inner ℝ ℂ _ (x - planeToComplex (r a))
      (planeToComplex (velocity r a)) = 0 := by
  have h := nearest_inner_velocity_eq_zero hr x a ha
  rw [show x - planeToComplex (r a) =
    -(planeToComplex (r a) - x) by ring, inner_neg_left, h, neg_zero]

theorem nearestScalar_re_nonneg {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) (x : ℂ)
    (ha : ∀ t : ℝ,
      ‖planeToComplex (r a) - x‖ ≤ ‖planeToComplex (r t) - x‖)
    (δ : ℝ) (hδ : δ ∈ Icc (0 : ℝ) period) :
    0 ≤ (nearestScalar r a x δ).re := by
  let w : ℂ := x - planeToComplex (r a)
  let e : ℂ := planeToComplex (extendedSecant r a δ)
  have he : e ≠ 0 := by
    intro hzero
    apply extendedSecant_ne_zero hr a δ hδ
    apply planeToComplex.injective
    simpa [e] using hzero
  by_cases hzero : δ = 0
  · subst δ
    have hwinner : @inner ℝ ℂ _ w (planeToComplex (velocity r a)) = 0 := by
      simpa [w] using nearest_displacement_inner_velocity_eq_zero hr x a ha
    have hdiv :
        (w / planeToComplex (velocity r a)).re = 0 := by
      rw [div_re_eq_inner_div_normSq, hwinner, zero_div]
    rw [nearestScalar, chordScale_zero, extendedSecant_zero,
      Complex.sub_re, hdiv]
    simp
  by_cases hend : δ = period
  · subst δ
    have hwinner : @inner ℝ ℂ _ w (-planeToComplex (velocity r a)) = 0 := by
      change @inner ℝ ℂ _ (x - planeToComplex (r a))
        (-planeToComplex (velocity r a)) = 0
      rw [inner_neg_right,
        nearest_displacement_inner_velocity_eq_zero hr x a ha, neg_zero]
    have hdiv :
        (w / -planeToComplex (velocity r a)).re = 0 := by
      rw [div_re_eq_inner_div_normSq, hwinner, zero_div]
    rw [nearestScalar, chordScale_period, extendedSecant_period, map_neg,
      Complex.sub_re, hdiv]
    simp
  · have hδopen : δ ∈ Ioo (0 : ℝ) period :=
      ⟨lt_of_le_of_ne hδ.1 (Ne.symm hzero), lt_of_le_of_ne hδ.2 hend⟩
    have hlpos := chordScale_pos hδopen
    have hnear : ‖w‖ ≤ ‖(chordScale δ : ℂ) * e - w‖ := by
      calc
        ‖w‖ = ‖planeToComplex (r a) - x‖ := by
          rw [show planeToComplex (r a) - x = -w by simp [w]]
          exact (norm_neg w).symm
        _ ≤ ‖planeToComplex (r (a + δ)) - x‖ := ha (a + δ)
        _ = ‖(chordScale δ : ℂ) * e - w‖ := by
          congr 1
          rw [← complex_chord_factor hr a δ]
          simp only [map_sub]
          simp [w]
    simpa [nearestScalar, w, e] using
      scalar_re_nonneg_of_nearest (chordScale δ) hlpos e w he hnear

private abbrev ParameterInterval := Icc (0 : ℝ) period

private def parameterZero : ParameterInterval :=
  ⟨0, le_rfl, period_pos.le⟩

private def parameterPeriod : ParameterInterval :=
  ⟨period, period_pos.le, le_rfl⟩

/-- A nonvanishing path in the closed right half-plane whose endpoints are
opposites changes principal argument by exactly `π` or `-π`. -/
theorem log_endpoint_im_eq_pi_or_neg (Q : C(ParameterInterval, ℂ))
    (hQ_ne : ∀ δ, Q δ ≠ 0)
    (hQ_re : ∀ δ, 0 ≤ (Q δ).re)
    (hend : Q parameterPeriod = -Q parameterZero) :
    (Complex.log (Q parameterPeriod) - Complex.log (Q parameterZero)).im =
        Real.pi ∨
      (Complex.log (Q parameterPeriod) - Complex.log (Q parameterZero)).im =
        -Real.pi := by
  let z := Q parameterZero
  have hz_re : z.re = 0 := by
    have h0 := hQ_re parameterZero
    have hL := hQ_re parameterPeriod
    rw [hend] at hL
    have hL' : 0 ≤ -z.re := by simpa [z] using hL
    linarith
  have hz_im_ne : z.im ≠ 0 := by
    intro him
    apply hQ_ne parameterZero
    apply Complex.ext
    · simpa [z] using hz_re
    · simpa [z] using him
  have him :
      (Complex.log (Q parameterPeriod) -
        Complex.log (Q parameterZero)).im = (-z).arg - z.arg := by
    rw [Complex.sub_im, Complex.log_im, Complex.log_im, hend]
  rcases lt_or_gt_of_ne hz_im_ne with hneg | hpos
  · left
    have hargz : z.arg = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hz_re, hneg⟩
    have hargneg : (-z).arg = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr
        ⟨by simp [hz_re], by simpa using hneg⟩
    rw [hargz, hargneg] at him
    linarith
  · right
    have hargz : z.arg = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨hz_re, hpos⟩
    have hargneg : (-z).arg = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr
        ⟨by simp [hz_re], by simpa using hpos⟩
    rw [hargz, hargneg] at him
    linarith

noncomputable def nearestScalarMap {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) (x : ℂ) :
    C(ParameterInterval, ℂ) :=
  { toFun := fun δ => nearestScalar r a x δ
    continuous_toFun := nearestScalar_continuous hr a x }

theorem nearestScalar_period_eq_neg_zero {r : ℝ → Plane}
    (a : ℝ) (x : ℂ) :
    nearestScalar r a x period = -nearestScalar r a x 0 := by
  rw [nearestScalar, nearestScalar, chordScale_period, chordScale_zero,
    extendedSecant_period, extendedSecant_zero, map_neg, div_neg]
  simp

theorem nearestScalar_log_endpoint_im {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) (x : ℂ)
    (hx : x ∉ Set.range (curveCircle r hr))
    (ha : ∀ t : ℝ,
      ‖planeToComplex (r a) - x‖ ≤ ‖planeToComplex (r t) - x‖) :
    (Complex.log (nearestScalar r a x period) -
          Complex.log (nearestScalar r a x 0)).im = Real.pi ∨
      (Complex.log (nearestScalar r a x period) -
          Complex.log (nearestScalar r a x 0)).im = -Real.pi := by
  let Q := nearestScalarMap hr a x
  have hQ_ne (δ : ParameterInterval) : Q δ ≠ 0 := by
    exact nearestScalar_ne_zero hr a x hx δ δ.property
  have hQ_re (δ : ParameterInterval) : 0 ≤ (Q δ).re := by
    exact nearestScalar_re_nonneg hr a x ha δ δ.property
  have hend : Q parameterPeriod = -Q parameterZero := by
    exact nearestScalar_period_eq_neg_zero a x
  simpa [Q, nearestScalarMap, parameterPeriod, parameterZero] using
    log_endpoint_im_eq_pi_or_neg Q hQ_ne hQ_re hend

/-- The integral of the logarithmic derivative of a nonvanishing differentiable
path is the endpoint difference of any continuous logarithmic lift. -/
theorem integral_logDeriv_eq_logLift_sub (q q' : ℝ → ℂ)
    (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq'cont : Continuous q')
    (hqne : ∀ t, q t ≠ 0)
    (H : C(ParameterInterval, ℂ))
    (hH : ∀ δ, Complex.exp (H δ) = q δ) :
    (∫ t in (0 : ℝ)..period, q' t / q t) =
      H parameterPeriod - H parameterZero := by
  have hqcont : Continuous q :=
    continuous_iff_continuousAt.mpr fun t => (hq t).continuousAt
  have hfcont : Continuous (fun t => q' t / q t) :=
    hq'cont.div₀ hqcont hqne
  let I : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, q' u / q u
  have hI (t : ℝ) : HasDerivAt I (q' t / q t) t := by
    dsimp [I]
    exact intervalIntegral.integral_hasDerivAt_right
      (hfcont.intervalIntegrable 0 t)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hfcont.continuousAt
  let h : ℝ → ℂ := fun t => Complex.exp (-I t) * q t
  have hhderiv (t : ℝ) : HasDerivAt h 0 t := by
    have hcalc := (hI t).neg.cexp.mul (hq t)
    change HasDerivAt h
      (Complex.exp (-I t) * (-(q' t / q t)) * q t +
        Complex.exp (-I t) * q' t) t at hcalc
    have hcoeff :
        Complex.exp (-I t) * (-(q' t / q t)) * q t +
          Complex.exp (-I t) * q' t = 0 := by
      rw [show Complex.exp (-I t) * (-(q' t / q t)) * q t =
          -(Complex.exp (-I t) * ((q' t / q t) * q t)) by ring,
        div_mul_cancel₀ _ (hqne t)]
      ring
    rw [hcoeff] at hcalc
    exact hcalc
  have hconst (t : ℝ) : h t = h 0 := by
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := t) (f := h) (f' := fun _ => (0 : ℂ))
      (fun u _ => hhderiv u) (continuous_const.intervalIntegrable 0 t)
    apply sub_eq_zero.mp
    simpa using hfund.symm
  have hI0 : I 0 = 0 := by simp [I]
  have hexpI (t : ℝ) : Complex.exp (I t) * q 0 = q t := by
    have ht := hconst t
    change Complex.exp (-I t) * q t = Complex.exp (-I 0) * q 0 at ht
    rw [hI0] at ht
    simp only [neg_zero, Complex.exp_zero, one_mul] at ht
    calc
      Complex.exp (I t) * q 0 =
          Complex.exp (I t) * (Complex.exp (-I t) * q t) := by rw [ht]
      _ = (Complex.exp (I t) * Complex.exp (-I t)) * q t := by ring
      _ = q t := by rw [← Complex.exp_add]; simp
  have hIcont : Continuous I :=
    continuous_iff_continuousAt.mpr fun t => (hI t).continuousAt
  let G : C(ParameterInterval, ℂ) :=
    { toFun := fun δ => H parameterZero + I δ
      continuous_toFun := continuous_const.add
        (hIcont.comp continuous_subtype_val) }
  have hGexp (δ : ParameterInterval) : Complex.exp (G δ) = q δ := by
    change Complex.exp (H parameterZero + I δ) = q δ
    rw [Complex.exp_add, hH parameterZero]
    change q 0 * Complex.exp (I δ) = q δ
    simpa [mul_comm] using hexpI δ
  have hbase : G parameterZero = H parameterZero := by
    simp [G, parameterZero, hI0]
  letI : ContractibleSpace ParameterInterval :=
    (convex_Icc (0 : ℝ) period).contractibleSpace
      ⟨0, le_rfl, period_pos.le⟩
  letI : LocPathConnectedSpace ParameterInterval :=
    (convex_Icc (0 : ℝ) period).locPathConnectedSpace
  have hmaps : G = H :=
    Submission.Helpers.continuousMap_eq_of_exp_eq G H parameterZero hbase
      (fun δ => (hGexp δ).trans (hH δ).symm)
  calc
    (∫ t in (0 : ℝ)..period, q' t / q t) = I period := rfl
    _ = G parameterPeriod - G parameterZero := by
      simp [G, parameterPeriod, parameterZero, hI0]
    _ = H parameterPeriod - H parameterZero := by rw [hmaps]

noncomputable def complexCurve (r : ℝ → Plane) (t : ℝ) : ℂ :=
  planeToComplex (r t)

noncomputable def complexVelocity (r : ℝ → Plane) (t : ℝ) : ℂ :=
  planeToComplex (velocity r t)

/-- The analytic winding integral of the closed curve about `x`. It is
normalized by `2π`, which is `period` in the challenge interface. -/
noncomputable def analyticWinding (r : ℝ → Plane) (x : ℂ) : ℝ :=
  (∫ t in (0 : ℝ)..period,
    (complexVelocity r t / (complexCurve r t - x)).im) / period

theorem complexCurve_periodic {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Function.Periodic (complexCurve r) period := by
  intro t
  exact congrArg planeToComplex (hr.periodic t)

theorem complexVelocity_periodic {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Function.Periodic (complexVelocity r) period := by
  intro t
  exact congrArg planeToComplex (velocity_periodic hr t)

theorem hasDerivAt_complexCurve' {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (t : ℝ) :
    HasDerivAt (complexCurve r) (complexVelocity r t) t := by
  exact hasDerivAt_complexCurve hr t

/-- If the tangent makes the negative branch of the orientation-free turning
alternative, then the curve has analytic winding `0` or `-1` about every point
of its complement. -/
theorem analyticWinding_eq_zero_or_neg_one {r : ℝ → Plane} {α : ℝ → ℝ}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (hα : IsTangentAngleLift r α)
    (hturn : α period - α 0 = -period)
    (x : ℂ) (hx : x ∉ Set.range (curveCircle r hr)) :
    analyticWinding r x = 0 ∨ analyticWinding r x = -1 := by
  obtain ⟨a, ha⟩ := exists_nearest_parameter hr x
  obtain ⟨F, hF⟩ := exists_secantLog hr
  let Q := nearestScalarMap hr a x
  have hQ_ne (δ : ParameterInterval) : Q δ ≠ 0 := by
    exact nearestScalar_ne_zero hr a x hx δ δ.property
  have hQ_re (δ : ParameterInterval) : 0 ≤ (Q δ).re := by
    exact nearestScalar_re_nonneg hr a x ha δ δ.property
  have hQ_slit (δ : ParameterInterval) : Q δ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hpos : 0 < (Q δ).re
    · exact Or.inl hpos
    · refine Or.inr ?_
      intro him
      apply hQ_ne δ
      apply Complex.ext
      · simpa using le_antisymm (le_of_not_gt hpos) (hQ_re δ)
      · simpa using him
  let V : C(ParameterInterval, ℂ) := F.comp (stripVerticalMap a)
  let P : C(ParameterInterval, ℂ) :=
    { toFun := fun δ => Complex.log (Q δ)
      continuous_toFun := Q.continuous.clog hQ_slit }
  let H : C(ParameterInterval, ℂ) := V + P
  let q : ℝ → ℂ := fun δ => complexCurve r (a + δ) - x
  let q' : ℝ → ℂ := fun δ => complexVelocity r (a + δ)
  have hqne (δ : ℝ) : q δ ≠ 0 := by
    intro hzero
    apply hx
    refine ⟨Circle.exp (a + δ), ?_⟩
    rw [curveCircle_exp]
    exact sub_eq_zero.mp hzero
  have hq (δ : ℝ) : HasDerivAt q (q' δ) δ := by
    change HasDerivAt (fun u => complexCurve r (a + u) - x)
      (complexVelocity r (a + δ)) δ
    exact ((hasDerivAt_complexCurve' hr (a + δ)).comp_const_add a δ).sub_const x
  have hq'cont : Continuous q' := by
    exact planeToComplex.continuous.comp
      ((velocity_continuous hr).comp (continuous_const.add continuous_id))
  have hH (δ : ParameterInterval) : Complex.exp (H δ) = q δ := by
    change Complex.exp (V δ + P δ) = q δ
    rw [Complex.exp_add]
    have hV : Complex.exp (V δ) =
        planeToComplex (extendedSecant r a δ) := by
      simpa [V, stripVerticalMap] using hF (stripVerticalMap a δ)
    have hP : Complex.exp (P δ) = nearestScalar r a x δ := by
      exact Complex.exp_log (hQ_ne δ)
    rw [hV, hP]
    exact nearestScalar_factor hr a x δ δ.property
  have hlog := integral_logDeriv_eq_logLift_sub q q' hq hq'cont hqne H hH
  let p₀ : secantStrip := stripBottom a
  have hperiod := secantLog_bottom_period hr F hF p₀ 0
  have hangle := secantLog_bottom_period_eq_angle hα F hF 0
  have hperiod' :
      F (stripBottom period) - F (stripBottom 0) =
        2 * (F (stripTop a) - F (stripBottom a)) := by
    simpa [p₀] using hperiod
  have hangle' :
      F (stripBottom period) - F (stripBottom 0) =
        (-period) * Complex.I := by
    have hturnC : ((α period : ℂ) - (α 0 : ℂ)) = -(period : ℂ) := by
      exact_mod_cast hturn
    simpa [hturnC] using hangle
  have htwice :
      (2 : ℂ) * (F (stripTop a) - F (stripBottom a)) =
        (-period) * Complex.I :=
    hperiod'.symm.trans hangle'
  have hVdiff :
      V parameterPeriod - V parameterZero =
        -(Real.pi : ℂ) * Complex.I := by
    have hVperiod : V parameterPeriod = F (stripTop a) := by
      change F (stripVerticalMap a parameterPeriod) = F (stripTop a)
      congr 1
    have hVzero : V parameterZero = F (stripBottom a) := by
      change F (stripVerticalMap a parameterZero) = F (stripBottom a)
      congr 1
    have hmul :
        (2 : ℂ) * (V parameterPeriod - V parameterZero) =
          (2 : ℂ) * (-(Real.pi : ℂ) * Complex.I) := by
      rw [hVperiod, hVzero, htwice]
      simp [period]
      ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hmul
  have hPim :
      (P parameterPeriod - P parameterZero).im = Real.pi ∨
        (P parameterPeriod - P parameterZero).im = -Real.pi := by
    simpa [P, Q, nearestScalarMap, parameterPeriod, parameterZero] using
      nearestScalar_log_endpoint_im hr a x hx ha
  have hHsplit :
      H parameterPeriod - H parameterZero =
        (V parameterPeriod - V parameterZero) +
          (P parameterPeriod - P parameterZero) := by
    simp [H]
    ring
  have hHim :
      (H parameterPeriod - H parameterZero).im = 0 ∨
        (H parameterPeriod - H parameterZero).im = -period := by
    rcases hPim with hPim | hPim
    · left
      rw [hHsplit, hVdiff, Complex.add_im, Complex.mul_im, hPim]
      norm_num
    · right
      rw [hHsplit, hVdiff, Complex.add_im, Complex.mul_im, hPim]
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.I_im, mul_one]
      simp [period]
      ring
  let f : ℝ → ℂ := fun t =>
    complexVelocity r t / (complexCurve r t - x)
  have hfcont : Continuous f := by
    have hden : ∀ t, complexCurve r t - x ≠ 0 := by
      intro t hzero
      apply hx
      refine ⟨Circle.exp t, ?_⟩
      rw [curveCircle_exp]
      exact sub_eq_zero.mp hzero
    exact (planeToComplex.continuous.comp (velocity_continuous hr)).div₀
      ((planeToComplex.continuous.comp hr.smooth.continuous).sub continuous_const)
      hden
  have hfper : Function.Periodic f period := by
    intro t
    simp only [f]
    rw [complexVelocity_periodic hr t, complexCurve_periodic hr t]
  have hshift :
      (∫ t in (0 : ℝ)..period, q' t / q t) =
        ∫ t in (0 : ℝ)..period, f t := by
    calc
      (∫ t in (0 : ℝ)..period, q' t / q t) =
          ∫ t in (0 : ℝ)..period, f (t + a) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp [q, q', f, add_comm]
      _ = ∫ t in a..period + a, f t := by
        simpa only [zero_add] using
          intervalIntegral.integral_comp_add_right (a := 0) (b := period) f a
      _ = ∫ t in (0 : ℝ)..period, f t := by
        simpa [add_comm] using hfper.intervalIntegral_add_eq a 0
  have hfint : IntervalIntegrable f volume 0 period :=
    hfcont.intervalIntegrable _ _
  have himIntegral :
      (∫ t in (0 : ℝ)..period, (f t).im) =
        (H parameterPeriod - H parameterZero).im := by
    change (∫ t in (0 : ℝ)..period, RCLike.im (f t)) =
      RCLike.im (H parameterPeriod - H parameterZero)
    rw [intervalIntegral.intervalIntegral_im hfint, ← hshift, hlog]
  rcases hHim with hzero | hneg
  · left
    rw [analyticWinding, show
      (fun t =>
        (complexVelocity r t / (complexCurve r t - x)).im) =
          fun t => (f t).im by rfl,
      himIntegral, hzero, zero_div]
  · right
    rw [analyticWinding, show
      (fun t =>
        (complexVelocity r t / (complexCurve r t - x)).im) =
          fun t => (f t).im by rfl,
      himIntegral, hneg]
    exact neg_div_self period_pos.ne'

end

end Submission.Orientation
