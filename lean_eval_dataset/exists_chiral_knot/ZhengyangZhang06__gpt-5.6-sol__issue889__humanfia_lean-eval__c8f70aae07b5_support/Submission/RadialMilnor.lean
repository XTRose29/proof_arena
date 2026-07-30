import Submission.Milnor

open Complex

namespace Submission.RadialMilnor

noncomputable section

abbrev CSphere := Milnor.CSphere

def radialCube (w : ℂ) : ℂ :=
  if w = 0 then 0 else w ^ 3 / ‖w‖

@[simp] theorem radialCube_zero : radialCube 0 = 0 := by
  simp [radialCube]

theorem radialCube_of_ne {w : ℂ} (hw : w ≠ 0) :
    radialCube w = w ^ 3 / ‖w‖ := by
  simp [radialCube, hw]

theorem norm_radialCube (w : ℂ) : ‖radialCube w‖ = ‖w‖ ^ 2 := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [radialCube_of_ne hw, norm_div, norm_pow]
    have hnormCast : ‖(‖w‖ : ℂ)‖ = ‖w‖ := by simp
    rw [hnormCast]
    field_simp [norm_ne_zero_iff.mpr hw]

theorem radialCube_continuous : Continuous radialCube := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst w
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
    intro y hy
    have hynorm : ‖y‖ < min 1 ε := by simpa only [dist_zero_right] using hy
    simp only [radialCube_zero, dist_zero_right, norm_radialCube]
    have hyOne : ‖y‖ < 1 := lt_of_lt_of_le hynorm (min_le_left 1 ε)
    have hyEps : ‖y‖ < ε := lt_of_lt_of_le hynorm (min_le_right 1 ε)
    nlinarith [norm_nonneg y]
  · have hcontinuous : ContinuousAt (fun z : ℂ => z ^ 3 / (‖z‖ : ℂ)) w := by
      have hnorm : ContinuousAt (fun z : ℂ => (‖z‖ : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp continuousAt_id.norm
      exact (continuousAt_id.pow 3).div hnorm (by
        exact_mod_cast norm_ne_zero_iff.mpr hw)
    apply hcontinuous.congr_of_eventuallyEq
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hw] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simp [radialCube, hz0]

theorem radialCube_smul_of_nonneg (r : ℝ) (hr : 0 ≤ r) (w : ℂ) :
    radialCube ((r : ℂ) * w) = (r : ℂ) ^ 2 * radialCube w := by
  by_cases hr0 : r = 0
  · simp [hr0]
  by_cases hw : w = 0
  · simp [hw]
  rw [radialCube_of_ne (mul_ne_zero (ofReal_ne_zero.mpr hr0) hw),
    radialCube_of_ne hw, mul_pow, norm_mul]
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_nonneg hr]
  rw [hrnorm]
  push_cast
  field_simp [hr0, norm_ne_zero_iff.mpr hw]

def cubeRoot (r : ℂ) : ℂ := r ^ ((3 : ℂ)⁻¹)

@[simp] theorem cubeRoot_pow_three (r : ℂ) : cubeRoot r ^ 3 = r := by
  exact Complex.cpow_nat_inv_pow r (by norm_num)

theorem cubeRoot_ne_zero {r : ℂ} (hr : r ≠ 0) : cubeRoot r ≠ 0 := by
  intro hzero
  have := cubeRoot_pow_three r
  rw [hzero, zero_pow (by norm_num)] at this
  exact hr this.symm

def radialMultiplier (r : ℂ) : ℂ :=
  if r = 0 then 0
  else (Real.sqrt ‖r‖ : ℂ) * (cubeRoot r / ‖cubeRoot r‖)

@[simp] theorem radialMultiplier_zero : radialMultiplier 0 = 0 := by
  simp [radialMultiplier]

theorem radialMultiplier_of_ne {r : ℂ} (hr : r ≠ 0) :
    radialMultiplier r =
      (Real.sqrt ‖r‖ : ℂ) * (cubeRoot r / ‖cubeRoot r‖) := by
  simp [radialMultiplier, hr]

theorem norm_radialMultiplier (r : ℂ) :
    ‖radialMultiplier r‖ = Real.sqrt ‖r‖ := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [radialMultiplier_of_ne hr, norm_mul, norm_div]
    have hroot : cubeRoot r ≠ 0 := cubeRoot_ne_zero hr
    have hnormCast : ‖(‖cubeRoot r‖ : ℂ)‖ = ‖cubeRoot r‖ := by simp
    rw [hnormCast, div_self (norm_ne_zero_iff.mpr hroot), mul_one]
    simp

theorem radialMultiplier_ne_zero {r : ℂ} (hr : r ≠ 0) :
    radialMultiplier r ≠ 0 := by
  rw [ne_eq, ← norm_eq_zero, norm_radialMultiplier]
  exact Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hr)

theorem radialMultiplier_phase (r : ℂ) :
    radialMultiplier r ^ 3 / ‖radialMultiplier r‖ = r := by
  by_cases hr : r = 0
  · simp [hr]
  · let u : ℂ := cubeRoot r
    have hu : u ≠ 0 := cubeRoot_ne_zero hr
    have huPow : u ^ 3 = r := cubeRoot_pow_three r
    have huNormPow : ‖u‖ ^ 3 = ‖r‖ := by
      calc
        ‖u‖ ^ 3 = ‖u ^ 3‖ := by rw [norm_pow]
        _ = ‖r‖ := by rw [huPow]
    have hrNormPos : 0 < ‖r‖ := norm_pos_iff.mpr hr
    have hsqrtPos : 0 < Real.sqrt ‖r‖ := Real.sqrt_pos.2 hrNormPos
    rw [norm_radialMultiplier, radialMultiplier_of_ne hr, mul_pow, div_pow]
    change ((Real.sqrt ‖r‖ : ℂ) ^ 3 * (u ^ 3 / (‖u‖ : ℂ) ^ 3)) /
        (Real.sqrt ‖r‖ : ℂ) = r
    rw [huPow]
    have hsqrtSq : Real.sqrt ‖r‖ ^ 2 = ‖r‖ := Real.sq_sqrt hrNormPos.le
    field_simp [ne_of_gt hsqrtPos, norm_ne_zero_iff.mpr hu]
    norm_cast
    exact hsqrtSq.trans huNormPow.symm

theorem radialMultiplier_continuousAt_of_re_nonneg {r : ℂ} (hrRe : 0 ≤ r.re) :
    ContinuousAt radialMultiplier r := by
  by_cases hr : r = 0
  · subst r
    rw [ContinuousAt, radialMultiplier_zero, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun z => norm_nonneg (radialMultiplier z))
      (fun z => (norm_radialMultiplier z).le) ?_
    have hnormCont : Continuous (fun z : ℂ => ‖z‖) := continuous_norm
    have hsqrt : Filter.Tendsto (fun z : ℂ => Real.sqrt ‖z‖) (nhds 0)
        (nhds (Real.sqrt ‖(0 : ℂ)‖)) :=
      (Real.continuous_sqrt.comp hnormCont).continuousAt
    simpa using hsqrt
  · have hroot : ContinuousAt cubeRoot r := by
      exact (Complex.continuousAt_cpow_const_of_re_pos (Or.inl hrRe) (by norm_num))
    have hrootNorm : ContinuousAt (fun z => (‖cubeRoot z‖ : ℂ)) r :=
      Complex.continuous_ofReal.continuousAt.comp hroot.norm
    have hsqrtNorm : ContinuousAt (fun z : ℂ => (Real.sqrt ‖z‖ : ℂ)) r :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuous_sqrt.comp continuous_norm).continuousAt)
    have hformula : ContinuousAt
        (fun z : ℂ => (Real.sqrt ‖z‖ : ℂ) *
          (cubeRoot z / (‖cubeRoot z‖ : ℂ))) r := by
      exact hsqrtNorm.mul (hroot.div hrootNorm (by
        exact_mod_cast norm_ne_zero_iff.mpr (cubeRoot_ne_zero hr)))
    apply hformula.congr_of_eventuallyEq
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hr] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact radialMultiplier_of_ne hz0

theorem radialCube_mul_radialMultiplier (r w : ℂ) :
    radialCube (radialMultiplier r * w) = r * radialCube w := by
  by_cases hr : r = 0
  · simp [hr]
  by_cases hw : w = 0
  · simp [hw]
  have hm : radialMultiplier r ≠ 0 := radialMultiplier_ne_zero hr
  rw [radialCube_of_ne (mul_ne_zero hm hw), radialCube_of_ne hw,
    mul_pow, norm_mul]
  calc
    radialMultiplier r ^ 3 * w ^ 3 /
          (‖radialMultiplier r‖ * ‖w‖ : ℝ) =
        (radialMultiplier r ^ 3 / ‖radialMultiplier r‖) *
          (w ^ 3 / ‖w‖) := by
      push_cast
      field_simp [norm_ne_zero_iff.mpr hm, norm_ne_zero_iff.mpr hw]
    _ = r * (w ^ 3 / ‖w‖) := by rw [radialMultiplier_phase]

def basePolynomial (q : CSphere) : ℂ :=
  16 * q.1.1 ^ 2 + 9 * radialCube q.1.2

def polynomial (q : CSphere) : ℂ :=
  I * basePolynomial q

theorem basePolynomial_continuous : Continuous basePolynomial := by
  have hz : Continuous (fun q : CSphere => q.1.1) := by fun_prop
  have hw : Continuous (fun q : CSphere => q.1.2) := by fun_prop
  exact (continuous_const.mul (hz.pow 2)).add
    (continuous_const.mul (radialCube_continuous.comp hw))

theorem polynomial_continuous : Continuous polynomial := by
  exact continuous_const.mul basePolynomial_continuous

theorem polynomial_eq_zero_iff (q : CSphere) :
    polynomial q = 0 ↔ basePolynomial q = 0 := by
  simp [polynomial, I_ne_zero]

theorem basePolynomial_north : basePolynomial Milnor.north = -9 * I := by
  simp [basePolynomial, Milnor.north, radialCube, norm_I]

@[simp] theorem polynomial_north : polynomial Milnor.north = 9 := by
  rw [polynomial, basePolynomial_north]
  calc
    I * (-9 * I) = -(9 * (I * I)) := by ring
    _ = 9 := by rw [I_mul_I]; norm_num

theorem basePolynomial_weightedRotate (s : ℝ) (q : CSphere) :
    basePolynomial (Milnor.weightedRotate s q) =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) * basePolynomial q := by
  have h2 : Complex.exp (((3 : ℝ) * s : ℝ) * I) ^ 2 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 : Complex.exp (((2 : ℝ) * s : ℝ) * I) ^ 3 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnorm : ‖Complex.exp (((2 * s : ℝ) : ℂ) * I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I (2 * s)
  by_cases hw : q.1.2 = 0
  · rw [basePolynomial]
    change 16 * (Complex.exp (((3 : ℝ) * s : ℝ) * I) * q.1.1) ^ 2 +
        9 * radialCube (Complex.exp (((2 : ℝ) * s : ℝ) * I) * q.1.2) =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) *
        (16 * q.1.1 ^ 2 + 9 * radialCube q.1.2)
    rw [hw]
    simp only [mul_zero, radialCube_zero, mul_zero, add_zero, mul_pow, h2]
    ring
  · have hrot_ne : Milnor.rotate 2 s q.1.2 ≠ 0 := by
      exact mul_ne_zero (Complex.exp_ne_zero _) hw
    rw [basePolynomial]
    change 16 * Milnor.rotate 3 s q.1.1 ^ 2 +
        9 * radialCube (Milnor.rotate 2 s q.1.2) =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) *
        (16 * q.1.1 ^ 2 + 9 * radialCube q.1.2)
    rw [radialCube_of_ne hrot_ne, radialCube_of_ne hw]
    unfold Milnor.rotate
    rw [mul_pow, mul_pow]
    rw [show Complex.exp (((((3 : ℕ) : ℝ) * s : ℝ) : ℂ) * I) ^ 2 =
        Complex.exp (((6 : ℝ) * s : ℝ) * I) by simpa using h2]
    rw [show Complex.exp (((((2 : ℕ) : ℝ) * s : ℝ) : ℂ) * I) ^ 3 =
        Complex.exp (((6 : ℝ) * s : ℝ) * I) by simpa using h3]
    rw [norm_mul, show ‖Complex.exp (((((2 : ℕ) : ℝ) * s : ℝ) : ℂ) * I)‖ = 1 by
      simpa using hnorm, one_mul]
    ring

theorem polynomial_weightedRotate (s : ℝ) (q : CSphere) :
    polynomial (Milnor.weightedRotate s q) =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) * polynomial q := by
  rw [polynomial, basePolynomial_weightedRotate, polynomial]
  ring

theorem normSq_eq_of_basePolynomial_zero {z w : ℂ}
    (hsphere : normSq z + normSq w = 1)
    (hzero : 16 * z ^ 2 + 9 * radialCube w = 0) :
    normSq z = 9 / 25 ∧ normSq w = 16 / 25 := by
  have hw : w ≠ 0 := by
    intro hw
    rw [hw, radialCube_zero, mul_zero, add_zero] at hzero
    have hzsq : z * z = 0 := by
      have : z ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
      simpa [pow_two] using this
    have hz : z = 0 := by
      rcases mul_eq_zero.mp hzsq with hz | hz <;> exact hz
    simp [hz, hw, normSq_apply] at hsphere
  have heq : (16 : ℂ) * z ^ 2 = -((9 : ℂ) * radialCube w) := by
    exact eq_neg_of_add_eq_zero_left hzero
  have hnorm := congrArg norm heq
  rw [norm_mul, norm_ofNat, norm_pow, norm_neg, norm_mul, norm_ofNat,
    norm_radialCube] at hnorm
  have hzNormSq : ‖z‖ ^ 2 = normSq z := by
    rw [normSq_eq_norm_sq]
  have hwNormSq : ‖w‖ ^ 2 = normSq w := by
    rw [normSq_eq_norm_sq]
  rw [hzNormSq, hwNormSq] at hnorm
  constructor <;> nlinarith

theorem oldPolynomial_zero_of_basePolynomial_zero {z w : ℂ}
    (hsphere : normSq z + normSq w = 1)
    (hzero : 16 * z ^ 2 + 9 * radialCube w = 0) :
    64 * z ^ 2 + 45 * w ^ 3 = 0 := by
  obtain ⟨_, hwSq⟩ := normSq_eq_of_basePolynomial_zero hsphere hzero
  have hwNormSq : ‖w‖ ^ 2 = 16 / 25 := by
    simpa [normSq_eq_norm_sq] using hwSq
  have hwNorm : ‖w‖ = 4 / 5 := by
    have hnonneg := norm_nonneg w
    nlinarith
  have hw : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hwNorm]; norm_num)
  rw [radialCube_of_ne hw, hwNorm] at hzero
  norm_num at hzero
  linear_combination 4 * hzero

theorem basePolynomial_zero_iff_range (q : CSphere) :
    basePolynomial q = 0 ↔
      q ∈ Set.range (fun t : ℝ =>
        (Milnor.compactify (AlgebraicTrefoil.curve t)).1) := by
  constructor
  · intro hzero
    obtain ⟨t, hz, hw⟩ := AlgebraicTrefoil.exists_sphereCurve_of_polynomial_zero
      q.2 (oldPolynomial_zero_of_basePolynomial_zero q.2 hzero)
    refine ⟨t, ?_⟩
    change (Milnor.compactify (AlgebraicTrefoil.curve t)).1 = q
    rw [Milnor.compactify_curve]
    apply Subtype.ext
    exact Prod.ext hz.symm hw.symm
  · rintro ⟨t, rfl⟩
    change basePolynomial (Milnor.compactify (AlgebraicTrefoil.curve t)).1 = 0
    rw [Milnor.compactify_curve]
    change 16 * AlgebraicTrefoil.sphereCurveZ t ^ 2 +
      9 * radialCube (AlgebraicTrefoil.sphereCurveW t) = 0
    have hwNorm : ‖AlgebraicTrefoil.sphereCurveW t‖ = 4 / 5 := by
      have hwSq : ‖AlgebraicTrefoil.sphereCurveW t‖ ^ 2 = 16 / 25 := by
        rw [← normSq_eq_norm_sq]
        simp [AlgebraicTrefoil.sphereCurveW, normSq_apply]
        nlinarith [Real.sin_sq_add_cos_sq (2 * t)]
      nlinarith [norm_nonneg (AlgebraicTrefoil.sphereCurveW t)]
    have hw : AlgebraicTrefoil.sphereCurveW t ≠ 0 := by
      exact norm_ne_zero_iff.mp (by rw [hwNorm]; norm_num)
    rw [radialCube_of_ne hw, hwNorm,
      AlgebraicTrefoil.sphereCurveZ_eq_exp,
      AlgebraicTrefoil.sphereCurveW_eq_exp]
    have h2 : Complex.exp (((3 * t : ℝ) : ℂ) * I) ^ 2 =
        Complex.exp (((6 * t : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h3 : Complex.exp (((2 * t : ℝ) : ℂ) * I) ^ 3 =
        Complex.exp (((6 * t : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, mul_pow, h2, h3]
    norm_num
    ring

theorem polynomial_zero_iff_range (q : CSphere) :
    polynomial q = 0 ↔
      q ∈ Set.range (fun t : ℝ =>
        (Milnor.compactify (AlgebraicTrefoil.curve t)).1) := by
  rw [polynomial_eq_zero_iff, basePolynomial_zero_iff_range]

theorem polynomial_curve (t : ℝ) :
    polynomial (Milnor.compactify (AlgebraicTrefoil.curve t)).1 = 0 := by
  rw [polynomial_zero_iff_range]
  exact ⟨t, rfl⟩

def monodromy : CSphere ≃ CSphere := Milnor.weightedRotate (Real.pi / 3)

theorem polynomial_monodromy (q : CSphere) :
    polynomial (monodromy q) = polynomial q := by
  rw [monodromy, polynomial_weightedRotate]
  have harg : (((6 : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * I =
      2 * (Real.pi : ℂ) * I := by
    push_cast
    ring
  rw [harg, Complex.exp_two_pi_mul_I, one_mul]

def Fiber := {q : CSphere // 0 < (polynomial q).re ∧ (polynomial q).im = 0}

instance : TopologicalSpace Fiber := by
  unfold Fiber
  infer_instance

def fiberMonodromy : Fiber ≃ Fiber where
  toFun q := ⟨monodromy q.1, by rw [polynomial_monodromy]; exact q.2⟩
  invFun q := ⟨monodromy.symm q.1, by
    have h := polynomial_monodromy (monodromy.symm q.1)
    rw [monodromy.apply_symm_apply] at h
    rw [← h]
    exact q.2⟩
  left_inv q := by
    apply Subtype.ext
    exact monodromy.symm_apply_apply q.1
  right_inv q := by
    apply Subtype.ext
    exact monodromy.apply_symm_apply q.1

def fiberMonodromyHomeomorph : Fiber ≃ₜ Fiber where
  toEquiv := fiberMonodromy
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Milnor.weightedRotateHomeomorph (Real.pi / 3)).continuous.comp
      continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (Milnor.weightedRotateHomeomorph (Real.pi / 3)).symm.continuous.comp
      continuous_subtype_val

end

end Submission.RadialMilnor
