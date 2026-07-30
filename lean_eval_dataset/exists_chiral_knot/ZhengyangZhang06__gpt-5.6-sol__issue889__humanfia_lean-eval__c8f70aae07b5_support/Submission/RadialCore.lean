import Submission.RadialSpine

open Complex

namespace Submission.RadialCore

noncomputable section

def zCoordinate (z : ℂ) : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) * z

def wCoordinate (w : ℂ) : ℂ :=
  Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * I) * w

theorem zCoordinate_sq (z : ℂ) : zCoordinate z ^ 2 = I * z ^ 2 := by
  unfold zCoordinate
  rw [mul_pow]
  have hexp :
      Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) ^ 2 = I := by
    rw [← Complex.exp_nat_mul]
    have harg :
        ((2 : ℕ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * I) =
          (Real.pi / 2 : ℂ) * I := by
      push_cast
      ring
    rw [harg, Complex.exp_pi_div_two_mul_I]
  rw [hexp]

theorem norm_zCoordinate (z : ℂ) : ‖zCoordinate z‖ = ‖z‖ := by
  unfold zCoordinate
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem radialCube_wCoordinate (w : ℂ) :
    RadialMilnor.radialCube (wCoordinate w) =
      I * RadialMilnor.radialCube w := by
  by_cases hw : w = 0
  · simp [hw, wCoordinate]
  · have hrot : wCoordinate w ≠ 0 := by
      exact mul_ne_zero (Complex.exp_ne_zero _) hw
    rw [RadialMilnor.radialCube_of_ne hrot,
      RadialMilnor.radialCube_of_ne hw]
    unfold wCoordinate
    rw [mul_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hexp :
        Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * I) ^ 3 = I := by
      rw [← Complex.exp_nat_mul]
      have harg :
          ((3 : ℕ) : ℂ) * (((Real.pi / 6 : ℝ) : ℂ) * I) =
            (Real.pi / 2 : ℂ) * I := by
        push_cast
        ring
      rw [harg, Complex.exp_pi_div_two_mul_I]
    rw [hexp]
    ring

theorem norm_wCoordinate (w : ℂ) : ‖wCoordinate w‖ = ‖w‖ := by
  unfold wCoordinate
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem zTerm_eq_coordinate (z : ℂ) :
    RadialSpine.zTerm z = 16 * zCoordinate z ^ 2 := by
  rw [zCoordinate_sq]
  simp [RadialSpine.zTerm]
  ring

theorem wTerm_eq_coordinate (w : ℂ) :
    RadialSpine.wTerm w = 9 * RadialMilnor.radialCube (wCoordinate w) := by
  rw [radialCube_wCoordinate]
  simp [RadialSpine.wTerm]
  ring

theorem spine_term_sum_pos (q : RadialSpine.Spine) :
    0 < (RadialSpine.zTerm q.1.1.1.1).re +
      (RadialSpine.wTerm q.1.1.1.2).re := by
  have h := q.1.2.1
  rw [RadialSpine.polynomial_eq_terms] at h
  simpa using h

theorem spine_abs_zTerm_re (q : RadialSpine.Spine) :
    |(RadialSpine.zTerm q.1.1.1.1).re| = 16 * normSq q.1.1.1.1 := by
  calc
    |(RadialSpine.zTerm q.1.1.1.1).re| =
        ‖RadialSpine.zTerm q.1.1.1.1‖ :=
      Complex.abs_re_eq_norm.mpr q.2.1
    _ = 16 * ‖q.1.1.1.1‖ ^ 2 := RadialSpine.norm_zTerm _
    _ = 16 * normSq q.1.1.1.1 := by rw [normSq_eq_norm_sq]

theorem spine_abs_wTerm_re (q : RadialSpine.Spine) :
    |(RadialSpine.wTerm q.1.1.1.2).re| = 9 * normSq q.1.1.1.2 := by
  calc
    |(RadialSpine.wTerm q.1.1.1.2).re| =
        ‖RadialSpine.wTerm q.1.1.1.2‖ :=
      Complex.abs_re_eq_norm.mpr q.2.2
    _ = 9 * ‖q.1.1.1.2‖ ^ 2 := RadialSpine.norm_wTerm _
    _ = 9 * normSq q.1.1.1.2 := by rw [normSq_eq_norm_sq]

theorem spine_diamond (q : RadialSpine.Spine) :
    |(RadialSpine.zTerm q.1.1.1.1).re| / 16 +
        |(RadialSpine.wTerm q.1.1.1.2).re| / 9 = 1 := by
  rw [spine_abs_zTerm_re, spine_abs_wTerm_re]
  calc
    16 * normSq q.1.1.1.1 / 16 + 9 * normSq q.1.1.1.2 / 9 =
        normSq q.1.1.1.1 + normSq q.1.1.1.2 := by ring
    _ = 1 := q.1.1.2

def Core := {q : RadialSpine.Spine //
  0 ≤ (RadialSpine.zTerm q.1.1.1.1).re ∧
    0 ≤ (RadialSpine.wTerm q.1.1.1.2).re}

instance : TopologicalSpace Core := by
  unfold Core
  infer_instance

theorem core_diamond (q : Core) :
    (RadialSpine.zTerm q.1.1.1.1.1).re / 16 +
        (RadialSpine.wTerm q.1.1.1.1.2).re / 9 = 1 := by
  have h := spine_diamond q.1
  rwa [abs_of_nonneg q.2.1, abs_of_nonneg q.2.2] at h

theorem core_term_sum_pos (q : Core) :
    0 < (RadialSpine.zTerm q.1.1.1.1.1).re +
      (RadialSpine.wTerm q.1.1.1.1.2).re :=
  spine_term_sum_pos q.1

private theorem w_ne_of_zTerm_re_neg (q : RadialSpine.Spine)
    (hzneg : (RadialSpine.zTerm q.1.1.1.1).re < 0) : q.1.1.1.2 ≠ 0 := by
  have hwpos : 0 < (RadialSpine.wTerm q.1.1.1.2).re := by
    linarith [spine_term_sum_pos q]
  intro hw
  simp [hw, RadialSpine.wTerm_zero] at hwpos

private theorem z_ne_of_wTerm_re_neg (q : RadialSpine.Spine)
    (hwneg : (RadialSpine.wTerm q.1.1.1.2).re < 0) : q.1.1.1.1 ≠ 0 := by
  have hzpos : 0 < (RadialSpine.zTerm q.1.1.1.1).re := by
    linarith [spine_term_sum_pos q]
  intro hz
  simp [hz, RadialSpine.zTerm_zero] at hzpos

private def normalizeW (q : RadialSpine.Spine) : ℂ :=
  ((‖q.1.1.1.2‖⁻¹ : ℝ) : ℂ) * q.1.1.1.2

private def normalizeZ (q : RadialSpine.Spine) : ℂ :=
  ((‖q.1.1.1.1‖⁻¹ : ℝ) : ℂ) * q.1.1.1.1

private theorem normSq_normalizeW (q : RadialSpine.Spine)
    (hw : q.1.1.1.2 ≠ 0) : normSq (normalizeW q) = 1 := by
  rw [normalizeW, normSq_mul, normSq_ofReal, normSq_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hw]

private theorem normSq_normalizeZ (q : RadialSpine.Spine)
    (hz : q.1.1.1.1 ≠ 0) : normSq (normalizeZ q) = 1 := by
  rw [normalizeZ, normSq_mul, normSq_ofReal, normSq_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hz]

private def retractNegativeZ (q : RadialSpine.Spine)
    (hzneg : (RadialSpine.zTerm q.1.1.1.1).re < 0) : Core := by
  have hwpos : 0 < (RadialSpine.wTerm q.1.1.1.2).re := by
    linarith [spine_term_sum_pos q]
  have hw := w_ne_of_zTerm_re_neg q hzneg
  let r : ℝ := ‖q.1.1.1.2‖⁻¹
  have hrpos : 0 < r := inv_pos.mpr (norm_pos_iff.mpr hw)
  have hrSqIm : ((r : ℂ) ^ 2).im = 0 := by simp [pow_two]
  let sphere : RadialMilnor.CSphere := ⟨(0, normalizeW q), by
    change normSq 0 + normSq (normalizeW q) = 1
    rw [normSq_normalizeW q hw]
    simp⟩
  let fiber : RadialMilnor.Fiber := ⟨sphere, by
    rw [RadialSpine.polynomial_eq_terms]
    change 0 < (RadialSpine.zTerm 0 +
        RadialSpine.wTerm (((r : ℝ) : ℂ) * q.1.1.1.2)).re ∧
      (RadialSpine.zTerm 0 +
        RadialSpine.wTerm (((r : ℝ) : ℂ) * q.1.1.1.2)).im = 0
    rw [RadialSpine.zTerm_zero, zero_add,
      RadialSpine.wTerm_smul_nonneg r hrpos.le]
    constructor
    · simpa [mul_re, pow_two, q.2.2] using
        mul_pos (sq_pos_of_pos hrpos) hwpos
    · rw [mul_im, hrSqIm, q.2.2]
      simp⟩
  let spine : RadialSpine.Spine := ⟨fiber, by
    change (RadialSpine.zTerm 0).im = 0 ∧
      (RadialSpine.wTerm (((r : ℝ) : ℂ) * q.1.1.1.2)).im = 0
    rw [RadialSpine.zTerm_zero,
      RadialSpine.wTerm_smul_nonneg r hrpos.le]
    constructor
    · simp
    · rw [mul_im, hrSqIm, q.2.2]
      simp⟩
  exact ⟨spine, by
    change 0 ≤ (RadialSpine.zTerm 0).re ∧
      0 ≤ (RadialSpine.wTerm (((r : ℝ) : ℂ) * q.1.1.1.2)).re
    rw [RadialSpine.zTerm_zero,
      RadialSpine.wTerm_smul_nonneg r hrpos.le]
    constructor
    · simp
    · simpa [mul_re, pow_two, q.2.2] using
        (mul_pos (sq_pos_of_pos hrpos) hwpos).le⟩

private def retractNegativeW (q : RadialSpine.Spine)
    (hwneg : (RadialSpine.wTerm q.1.1.1.2).re < 0) : Core := by
  have hzpos : 0 < (RadialSpine.zTerm q.1.1.1.1).re := by
    linarith [spine_term_sum_pos q]
  have hz := z_ne_of_wTerm_re_neg q hwneg
  let r : ℝ := ‖q.1.1.1.1‖⁻¹
  have hrpos : 0 < r := inv_pos.mpr (norm_pos_iff.mpr hz)
  have hrSqIm : ((r : ℂ) ^ 2).im = 0 := by simp [pow_two]
  let sphere : RadialMilnor.CSphere := ⟨(normalizeZ q, 0), by
    change normSq (normalizeZ q) + normSq 0 = 1
    rw [normSq_normalizeZ q hz]
    simp⟩
  let fiber : RadialMilnor.Fiber := ⟨sphere, by
    rw [RadialSpine.polynomial_eq_terms]
    change 0 < (RadialSpine.zTerm (((r : ℝ) : ℂ) * q.1.1.1.1) +
        RadialSpine.wTerm 0).re ∧
      (RadialSpine.zTerm (((r : ℝ) : ℂ) * q.1.1.1.1) +
        RadialSpine.wTerm 0).im = 0
    rw [RadialSpine.wTerm_zero, add_zero,
      RadialSpine.zTerm_smul_nonneg r hrpos.le]
    constructor
    · simpa [mul_re, pow_two, q.2.1] using
        mul_pos (sq_pos_of_pos hrpos) hzpos
    · rw [mul_im, hrSqIm, q.2.1]
      simp⟩
  let spine : RadialSpine.Spine := ⟨fiber, by
    change (RadialSpine.zTerm (((r : ℝ) : ℂ) * q.1.1.1.1)).im = 0 ∧
      (RadialSpine.wTerm 0).im = 0
    rw [RadialSpine.wTerm_zero,
      RadialSpine.zTerm_smul_nonneg r hrpos.le]
    constructor
    · rw [mul_im, hrSqIm, q.2.1]
      simp
    · simp⟩
  exact ⟨spine, by
    change 0 ≤ (RadialSpine.zTerm (((r : ℝ) : ℂ) * q.1.1.1.1)).re ∧
      0 ≤ (RadialSpine.wTerm 0).re
    rw [RadialSpine.wTerm_zero,
      RadialSpine.zTerm_smul_nonneg r hrpos.le]
    constructor
    · simpa [mul_re, pow_two, q.2.1] using
        (mul_pos (sq_pos_of_pos hrpos) hzpos).le
    · simp⟩

def coreRetraction (q : RadialSpine.Spine) : Core :=
  if hzneg : (RadialSpine.zTerm q.1.1.1.1).re < 0 then
    retractNegativeZ q hzneg
  else if hwneg : (RadialSpine.wTerm q.1.1.1.2).re < 0 then
    retractNegativeW q hwneg
  else
    ⟨q, le_of_not_gt hzneg, le_of_not_gt hwneg⟩

@[simp] theorem coreRetraction_core (q : Core) : coreRetraction q.1 = q := by
  rw [coreRetraction, dif_neg (not_lt_of_ge q.2.1),
    dif_neg (not_lt_of_ge q.2.2)]
  rfl

end


end Submission.RadialCore
