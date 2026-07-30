import Submission.Scalar

namespace Submission.Majorant

noncomputable section

theorem loss_error_exponent_step (n : ℕ) :
    lossExponent n + errorExponent (n + 1) ≤ 2 * errorExponent n := by
  unfold errorExponent
  rw [pow_succ]
  have hloss : 3 * lossExponent (n + 1) ≤ 5 * lossExponent n := by
    unfold lossExponent
    simp only [pow_two]
    nlinarith
  omega

theorem lossExponent_le_errorExponent (n : ℕ) :
    lossExponent n ≤ errorExponent n := by
  unfold errorExponent
  omega

theorem errorBudget_nonneg {B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ errorBudget B n := by
  unfold errorBudget
  positivity

theorem errorBudget_pos {B : ℝ} (hB : 0 < B) (n : ℕ) :
    0 < errorBudget B n := by
  unfold errorBudget
  positivity

theorem errorBudget_le_one {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    errorBudget B n ≤ 1 := by
  unfold errorBudget
  have hi : B⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]
    exact hB
  exact pow_le_one₀ (inv_nonneg.mpr (by linarith)) hi

theorem loss_mul_errorBudget_le_incrementBudget {B : ℝ}
    (hB : 2 ≤ B) (n : ℕ) :
    B ^ lossExponent n * errorBudget B n ≤ incrementBudget n := by
  have hBpos : 0 < B := by linarith
  have hBne : B ≠ 0 := hBpos.ne'
  have hq0 : 0 ≤ B⁻¹ := inv_nonneg.mpr hBpos.le
  have hq : B⁻¹ ≤ (1 : ℝ) / 2 := by
    rw [inv_le_iff_one_le_mul₀' hBpos]
    nlinarith
  have hsub : n + 4 ≤ errorExponent n - lossExponent n := by
    have hn := nat_succ_le_two_pow n
    unfold errorExponent
    omega
  have heq : B ^ lossExponent n * errorBudget B n =
      B⁻¹ ^ (errorExponent n - lossExponent n) := by
    have hle := lossExponent_le_errorExponent n
    unfold errorBudget
    rw [pow_sub₀ (B⁻¹) (inv_ne_zero hBne) hle]
    simp only [inv_pow, inv_inv]
    ring
  rw [heq]
  calc
    B⁻¹ ^ (errorExponent n - lossExponent n) ≤
        ((1 : ℝ) / 2) ^ (errorExponent n - lossExponent n) :=
      pow_le_pow_left₀ hq0 hq _
    _ ≤ ((1 : ℝ) / 2) ^ (n + 4) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hsub
    _ = incrementBudget n := rfl

theorem errorBudget_contracts {B : ℝ} (hB : 2 ≤ B) (n : ℕ) :
    B ^ lossExponent n * errorBudget B n ^ 2 ≤ errorBudget B (n + 1) := by
  have hBpos : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hBne : B ≠ 0 := hBpos.ne'
  have hexp := loss_error_exponent_step n
  have hq0 : 0 ≤ B⁻¹ := inv_nonneg.mpr hBpos.le
  have hq1 : B⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hBpos]
    exact hB1
  have hloss : lossExponent n ≤ 2 * errorExponent n := by
    omega
  have hsub : errorExponent (n + 1) ≤
      2 * errorExponent n - lossExponent n := by
    omega
  calc
    B ^ lossExponent n * errorBudget B n ^ 2 =
        B ^ lossExponent n * B⁻¹ ^ (2 * errorExponent n) := by
      unfold errorBudget
      rw [← pow_mul]
      rw [Nat.mul_comm (errorExponent n) 2]
    _ = B⁻¹ ^ (2 * errorExponent n - lossExponent n) := by
      rw [pow_sub₀ (B⁻¹) (inv_ne_zero hBne) hloss]
      simp only [inv_pow, inv_inv]
      ring
    _ ≤ B⁻¹ ^ errorExponent (n + 1) :=
      pow_le_pow_of_le_one hq0 hq1 hsub
    _ = errorBudget B (n + 1) := rfl

theorem incrementBudget_nonneg (n : ℕ) : 0 ≤ incrementBudget n := by
  unfold incrementBudget
  positivity

theorem incrementBudget_partial_sum_le (n : ℕ) :
    (∑ i ∈ Finset.range n, incrementBudget i) ≤ (1 : ℝ) / 8 := by
  have hgeom := geom_sum_mul ((1 : ℝ) / 2) n
  have hsum : (∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ i) ≤ 2 := by
    have hp : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    nlinarith
  calc
    (∑ i ∈ Finset.range n, incrementBudget i) =
        ((1 : ℝ) / 2) ^ 4 *
          ∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      unfold incrementBudget
      rw [← pow_add]
      congr 1
      omega
    _ ≤ ((1 : ℝ) / 2) ^ 4 * 2 := by gcongr
    _ = (1 : ℝ) / 8 := by norm_num

theorem incrementBudget_partial_sum_le_one (n : ℕ) :
    (∑ i ∈ Finset.range n, incrementBudget i) ≤ 1 :=
  (incrementBudget_partial_sum_le n).trans (by norm_num)

end

end Submission.Majorant
