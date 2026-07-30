import ChallengeDeps
import Submission.BrunnMinkowski

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set
open scoped Pointwise

namespace Submission.ParallelVolume

theorem brunn_minkowski_E {n : ℕ} (hn : 1 ≤ n) {A B : Set (E n)}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B)) :
    volume A ^ (n : ℝ)⁻¹ + volume B ^ (n : ℝ)⁻¹
      ≤ volume (A + B) ^ (n : ℝ)⁻¹ := by
  cases n with
  | zero => simp at hn
  | succ d =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        BrunnMinkowski.brunn_minkowski_euclideanSpace (d := d)
          hA_nonempty hA_measurable hB_nonempty hB_measurable hAB_measurable

theorem add_ball_zero_eq_thickening {n : ℕ} (A : Set (E n)) (r : ℝ) :
    A + ball (0 : E n) r = thickening r A := by
  exact add_ball_zero (s := A) (δ := r)

theorem brunn_minkowski_thickening {n : ℕ} (hn : 1 ≤ n) {A : Set (E n)}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    {r : ℝ} (hr : 0 < r) :
    volume A ^ (n : ℝ)⁻¹ + volume (ball (0 : E n) r) ^ (n : ℝ)⁻¹
      ≤ volume (thickening r A) ^ (n : ℝ)⁻¹ := by
  rw [← add_ball_zero_eq_thickening]
  apply brunn_minkowski_E hn hA_nonempty hA_measurable
  · exact ⟨0, by simpa using hr⟩
  · exact measurableSet_ball
  · rw [add_ball_zero_eq_thickening]
    exact isOpen_thickening.measurableSet

theorem volume_ball_rpow_inv_nat {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    volume (ball (0 : E n) r) ^ (n : ℝ)⁻¹ =
      ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr (Nat.cast_nonneg n)),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [mul_inv_cancel₀ hnR, ENNReal.rpow_one]

theorem brunn_minkowski_thickening_unit_ball {n : ℕ} (hn : 1 ≤ n)
    {A : Set (E n)} (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    {r : ℝ} (hr : 0 < r) :
    volume A ^ (n : ℝ)⁻¹ +
        ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹
      ≤ volume (thickening r A) ^ (n : ℝ)⁻¹ := by
  simpa only [volume_ball_rpow_inv_nat hn r] using
    brunn_minkowski_thickening hn hA_nonempty hA_measurable hr

end Submission.ParallelVolume
