import ChallengeDeps
import Submission.ParallelVolume

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set

namespace Submission.OuterContent

/-- A one-sided upper Minkowski-content bound, stated in the epsilon form needed by the
Brunn--Minkowski argument. -/
def HasOuterContentLE {n : ℕ} (A : Set (E n)) (s : ℝ≥0∞) : Prop :=
  ∀ ε : NNReal, 0 < ε → ∃ r : ℝ, 0 < r ∧
    volume (thickening r A) ≤ volume A + ENNReal.ofReal r * (s + (ε : ℝ≥0∞))

private theorem rpow_inv_nat_pow {n : ℕ} (hn : 1 ≤ n) (a : ℝ≥0∞) :
    (a ^ (n : ℝ)⁻¹) ^ n = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [inv_mul_cancel₀ hnR, ENNReal.rpow_one]

private theorem rpow_inv_nat_pow_pred {n : ℕ} (hn : 1 ≤ n) (a : ℝ≥0∞) :
    (a ^ (n : ℝ)⁻¹) ^ (n - 1) = a ^ (((n : ℝ) - 1) / n) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  rw [Nat.cast_sub hn, Nat.cast_one, div_eq_mul_inv, mul_comm]

theorem surface_bound_of_hasOuterContentLE {n : ℕ} (hn : 1 ≤ n)
    {A : Set (E n)} (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hA_finite : volume A ≠ ⊤) {s : ℝ≥0∞} (hcontent : HasOuterContentLE A s) :
    (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume A ^ (((n : ℝ) - 1) / n) ≤ s := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _hs_finite ↦ ?_
  rcases hcontent ε hε with ⟨r, hr, hupper⟩
  have hbm := ParallelVolume.brunn_minkowski_thickening_unit_ball
    hn hA_nonempty hA_measurable hr
  have hbm_pow :
      (volume A ^ (n : ℝ)⁻¹ +
          ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹) ^ n
        ≤ volume (thickening r A) := by
    calc
      _ ≤ (volume (thickening r A) ^ (n : ℝ)⁻¹) ^ n := by gcongr
      _ = _ := rpow_inv_nat_pow hn _
  have hbernoulli :
      (volume A ^ (n : ℝ)⁻¹) ^ n +
          (n : ℝ≥0∞) * (volume A ^ (n : ℝ)⁻¹) ^ (n - 1) *
            (ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹)
        ≤ (volume A ^ (n : ℝ)⁻¹ +
          ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹) ^ n := by
    apply pow_add_mul_le_add_pow_of_sq_nonneg <;> positivity
  have hchain := hbernoulli.trans (hbm_pow.trans hupper)
  rw [rpow_inv_nat_pow hn, rpow_inv_nat_pow_pred hn] at hchain
  have hcancel :
      (n : ℝ≥0∞) * volume A ^ (((n : ℝ) - 1) / n) *
          (ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹)
        ≤ ENNReal.ofReal r * (s + ε) :=
    (ENNReal.add_le_add_iff_left hA_finite).mp hchain
  have hr0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hr0 hrtop).mp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hcancel

end Submission.OuterContent
