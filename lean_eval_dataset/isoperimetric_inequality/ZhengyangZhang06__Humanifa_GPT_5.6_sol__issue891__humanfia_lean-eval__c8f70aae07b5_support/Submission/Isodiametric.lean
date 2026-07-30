import ChallengeDeps
import Submission.ParallelVolume

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set
open scoped Pointwise

namespace Submission.Isodiametric

/-- The sharp Euclidean isodiametric inequality.  The proof is the standard one-line
consequence of Brunn--Minkowski: the half difference set has at least the volume of the
original set and is contained in the ball whose radius is half the diameter. -/
theorem volume_le_closedBall_half_diam {n : ℕ} (hn : 1 ≤ n) {A : Set (E n)}
    (hA : A.Nonempty) (hAbdd : Bornology.IsBounded A) :
    volume A ≤ volume (closedBall (0 : E n) (Metric.diam A / 2)) := by
  let K : Set (E n) := closure A
  let D : Set (E n) := K + -K
  let c : NNReal := (2 : NNReal)⁻¹
  have hKcpt : IsCompact K := hAbdd.isCompact_closure
  have hKne : K.Nonempty := hA.closure
  have hnegKcpt : IsCompact (-K) := hKcpt.neg
  have hnegKne : (-K).Nonempty := hKne.neg
  have hDcpt : IsCompact D := hKcpt.add hnegKcpt
  have hbm :
      volume K ^ (n : ℝ)⁻¹ + volume (-K) ^ (n : ℝ)⁻¹
        ≤ volume D ^ (n : ℝ)⁻¹ := by
    exact ParallelVolume.brunn_minkowski_E hn hKne hKcpt.measurableSet hnegKne
      hnegKcpt.measurableSet hDcpt.measurableSet
  have hvolneg : volume (-K) = volume K := by
    simp only [Measure.measure_neg]
  rw [hvolneg] at hbm
  have hc : (c : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by simp [c]
  have hroot : volume K ^ (n : ℝ)⁻¹ ≤ volume (c • D) ^ (n : ℝ)⁻¹ := by
    rw [Measure.addHaar_nnreal_smul]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (n : ℝ)⁻¹),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    rw [mul_inv_cancel₀ hnR, ENNReal.rpow_one, hc]
    calc
      volume K ^ (n : ℝ)⁻¹ = 2⁻¹ *
          (volume K ^ (n : ℝ)⁻¹ + volume K ^ (n : ℝ)⁻¹) := by
        rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top, one_mul]
      _ ≤ 2⁻¹ * volume D ^ (n : ℝ)⁻¹ := by gcongr
  have hvolK : volume K ≤ volume (c • D) := by
    rwa [ENNReal.rpow_le_rpow_iff (by positivity : 0 < (n : ℝ)⁻¹)] at hroot
  have hsubset : c • D ⊆ closedBall (0 : E n) (Metric.diam A / 2) := by
    rintro x ⟨z, hzD, rfl⟩
    rcases hzD with ⟨a, haK, nb, hnb, rfl⟩
    let b : E n := -nb
    have hbK : b ∈ K := by simpa [b] using hnb
    have hab : a + nb = a - b := by simp [b]
    change (c : ℝ) • (a + nb) ∈ closedBall (0 : E n) (Metric.diam A / 2)
    rw [hab]
    have hdist : dist a b ≤ Metric.diam A := by
      rw [← Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem hKcpt.isBounded haK hbK
    have hcR : (c : ℝ) = 2⁻¹ := by norm_num [c]
    rw [mem_closedBall_zero_iff, norm_smul, hcR, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
    calc
      2⁻¹ * ‖a - b‖ ≤ 2⁻¹ * Metric.diam A :=
        mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hdist)
          (by positivity)
      _ = Metric.diam A / 2 := by ring
  exact (measure_mono subset_closure).trans (hvolK.trans (measure_mono hsubset))

end Submission.Isodiametric
