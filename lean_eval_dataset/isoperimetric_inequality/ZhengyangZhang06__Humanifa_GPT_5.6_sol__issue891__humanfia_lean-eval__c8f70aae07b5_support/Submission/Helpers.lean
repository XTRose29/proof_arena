import ChallengeDeps

open LeanEval.Geometry
open MeasureTheory ENNReal Metric

namespace Submission.Helpers

theorem isoperimetric_of_volume_eq_zero (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hB : volume B = 0) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  have hn1 : n - 1 ≠ 0 := by omega
  simp [hB, hn1]

theorem isoperimetric_of_boundary_eq_top (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hfrontier : μHE[n - 1] (frontier B) = ⊤) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  have hn0 : n ≠ 0 := by omega
  simp [hfrontier, hn0]

theorem volume_frontier_eq_zero_of_boundary_ne_top (n : ℕ) (hn : 2 ≤ n)
    (B : Set (E n)) (hfrontier : μHE[n - 1] (frontier B) ≠ ⊤) :
    volume (frontier B) = 0 := by
  have hdim : n - 1 < n := by omega
  rcases Measure.euclideanHausdorffMeasure_zero_or_top hdim (frontier B) with hzero | htop
  · simpa only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using hzero
  · exact (hfrontier htop).elim

theorem volume_interior_eq_of_boundary_ne_top (n : ℕ) (hn : 2 ≤ n)
    (B : Set (E n)) (hfrontier : μHE[n - 1] (frontier B) ≠ ⊤) :
    volume (interior B) = volume B := by
  have hzero := volume_frontier_eq_zero_of_boundary_ne_top n hn B hfrontier
  exact measure_interior_of_null_frontier hzero

theorem frontier_interior_subset {n : ℕ} (B : Set (E n)) :
    frontier (interior B) ⊆ frontier B := by
  intro x hx
  rw [frontier] at hx ⊢
  exact ⟨closure_mono interior_subset hx.1, by simpa using hx.2⟩

theorem isoperimetric_of_interior (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hfrontier : μHE[n - 1] (frontier B) ≠ ⊤)
    (hinterior :
      (n : ℝ≥0∞) ^ n * (volume (interior B)) ^ (n - 1) *
          volume (closedBall (0 : E n) 1)
        ≤ (μHE[n - 1] (frontier (interior B))) ^ n) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  rw [← volume_interior_eq_of_boundary_ne_top n hn B hfrontier]
  refine hinterior.trans ?_
  gcongr
  exact frontier_interior_subset B

theorem isoperimetric_of_toReal (n : ℕ) (B : Set (E n))
    (hleft :
      (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1) ≠ ⊤)
    (hright : (μHE[n - 1] (frontier B)) ^ n ≠ ⊤)
    (hreal :
      (n : ℝ) ^ n * (volume B).toReal ^ (n - 1) *
          (volume (closedBall (0 : E n) 1)).toReal
        ≤ (μHE[n - 1] (frontier B)).toReal ^ n) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  apply (ENNReal.toReal_le_toReal hleft hright).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] using hreal

/-- The conventional surface form of the inequality implies the powered form used by the
benchmark.  Keeping this algebra separate leaves the geometric core free of `ENNReal` power
bookkeeping. -/
theorem isoperimetric_of_surface_bound (n : ℕ) (hn : n ≠ 0) (B : Set (E n))
    (hsurface :
      (n : ℝ≥0∞) * (volume (closedBall (0 : E n) 1)) ^ (1 / (n : ℝ)) *
          (volume B) ^ (((n : ℝ) - 1) / (n : ℝ))
        ≤ μHE[n - 1] (frontier B)) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  have hpow := ENNReal.rpow_le_rpow hsurface (Nat.cast_nonneg n)
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [ENNReal.mul_rpow_of_nonneg _ _ hnnonneg,
    ENNReal.mul_rpow_of_nonneg _ _ hnnonneg,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hpow
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hone : 1 / (n : ℝ) * n = 1 := by field_simp
  have hsub : ((n : ℝ) - 1) / n * n = (n - 1 : ℕ) := by
    rw [div_mul_cancel₀ _ hnR, Nat.cast_sub hn1]
    norm_num
  rw [hone, hsub, ENNReal.rpow_one] at hpow
  simp only [ENNReal.rpow_natCast] at hpow
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hpow

end Submission.Helpers
