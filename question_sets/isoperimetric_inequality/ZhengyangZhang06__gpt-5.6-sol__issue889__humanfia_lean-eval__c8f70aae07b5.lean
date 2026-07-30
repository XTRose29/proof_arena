import ChallengeDeps
import Submission.Helpers
import Submission.MollifiedBoundary

open LeanEval.Geometry
open MeasureTheory ENNReal Metric

namespace Submission

theorem isoperimetric (n : ℕ) (_hn : 2 ≤ n) (B : Set (E n))
    (_hB : MeasurableSet B) (_hBdd : Bornology.IsBounded B) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  by_cases hvol : volume B = 0
  · exact Helpers.isoperimetric_of_volume_eq_zero n _hn B hvol
  by_cases hfrontier : μHE[n - 1] (frontier B) = ⊤
  · exact Helpers.isoperimetric_of_boundary_eq_top n _hn B hfrontier
  apply Helpers.isoperimetric_of_interior n _hn B hfrontier
  have hinteriorBdd : Bornology.IsBounded (interior B) := _hBdd.subset interior_subset
  have hfrontierInterior : μHE[n - 1] (frontier (interior B)) ≠ ⊤ := by
    intro htop
    apply hfrontier
    apply top_unique
    rw [← htop]
    exact measure_mono (Helpers.frontier_interior_subset B)
  apply Helpers.isoperimetric_of_surface_bound n (by omega) (interior B)
  simpa only [one_div] using
    MollifiedBoundary.surface_bound_open _hn isOpen_interior hinteriorBdd
      hfrontierInterior

end Submission
