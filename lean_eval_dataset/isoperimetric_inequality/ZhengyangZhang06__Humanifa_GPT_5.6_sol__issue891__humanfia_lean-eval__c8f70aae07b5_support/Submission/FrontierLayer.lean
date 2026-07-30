import ChallengeDeps

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set

namespace Submission.FrontierLayer

/-- Every new point in a positive thickening can be joined to the original set through its
frontier.  The finite-dimensional hypothesis supplies a closest frontier point. -/
theorem thickening_diff_subset_thickening_frontier {n : ℕ} {A : Set (E n)} {r : ℝ}
    (_hr : 0 < r) : thickening r A \ A ⊆ thickening r (frontier A) := by
  intro x hx
  rcases (mem_thickening_iff.mp hx.1) with ⟨z, hzA, hxz⟩
  have hA : A.Nonempty := ⟨z, hzA⟩
  have hcompl : Aᶜ ≠ (univ : Set (E n)) := by
    simpa only [compl_ne_univ] using hA
  rcases exists_mem_frontier_infDist_compl_eq_dist (s := Aᶜ) hx.2 hcompl with
    ⟨y, hyfrontier, hxy⟩
  rw [frontier_compl] at hyfrontier
  apply mem_thickening_iff.mpr
  refine ⟨y, hyfrontier, ?_⟩
  rw [← hxy]
  simpa only [compl_compl] using (infDist_le_dist_of_mem hzA).trans_lt hxz

/-- A set is contained in each of its positive open thickenings. -/
theorem subset_thickening {n : ℕ} {A : Set (E n)} {r : ℝ} (hr : 0 < r) :
    A ⊆ thickening r A := by
  intro x hx
  exact mem_thickening_iff.mpr ⟨x, hx, by simpa using hr⟩

/-- Decompose the volume of a positive thickening into the old volume and its exterior layer. -/
theorem volume_thickening_eq_add_diff {n : ℕ} {A : Set (E n)}
    (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r) :
    volume (thickening r A) = volume A + volume (thickening r A \ A) := by
  rw [← measure_union disjoint_sdiff_self_right
    (Metric.isOpen_thickening.measurableSet.diff hA)]
  congr 1
  rw [union_sdiff_self, union_eq_right.mpr (subset_thickening hr)]

end Submission.FrontierLayer
