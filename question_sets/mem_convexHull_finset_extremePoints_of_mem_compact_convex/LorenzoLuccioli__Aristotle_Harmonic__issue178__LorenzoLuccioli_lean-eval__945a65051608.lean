/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: mem_convexHull_finset_extremePoints_of_mem_compact_convex
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 945a650516082dfeba205b6b4c2ffab1515b0669
issue_number: 178
-/
import Mathlib
import Submission.Helpers
import Submission.Minkowski

open Set

namespace Submission

theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  have hx_hull : x ∈ convexHull ℝ (s.extremePoints ℝ) := by
    rw [Submission.Minkowski.compact_convex_eq_convexHull_extremePoints hscomp hsconv]
    exact hx
  exact Submission.Helpers.caratheodory_finset hx_hull

end Submission
