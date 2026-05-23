import Mathlib

open Set Finset BigOperators

namespace Submission.Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Carathéodory extraction: from membership in convex hull, extract a finset of bounded size. -/
theorem caratheodory_finset {A : Set E} {x : E} (hx : x ∈ convexHull ℝ A) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ A ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  refine ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
    ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  set t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have h1 := (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
  rw [Fintype.card_coe] at h1
  exact h1.trans (Nat.succ_le_succ (Submodule.finrank_le _))

end Submission.Helpers
