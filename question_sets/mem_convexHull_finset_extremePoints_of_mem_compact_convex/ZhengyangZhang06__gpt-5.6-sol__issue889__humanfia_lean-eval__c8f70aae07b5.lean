import Mathlib
import Submission.Helpers

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
  have hx' :=
    Helpers.mem_convexHull_extremePoints_of_compact_convex hscomp hsconv hx
  rw [convexHull_eq_union] at hx'
  simp only [Set.mem_iUnion, exists_prop] at hx'
  obtain ⟨t, ht, hind, hxt⟩ := hx'
  refine ⟨t, ht, ?_, hxt⟩
  calc
    t.card = Fintype.card t := by simp
    _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 :=
      hind.card_le_finrank_succ
    _ ≤ Module.finrank ℝ E + 1 :=
      Nat.add_le_add_right (Submodule.finrank_le _) 1

end Submission
