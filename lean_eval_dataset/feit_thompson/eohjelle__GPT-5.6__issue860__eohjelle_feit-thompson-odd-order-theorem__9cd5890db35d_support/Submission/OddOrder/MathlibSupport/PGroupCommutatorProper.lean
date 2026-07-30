import Mathlib.GroupTheory.Nilpotent

/-!
The commutator of a nontrivial finite primary group is proper.
-/

namespace Submission.OddOrder.MathlibSupport

variable {H : Type*} [Group H] [Finite H]

/-- A nontrivial finite `p`-group cannot be perfect. -/
theorem commutator_ne_top_of_isPGroup
    {p : ℕ} [Fact p.Prime] [Nontrivial H] (hH : IsPGroup p H) :
    _root_.commutator H ≠ ⊤ := by
  letI : Group.IsNilpotent H := IsPGroup.isNilpotent (p := p) hH
  exact (IsSolvable.commutator_lt_top_of_nontrivial H).ne

end Submission.OddOrder.MathlibSupport
