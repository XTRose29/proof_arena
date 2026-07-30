import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

/-!
An elementary cross-prime criterion for a finite-primary group to be
commutative.
-/

namespace Submission.OddOrder.MathlibSupport

variable {H : Type*} [Group H]

/-- A `q`-group is commutative if its commutator subgroup is a `p`-group for
a distinct prime `p`. -/
theorem isMulCommutative_of_isPGroup_of_commutator_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hH : IsPGroup q H) (hcomm : IsPGroup p (_root_.commutator H))
    (hpq : p ≠ q) :
    IsMulCommutative H := by
  let D : Subgroup H := _root_.commutator H
  have hDq : IsPGroup q D := hH.to_subgroup D
  have hdis : Disjoint D D :=
    IsPGroup.disjoint_of_ne q p hpq.symm D D hDq hcomm
  exact (_root_.commutator_eq_bot_iff H).mp (disjoint_self.mp hdis)

end Submission.OddOrder.MathlibSupport
