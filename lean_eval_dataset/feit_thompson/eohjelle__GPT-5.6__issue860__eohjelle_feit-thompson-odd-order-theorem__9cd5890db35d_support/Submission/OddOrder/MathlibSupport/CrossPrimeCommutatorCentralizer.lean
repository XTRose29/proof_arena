import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

/-!
Centralization forced by disjoint prime-power commutator subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {H : Type*} [Group H]

/-- A normal `q`-subgroup is centralized by the ambient group when the
ambient commutator is a `p`-group for a different prime. -/
theorem le_centralizer_of_normal_isPGroup_of_commutator_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (P : Subgroup H) [P.Normal]
    (hP : IsPGroup q P) (hcomm : IsPGroup p (_root_.commutator H))
    (hpq : p ≠ q) :
    (⊤ : Subgroup H) ≤ Subgroup.centralizer (P : Set H) := by
  let D : Subgroup H := _root_.commutator H
  have hdis : Disjoint P D :=
    IsPGroup.disjoint_of_ne q p hpq.symm P D hP hcomm
  have hleP : ⁅(⊤ : Subgroup H), P⁆ ≤ P :=
    Subgroup.commutator_le_right ⊤ P
  have hleD : ⁅(⊤ : Subgroup H), P⁆ ≤ D := by
    dsimp only [D]
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_rfl le_top
  have hbot : ⁅(⊤ : Subgroup H), P⁆ = ⊥ := by
    apply le_antisymm
    · rw [← hdis.eq_bot]
      exact le_inf hleP hleD
    · exact bot_le
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

end Submission.OddOrder.MathlibSupport
