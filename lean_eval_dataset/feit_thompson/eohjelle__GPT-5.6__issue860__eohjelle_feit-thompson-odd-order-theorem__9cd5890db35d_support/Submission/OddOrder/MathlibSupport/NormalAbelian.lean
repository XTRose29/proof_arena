import Mathlib

/-!
Normal abelian subgroups and finite maximality.

MathComp's odd-order development repeatedly selects a maximal subgroup among
the normal abelian subgroups of a finite group.  This file provides that small
order-theoretic bridge independently of the later `p`-group argument.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A subgroup that is both normal in the ambient group and abelian. -/
def IsNormalAbelian (A : Subgroup G) : Prop :=
  A.Normal ∧ IsMulCommutative A

theorem isNormalAbelian_bot : IsNormalAbelian (⊥ : Subgroup G) :=
  ⟨inferInstance, inferInstance⟩

theorem isNormalAbelian_center : IsNormalAbelian (Subgroup.center G) :=
  ⟨inferInstance, inferInstance⟩

theorem IsNormalAbelian.normal {A : Subgroup G} (hA : IsNormalAbelian A) : A.Normal :=
  hA.1

theorem IsNormalAbelian.isMulCommutative {A : Subgroup G} (hA : IsNormalAbelian A) :
    IsMulCommutative A :=
  hA.2

/-- Every finite group has an inclusion-maximal normal abelian subgroup. -/
theorem exists_maximal_isNormalAbelian [Finite G] :
    ∃ M : Subgroup G, IsNormalAbelian M ∧
      ∀ {A : Subgroup G}, IsNormalAbelian A → M ≤ A → A ≤ M := by
  classical
  let s : Set (Subgroup G) := {A | IsNormalAbelian A}
  have hs : s.Nonempty := ⟨⊥, isNormalAbelian_bot⟩
  obtain ⟨M, hM, hMmax⟩ := s.toFinite.exists_maximal hs
  exact ⟨M, hM, fun hA hMA => hMmax hA hMA⟩

/-- Equality form of maximality, convenient for replacing a larger candidate. -/
theorem eq_of_isNormalAbelian_of_maximal {M : Subgroup G}
    (hMmax : ∀ {A : Subgroup G}, IsNormalAbelian A → M ≤ A → A ≤ M)
    {A : Subgroup G} (hA : IsNormalAbelian A) (hMA : M ≤ A) : A = M :=
  le_antisymm (hMmax hA hMA) hMA

end Submission.OddOrder.MathlibSupport
