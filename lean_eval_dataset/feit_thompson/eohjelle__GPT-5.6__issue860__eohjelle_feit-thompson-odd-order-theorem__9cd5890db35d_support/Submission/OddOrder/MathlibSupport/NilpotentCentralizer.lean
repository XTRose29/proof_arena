import Submission.OddOrder.MathlibSupport.Centralizer
import Mathlib.GroupTheory.Nilpotent

/-!
The normalizer-condition half of the nilpotent coprime-action argument.

Inside a nilpotent group, the only self-normalizing subgroup is the whole
group.  Applied to the fixed-point subgroup `C_H(A)`, this shows that if `A`
centralizes the internal normalizer of `C_H(A)`, then it centralizes `H`.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The centralizer of `A` as a subgroup of the subtype group `H`. -/
def centralizerIn (H A : Subgroup G) : Subgroup H :=
  (Subgroup.centralizer (A : Set G)).subgroupOf H

theorem centralizerIn_map_subtype (H A : Subgroup G) :
    (centralizerIn H A).map H.subtype = centralizerWithin H A := by
  rw [centralizerIn, Subgroup.subgroupOf_map_subtype, centralizerWithin, inf_comm]

theorem centralizes_of_centralizes_normalizer_centralizer
    {H A : Subgroup G} [Group.IsNilpotent H]
    (hA : A ≤ Subgroup.centralizer
      ((Subgroup.normalizer (centralizerIn H A : Set H)).map H.subtype : Set G)) :
    A ≤ Subgroup.centralizer (H : Set G) := by
  let C : Subgroup H := centralizerIn H A
  let N : Subgroup H := Subgroup.normalizer (C : Set H)
  have hNC : N ≤ C := by
    intro n hn
    change (n : G) ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hna := Subgroup.mem_centralizer_iff.mp (hA ha) (n : G) (by
      change (n : G) ∈ N.map H.subtype
      exact ⟨n, hn, rfl⟩)
    exact hna.symm
  have hN_eq : N = C := le_antisymm hNC Subgroup.le_normalizer
  have hCtop : C = ⊤ := by
    apply normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent C
    exact hN_eq
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhC : (⟨h, hh⟩ : H) ∈ C := by
    rw [hCtop]
    exact Subgroup.mem_top _
  change h ∈ Subgroup.centralizer (A : Set G) at hhC
  exact (Subgroup.mem_centralizer_iff.mp hhC a ha).symm

end Submission.OddOrder.MathlibSupport
