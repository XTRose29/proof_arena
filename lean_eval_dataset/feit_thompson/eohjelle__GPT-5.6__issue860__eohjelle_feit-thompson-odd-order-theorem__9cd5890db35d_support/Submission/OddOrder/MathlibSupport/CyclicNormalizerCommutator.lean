import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Commutators inside the normalizer of a cyclic subgroup centralize it.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- If two subgroups normalize a cyclic subgroup, their mutual commutator
centralizes that cyclic subgroup. -/
theorem commutator_le_centralizer_of_normalizes_isCyclic
    (S H K : Subgroup G) (hS : IsCyclic S)
    (hH : H ≤ Subgroup.normalizer (S : Set G))
    (hK : K ≤ Subgroup.normalizer (S : Set G)) :
    ⁅H, K⁆ ≤ Subgroup.centralizer (S : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (S : Set G)
  let HN : Subgroup N := H.subgroupOf N
  let KN : Subgroup N := K.subgroupOf N
  letI : IsCyclic S := hS
  let _ := (hS.mulAutMulEquiv S).toMonoidHom.commGroupOfInjective
    (hS.mulAutMulEquiv S).injective
  have hderivedKer : _root_.commutator N ≤ S.normalizerMonoidHom.ker :=
    Abelianization.commutator_subset_ker S.normalizerMonoidHom
  have hsmallKer : ⁅HN, KN⁆ ≤ S.normalizerMonoidHom.ker :=
    (Subgroup.commutator_mono le_top le_top).trans hderivedKer
  have hmap : ⁅HN, KN⁆.map N.subtype = ⁅H, K⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hH,
      Subgroup.map_subgroupOf_eq_of_le hK]
  intro x hx
  rw [← hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyker := hsmallKer hy
  rw [Subgroup.normalizerMonoidHom_ker] at hyker
  exact hyker

end Submission.OddOrder.MathlibSupport
