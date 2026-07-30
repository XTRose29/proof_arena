import Mathlib.GroupTheory.Nilpotent

/-!
Normalizer growth inside finite p-groups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem subgroup_lt_normalizer_of_isPGroup {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (D : Subgroup G) (hD : D < ⊤) :
    D < Subgroup.normalizer (D : Set G) := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  exact Group.normalizerCondition_of_isNilpotent D hD

/-- Ambient form of the p-group normalizer condition: a proper subgroup `D`
of a p-subgroup `P` is properly contained in `P ∩ N_G(D)`. -/
theorem lt_inf_normalizer_of_isPGroup {p : ℕ} [Fact p.Prime]
    {P D : Subgroup G} (hP : IsPGroup p P) (hDP : D < P) :
    D < P ⊓ Subgroup.normalizer (D : Set G) := by
  let DP : Subgroup P := D.subgroupOf P
  have hDPtop : DP < ⊤ := by
    rw [← Subgroup.map_subtype_lt_map_subtype]
    rw [show DP.map P.subtype = D by
      exact Subgroup.map_subgroupOf_eq_of_le hDP.le]
    rw [← MonoidHom.range_eq_map, P.range_subtype]
    exact hDP
  have hnormalizer : DP < Subgroup.normalizer (DP : Set P) :=
    subgroup_lt_normalizer_of_isPGroup hP DP hDPtop
  have hmapped : DP.map P.subtype <
      (Subgroup.normalizer (DP : Set P)).map P.subtype :=
    Subgroup.map_subtype_lt_map_subtype.mpr hnormalizer
  rw [show DP.map P.subtype = D by
      exact Subgroup.map_subgroupOf_eq_of_le hDP.le] at hmapped
  have hnormalizerMap :
      (Subgroup.normalizer (DP : Set P)).map P.subtype =
        P ⊓ Subgroup.normalizer (D : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hDP.le]
    simp [inf_comm]
  rwa [hnormalizerMap] at hmapped

end Submission.OddOrder.MathlibSupport
