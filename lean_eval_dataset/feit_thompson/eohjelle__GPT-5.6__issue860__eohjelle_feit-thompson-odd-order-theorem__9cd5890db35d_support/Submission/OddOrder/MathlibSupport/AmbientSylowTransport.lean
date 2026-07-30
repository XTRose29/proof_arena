import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow

/-!
# Transporting ambiently represented Sylow subgroups

The predicate `IsSylowSubgroupOf p S H` represents a Sylow subgroup of an
ambient subgroup `H` by its image `S` in the ambient group.  This file provides
the two elementary transports across an intermediate subgroup: extension when
the intervening index is prime to `p`, and restriction when the intermediate
subgroup already contains `S`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Extend an ambiently represented Sylow subgroup across an intermediate
subgroup whose index is prime to the Sylow prime. -/
theorem IsSylowSubgroupOf.extend_of_not_dvd_index
    {p : ℕ} [Fact p.Prime] {S H K : Subgroup G}
    (hS : IsSylowSubgroupOf p S H) (hHK : H ≤ K)
    (hpIndex : ¬ p ∣ (H.subgroupOf K).index) :
    IsSylowSubgroupOf p S K := by
  have hSH : S ≤ H := by
    rcases hS with ⟨P, rfl⟩
    exact Subgroup.map_subtype_le _
  have hSK : S ≤ K := hSH.trans hHK
  let SK : Subgroup K := S.subgroupOf K
  have hSKp : IsPGroup p SK :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hpSIndexH : ¬ p ∣ (S.subgroupOf H).index := by
    obtain ⟨P, hP⟩ := hS
    have hindex : (S.subgroupOf H).index = P.index := by
      calc
        (S.subgroupOf H).index = S.relIndex H := rfl
        _ = ((P : Subgroup H).map H.subtype).relIndex H := by rw [hP]
        _ = (P : Subgroup H).relIndex ⊤ := by
          simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using
            Subgroup.relIndex_map_map_of_injective
              (P : Subgroup H) ⊤ H.subtype_injective
        _ = P.index := (P : Subgroup H).relIndex_top_right
    rw [hindex]
    exact P.not_dvd_index
  have hpSKindex : ¬ p ∣ SK.index := by
    have hfactor : SK.index =
        (S.subgroupOf H).index * (H.subgroupOf K).index := by
      change S.relIndex K = S.relIndex H * H.relIndex K
      exact (S.relIndex_mul_relIndex H K hSH hHK).symm
    rw [hfactor]
    exact Nat.Prime.not_dvd_mul (Fact.out : p.Prime) hpSIndexH hpIndex
  let P : Sylow p K := hSKp.toSylow hpSKindex
  refine ⟨P, ?_⟩
  change S = SK.map K.subtype
  exact (Subgroup.map_subgroupOf_eq_of_le hSK).symm

/-- Restrict an ambiently represented Sylow subgroup to an intermediate
subgroup which already contains it. -/
theorem IsSylowSubgroupOf.restrict_of_le
    {p : ℕ} [Fact p.Prime] {S H K : Subgroup G}
    (hS : IsSylowSubgroupOf p S K) (hSH : S ≤ H) (hHK : H ≤ K) :
    IsSylowSubgroupOf p S H := by
  let SH : Subgroup H := S.subgroupOf H
  have hSHp : IsPGroup p SH :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hpSIndexK : ¬ p ∣ (S.subgroupOf K).index := by
    obtain ⟨P, hP⟩ := hS
    have hindex : (S.subgroupOf K).index = P.index := by
      calc
        (S.subgroupOf K).index = S.relIndex K := rfl
        _ = ((P : Subgroup K).map K.subtype).relIndex K := by rw [hP]
        _ = (P : Subgroup K).relIndex ⊤ := by
          simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using
            Subgroup.relIndex_map_map_of_injective
              (P : Subgroup K) ⊤ K.subtype_injective
        _ = P.index := (P : Subgroup K).relIndex_top_right
    rw [hindex]
    exact P.not_dvd_index
  have hpSHindex : ¬ p ∣ SH.index := by
    intro hp
    apply hpSIndexK
    change p ∣ S.relIndex H at hp
    rw [← Subgroup.relIndex_subgroupOf (H := S) hHK] at hp
    have hSKHK : S.subgroupOf K ≤ H.subgroupOf K := by
      intro x hx
      exact hSH hx
    exact hp.trans (Subgroup.relIndex_dvd_index_of_le
      hSKHK)
  let P : Sylow p H := hSHp.toSylow hpSHindex
  refine ⟨P, ?_⟩
  change S = SH.map H.subtype
  exact (Subgroup.map_subgroupOf_eq_of_le hSH).symm

end Submission.OddOrder.MathlibSupport
