import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Submission.OddOrder.BG.Section04.OddPGroupRankOne

/-!
Odd-order Z-groups and local elementary abelian rank.

This is the mathlib-facing form of `BGsection4.v: odd_rank1_Zgroup`.  Rather
than adding MathComp's global numerical group-rank function, the rank-one
condition is stated locally on every Sylow subgroup as the absence of an
elementary abelian subgroup of rank two.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- `BGsection4.v: odd_rank1_Zgroup`, with the rank bound expanded into its
Sylow-local elementary-abelian meaning. -/
theorem odd_isZGroup_iff_sylow_no_elementaryAbelian_rank_two
    (hodd : Odd (Nat.card G)) :
    IsZGroup G ↔
      ∀ (p : ℕ) (_hp : p.Prime) (P : Sylow p G),
        ¬ ∃ E : Subgroup P, IsElementaryAbelianOfRank p 2 E := by
  constructor
  · intro hZ p hp P
    letI : Fact p.Prime := ⟨hp⟩
    letI : IsZGroup G := hZ
    have hoddP : Odd (Nat.card P) :=
      odd_natCard_subgroup (P : Subgroup G) hodd
    exact
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        P.isPGroup' hoddP).mp inferInstance
  · intro hlocal
    refine ⟨?_⟩
    intro p hp P
    letI : Fact p.Prime := ⟨hp⟩
    have hoddP : Odd (Nat.card P) :=
      odd_natCard_subgroup (P : Subgroup G) hodd
    exact
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        P.isPGroup' hoddP).mpr (hlocal p hp P)

end Submission.OddOrder.BG.Section04
