import Submission.OddOrder.BG.Section04.NormalRankTwo

/-!
The rank-one consequence following Bender--Glauberman Lemma 4.5.

MathComp states this using its numerical `p`-rank.  The mathlib-facing form
below avoids introducing a second group-rank API: rank at most one is expressed
as the absence of an elementary abelian subgroup of rank two.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: odd_pgroup_rank1_cyclic`, with `p`-rank at most one
expressed by the absence of an elementary abelian rank-two subgroup. -/
theorem odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G)) :
    IsCyclic G ↔
      ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 2 E := by
  constructor
  · intro hcyclic
    rintro ⟨E, hE⟩
    have htop : IsCyclic (⊤ : Subgroup G) :=
      Subgroup.topEquiv.isCyclic.mpr hcyclic
    letI : IsCyclic (⊤ : Subgroup G) := htop
    have hEcyclic : IsCyclic E := Subgroup.isCyclic_of_le le_top
    exact hE.not_isCyclic Fact.out hEcyclic
  · intro hno
    by_contra hncyclic
    obtain ⟨E, _, hE⟩ := ex_odd_normal_p2Elem hG hodd hncyclic
    exact hno ⟨E, hE⟩

end Submission.OddOrder.BG.Section04
