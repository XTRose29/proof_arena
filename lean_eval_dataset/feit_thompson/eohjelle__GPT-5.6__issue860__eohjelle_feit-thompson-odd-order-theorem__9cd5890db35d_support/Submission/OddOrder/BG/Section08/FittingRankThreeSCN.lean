import Submission.OddOrder.BG.Section05.SCNRankThree
import Submission.OddOrder.MathlibSupport.SCNFunctorial

/-!
A rank-three SCN subgroup inside a finite odd `p`-group.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.MathlibSupport

universe u

/-- A finite odd `p`-group containing an elementary-abelian subgroup of
rank three contains an SCN subgroup with the same rank bound. -/
theorem exists_scn_rank_three_of_hasElementaryAbelianRankAtLeast
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup G)
    (hP : IsPGroup p P)
    (hodd : Odd (Nat.card P))
    (hRank3 : HasElementaryAbelianRankAtLeast p 3 P) :
    ∃ A : Subgroup G,
      IsSCN P A ∧ HasElementaryAbelianRankAtLeast p 3 A := by
  obtain ⟨E, hEP, hE⟩ := hRank3
  let e : E.subgroupOf P ≃* E := Subgroup.subgroupOfEquivOfLe hEP
  have hEinP : IsElementaryAbelianOfRank p 3 (E.subgroupOf P) := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.of_equiv e.symm
        commutative := isMulCommutative_iff.mpr ?_
        pow_eq_one := ?_
        card_eq := ?_ }
    · intro x y
      apply e.injective
      exact mul_comm' (e x) (e y)
    · intro x
      apply e.injective
      simpa using hE.pow_eq_one (e x)
    · exact (Nat.card_congr e.toEquiv).trans hE.card_eq
  obtain ⟨B, hBSCN, hBRank3⟩ :=
    rank3_SCN3 hP hodd ⟨E.subgroupOf P, hEinP⟩
  refine ⟨B.map P.subtype, ?_, ?_⟩
  · have hSCN :=
      hBSCN.map_of_injective P.subtype P.subtype_injective
    rw [← MonoidHom.range_eq_map, P.range_subtype] at hSCN
    exact hSCN
  · obtain ⟨F, hFB, hF⟩ := hBRank3
    exact ⟨F.map P.subtype, Subgroup.map_mono hFB,
      isElementaryAbelianOfRank_map_of_injective
        hF P.subtype P.subtype_injective⟩

end Submission.OddOrder.BG.Section08
