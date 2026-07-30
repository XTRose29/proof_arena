import Submission.OddOrder.BG.Section08.SCNFittingUniqueness
import Submission.OddOrder.BG.Section08.NonPCoreFittingUniqueness
import Submission.OddOrder.BG.Section08.FittingRankThreeSCN
import Submission.OddOrder.MathlibSupport.PMaxElemExistence

/-!
# Bender--Glauberman Section 8: Fitting uniqueness

This file combines the two branches of Bender--Glauberman Theorem 8.1 to
show that a Fitting subgroup of elementary-abelian rank at least three has a
unique maximal overgroup.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- A Fitting subgroup containing an elementary-abelian subgroup of rank
three has a unique maximal overgroup. -/
theorem Fitting_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hRank3 : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 3 (fittingWithin M)) :
    fittingWithin M ∈ minSimple_uniq_max_groups (G := G) := by
  obtain ⟨p, hp, E, hEF, hE⟩ := hRank3
  letI : Fact p.Prime := ⟨hp⟩
  have hFM : fittingWithin M ≤ M := fittingWithin_le M
  have hFproper : fittingWithin M < ⊤ := sub_mmax_proper hM hFM
  by_cases hFp : IsPGroup p (fittingWithin M)
  · have hFsubp : IsPGroup p ((fittingWithin M).subgroupOf M) :=
      hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFM).symm
    obtain ⟨P, hFP⟩ := hFsubp.exists_le_sylow
    have hFleP :
        fittingWithin M ≤ (P : Subgroup M).map M.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hFM]
      exact Subgroup.map_mono hFP
    have hRankP : HasElementaryAbelianRankAtLeast p 3
        ((P : Subgroup M).map M.subtype) :=
      ⟨E, hEF.trans hFleP, hE⟩
    obtain ⟨A, hSCN, hRankA⟩ :=
      exists_scn_rank_three_of_hasElementaryAbelianRankAtLeast
        ((P : Subgroup M).map M.subtype)
        (P.isPGroup'.map M.subtype)
        (mFT_odd ((P : Subgroup M).map M.subtype)) hRankP
    have hA :=
      SCN_Fitting_Uniqueness p M P A hM hFp
        ⟨E, hEF, hE⟩ hSCN hRankA
    exact uniq_mmaxS hA.2.1 hFproper hA.2.2
  · obtain ⟨A₀, hA₀, hEA₀⟩ :=
      exists_isPMaxElem_ge
        (A := fittingWithin M) (E := E)
        ⟨hEF, hE.toIsElementaryAbelianGroup⟩
    have hC :=
      non_pcore_Fitting_Uniqueness p M A₀ hM hFp hA₀
        ⟨E, hEA₀, hE⟩
    exact uniq_mmaxS
      (centralizerWithin_le_left (fittingWithin M) A₀) hFproper hC

end Submission.OddOrder.BG.Section08
