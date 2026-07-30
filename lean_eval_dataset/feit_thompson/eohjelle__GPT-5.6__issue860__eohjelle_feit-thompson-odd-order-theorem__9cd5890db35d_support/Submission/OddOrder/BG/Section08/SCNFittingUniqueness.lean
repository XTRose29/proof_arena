import Submission.OddOrder.BG.Section08.SCNFittingMaximalOvergroup
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThreeConverse

/-!
# Bender--Glauberman Theorem 8.1(b): SCN--Fitting uniqueness

This file completes the SCN branch of Bender--Glauberman Theorem 8.1.  The
chosen Sylow subgroup is an ambient Sylow subgroup, the SCN subgroup lies in
the Fitting subgroup, and every maximal overgroup of the SCN subgroup is the
original maximal subgroup.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- Bender--Glauberman Theorem 8.1(b): in the `p`-Fitting branch, an SCN
subgroup of rank at least three lies in the Fitting subgroup and has a unique
maximal overgroup, while the chosen Sylow subgroup is already ambient. -/
theorem SCN_Fitting_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (_hRankF : ∃ E : Subgroup G,
      E ≤ fittingWithin M ∧ IsElementaryAbelianOfRank p 3 E)
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : ∃ E : Subgroup G,
      E ≤ A ∧ IsElementaryAbelianOfRank p 3 E) :
    (∃ Q : Sylow p G,
      (Q : Subgroup G) = (P : Subgroup M).map M.subtype) ∧
    A ≤ fittingWithin M ∧
    A ∈ minSimple_uniq_max_groups (G := G) := by
  have hAp : IsPGroup p A :=
    IsPGroup.to_le (P.isPGroup'.map M.subtype) hSCN.le_sylow
  have hRankA' : 3 ≤ Group.rank A :=
    group_rank_ge_three_of_exists_elementaryAbelian_rank_three_le
      A hAp hSCN.commutative hRankA
  have hQ :=
    scn_fitting_exists_ambient_sylow
      p M P A hM hFp hSCN hRankA'
  have hAF := scn_fitting_le p M P A hM hFp hSCN hRankA'
  refine ⟨hQ, hAF, ?_⟩
  apply (uniq_mmax_subset1 hM
    (hAF.trans (fittingWithin_le M))).mpr
  intro H hH
  exact Set.mem_singleton_iff.mpr
    (scn_fitting_maximal_overgroup
      p M P A H hM hFp hSCN hRankA' hH.1 hH.2)

end Submission.OddOrder.BG.Section08
