import Submission.OddOrder.BG.Section08.FittingUniqueness
import Submission.OddOrder.BG.Section09.AnyCentralizerRankThreeUniqueness

/-!
# Bender--Glauberman Corollary 9.4

A maximal subgroup whose Fitting subgroup has elementary-abelian
`p`-rank at least three transfers uniqueness to every `p`-subgroup of
elementary-abelian rank at least three.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section08
open Submission.OddOrder.MathlibSupport

universe u

private theorem not_isCyclic_of_elementaryAbelian_rank_three
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsCyclic E := by
  intro hcyclic
  letI : IsCyclic E := hcyclic
  letI := Fintype.ofFinite E
  classical
  have hle : Nat.card E ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hE.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := E) (Fact.out : p.Prime).pos)
  have hlt : p < p ^ 3 := by
    simpa using
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
        (by omega : 1 < 3))
  exact (not_lt_of_ge (hE.card_eq ▸ hle)) hlt

/-- `BGsection9.v: any_rank3_Fitting_Uniqueness`
(Bender--Glauberman Corollary 9.4). -/
theorem any_rank3_Fitting_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hRankF : HasElementaryAbelianRankAtLeast p 3 (fittingWithin M))
    (hP : IsPGroup p P)
    (hRankP : HasElementaryAbelianRankAtLeast p 3 P) :
    P ∈ minSimple_uniq_max_groups (G := G) := by
  classical
  rcases hRankF with ⟨E, hEF, hE⟩
  rcases hRankP with ⟨B, hBP, hB⟩
  have hBp : IsPGroup p B := hB.isPGroup
  have hBnoncyc : ¬ IsCyclic B :=
    not_isCyclic_of_elementaryAbelian_rank_three hB
  have hRankCB : HasElementaryAbelianRankAtLeast p 3
      (Subgroup.centralizer (B : Set G)) :=
    ⟨B, Subgroup.le_centralizer_iff_isMulCommutative.mpr hB.commutative, hB⟩

  have hBuniq : B ∈ minSimple_uniq_max_groups (G := G) := by
    by_cases hFp : IsPGroup p (fittingWithin M)
    · have hFM : fittingWithin M ≤ M := fittingWithin_le M
      have hFsubp : IsPGroup p ((fittingWithin M).subgroupOf M) :=
        hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFM).symm
      obtain ⟨S, hFS⟩ := hFsubp.exists_le_sylow
      have hFleS :
          fittingWithin M ≤ (S : Subgroup M).map M.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hFM]
        exact Subgroup.map_mono hFS
      have hRankS : HasElementaryAbelianRankAtLeast p 3
          ((S : Subgroup M).map M.subtype) :=
        ⟨E, hEF.trans hFleS, hE⟩
      obtain ⟨A, hSCN, hRankA⟩ :=
        exists_scn_rank_three_of_hasElementaryAbelianRankAtLeast
          ((S : Subgroup M).map M.subtype)
          (S.isPGroup'.map M.subtype)
          (mFT_odd ((S : Subgroup M).map M.subtype)) hRankS
      have hAdata :=
        SCN_Fitting_Uniqueness p M S A hM hFp
          ⟨E, hEF, hE⟩ hSCN hRankA
      have hAp : IsPGroup p A :=
        IsPGroup.to_le (S.isPGroup'.map M.subtype) hSCN.le_sylow
      exact any_cent_rank3_Uniqueness hSCN.commutative hAp hRankA
        hAdata.2.2 hBp hBnoncyc hRankCB
    · obtain ⟨A₀, hA₀, hEA₀⟩ :=
        exists_isPMaxElem_ge
          (A := fittingWithin M) (E := E)
          ⟨hEF, hE.toIsElementaryAbelianGroup⟩
      let C₀ : Subgroup G := centralizerWithin (fittingWithin M) A₀
      have hC₀uniq : C₀ ∈ minSimple_uniq_max_groups (G := G) := by
        dsimp only [C₀]
        exact non_pcore_Fitting_Uniqueness p M A₀ hM hFp hA₀
          ⟨E, hEA₀, hE⟩

      have htopEnoncyc : ¬ IsCyclic (⊤ : Subgroup E) := by
        intro htopcyclic
        exact (not_isCyclic_of_elementaryAbelian_rank_three hE)
          (Subgroup.topEquiv.isCyclic.mp htopcyclic)
      obtain ⟨D₀, _hD₀top, _hD₀normal, hD₀⟩ :=
        odd_normal_p2Elem_exists hE.isPGroup (mFT_odd E)
          (⊤ : Subgroup E) htopEnoncyc
      let D : Subgroup G := D₀.map E.subtype
      have hDA₀ : D ≤ A₀ := by
        dsimp only [D]
        exact (Subgroup.map_subtype_le D₀).trans hEA₀
      have hD : IsElementaryAbelianOfRank p 2 D := by
        dsimp only [D]
        exact hD₀.map_of_injective E.subtype E.subtype_injective
      have hRankA₀two : HasElementaryAbelianRankAtLeast p 2 A₀ :=
        ⟨D, hDA₀, hD⟩
      have hA₀centralC₀ : A₀ ≤ Subgroup.centralizer (C₀ : Set G) := by
        apply Subgroup.le_centralizer_iff.mp
        dsimp only [C₀, centralizerWithin]
        exact inf_le_right
      have hA₀uniq : A₀ ∈ minSimple_uniq_max_groups (G := G) :=
        cent_uniq_Uniqueness hC₀uniq hA₀centralC₀
          ⟨p, Fact.out, hRankA₀two⟩
      exact any_cent_rank3_Uniqueness hA₀.elementary.commutative
        hA₀.elementary.isPGroup ⟨E, hEA₀, hE⟩ hA₀uniq
        hBp hBnoncyc hRankCB

  exact uniq_mmaxS hBP (mFT_pgroup_proper P hP) hBuniq

end Submission.OddOrder.BG.Section09
