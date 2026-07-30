import Submission.OddOrder.BG.Section09.SCNFittingPrimeComplementCentralizer
import Submission.OddOrder.BG.Section09.SylowNormalizerCommutator

/-!
# Bender--Glauberman Lemma 9.5: uniqueness for the Sylow commutator

This file ports the block immediately following `cDP0` in `BGsection9.v`.
For each maximal subgroup selected by the SCN centralizer, the normalizer of
the Sylow--normalizer commutator has that maximal subgroup as its unique
maximal overgroup.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection9.v`, lines 377--402: uniqueness of the maximal overgroup of
the normalizer of `[P, N(P)]`. -/
theorem normalizer_sylow_commutator_unique_maximal_of_scn_not_unique
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hSCN : IsSCN (P : Subgroup G) A)
    (hRankA : 3 ≤ Group.rank A)
    (hnotuniq : A ∉ minSimple_uniq_max_groups (G := G)) :
    ∀ {M : Subgroup G}, M ∈ minSimple_max_groups (G := G) →
      Subgroup.centralizer (A : Set G) ≤ M →
      let P0 := ⁅(P : Subgroup G),
        Subgroup.normalizer ((P : Subgroup G) : Set G)⁆
      minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (P0 : Set G) : Set G) = {M} := by
  classical
  intro M hM hCAM
  dsimp only
  let P0 : Subgroup G :=
    ⁅(P : Subgroup G),
      Subgroup.normalizer ((P : Subgroup G) : Set G)⁆
  let F : Subgroup G := fittingWithin M
  let D : Subgroup G := (pPrimeCore p F).map F.subtype

  have hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M :=
    normalizer_sylow_le_maximal_of_scn_not_unique
      P hSCN hRankA hnotuniq hM hCAM
  have hPM : (P : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans hNPM
  have hFM : F ≤ M := by
    simpa only [F] using fittingWithin_le M

  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  obtain ⟨EA, hEAA, hEA⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      A hAp hSCN.commutative hRankA
  have hEAne : EA ≠ ⊥ := by
    apply EA.one_lt_card_iff_ne_bot.mp
    rw [hEA.card_eq]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hPbot
    exact hEAne
      (eq_bot_iff.mpr (hEAA.trans (hSCN.le_sylow.trans hPbot.le)))
  have hP0ne : P0 ≠ ⊥ := by
    simpa only [P0] using sylow_commutator_normalizer_ne_bot P hPne
  have hP0P : P0 ≤ (P : Subgroup G) := by
    dsimp only [P0]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp le_rfl
  have hP0p : IsPGroup p P0 :=
    IsPGroup.to_le P.isPGroup' hP0P
  have hP0M : P0 ≤ M := hP0P.trans hPM
  have hNP0proper : Subgroup.normalizer (P0 : Set G) < ⊤ :=
    mFT_norm_proper P0 hP0ne (mFT_pgroup_proper P0 hP0p)

  have hP0centD : P0 ≤ Subgroup.centralizer (D : Set G) := by
    simpa only [P0, D, F] using
      (sylow_commutator_le_centralizer_fitting_pPrimeCore_of_scn_not_unique
        P hSCN hRankA hnotuniq hM hCAM)

  by_cases hRankHigh : ∃ q : ℕ, q.Prime ∧
      HasElementaryAbelianRankAtLeast q 3 F
  · obtain ⟨q, hq, E, hEF, hE⟩ := hRankHigh
    have hNoP :
        ¬ HasElementaryAbelianRankAtLeast p 3 F := by
      simpa only [F] using
        (no_fitting_rank_three_of_scn_not_unique
          P hSCN hRankA hnotuniq hM)
    have hqp : q ≠ p := by
      intro hEq
      subst q
      exact hNoP ⟨E, hEF, hE⟩
    letI : Fact q.Prime := ⟨hq⟩
    let Oq : Subgroup G := (pCore q F).map F.subtype
    have hEOq : E ≤ Oq := by
      have hEsub : IsElementaryAbelianOfRank q 3 (E.subgroupOf F) :=
        hE.subgroupOf hEF
      have hEcore : E.subgroupOf F ≤ pCore q F :=
        hEsub.isPGroup.le_pCore_of_isNilpotent
      dsimp only [Oq]
      rw [← Subgroup.map_subgroupOf_eq_of_le hEF]
      exact Subgroup.map_mono hEcore
    have hOqF : Oq ≤ F := by
      dsimp only [Oq]
      exact Subgroup.map_subtype_le _
    have hOqM : Oq ≤ M := hOqF.trans hFM
    have hOqD : Oq ≤ D := by
      dsimp only [Oq, D]
      exact Subgroup.map_mono
        (pCore_le_pPrimeCore_of_ne
          (G := F) (p := p) (q := q) hqp.symm)
    have hOqp : IsPGroup q Oq := by
      dsimp only [Oq]
      exact pCore_isPGroup.map F.subtype
    have hOqRank : HasElementaryAbelianRankAtLeast q 3 Oq :=
      ⟨E, hEOq, hE⟩
    have hOquniq : Oq ∈ minSimple_uniq_max_groups (G := G) :=
      any_rank3_Fitting_Uniqueness hM
        (by simpa only [F] using
          (show HasElementaryAbelianRankAtLeast q 3 F from
            ⟨E, hEF, hE⟩))
        hOqp hOqRank
    have hOqdef :
        minSimple_max_groups_of (G := G) (Oq : Set G) = {M} :=
      def_uniq_mmax hOquniq hM hOqM
    have hOqNP0 : Oq ≤ Subgroup.normalizer (P0 : Set G) := by
      have hP0centOq : P0 ≤ Subgroup.centralizer (Oq : Set G) :=
        hP0centD.trans (Subgroup.centralizer_le hOqD)
      exact (Subgroup.le_centralizer_iff.mp hP0centOq).trans
        (Subgroup.centralizer_le_normalizer (P0 : Set G))
    exact def_uniq_mmaxS hOqNP0 hNP0proper hOqdef

  · have hRankCore : ∀ q : ℕ, q.Prime →
        ¬ ∃ E : Subgroup (fittingCore M),
          IsElementaryAbelianOfRank q 3 E := by
      intro q hq
      rintro ⟨E, hE⟩
      let EM : Subgroup M := E.map (fittingCore M).subtype
      let EG : Subgroup G := EM.map M.subtype
      have hEM : IsElementaryAbelianOfRank q 3 EM := by
        dsimp only [EM]
        exact hE.map_of_injective (fittingCore M).subtype
          (fittingCore M).subtype_injective
      have hEG : IsElementaryAbelianOfRank q 3 EG := by
        dsimp only [EG]
        exact hEM.map_of_injective M.subtype M.subtype_injective
      have hEGF : EG ≤ F := by
        dsimp only [EG, EM, F, fittingWithin]
        exact Subgroup.map_mono (Subgroup.map_subtype_le E)
      exact hRankHigh ⟨q, hq, EG, hEGF, hEG⟩

    have hderM : _root_.commutator M ≤ fittingCore M :=
      rank2_der1_sub_Fitting (mFT_odd M) (mmax_sol hM) hRankCore
    let PM : Sylow p M := P.subtype hPM
    have hPMmap : (PM : Subgroup M).map M.subtype =
        (P : Subgroup G) := by
      dsimp only [PM]
      rw [Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hPM]

    let Fp : Subgroup G := (pCore p F).map F.subtype
    letI : Group.IsNilpotent F := by
      dsimp only [F]
      infer_instance
    have hFpP : Fp ≤ (P : Subgroup G) := by
      have hFpEq : Fp = (pCore p M).map M.subtype := by
        simpa only [Fp, F] using map_pCore_fittingWithin_eq_map_pCore M p
      calc
        Fp = (pCore p M).map M.subtype := hFpEq
        _ ≤ (PM : Subgroup M).map M.subtype :=
          Subgroup.map_mono (pCore_le_sylow PM)
        _ = (P : Subgroup G) := hPMmap
    have hFpNormP0 : Fp ≤ Subgroup.normalizer (P0 : Set G) :=
      hFpP.trans (by
        simpa only [P0] using
          (Subgroup.normalizer_commutator_ge_left
            (P : Subgroup G)
            (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    have hDNormP0 : D ≤ Subgroup.normalizer (P0 : Set G) :=
      (Subgroup.le_centralizer_iff.mp hP0centD).trans
        (Subgroup.centralizer_le_normalizer (P0 : Set G))
    have hdecomp : Fp ⊔ D = F := by
      calc
        Fp ⊔ D =
            ((pCore p F) ⊔ pPrimeCore p F).map F.subtype := by
          simp only [Fp, D, Subgroup.map_sup]
        _ = (⊤ : Subgroup F).map F.subtype := by
          rw [sup_pCore_pPrimeCore_eq_top_of_isNilpotent]
        _ = F := by
          rw [← MonoidHom.range_eq_map, F.range_subtype]
    have hFNormP0 : F ≤ Subgroup.normalizer (P0 : Set G) := by
      rw [← hdecomp]
      exact sup_le hFpNormP0 hDNormP0

    have hNPMmap :
        (Subgroup.normalizer ((PM : Subgroup M) : Set M)).map M.subtype ≤
          Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      calc
        (Subgroup.normalizer ((PM : Subgroup M) : Set M)).map M.subtype ≤
            Subgroup.normalizer
              ((PM : Subgroup M).map M.subtype : Set G) :=
          (PM : Subgroup M).le_normalizer_map M.subtype
        _ = Subgroup.normalizer ((P : Subgroup G) : Set G) := by
          rw [hPMmap]
    have hNPMNormP0 :
        (Subgroup.normalizer ((PM : Subgroup M) : Set M)).map M.subtype ≤
          Subgroup.normalizer (P0 : Set G) :=
      hNPMmap.trans (by
        simpa only [P0] using
          (Subgroup.normalizer_commutator_ge_right
            (P : Subgroup G)
            (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    have hgenM :
        fittingCore M ⊔
          Subgroup.normalizer ((PM : Subgroup M) : Set M) = ⊤ :=
      fittingCore_sup_normalizer_sylow_eq_top PM hderM
    have hFitMapNormP0 :
        (fittingCore M).map M.subtype ≤
          Subgroup.normalizer (P0 : Set G) := by
      change fittingWithin M ≤ Subgroup.normalizer (P0 : Set G)
      simpa only [F] using hFNormP0
    have htopMapNormP0 :
        (⊤ : Subgroup M).map M.subtype ≤
          Subgroup.normalizer (P0 : Set G) := by
      rw [← hgenM, Subgroup.map_sup]
      exact sup_le hFitMapNormP0 hNPMNormP0
    have hMNormP0 : M ≤ Subgroup.normalizer (P0 : Set G) := by
      calc
        M = (⊤ : Subgroup M).map M.subtype := by
          rw [← MonoidHom.range_eq_map, M.range_subtype]
        _ ≤ Subgroup.normalizer (P0 : Set G) := htopMapNormP0
    have hP0normalM : (P0.subgroupOf M).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hMNormP0
    have hNormEq : Subgroup.normalizer (P0 : Set G) = M :=
      mmax_normal hM hP0M hP0normalM hP0ne
    rw [hNormEq]
    exact mmax_sup_id hM

end Submission.OddOrder.BG.Section09
