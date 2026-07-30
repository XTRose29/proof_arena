import Submission.OddOrder.BG.Section08.SCNFittingSetup
import Submission.OddOrder.BG.Section08.SCNFittingPuigCenter

/-!
# Bender--Glauberman Theorem 8.1(b): maximal overgroups

This file ports the extremal maximal-overgroup argument in the SCN branch of
Theorem 8.1.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- Every maximal overgroup of the SCN subgroup in the `p`-Fitting branch is
the original maximal subgroup. -/
theorem scn_fitting_maximal_overgroup
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A H : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A)
    (hH : H ∈ minSimple_max_groups (G := G))
    (hAH : A ≤ H) :
    H = M := by
  classical
  by_contra hHM
  let Alt : Set (Subgroup G) :=
    {D | D ∈ minSimple_max_groups (G := G) ∧ A ≤ D ∧ D ≠ M}
  let score : Subgroup G → ℕ := fun D =>
    Nat.card (default : Sylow p ↑(D ⊓ M))
  have hHAlt : H ∈ Alt := ⟨hH, hAH, hHM⟩
  obtain ⟨D, hDAlt, hDmax⟩ :=
    Set.exists_max_image Alt score Alt.toFinite ⟨H, hHAlt⟩
  have hD : D ∈ minSimple_max_groups (G := G) := hDAlt.1
  have hAD : A ≤ D := hDAlt.2.1
  have hDM : D ≠ M := hDAlt.2.2
  let I : Subgroup G := D ⊓ M
  have hAM : A ≤ M :=
    (scn_fitting_le p M P A hM hFp hSCN hRankA).trans
      (fittingWithin_le M)
  have hAI : A ≤ I := le_inf hAD hAM
  have hAp : IsPGroup p A :=
    IsPGroup.to_le (P.isPGroup'.map M.subtype) hSCN.le_sylow
  let AI : Subgroup I := A.subgroupOf I
  have hAIp : IsPGroup p AI :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAI).symm
  obtain ⟨R, hAIR⟩ := hAIp.exists_le_sylow
  let RG : Subgroup G := (R : Subgroup I).map I.subtype
  have hARG : A ≤ RG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAI]
    exact Subgroup.map_mono hAIR
  have hRGI : RG ≤ I := Subgroup.map_subtype_le _
  have hRGD : RG ≤ D := hRGI.trans inf_le_left
  have hRGM : RG ≤ M := hRGI.trans inf_le_right
  have hRGp : IsPGroup p RG := R.isPGroup'.map I.subtype
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hzero : Group.rank A = 0 := by
      rw [hAbot]
      exact Group.rank_eq_zero _
    omega
  have hRGne : RG ≠ ⊥ := fun hRGbot =>
    hAne (le_bot_iff.mp (hARG.trans_eq hRGbot))

  have hscoreD : score D = Nat.card RG := by
    dsimp only [score, RG, I]
    rw [Subgroup.card_map_of_injective I.subtype_injective]
    exact (default : Sylow p ↑(D ⊓ M)).card_eq_multiplicity.trans
      R.card_eq_multiplicity.symm

  have sylowD_of_normalizer_le
      (hNRM : Subgroup.normalizer (RG : Set G) ≤ M) :
      ∃ RD : Sylow p D,
        (RD : Subgroup D).map D.subtype = RG := by
    let RDsub : Subgroup D := RG.subgroupOf D
    have hRDp : IsPGroup p RDsub :=
      hRGp.of_equiv (Subgroup.subgroupOfEquivOfLe hRGD).symm
    let RD : Sylow p D :=
      { toSubgroup := RDsub
        isPGroup' := hRDp
        is_maximal' := by
          intro X hXp hRDX
          by_contra hXne
          have hRDltX : RDsub < X :=
            lt_of_le_of_ne hRDX (Ne.symm hXne)
          let XG : Subgroup G := X.map D.subtype
          have hXGp : IsPGroup p XG := hXp.map D.subtype
          have hRGltXG : RG < XG := by
            rw [← Subgroup.map_subgroupOf_eq_of_le hRGD]
            exact Subgroup.map_subtype_lt_map_subtype.mpr hRDltX
          let T : Subgroup G :=
            XG ⊓ Subgroup.normalizer (RG : Set G)
          have hRGltT : RG < T := by
            exact lt_inf_normalizer_of_isPGroup hXGp hRGltXG
          have hTD : T ≤ D :=
            inf_le_left.trans (Subgroup.map_subtype_le X)
          have hTM : T ≤ M := inf_le_right.trans hNRM
          have hTI : T ≤ I := le_inf hTD hTM
          let TI : Subgroup I := T.subgroupOf I
          have hTIp : IsPGroup p TI :=
            (hXGp.to_le inf_le_left).of_equiv
              (Subgroup.subgroupOfEquivOfLe hTI).symm
          have hRTI : (R : Subgroup I) ≤ TI := by
            intro x hx
            change (x : G) ∈ T
            exact hRGltT.le (Subgroup.mem_map_of_mem I.subtype hx)
          have hTIR : TI = (R : Subgroup I) :=
            R.is_maximal' hTIp hRTI
          have hTRG : T = RG := by
            rw [← Subgroup.map_subgroupOf_eq_of_le hTI]
            change TI.map I.subtype = RG
            rw [hTIR]
          exact hRGltT.ne hTRG.symm }
    refine ⟨RD, ?_⟩
    change RDsub.map D.subtype = RG
    exact Subgroup.map_subgroupOf_eq_of_le hRGD

  have hsylowD : ∃ RD : Sylow p D,
      (RD : Subgroup D).map D.subtype = RG := by
    let RM : Subgroup M := RG.subgroupOf M
    have hRMp : IsPGroup p RM :=
      hRGp.of_equiv (Subgroup.subgroupOfEquivOfLe hRGM).symm
    obtain ⟨Q, hRMQ⟩ := hRMp.exists_le_sylow
    let QG : Subgroup G := (Q : Subgroup M).map M.subtype
    have hQGp : IsPGroup p QG := Q.isPGroup'.map M.subtype
    by_cases hRMQeq : RM = (Q : Subgroup M)
    · have hQGRG : QG = RG := by
        dsimp only [QG]
        rw [← hRMQeq]
        exact Subgroup.map_subgroupOf_eq_of_le hRGM
      obtain ⟨S, hSP⟩ :=
        scn_fitting_exists_ambient_sylow
          p M P A hM hFp hSCN hRankA
      obtain ⟨Q₀, hQGQ₀⟩ := hQGp.exists_le_sylow
      have hcardQG : Nat.card QG = Nat.card (Q₀ : Subgroup G) := by
        calc
          Nat.card QG = Nat.card (Q : Subgroup M) :=
            Subgroup.card_map_of_injective M.subtype_injective
          _ = Nat.card (P : Subgroup M) :=
            Q.card_eq_multiplicity.trans P.card_eq_multiplicity.symm
          _ = Nat.card ((P : Subgroup M).map M.subtype) :=
            (Subgroup.card_map_of_injective M.subtype_injective).symm
          _ = Nat.card (S : Subgroup G) := by rw [hSP]
          _ = Nat.card (Q₀ : Subgroup G) :=
            S.card_eq_multiplicity.trans Q₀.card_eq_multiplicity.symm
      have hQGeqQ₀ : QG = (Q₀ : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hQGQ₀ hcardQG.ge
      have hQ₀D : (Q₀ : Subgroup G) ≤ D := by
        rw [← hQGeqQ₀, hQGRG]
        exact hRGD
      let RD : Sylow p D := Q₀.subtype hQ₀D
      refine ⟨RD, ?_⟩
      dsimp only [RD]
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hQ₀D]
      exact hQGeqQ₀.symm.trans hQGRG
    · have hRMltQ : RM < (Q : Subgroup M) :=
        lt_of_le_of_ne hRMQ hRMQeq
      have hRGltQG : RG < QG := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hRGM]
        exact Subgroup.map_subtype_lt_map_subtype.mpr hRMltQ
      let T : Subgroup G :=
        QG ⊓ Subgroup.normalizer (RG : Set G)
      have hRGltT : RG < T :=
        lt_inf_normalizer_of_isPGroup hQGp hRGltQG
      have hNproper : Subgroup.normalizer (RG : Set G) < ⊤ :=
        mFT_norm_proper RG hRGne (mFT_pgroup_proper RG hRGp)
      obtain ⟨E, hE, hNE⟩ :=
        mmax_exists (Subgroup.normalizer (RG : Set G)) hNproper
      have hAE : A ≤ E :=
        hARG.trans (Subgroup.le_normalizer.trans hNE)
      by_cases hEM : E = M
      · apply sylowD_of_normalizer_le
        exact hNE.trans_eq hEM
      · have hEAlt : E ∈ Alt := ⟨hE, hAE, hEM⟩
        have hTM : T ≤ M :=
          inf_le_left.trans (by
            dsimp only [QG]
            exact Subgroup.map_subtype_le (Q : Subgroup M))
        have hTE : T ≤ E := inf_le_right.trans hNE
        let J : Subgroup G := E ⊓ M
        have hTJ : T ≤ J := le_inf hTE hTM
        let TJ : Subgroup J := T.subgroupOf J
        have hTJp : IsPGroup p TJ :=
          (hQGp.to_le inf_le_left).of_equiv
            (Subgroup.subgroupOfEquivOfLe hTJ).symm
        obtain ⟨S, hTJS⟩ := hTJp.exists_le_sylow
        have hcardRGltT : Nat.card RG < Nat.card T :=
          natCard_subgroup_lt_of_lt hRGltT
        have hcardTleS : Nat.card T ≤ Nat.card (S : Subgroup J) := by
          rw [← natCard_subgroupOf_eq hTJ]
          exact Subgroup.card_le_of_le hTJS
        have hcardSscore : Nat.card (S : Subgroup J) = score E := by
          dsimp only [score, J]
          exact S.card_eq_multiplicity.trans
            (default : Sylow p ↑(E ⊓ M)).card_eq_multiplicity.symm
        have hscoreEleD : score E ≤ score D := hDmax E hEAlt
        have : Nat.card RG < Nat.card RG := calc
          Nat.card RG < Nat.card T := hcardRGltT
          _ ≤ Nat.card (S : Subgroup J) := hcardTleS
          _ = score E := hcardSscore
          _ ≤ score D := hscoreEleD
          _ = Nat.card RG := hscoreD
        exact (lt_irrefl _ this).elim

  obtain ⟨RD, hRDmap⟩ := hsylowD
  let OpD : Subgroup G := (pPrimeCore p D).map D.subtype
  have hOpDproper : OpD < ⊤ :=
    lt_of_le_of_lt (Subgroup.map_subtype_le _) (mmax_proper hD)
  have hOpDprime : IsPPrimeSubgroup p OpD := by
    rw [IsPPrimeSubgroup]
    dsimp only [OpD]
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact pPrimeCore_coprime_card
  have hAnormOpD : A ≤ Subgroup.normalizer (OpD : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      D A (pPrimeCore p D) (hAD.trans Subgroup.le_normalizer)
  have hOpDbot : OpD = ⊥ :=
    eq_bot_of_isPPrimeSubgroup_of_normalized_of_maxNormed
      p A
        (fun q hqp => scn_fitting_max_normed_eq_bot
          p M P A hM hFp hSCN hRankA q hqp)
        hOpDproper hOpDprime hAnormOpD
  have hcoreD : pPrimeCore p D = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (pPrimeCore p D) D.subtype_injective).mp
    simpa only [OpD] using hOpDbot
  have hARD : A ≤ (RD : Subgroup D).map D.subtype := by
    rwa [hRDmap]
  obtain ⟨S, hSmap⟩ :=
    exists_ambient_sylow_eq_map_of_pPrimeCore_eq_bot
      p D RD hD hcoreD hARD hAne
  have hSRG : (S : Subgroup G) = RG := hSmap.trans hRDmap

  let Z : Subgroup G := centerWithin (puig RG)
  have hZRG : Z ≤ RG := by
    simpa only [Z, hRDmap] using
      centerWithin_puig_map_sylow_le_map_sylow RD
  have hZD : Z ≤ D := hZRG.trans hRGD
  have hZnormalD : (Z.subgroupOf D).Normal := by
    simpa only [Z, hRDmap] using
      centerWithin_puig_map_sylow_normal_subgroupOf
        D RD (mFT_odd D) (mmax_sol hD) hcoreD
  have hZne : Z ≠ ⊥ := by
    simpa only [Z, hRDmap] using
      centerWithin_puig_map_sylow_ne_bot_of_le RD hARD hAne
  have hNormZD : Subgroup.normalizer (Z : Set G) = D :=
    mmax_normal hD hZD hZnormalD hZne

  have hSM : (S : Subgroup G) ≤ M := by
    rw [hSRG]
    exact hRGM
  let SM : Sylow p M := S.subtype hSM
  have hSMmap : (SM : Subgroup M).map M.subtype = RG := by
    dsimp only [SM]
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSM]
    exact hSRG
  have hcoreM : pPrimeCore p M = ⊥ :=
    pPrimeCore_eq_bot_of_fittingWithin_isPGroup
      p M (mmax_sol hM) hFp
  have hZM : Z ≤ M := hZRG.trans hRGM
  have hZnormalM : (Z.subgroupOf M).Normal := by
    simpa only [Z, hSMmap] using
      centerWithin_puig_map_sylow_normal_subgroupOf
        M SM (mFT_odd M) (mmax_sol hM) hcoreM
  have hNormZM : Subgroup.normalizer (Z : Set G) = M :=
    mmax_normal hM hZM hZnormalM hZne
  exact hDM (hNormZD.symm.trans hNormZM)

end Submission.OddOrder.BG.Section08
