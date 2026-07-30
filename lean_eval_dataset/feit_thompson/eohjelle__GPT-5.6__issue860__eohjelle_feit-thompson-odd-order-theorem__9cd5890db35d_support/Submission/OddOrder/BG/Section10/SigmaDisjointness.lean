import Submission.OddOrder.BG.Section10.BetaHallStructure
import Submission.OddOrder.BG.Section10.SigmaDisjoint
import Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement
import Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel
import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.BG.Section07.NormedTransSuperset
import Submission.OddOrder.BG.Section07.PLengthOneNormedConstrained
import Submission.OddOrder.BG.Section07.PrimeSetCorePPrime
import Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent
import Submission.OddOrder.MathlibSupport.Critical
import Submission.OddOrder.MathlibSupport.CrossPrimeHomKernel
import Submission.OddOrder.MathlibSupport.CyclicNormalizerCommutator
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.FittingSelfCentralizing
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Bender--Glauberman Section 10: sigma disjointness

This file completes the final source slice of `BGsection10.v`, namely
Propositions 10.10 and 10.11 and Lemma 10.12.  The already verified module
`SigmaDisjoint` supplies Lemma 10.12(b)'s subgroup intersection.  Here we
also port the rank-two signaliser theorem, the four sigma-complement
conclusions, the common-prime argument, and the full source-shaped wrapper.

The preceding part of the official source slice is owned by
`BetaHallStructure`.  It exports the source declarations `Mbeta_der1`,
`beta_max_pdiv`, `Mbeta_Hall`, `Mbeta_Hall_G`, `Mbeta_quo_nil`,
`beta'_der1_nil`, `beta'_cent_Sylow`, and `nonuniq_norm_Sylow_pprod`
(Corollary 10.9(b)).
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.MathlibSupport
open scoped Pointwise IsMulCommutative commutatorElement

universe u

noncomputable section

private theorem subgroup_map_symm_map_signaliser
    {K : Type*} [Group K] (H : Subgroup K) (e : K ≃* K) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  simp

private theorem subgroup_symm_map_map_signaliser
    {K : Type*} [Group K] (H : Subgroup K) (e : K ≃* K) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  simpa using subgroup_map_symm_map_signaliser H e.symm

private theorem IsNormedPiCandidate.map_equiv_signaliser
    {K : Type*} [Group K] [Finite K]
    (A Y : Subgroup K) (pi : Set ℕ) (e : K ≃* K)
    (hY : IsNormedPiCandidate (A : Set K) pi Y) :
    IsNormedPiCandidate
      (A.map e.toMonoidHom : Set K) pi
      (Y.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hY.1
  · have hnorm : A ≤ Subgroup.normalizer (Y : Set K) := hY.2
    have hmapped :
        A.map e.toMonoidHom ≤
          (Subgroup.normalizer (Y : Set K)).map e.toMonoidHom :=
      Subgroup.map_mono hnorm
    rw [Subgroup.map_equiv_normalizer_eq Y e] at hmapped
    exact hmapped

/-- Maximal normalized prime-set subgroups transport through an automorphism,
with the normalizing subgroup transported simultaneously. -/
private theorem mem_max_normed_map_equiv_signaliser
    {K : Type*} [Group K] [Finite K]
    (A Q : Subgroup K) (pi : Set ℕ) (e : K ≃* K)
    (hQ : Q ∈ max_normed_pgroups (A : Set K) pi) :
    Q.map e.toMonoidHom ∈
      max_normed_pgroups (A.map e.toMonoidHom : Set K) pi := by
  refine
    ⟨IsNormedPiCandidate.map_equiv_signaliser A Q pi e hQ.prop, ?_⟩
  intro Y hY hQY
  let Y₀ : Subgroup K := Y.map e.symm.toMonoidHom
  have hY₀ :
      IsNormedPiCandidate (A : Set K) pi Y₀ := by
    have h :=
      IsNormedPiCandidate.map_equiv_signaliser
        (A.map e.toMonoidHom) Y pi e.symm hY
    rw [subgroup_map_symm_map_signaliser A e] at h
    simpa [Y₀] using h
  have hQY₀ : Q ≤ Y₀ := by
    have hmapped :
        (Q.map e.toMonoidHom).map e.symm.toMonoidHom ≤
          Y.map e.symm.toMonoidHom :=
      Subgroup.map_mono hQY
    rw [subgroup_map_symm_map_signaliser Q e] at hmapped
    exact hmapped
  have hY₀Q : Y₀ ≤ Q := hQ.2 hY₀ hQY₀
  have hmapped :
      Y₀.map e.toMonoidHom ≤ Q.map e.toMonoidHom :=
    Subgroup.map_mono hY₀Q
  change
    (Y.map e.symm.toMonoidHom).map e.toMonoidHom ≤
      Q.map e.toMonoidHom at hmapped
  rw [subgroup_symm_map_map_signaliser Y e] at hmapped
  exact hmapped

/-- Every subgroup of a finite `p`-group is subnormal. -/
private theorem subgroup_isSubnormal_of_isPGroup_signaliser
    {K : Type*} [Group K] [Finite K]
    {r : ℕ} [Fact r.Prime]
    (hK : IsPGroup r K) (L : Subgroup K) :
    L.IsSubnormal := by
  letI : Group.IsNilpotent K := hK.isNilpotent
  refine
    (measure (fun D : Subgroup K =>
      Nat.card K - Nat.card D)).wf.induction L ?_
  intro D ih
  by_cases hDtop : D = ⊤
  · simpa [hDtop]
  let N : Subgroup K := Subgroup.normalizer (D : Set K)
  have hDN : D < N :=
    Group.normalizerCondition_of_isNilpotent D
      (lt_top_iff_ne_top.mpr hDtop)
  have hNcardLe : Nat.card N ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos N.card_subgroup_dvd_card
  have hDcardLt : Nat.card D < Nat.card N :=
    natCard_subgroup_lt_of_lt hDN
  have hmeasure :
      Nat.card K - Nat.card N <
        Nat.card K - Nat.card D := by
    omega
  have hNsn : N.IsSubnormal := ih N hmeasure
  have hDnormalN : (D.subgroupOf N).Normal := by
    apply
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDN.le).2
    exact le_rfl
  exact
    Subgroup.IsSubnormal.step D N hDN.le hNsn hDnormalN

private theorem isNarrow_subgroup_iff_top_signaliser
    {K : Type*} [Group K]
    {r : ℕ} [Fact r.Prime]
    (R : Subgroup K) :
    IsNarrow r R ↔ IsNarrow r (⊤ : Subgroup R) := by
  have hiff :=
    isNarrow_map_iff_of_injective
      (p := r) R.subtype R.subtype_injective
      (⊤ : Subgroup R)
  have hmapTop :
      (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hmapTop] at hiff
  exact hiff

/-- `BGsection10.v: max_normed_2Elem_signaliser`, Proposition 10.10. -/
theorem max_normed_2Elem_signaliser
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A Q : Subgroup G}
    (hpq : p ≠ q)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAmax : IsPMaxElem p (⊤ : Subgroup G) A)
    (hQmax :
      Q ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ))
    (hqCA :
      q ∣ Nat.card (Subgroup.centralizer (A : Set G))) :
    ∃ P : Sylow p G,
      A ≤ (P : Subgroup G) ∧
      ((pPrimeCore p
          (Subgroup.centralizer
            ((P : Subgroup G) : Set G))).map
            (Subgroup.centralizer
              ((P : Subgroup G) : Set G)).subtype : Set G) *
          ((Subgroup.normalizer
                ((P : Subgroup G) : Set G) ⊓
              Subgroup.normalizer (Q : Set G) :
            Subgroup G) : Set G) =
        (Subgroup.normalizer
          ((P : Subgroup G) : Set G) : Set G) ∧
      (P : Subgroup G) ≤
        (_root_.commutator
          (Subgroup.normalizer (Q : Set G))).map
            (Subgroup.normalizer (Q : Set G)).subtype ∧
      (IsNarrow q Q →
        (P : Subgroup G) ≤
          Subgroup.centralizer (Q : Set G)) := by
  classical
  have hAne : A ≠ ⊥ := hA.ne_bot
  letI : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAne
  have hAp : IsPGroup p A := hA.isPGroup
  have hsupport :
      primeSupport (Nat.card A) = {p} :=
    hAp.primeSupport_natCard_eq_singleton
  have hqA : q ∉ primeSupport (Nat.card A) := by
    rw [hsupport]
    simpa only [Set.mem_singleton_iff] using hpq.symm
  have hAcentral :
      A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr
      hA.commutative
  have hcstrA : NormedConstrained A :=
    plength_1_normed_constrained p A hAne hAmax
      (fun _ hH => mFT_proper_plength1 p hH)
  have htransA :
      ∀ Q₁ Q₂ : Subgroup G,
        Q₁ ∈
            max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
        Q₂ ∈
            max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
        ∃ k : G,
          k ∈ centralPrimeComplementCore A ∧
          Q₂ =
            Q₁.map (MulAut.conj k⁻¹).toMonoidHom :=
    normed_constrained_rank2_trans A hcstrA hqA hqCA
      ⟨p, A, Fact.out, le_rfl, hAcentral, hA⟩

  obtain ⟨P₀, hAP₀⟩ := hAp.exists_le_sylow
  let PG₀ : Subgroup G := (P₀ : Subgroup G)
  have hPG₀p : IsPGroup p PG₀ := by
    simpa [PG₀] using P₀.isPGroup'
  have hsnAP₀ : (A.subgroupOf PG₀).IsSubnormal :=
    subgroup_isSubnormal_of_isPGroup_signaliser
      hPG₀p (A.subgroupOf PG₀)
  have hPG₀pi :
      IsPiNumber (primeSupport (Nat.card A))
        (Nat.card PG₀) := by
    rw [hsupport]
    exact
      hPG₀p.isPiNumber_natCard
        (Set.mem_singleton p)
  have hsup₀ :=
    normed_trans_superset A PG₀ hcstrA hqA hAP₀
      hsnAP₀ hPG₀pi htransA

  obtain ⟨Q₀, hQ₀maxP₀, _⟩ :=
    max_normed_exists
      (PG₀ : Set G) ({q} : Set ℕ) (⊥ : Subgroup G)
      (by simpa using
        (IsPiNumber.one (pi := ({q} : Set ℕ))))
      Subgroup.le_normalizer_of_normal
  have hQ₀maxA :
      Q₀ ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) :=
    hsup₀.2.2.1 hQ₀maxP₀

  obtain ⟨k, hkCore, hQconj⟩ :=
    htransA Q₀ Q hQ₀maxA hQmax
  let e : G ≃* G := MulAut.conj k⁻¹
  let P : Sylow p G := k⁻¹ • P₀
  let PG : Subgroup G := (P : Subgroup G)
  have hPGcoe :
      PG = PG₀.map e.toMonoidHom := by
    change
      (MulAut.conj k⁻¹) • (P₀ : Subgroup G) =
        (P₀ : Subgroup G).map
          (MulAut.conj k⁻¹).toMonoidHom
    rfl
  have hkCentral :
      k ∈ Subgroup.centralizer (A : Set G) :=
    (primeSetCore_le
      (primeSupport (Nat.card A))ᶜ
      (Subgroup.centralizer (A : Set G))) hkCore
  have hkinvNormalizer :
      k⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem
      (Subgroup.centralizer_le_normalizer
        (A : Set G) hkCentral)
  have hAmap :
      A.map e.toMonoidHom = A := by
    dsimp only [e]
    exact
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        hkinvNormalizer
  have hAP : A ≤ PG := by
    calc
      A = A.map e.toMonoidHom := hAmap.symm
      _ ≤ PG₀.map e.toMonoidHom :=
        Subgroup.map_mono hAP₀
      _ = PG := hPGcoe.symm

  have hQ₀mapped :
      Q₀.map e.toMonoidHom ∈
        max_normed_pgroups
          (PG₀.map e.toMonoidHom : Set G)
          ({q} : Set ℕ) :=
    mem_max_normed_map_equiv_signaliser
      PG₀ Q₀ ({q} : Set ℕ) e hQ₀maxP₀
  have hQmaxP :
      Q ∈ max_normed_pgroups
        (PG : Set G) ({q} : Set ℕ) := by
    rw [hPGcoe, hQconj]
    exact hQ₀mapped

  have hPGp : IsPGroup p PG := by
    simpa [PG] using P.isPGroup'
  have hsnAP : (A.subgroupOf PG).IsSubnormal :=
    subgroup_isSubnormal_of_isPGroup_signaliser
      hPGp (A.subgroupOf PG)
  have hPGpi :
      IsPiNumber (primeSupport (Nat.card A))
        (Nat.card PG) := by
    rw [hsupport]
    exact
      hPGp.isPiNumber_natCard
        (Set.mem_singleton p)
  have hsup :=
    normed_trans_superset A PG hcstrA hqA hAP
      hsnAP hPGpi htransA
  have hconsequences := hsup.2.2.2 Q hQmaxP

  let NP : Subgroup G :=
    Subgroup.normalizer (PG : Set G)
  let NQ : Subgroup G :=
    Subgroup.normalizer (Q : Set G)
  let CP : Subgroup G :=
    Subgroup.centralizer (PG : Set G)
  let Op : Subgroup G :=
    (pPrimeCore p CP).map CP.subtype

  have hcoreEq :
      centralizerWithin
          (centralPrimeComplementCore A) PG =
        Op := by
    calc
      centralizerWithin
          (centralPrimeComplementCore A) PG =
          primeSetCore
            (primeSupport (Nat.card A))ᶜ CP := by
        simpa [CP] using hsup.1
      _ = primeSetCore ({p} : Set ℕ)ᶜ CP := by
        rw [hsupport]
      _ = Op := by
        simpa [Op] using
          (primeSetCore_compl_singleton_eq_map_pPrimeCore
            (p := p) CP)

  have hfactor :
      (NP : Set G) =
        (centralizerWithin
            (centralPrimeComplementCore A) PG : Set G) *
          ((NP ⊓ NQ : Subgroup G) : Set G) := by
    simpa [NP, NQ] using hconsequences.2
  have ha :
      (Op : Set G) *
          ((NP ⊓ NQ : Subgroup G) : Set G) =
        (NP : Set G) := by
    calc
      (Op : Set G) *
            ((NP ⊓ NQ : Subgroup G) : Set G) =
          (centralizerWithin
              (centralPrimeComplementCore A) PG : Set G) *
            ((NP ⊓ NQ : Subgroup G) : Set G) := by
        rw [hcoreEq]
      _ = (NP : Set G) := hfactor.symm

  have hPGderNP :
      PG ≤ ⁅NP, NP⁆ := by
    calc
      PG ≤
          (_root_.commutator NP).map NP.subtype := by
        simpa [PG, NP] using mFT_Sylow_der1 P
      _ = ⁅NP, NP⁆ := NP.map_subtype_commutator
  have hfocal :
      PG ⊓ ⁅NP, NP⁆ ≤ ⁅NQ, NQ⁆ := by
    simpa [NP, NQ] using hconsequences.1
  have hPGderNQ :
      PG ≤ ⁅NQ, NQ⁆ := by
    intro x hx
    exact hfocal ⟨hx, hPGderNP hx⟩
  have hb :
      PG ≤
        (_root_.commutator NQ).map NQ.subtype := by
    rw [NQ.map_subtype_commutator]
    exact hPGderNQ

  have hQp : IsPGroup q Q :=
    isPGroup_of_isPiNumber_singleton
      (mem_max_normed hQmax).1

  have hc :
      IsNarrow q Q →
        PG ≤ Subgroup.centralizer (Q : Set G) := by
    intro hQnarrow
    by_cases hQbot : Q = ⊥
    · intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyBot : y ∈ (⊥ : Subgroup G) := by
        rw [← hQbot]
        exact hy
      have hyOne : y = 1 :=
        Subgroup.mem_bot.mp hyBot
      subst y
      simp

    have hNQproper : NQ < ⊤ := by
      simpa [NQ] using
        mFT_norm_proper Q hQbot
          (mFT_pgroup_proper Q hQp)
    letI : IsSolvable NQ := mFT_sol hNQproper

    let rho : NQ →* MulAut Q :=
      Q.normalizerMonoidHom
    let AutQ : Subgroup (MulAut Q) := rho.range
    have hAutQsol : IsSolvable AutQ := by
      dsimp only [AutQ]
      exact
        solvable_of_surjective
          rho.rangeRestrict_surjective
    have hAutQodd : Odd (Nat.card AutQ) := by
      dsimp only [AutQ]
      exact
        (mFT_odd NQ).of_dvd_nat
          (Subgroup.card_range_dvd rho)
    have hQnarrowTop :
        IsNarrow q (⊤ : Subgroup Q) :=
      (isNarrow_subgroup_iff_top_signaliser Q).mp
        hQnarrow
    obtain ⟨_, hAutQquotComm, _⟩ :=
      Aut_narrow hQp (mFT_odd Q) AutQ
        hQnarrowTop hAutQsol hAutQodd
    have hAutQder :
        IsPGroup q (_root_.commutator AutQ) := by
      apply pCore_isPGroup.to_le
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        hAutQquotComm

    have hPNQ : PG ≤ NQ :=
      hb.trans
        (Subgroup.map_subtype_le
          (_root_.commutator NQ))
    let PNQ : Subgroup NQ := PG.subgroupOf NQ
    have hPNQp : IsPGroup p PNQ :=
      hPGp.of_equiv
        (Subgroup.subgroupOfEquivOfLe hPNQ).symm
    have hPNQder :
        PNQ ≤ _root_.commutator NQ := by
      intro x hx
      have hxPG : (x : G) ∈ PG := hx
      obtain ⟨y, hy, hyx⟩ := hb hxPG
      have hyEq : y = x := by
        apply Subtype.ext
        exact hyx
      simpa [hyEq] using hy

    have hmapDer :
        (_root_.commutator NQ).map rho =
          (_root_.commutator AutQ).map AutQ.subtype := by
      calc
        (_root_.commutator NQ).map rho =
            ⁅rho.range, rho.range⁆ :=
          map_commutator_eq NQ rho
        _ =
            (_root_.commutator AutQ).map
              AutQ.subtype := by
          simpa [AutQ] using
            (Subgroup.map_subtype_commutator AutQ).symm
    have hPNQmapLe :
        PNQ.map rho ≤
          (_root_.commutator AutQ).map
            AutQ.subtype := by
      calc
        PNQ.map rho ≤
            (_root_.commutator NQ).map rho :=
          Subgroup.map_mono hPNQder
        _ =
            (_root_.commutator AutQ).map
              AutQ.subtype :=
          hmapDer
    have hPNQmapQ :
        IsPGroup q (PNQ.map rho) :=
      IsPGroup.to_le
        (hAutQder.map AutQ.subtype) hPNQmapLe
    have hPNQmapP :
        IsPGroup p (PNQ.map rho) :=
      hPNQp.map rho
    have hPNQmapBot :
        PNQ.map rho = ⊥ :=
      eq_bot_of_isPGroup_of_isPGroup hpq
        (PNQ.map rho) hPNQmapP hPNQmapQ
    have hPNQker : PNQ ≤ rho.ker := by
      intro x hx
      apply MonoidHom.mem_ker.mpr
      have hrhoBot :
          rho x ∈ (⊥ : Subgroup (MulAut Q)) := by
        rw [← hPNQmapBot]
        exact ⟨x, hx, rfl⟩
      exact Subgroup.mem_bot.mp hrhoBot

    intro x hxPG
    let xn : NQ := ⟨x, hPNQ hxPG⟩
    have hxnPNQ : xn ∈ PNQ := hxPG
    have hxnKer : xn ∈ rho.ker :=
      hPNQker hxnPNQ
    change
      xn ∈ Q.normalizerMonoidHom.ker at hxnKer
    rw [Subgroup.normalizerMonoidHom_ker] at hxnKer
    exact hxnKer

  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · simpa [PG] using hAP
  · simpa [PG, NP, NQ, CP, Op] using ha
  · simpa [PG, NQ] using hb
  · simpa [PG] using hc

/-- A Sylow subgroup of a Hall subgroup maps to an ambient Sylow subgroup. -/
private theorem exists_sylow_eq_map_of_sylow_hall_10_11
    {H : Type u} [Group H] [Finite H]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup H} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup H := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

private theorem exists_elementaryAbelian_rank_three_of_rank_two_lt_10_11
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B E : Subgroup G}
    (hB : IsElementaryAbelianOfRank p 2 B)
    (hE : IsElementaryAbelianGroup p E) (hBE : B < E) :
    ∃ F : Subgroup G, F ≤ E ∧ IsElementaryAbelianOfRank p 3 F := by
  obtain ⟨n, hEcard⟩ := hE.isPGroup.exists_card_eq
  have hpowlt : p ^ 2 < p ^ n := by
    simpa only [hB.card_eq, hEcard] using
      natCard_subgroup_lt_of_lt hBE
  have hn : 3 ≤ n := by
    by_contra hnot
    have hnle : n ≤ 2 := by omega
    exact (not_lt_of_ge
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle)) hpowlt
  have hpThreeLe : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  obtain ⟨F₀, hF₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup hpThreeLe
  have hF₀ : IsElementaryAbelianOfRank p 3 F₀ := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.to_subgroup F₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hF₀card }
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  let F : Subgroup G := F₀.map E.subtype
  exact ⟨F, Subgroup.map_subtype_le F₀,
    hF₀.map_of_injective E.subtype E.subtype_injective⟩

private theorem piCore_isHall_of_isNilpotent_10_11
    {H : Type u} [Group H] [Finite H] [Group.IsNilpotent H]
    (pi : Set ℕ) : IsHall pi (piCore pi H) := by
  refine ⟨piCore_isPiNumber pi, ?_⟩
  intro p hp hpIndex hpPi
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p H := Classical.choice Sylow.nonempty
  have hPnormal : (P : Subgroup H).Normal := by infer_instance
  have hPpi : IsPiNumber pi (Nat.card P) :=
    P.isPGroup'.isPiNumber_natCard hpPi
  have hPle : (P : Subgroup H) ≤ piCore pi H :=
    le_piCore hPnormal hPpi
  exact P.not_dvd_index
    (hpIndex.trans (Subgroup.index_dvd_of_le hPle))

private theorem subgroup_characteristic_of_isCyclic_10_11
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact H.zpow_mem hx m

private theorem commutator_isNilpotent_of_alphaCore_eq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hbot : alphaCore M = ⊥) :
    Group.IsNilpotent (_root_.commutator M) := by
  have hsubbot : (alphaCore M).subgroupOf M = ⊥ := by
    simp [hbot]
  have hqnil := Malpha_quo_nil hM
  let eQ :
      (M ⧸ (alphaCore M).subgroupOf M) ≃*
        (M ⧸ (⊥ : Subgroup M)) :=
    QuotientGroup.quotientMulEquivOfEq hsubbot
  have heQrange : eQ.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr eQ.surjective
  have hmapQ :
      (_root_.commutator
          (M ⧸ (alphaCore M).subgroupOf M)).map
            eQ.toMonoidHom =
        _root_.commutator (M ⧸ (⊥ : Subgroup M)) := by
    simpa only [heQrange, _root_.commutator_def] using
      (map_commutator_eq
        (M ⧸ (alphaCore M).subgroupOf M) eQ.toMonoidHom)
  let eQD :
      _root_.commutator
          (M ⧸ (alphaCore M).subgroupOf M) ≃*
        _root_.commutator (M ⧸ (⊥ : Subgroup M)) :=
    (eQ.subgroupMap
      (_root_.commutator
        (M ⧸ (alphaCore M).subgroupOf M))).trans
      (MulEquiv.subgroupCongr hmapQ)
  letI : Group.IsNilpotent
      (_root_.commutator (M ⧸ (⊥ : Subgroup M))) :=
    Group.nilpotent_of_mulEquiv eQD
  let e : (M ⧸ (⊥ : Subgroup M)) ≃* M :=
    QuotientGroup.quotientBot
  have herange : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr e.surjective
  have hmap :
      (_root_.commutator (M ⧸ (⊥ : Subgroup M))).map
          e.toMonoidHom =
        _root_.commutator M := by
    simpa only [herange, _root_.commutator_def] using
      (map_commutator_eq (M ⧸ (⊥ : Subgroup M)) e.toMonoidHom)
  let eD : _root_.commutator (M ⧸ (⊥ : Subgroup M)) ≃*
      _root_.commutator M :=
    (e.subgroupMap
      (_root_.commutator (M ⧸ (⊥ : Subgroup M)))).trans
      (MulEquiv.subgroupCongr hmap)
  exact Group.nilpotent_of_mulEquiv eD

/-- A `pi`-subgroup lies in a normal `pi`-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    have hpPi : p ∈ pi := hLpi hp hpL
    have hpNotPi : p ∈ piᶜ :=
      hNHall.isPiNumber_index hp hpIndex
    exact hpNotPi hpPi
  intro x hxL
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : q x = 1 := orderOf_eq_one_iff.mp horderOne
  exact (QuotientGroup.eq_one_iff x).mp (by simpa [q] using hqOne)

/-- `BGsection10.v: sigma'_not_uniq`, Proposition 10.11(a). -/
theorem sigma'_not_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hKsigma' : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K)) :
    K ∉ minSimple_uniq_max_groups (G := G) := by
  classical
  intro hKuniq
  obtain ⟨E, hKE, hEM, hEHall⟩ :=
    exists_ambient_isHall_ge_of_isSolvable
      hKM (mmax_sol hM) (sigmaPrimes M)ᶜ hKsigma'
  have hEne : E ≠ ⊥ := by
    intro hEbot
    apply uniq_mmax_neq1 hKuniq
    exact le_bot_iff.mp (hEbot ▸ hKE)
  have hEcard : 1 < Nat.card E :=
    E.one_lt_card_iff_ne_bot.mpr hEne
  obtain ⟨p, hp, hpE, hpmax⟩ :=
    exists_maximal_prime_divisor hEcard
  letI : Fact p.Prime := ⟨hp⟩
  have hEcompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
    rw [← natCard_subgroupOf_eq hEM]
    exact hEHall.isPiNumber_card
  have hpCompl : p ∈ (sigmaPrimes M)ᶜ :=
    hEcompl hp hpE
  have hEsol : IsSolvable E := by
    letI : IsSolvable M := mmax_sol hM
    exact solvable_of_solvable_injective
      (f := Subgroup.inclusion hEM)
      (Subgroup.inclusion_injective hEM)
  have hRankCore : ∀ q : ℕ, q.Prime →
      ¬ ∃ A : Subgroup (fittingCore E),
        IsElementaryAbelianOfRank q 3 A := by
    intro q hq
    rintro ⟨A, hA⟩
    let AE : Subgroup E := A.map (fittingCore E).subtype
    let AG : Subgroup G := AE.map E.subtype
    have hAE : IsElementaryAbelianOfRank q 3 AE := by
      dsimp [AE]
      exact hA.map_of_injective (fittingCore E).subtype
        (fittingCore E).subtype_injective
    have hAG : IsElementaryAbelianOfRank q 3 AG := by
      dsimp [AG]
      exact hAE.map_of_injective E.subtype E.subtype_injective
    have hAGE : AG ≤ E := by
      dsimp [AG, AE]
      exact Subgroup.map_subtype_le _
    have hqAG : q ∣ Nat.card AG := by
      rw [hAG.card_eq]
      exact dvd_pow_self q (by omega)
    have hqE : q ∣ Nat.card E :=
      hqAG.trans (Subgroup.card_dvd_of_le hAGE)
    have hqCompl : q ∈ (sigmaPrimes M)ᶜ :=
      hEcompl hq hqE
    exact hqCompl (alpha_sub_sigma hM
      ⟨hq, AG, hAGE.trans hEM, hAG⟩)
  have hpIndex : ¬ p ∣ (pCore p E).index :=
    rank2_max_pcore_Sylow hpmax (mFT_odd E) hEsol hRankCore
  let PE : Sylow p E := pCore_isPGroup.toSylow hpIndex
  let H : Subgroup M := E.subgroupOf M
  let eH : H ≃* E := Subgroup.subgroupOfEquivOfLe hEM
  let PH : Sylow p H := PE.mapSurjective
    (f := eH.symm.toMonoidHom) eH.symm.surjective
  obtain ⟨PM, hPM⟩ :=
    exists_sylow_eq_map_of_sylow_hall_10_11 hp hEHall hpCompl PH
  let P : Subgroup G := ambientSylow E PE
  have hPambient : ambientSylow M PM = P := by
    dsimp [ambientSylow, P]
    rw [hPM]
    change
      ((((PE : Subgroup E).map eH.symm.toMonoidHom).map H.subtype).map
          M.subtype) =
        (PE : Subgroup E).map E.subtype
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun f : E →* G => (PE : Subgroup E).map f)
    ext x
    rfl
  have hPE : P ≤ E := by
    dsimp [P, ambientSylow]
    exact Subgroup.map_subtype_le _
  have hPnormalE : (P.subgroupOf E).Normal := by
    dsimp [P, ambientSylow]
    change ((((PE : Subgroup E).map E.subtype).comap E.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
    change (pCore p E).Normal
    infer_instance
  have hEnormP : E ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPE).mp hPnormalE
  have hPp : IsPGroup p P := by
    dsimp [P, ambientSylow]
    exact PE.isPGroup'.map E.subtype
  have hPne : P ≠ ⊥ := by
    have hPEne : (PE : Subgroup E) ≠ ⊥ :=
      PE.ne_bot_of_dvd_card hpE
    intro hPbot
    exact hPEne ((Subgroup.map_eq_bot_iff_of_injective
      (PE : Subgroup E) E.subtype_injective).mp hPbot)
  have hKfamily :
      minSimple_max_groups_of (G := G) (K : Set G) = {M} :=
    def_uniq_mmax hKuniq hM hKM
  have hNormProper : Subgroup.normalizer (P : Set G) < ⊤ :=
    mFT_norm_proper P hPne (mFT_pgroup_proper P hPp)
  have hNormM : Subgroup.normalizer (P : Set G) ≤ M :=
    sub_uniq_mmax hKfamily (hKE.trans hEnormP) hNormProper
  apply hpCompl
  refine ⟨hp, PM, ?_⟩
  simpa [hPambient] using hNormM

/-- `BGsection10.v: sub'cent_sigma_rank1`, Proposition 10.11(b). -/
theorem sub'cent_sigma_rank1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hKsigma' : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K)) :
    ∀ p : ℕ, p.Prime →
      ¬ HasElementaryAbelianRankAtLeast p 2
        (centralizerWithin K (sigmaCore M)) := by
  classical
  intro p hp hRank
  letI : Fact p.Prime := ⟨hp⟩
  rcases hRank with ⟨A, hAC, hA⟩
  have hAK : A ≤ K :=
    hAC.trans (centralizerWithin_le_left K (sigmaCore M))
  have hAcentSigma :
      A ≤ Subgroup.centralizer (sigmaCore M : Set G) :=
    hAC.trans inf_le_right
  have hpA : p ∣ Nat.card A := by
    rw [hA.card_eq]
    exact dvd_pow_self p (by omega)
  have hpK : p ∣ Nat.card K :=
    hpA.trans (Subgroup.card_dvd_of_le hAK)
  have hpCompl : p ∈ (sigmaPrimes M)ᶜ :=
    hKsigma' hp hpK
  have hKproper : K < ⊤ :=
    lt_of_le_of_lt hKM (mmax_proper hM)
  have hNoRankThreeCentralizer : ∀ q : ℕ, q.Prime →
      ¬ HasElementaryAbelianRankAtLeast q 3
        (Subgroup.centralizer (A : Set G)) := by
    intro q hq hqRank
    have hAuniq :
        A ∈ minSimple_uniq_max_groups (G := G) :=
      cent_rank3_Uniqueness
        ⟨p, hp, A, le_rfl, hA⟩ ⟨q, hq, hqRank⟩
    exact sigma'_not_uniq hM hKM hKsigma'
      (uniq_mmaxS hAK hKproper hAuniq)
  have hAmax : IsPMaxElem p (⊤ : Subgroup G) A := by
    refine ⟨⟨le_top, hA.toIsElementaryAbelianGroup⟩, ?_⟩
    intro B hB hAB
    apply le_antisymm ?_ hAB
    by_contra hnot
    have hABlt : A < B :=
      lt_of_le_of_ne hAB (fun hEq => hnot hEq.ge)
    obtain ⟨C, hCB, hC⟩ :=
      exists_elementaryAbelian_rank_three_of_rank_two_lt_10_11
        hA hB.2 hABlt
    have hBcentA : B ≤ Subgroup.centralizer (A : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      letI : IsMulCommutative B := hB.2.commutative
      exact congrArg (fun z : B ↦ (z : G))
        (mul_comm (⟨a, hAB ha⟩ : B) (⟨b, hb⟩ : B))
    exact hNoRankThreeCentralizer p hp
      ⟨C, hCB.trans hBcentA, hC⟩
  have hSigmaNe : sigmaCore M ≠ ⊥ := Msigma_neq1 hM
  have hSigmaCard : 1 < Nat.card (sigmaCore M) :=
    (sigmaCore M).one_lt_card_iff_ne_bot.mpr hSigmaNe
  obtain ⟨q, hq, hqSigmaCard, _hqmax⟩ :=
    exists_maximal_prime_divisor hSigmaCard
  letI : Fact q.Prime := ⟨hq⟩
  have hqSigma : q ∈ sigmaPrimes M :=
    sigmaCore_isPiNumber M hq hqSigmaCard
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hpCompl hqSigma
  let R : Sylow q M := Classical.choice Sylow.nonempty
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hRpi : IsPiNumber (sigmaPrimes M) (Nat.card R) :=
    R.isPGroup'.isPiNumber_natCard hqSigma
  have hRS : (R : Subgroup M) ≤ S :=
    isPiNumber_le_normal_isHall
      (by simpa [S] using sigmaCore_normal M)
      (by simpa [S] using Msigma_Hall hM) hRpi
  let Q : Subgroup G := ambientSylow M R
  obtain ⟨QG, hQG⟩ := sigma_Sylow_G hM hqSigma R
  have hQSigma : Q ≤ sigmaCore M := by
    dsimp [Q, ambientSylow]
    calc
      (R : Subgroup M).map M.subtype ≤ S.map M.subtype :=
        Subgroup.map_mono hRS
      _ = sigmaCore M :=
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)
  have hAcentQ : A ≤ Subgroup.centralizer (Q : Set G) :=
    hAcentSigma.trans (Subgroup.centralizer_le hQSigma)
  have hQcentA : Q ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff.mp hAcentQ
  have hQp : IsPGroup q Q := by
    change IsPGroup q (ambientSylow M R)
    rw [← hQG]
    exact QG.isPGroup'
  have hAQnorm :
      (A : Set G) ⊆ Subgroup.normalizer (Q : Set G) :=
    hAcentQ.trans
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  have hQmax :
      Q ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
    refine ⟨⟨hQp.isPiNumber_natCard (by simp), hAQnorm⟩, ?_⟩
    intro T hT hQT
    have hTq : IsPGroup q T :=
      isPGroup_of_isPiNumber_singleton hT.1
    have hQGT : (QG : Subgroup G) ≤ T := by
      rw [hQG]
      exact hQT
    have hTeq : T = (QG : Subgroup G) :=
      QG.is_maximal' hTq hQGT
    change T ≤ ambientSylow M R
    rw [← hQG]
    exact hTeq.le
  have hqG : q ∣ Nat.card G :=
    hqSigmaCard.trans (sigmaCore M).card_subgroup_dvd_card
  have hqQ : q ∣ Nat.card Q := by
    simpa only [Q, ← hQG] using
      QG.dvd_card_of_dvd_card hqG
  have hqCentA :
      q ∣ Nat.card (Subgroup.centralizer (A : Set G)) :=
    hqQ.trans (Subgroup.card_dvd_of_le hQcentA)
  obtain ⟨P, hAP, _hfactor, hPderNQ, _hnarrow⟩ :=
    max_normed_2Elem_signaliser hpq hA hAmax hQmax hqCentA
  have hAlphaBot : alphaCore M = ⊥ := by
    by_contra hAlphaNe
    have hcardAlpha : 1 < Nat.card (alphaCore M) :=
      (alphaCore M).one_lt_card_iff_ne_bot.mpr hAlphaNe
    obtain ⟨r, hr, hrAlphaCard, _⟩ :=
      exists_maximal_prime_divisor hcardAlpha
    letI : Fact r.Prime := ⟨hr⟩
    have hrAlpha : r ∈ alphaPrimes M :=
      alphaCore_isPiNumber M hr hrAlphaCard
    rcases hrAlpha with ⟨_hr, E, hEM, hE⟩
    let EM : Subgroup M := E.subgroupOf M
    have hEMpi :
        IsPiNumber (sigmaPrimes M) (Nat.card EM) := by
      rw [natCard_subgroupOf_eq hEM]
      exact hE.isPGroup.isPiNumber_natCard
        (alpha_sub_sigma hM ⟨hr, E, hEM, hE⟩)
    have hEMS : EM ≤ S :=
      isPiNumber_le_normal_isHall
        (by simpa [S] using sigmaCore_normal M)
        (by simpa [S] using Msigma_Hall hM) hEMpi
    have hESigma : E ≤ sigmaCore M := by
      calc
        E = EM.map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hEM).symm
        _ ≤ S.map M.subtype := Subgroup.map_mono hEMS
        _ = sigmaCore M :=
          Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)
    have hSigmaCentA :
        sigmaCore M ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mp hAcentSigma
    exact hNoRankThreeCentralizer r hr
      ⟨E, hESigma.trans hSigmaCentA, hE⟩
  let D : Subgroup M := _root_.commutator M
  have hDnil : Group.IsNilpotent D :=
    commutator_isNilpotent_of_alphaCore_eq_bot hM hAlphaBot
  let NQ : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hNQM : NQ ≤ M := by
    dsimp [NQ, Q]
    exact norm_sigma_Sylow hqSigma R
  have hDerivedMono :
      (_root_.commutator NQ).map NQ.subtype ≤
        D.map M.subtype := by
    calc
      (_root_.commutator NQ).map NQ.subtype = ⁅NQ, NQ⁆ :=
        NQ.map_subtype_commutator
      _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hNQM hNQM
      _ = (_root_.commutator M).map M.subtype :=
        M.map_subtype_commutator.symm
  have hPDG : (P : Subgroup G) ≤ D.map M.subtype :=
    hPderNQ.trans hDerivedMono
  have hPM : (P : Subgroup G) ≤ M :=
    hPDG.trans (Subgroup.map_subtype_le D)
  let PM : Sylow p M := P.subtype hPM
  have hPambient : ambientSylow M PM = (P : Subgroup G) := by
    dsimp [PM, ambientSylow]
    exact Subgroup.map_subgroupOf_eq_of_le hPM
  have hPMD : (PM : Subgroup M) ≤ D := by
    apply (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp
    change ambientSylow M PM ≤ D.map M.subtype
    rw [hPambient]
    exact hPDG
  letI : Group.IsNilpotent D := hDnil
  let PD : Sylow p D := PM.subtype hPMD
  have hPDnormal : (PD : Subgroup D).Normal := by infer_instance
  letI : (PD : Subgroup D).Characteristic :=
    PD.characteristic_of_normal hPDnormal
  have hPMnormal : (PM : Subgroup M).Normal := by
    have hmapNormal : ((PD : Subgroup D).map D.subtype).Normal := by
      infer_instance
    simpa [PD, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hPMD] using hmapNormal
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hPbot
    exact hA.ne_bot (eq_bot_iff.mpr (hAP.trans hPbot.le))
  have hNormP :
      Subgroup.normalizer ((P : Subgroup G) : Set G) = M :=
    mmax_normal hM hPM hPMnormal hPne
  apply hpCompl
  refine ⟨hp, PM, ?_⟩
  rw [hPambient, hNormP]

private theorem subgroupOf_sup_isComplement_10_11
    {G : Type u} [Group G] {H R : Subgroup G}
    (hnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hdis : Disjoint H R) :
    (H.subgroupOf (R ⊔ H)).IsComplement'
      (R.subgroupOf (R ⊔ H)) := by
  let J : Subgroup G := R ⊔ H
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : HJ.Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have hdisJ : Disjoint HJ RJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxbot : ((x : J) : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxbot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJ
  have hnormJ : RJ ≤ Subgroup.normalizer (HJ : Set J) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : HJ.Normal)]
    exact le_top
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left HJ RJ hnormJ]
  have hsup : HJ ⊔ RJ = ⊤ := by
    change H.subgroupOf J ⊔ R.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show H ≤ J from le_sup_right)
      (show R ≤ J from le_sup_left)]
    simp [J, sup_comm]
  rw [hsup]
  rfl

private theorem hall_le_piCore_of_isNilpotent_10_11
    {J : Type u} [Group J] [Finite J] [Group.IsNilpotent J]
    {pi : Set ℕ} {H : Subgroup J} (hH : IsHall pi H) :
    H ≤ piCore pi J := by
  calc
    H = (sylowSup H).map H.subtype := by
      rw [sylowSup_eq_top]
      exact H.range_subtype.symm.trans
        (MonoidHom.range_eq_map H.subtype)
    _ = ⨆ q : {q : ℕ // q.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (q : ℕ)) (G := H)) : Sylow q H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ piCore pi J := by
      apply iSup_le
      intro q
      letI : Fact (q : ℕ).Prime := ⟨q.property⟩
      let Q : Sylow (q : ℕ) H := Classical.choice Sylow.nonempty
      by_cases hQbot : (Q : Subgroup H) = ⊥
      · simp [Q, hQbot]
      have hqQ : (q : ℕ) ∣ Nat.card Q :=
        Q.isPGroup'.card_eq_or_dvd.resolve_left
          (fun hcard => hQbot (Subgroup.card_eq_one.mp hcard))
      have hqPi : (q : ℕ) ∈ pi :=
        hH.isPiNumber_card q.property
          (hqQ.trans (Q : Subgroup H).card_subgroup_dvd_card)
      have hmapQ : IsPGroup (q : ℕ)
          ((Q : Subgroup H).map H.subtype) :=
        Q.isPGroup'.map H.subtype
      exact (hmapQ.le_pCore_of_isNilpotent).trans
        (le_piCore (by infer_instance)
          (pCore_isPGroup.isPiNumber_natCard hqPi))

private theorem hall_eq_piCore_of_isNilpotent_10_11
    {J : Type u} [Group J] [Finite J] [Group.IsNilpotent J]
    {pi : Set ℕ} {H : Subgroup J} (hH : IsHall pi H) :
    H = piCore pi J := by
  have hle : H ≤ piCore pi J :=
    hall_le_piCore_of_isNilpotent_10_11 hH
  have hrelPi : IsPiNumber pi (H.relIndex (piCore pi J)) :=
    (piCore_isPiNumber pi).of_dvd
      (Subgroup.relIndex_dvd_card H (piCore pi J))
  have hrelCompl : IsPiNumber piᶜ
      (H.relIndex (piCore pi J)) :=
    hH.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hle)
  have hcop : (H.relIndex (piCore pi J)).Coprime
      (H.relIndex (piCore pi J)) :=
    hrelPi.coprime_compl hrelCompl
  have hone : H.relIndex (piCore pi J) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

private theorem centralizerWithin_commutator_eq_bot_of_coprime_abelian
    {G : Type u} [Group G] [Finite G] {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card P))
    (hKab : IsMulCommutative K) :
    centralizerWithin ⁅K, P⁆ P = ⊥ := by
  classical
  let T : Subgroup G := ⁅K, P⁆
  have hTK : T ≤ K := by
    dsimp [T]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPnormK
  have hPnormT : P ≤ Subgroup.normalizer (T : Set G) := by
    dsimp [T]
    exact Subgroup.normalizer_commutator_ge_right K P
  have hTcop : Nat.Coprime (Nat.card T) (Nat.card P) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hTK)
  letI : IsMulCommutative K := hKab
  letI : IsSolvable K :=
    _root_.isSolvable_of_comm (fun a b => mul_comm a b)
  have hidem : ⁅P, ⁅P, K⁆⁆ = ⁅P, K⁆ :=
    commutator_commutator_eq_of_coprime
      (K := K) (R := P) hPnormK hcop
  have hperfect : ⁅P, T⁆ = T := by
    dsimp [T]
    rw [Subgroup.commutator_comm K P]
    exact hidem
  letI : IsMulCommutative T := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    exact congrArg (fun z : K ↦ (z : G))
      (mul_comm (⟨x, hTK x.2⟩ : K) (⟨y, hTK y.2⟩ : K))
  apply le_antisymm _ bot_le
  intro x hx
  let xt : T := ⟨x, hx.1⟩
  have hfix : ∀ a : P,
      (a : G) * (xt : G) * (a : G)⁻¹ = (xt : G) := by
    intro a
    calc
      (a : G) * (xt : G) * (a : G)⁻¹ =
          (xt : G) * (a : G) * (a : G)⁻¹ := by
            rw [hx.2 (a : G) a.2]
      _ = (xt : G) := by simp
  have hxt : xt = 1 :=
    Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
        hPnormT hTcop hperfect xt hfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxt)

/-- Regard the elementary-abelian rank-three witness for `M` inside any
Sylow `p`-subgroup of `M`, viewed in the ambient group. -/
private theorem sylow_has_rank_three_of_mem_alpha
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p M) :
    HasElementaryAbelianRankAtLeast p 3 (ambientSylow M P) := by
  classical
  rcases hpAlpha with ⟨_hprime, E, hEM, hE⟩
  let EM : Subgroup M := E.subgroupOf M
  have hEMrank : IsElementaryAbelianOfRank p 3 EM :=
    hE.subgroupOf hEM
  obtain ⟨Q, hEMQ⟩ := hEMrank.isPGroup.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q P
  let C : Subgroup M := EM.map (MulAut.conj m).toMonoidHom
  have hQmap :
      (Q : Subgroup M).map (MulAut.conj m).toMonoidHom =
        (P : Subgroup M) := by
    change MulAut.conj m • (Q : Subgroup M) = (P : Subgroup M)
    rw [← Sylow.coe_subgroup_smul, hm]
  have hCP : C ≤ (P : Subgroup M) :=
    (Subgroup.map_mono hEMQ).trans_eq hQmap
  have hC : IsElementaryAbelianOfRank p 3 C :=
    hEMrank.map_of_injective (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective
  let D : Subgroup G := C.map M.subtype
  exact ⟨D, Subgroup.map_mono hCP,
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- `BGsection10.v: sub'cent_sigma_cyclic`, Proposition 10.11(c). -/
theorem sub'cent_sigma_cyclic
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hKsigma' : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K)) :
    let Y := centralizerWithin K (sigmaCore M) ⊓
      (_root_.commutator M).map M.subtype
    IsCyclic Y ∧ (Y.subgroupOf M).Normal := by
  classical
  dsimp only
  let Y : Subgroup G := centralizerWithin K (sigmaCore M) ⊓
    (_root_.commutator M).map M.subtype
  change IsCyclic Y ∧ (Y.subgroupOf M).Normal
  letI : IsSolvable M := mmax_sol hM
  let F : Subgroup M := fittingCore M
  let ZF : Subgroup F := piCore (sigmaPrimes M)ᶜ F
  let ZM : Subgroup M := ZF.map F.subtype
  let Z : Subgroup G := ZM.map M.subtype
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  letI : Group.IsNilpotent ZF := inferInstance
  letI : Group.IsNilpotent ZM :=
    Group.nilpotent_of_mulEquiv
      (ZF.equivMapOfInjective F.subtype F.subtype_injective)
  letI : Group.IsNilpotent Z :=
    Group.nilpotent_of_mulEquiv
      (ZM.equivMapOfInjective M.subtype M.subtype_injective)
  letI : F.Characteristic := by
    dsimp [F]
    infer_instance
  letI : ZF.Characteristic := by
    dsimp [ZF]
    infer_instance
  letI : ZM.Characteristic := by
    dsimp [ZM]
    infer_instance

  have hZFcompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card ZF) := by
    simpa [ZF] using
      (piCore_isPiNumber (G := F) (sigmaPrimes M)ᶜ)
  have hZMcompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card ZM) := by
    dsimp [ZM]
    rw [Subgroup.card_map_of_injective F.subtype_injective]
    exact hZFcompl
  have hZcompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card Z) := by
    dsimp [Z]
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hZMcompl
  have hZleM : Z ≤ M := by
    dsimp [Z]
    exact Subgroup.map_subtype_le _
  have hZnormalM : (Z.subgroupOf M).Normal := by
    change (((ZM.map M.subtype).comap M.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective]
    infer_instance

  let S : Subgroup M := (sigmaCore M).subgroupOf M
  letI : S.Normal := by
    simpa [S] using sigmaCore_normal M
  have hSsigma : IsPiNumber (sigmaPrimes M) (Nat.card S) := by
    rw [natCard_subgroupOf_eq (sigmaCore_le M)]
    exact sigmaCore_isPiNumber M
  have hdisZS : Disjoint ZM S :=
    Subgroup.disjoint_of_coprime_natCard
      (hSsigma.coprime_compl hZMcompl).symm
  have hcommZS := Subgroup.commute_of_normal_of_disjoint
    ZM S (by infer_instance) (by infer_instance) hdisZS
  have hZMcentS : ZM ≤ Subgroup.centralizer (S : Set M) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hcommZS z s hz hs).eq.symm
  have hZcentSigma :
      Z ≤ Subgroup.centralizer (sigmaCore M : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    let sm : M := ⟨s, sigmaCore_le M hs⟩
    have hsmS : sm ∈ S := hs
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hZMcentS hz) sm hsmS)
  have hcentZ : centralizerWithin Z (sigmaCore M) = Z := by
    apply le_antisymm
      (centralizerWithin_le_left Z (sigmaCore M))
    intro z hz
    exact mem_centralizerWithin.mpr
      ⟨hz, fun s hs =>
        Subgroup.mem_centralizer_iff.mp (hZcentSigma hz) s hs⟩

  have hNoRankZ : ∀ p : ℕ, p.Prime →
      ¬ HasElementaryAbelianRankAtLeast p 2 Z := by
    intro p hp hRank
    have hNo := sub'cent_sigma_rank1 hM hZleM hZcompl p hp
    apply hNo
    rwa [hcentZ]
  have hZZgroup : IsZGroup Z := by
    apply (odd_isZGroup_iff_sylow_no_elementaryAbelian_rank_two
      (mFT_odd Z)).mpr
    intro p hp P
    rintro ⟨E, hE⟩
    let E1 : Subgroup Z := E.map (P : Subgroup Z).subtype
    let EG : Subgroup G := E1.map Z.subtype
    have hE1 : IsElementaryAbelianOfRank p 2 E1 := by
      dsimp [E1]
      exact hE.map_of_injective (P : Subgroup Z).subtype
        (P : Subgroup Z).subtype_injective
    have hEG : IsElementaryAbelianOfRank p 2 EG := by
      dsimp [EG]
      exact hE1.map_of_injective Z.subtype Z.subtype_injective
    exact hNoRankZ p hp
      ⟨EG, Subgroup.map_subtype_le E1, hEG⟩
  letI : IsZGroup Z := hZZgroup
  have hZcyclic : IsCyclic Z := by infer_instance
  letI : IsCyclic Z := hZcyclic

  have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZleM).mp
      hZnormalM
  have hDerCentZ : ⁅M, M⁆ ≤ Subgroup.centralizer (Z : Set G) :=
    commutator_le_centralizer_of_normalizes_isCyclic
      Z M M hZcyclic hMnormZ hMnormZ
  have hMderCentZ :
      (_root_.commutator M).map M.subtype ≤
        Subgroup.centralizer (Z : Set G) := by
    rw [M.map_subtype_commutator]
    exact hDerCentZ

  let SF : Subgroup F := piCore (sigmaPrimes M) F
  have hSFHall : IsHall (sigmaPrimes M) SF := by
    simpa [SF] using
      (piCore_isHall_of_isNilpotent_10_11
        (H := F) (sigmaPrimes M))
  have hZFHall : IsHall (sigmaPrimes M)ᶜ ZF := by
    simpa [ZF] using
      (piCore_isHall_of_isNilpotent_10_11
        (H := F) (sigmaPrimes M)ᶜ)
  have hSFsupZF : SF ⊔ ZF = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpIndex
    have hpSFIndex : p ∣ SF.index :=
      hpIndex.trans (Subgroup.index_dvd_of_le
        (show SF ≤ SF ⊔ ZF from le_sup_left))
    have hpZFIndex : p ∣ ZF.index :=
      hpIndex.trans (Subgroup.index_dvd_of_le
        (show ZF ≤ SF ⊔ ZF from le_sup_right))
    have hpNotSigma : p ∈ (sigmaPrimes M)ᶜ :=
      hSFHall.isPiNumber_index hp hpSFIndex
    have hpSigma : p ∈ sigmaPrimes M := by
      have h := hZFHall.isPiNumber_index hp hpZFIndex
      simpa only [compl_compl] using h
    exact hpNotSigma hpSigma
  let SFM : Subgroup M := SF.map F.subtype
  have hSFMpi : IsPiNumber (sigmaPrimes M) (Nat.card SFM) := by
    dsimp [SFM]
    rw [Subgroup.card_map_of_injective F.subtype_injective]
    simpa [SF] using
      (piCore_isPiNumber (G := F) (sigmaPrimes M))
  have hSFMleS : SFM ≤ S := by
    apply isPiNumber_le_normal_isHall
      (hNnormal := (show S.Normal from inferInstance))
      (hNHall := by simpa [S] using Msigma_Hall hM)
      hSFMpi
  let SFG : Subgroup G := SFM.map M.subtype
  have hSFGleSigma : SFG ≤ sigmaCore M := by
    calc
      SFG ≤ S.map M.subtype := Subgroup.map_mono hSFMleS
      _ = sigmaCore M :=
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)
  have hFMdecomp : SFM ⊔ ZM = F := by
    calc
      SFM ⊔ ZM = (SF ⊔ ZF).map F.subtype := by
        simp only [SFM, ZM, Subgroup.map_sup]
      _ = (⊤ : Subgroup F).map F.subtype := by rw [hSFsupZF]
      _ = F := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hFGdecomp : SFG ⊔ Z = F.map M.subtype := by
    calc
      SFG ⊔ Z = (SFM ⊔ ZM).map M.subtype := by
        simp only [SFG, Z, Subgroup.map_sup]
      _ = F.map M.subtype := by rw [hFMdecomp]

  have hYleM : Y ≤ M := by
    dsimp [Y]
    exact inf_le_right.trans (Subgroup.map_subtype_le
      (_root_.commutator M))
  have hYK : Y ≤ K :=
    inf_le_left.trans
      (centralizerWithin_le_left K (sigmaCore M))
  have hYcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card Y) :=
    hKsigma'.of_dvd (Subgroup.card_dvd_of_le hYK)
  have hYcentSigma :
      Y ≤ Subgroup.centralizer (sigmaCore M : Set G) :=
    inf_le_left.trans inf_le_right
  have hYcentSFG :
      Y ≤ Subgroup.centralizer (SFG : Set G) :=
    hYcentSigma.trans (Subgroup.centralizer_le hSFGleSigma)
  have hYcentZ : Y ≤ Subgroup.centralizer (Z : Set G) :=
    inf_le_right.trans hMderCentZ
  have hcommSFG : ⁅Y, SFG⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYcentSFG
  have hcommZ : ⁅Y, Z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYcentZ
  have hcommSup : ⁅Y, SFG ⊔ Z⁆ = ⊥ := by
    apply le_antisymm
    · exact commutator_sup_le_of_normal
        (N := (⊥ : Subgroup G)) hcommSFG.le hcommZ.le
    · exact bot_le
  have hYcentFG :
      Y ≤ Subgroup.centralizer (F.map M.subtype : Set G) := by
    rw [← hFGdecomp]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommSup
  let YM : Subgroup M := Y.subgroupOf M
  have hYMcentF : YM ≤ Subgroup.centralizer (F : Set M) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hYcentFG hy)
      (f : G) (Subgroup.mem_map_of_mem M.subtype hf)
  have hYMF : YM ≤ F := by
    simpa only [F] using
      hYMcentF.trans (centralizer_fittingCore_le (G := M))

  let YF : Subgroup F := YM.subgroupOf F
  have hYFcompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card YF) := by
    rw [natCard_subgroupOf_eq hYMF,
      natCard_subgroupOf_eq hYleM]
    exact hYcompl
  have hYFZF : YF ≤ ZF :=
    isPiNumber_le_normal_isHall
      (hNnormal := (show ZF.Normal from inferInstance))
      hZFHall hYFcompl
  have hYMZM : YM ≤ ZM := by
    calc
      YM = YF.map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hYMF).symm
      _ ≤ ZF.map F.subtype := Subgroup.map_mono hYFZF
      _ = ZM := rfl
  have hYZ : Y ≤ Z := by
    calc
      Y = YM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hYleM).symm
      _ ≤ ZM.map M.subtype := Subgroup.map_mono hYMZM
      _ = Z := rfl

  have hYcyclic : IsCyclic Y := Subgroup.isCyclic_of_le hYZ
  let eZM : ZM ≃* Z :=
    ZM.equivMapOfInjective M.subtype M.subtype_injective
  have hZMcyclic : IsCyclic ZM := eZM.isCyclic.mpr hZcyclic
  letI : IsCyclic ZM := hZMcyclic
  let YMZ : Subgroup ZM := YM.subgroupOf ZM
  letI : YMZ.Characteristic :=
    subgroup_characteristic_of_isCyclic_10_11 YMZ
  have hYMnormal : YM.Normal := by
    have hmapNormal : (YMZ.map ZM.subtype).Normal := by
      infer_instance
    simpa [YMZ,
      Subgroup.map_subgroupOf_eq_of_le hYMZM] using hmapNormal
  exact ⟨hYcyclic, by simpa [YM] using hYMnormal⟩

/-- `BGsection10.v: commG_sigma'_1Elem_cyclic`, Proposition 10.11(d). -/
theorem commG_sigma'_1Elem_cyclic
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime] {K P : Subgroup G}
    (hKM : K ≤ M)
    (hKsigma' : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K))
    (hpSigma' : p ∉ sigmaPrimes M)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hPMN : P ≤ M ⊓ Subgroup.normalizer (K : Set G))
    (hregP : centralizerWithin (sigmaCore M) P = ⊥)
    (hKp' : IsPiNumber ({p} : Set ℕ)ᶜ (Nat.card K))
    (hKab : IsMulCommutative K) :
    let K₀ := ⁅K, P⁆
    K₀ ≤ Subgroup.centralizer (sigmaCore M : Set G) ∧
      IsCyclic K₀ ∧ (K₀.subgroupOf M).Normal := by
  classical
  dsimp only
  let S : Subgroup G := sigmaCore M
  let K₀ : Subgroup G := ⁅K, P⁆
  change K₀ ≤ Subgroup.centralizer (S : Set G) ∧
    IsCyclic K₀ ∧ (K₀.subgroupOf M).Normal
  letI : IsMulCommutative K := hKab
  have hPM : P ≤ M := hPMN.trans inf_le_left
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) :=
    hPMN.trans inf_le_right
  have hSM : S ≤ M := by simpa [S] using sigmaCore_le M
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    dsimp [S]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hK₀K : K₀ ≤ K := by
    dsimp [K₀]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPnormK
  have hK₀M : K₀ ≤ M := hK₀K.trans hKM
  have hK₀sigma' :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K₀) :=
    hKsigma'.of_dvd (Subgroup.card_dvd_of_le hK₀K)
  have hK₀p' : IsPiNumber ({p} : Set ℕ)ᶜ (Nat.card K₀) :=
    hKp'.of_dvd (Subgroup.card_dvd_of_le hK₀K)
  have hSpi : IsPiNumber (sigmaPrimes M) (Nat.card S) := by
    simpa [S] using sigmaCore_isPiNumber M
  have hPpi : IsPiNumber ({p} : Set ℕ) (Nat.card P) :=
    hP.isPGroup.isPiNumber_natCard (Set.mem_singleton p)
  have hPsigma' : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card P) :=
    hP.isPGroup.isPiNumber_natCard hpSigma'
  have hcopKP : Nat.Coprime (Nat.card K) (Nat.card P) :=
    (hPpi.coprime_compl hKp').symm
  have hcopK₀P : Nat.Coprime (Nat.card K₀) (Nat.card P) :=
    hcopKP.coprime_dvd_left (Subgroup.card_dvd_of_le hK₀K)
  have hcopSP : Nat.Coprime (Nat.card S) (Nat.card P) :=
    hSpi.coprime_compl hPsigma'
  have hcopK₀S : Nat.Coprime (Nat.card K₀) (Nat.card S) :=
    (hSpi.coprime_compl hK₀sigma').symm
  have hdisK₀S : Disjoint K₀ S :=
    Subgroup.disjoint_of_coprime_natCard hcopK₀S
  have hcentK₀P : centralizerWithin K₀ P = ⊥ := by
    simpa [K₀] using
      centralizerWithin_commutator_eq_bot_of_coprime_abelian
        hPnormK hcopKP hKab
  have hPnormK₀ : P ≤ Subgroup.normalizer (K₀ : Set G) := by
    dsimp [K₀]
    exact Subgroup.normalizer_commutator_ge_right K P
  have hK₀normS : K₀ ≤ Subgroup.normalizer (S : Set G) :=
    hK₀M.trans hMnormS
  have hPnormS : P ≤ Subgroup.normalizer (S : Set G) :=
    hPM.trans hMnormS
  let L : Subgroup G := K₀ ⊔ S
  have hPnormL : P ≤ Subgroup.normalizer (L : Set G) := by
    dsimp [L]
    exact (le_inf hPnormK₀ hPnormS).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup K₀ S)
  have hLM : L ≤ M := sup_le hK₀M hSM
  have hLcard : Nat.card L = Nat.card K₀ * Nat.card S := by
    simpa [L] using
      natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        hdisK₀S hK₀normS
  have hcopLP : Nat.Coprime (Nat.card L) (Nat.card P) := by
    rw [hLcard]
    exact hcopK₀P.mul_left hcopSP
  have hdisLP : Disjoint L P :=
    Subgroup.disjoint_of_coprime_natCard hcopLP

  let SM : Subgroup M := S.subgroupOf M
  let K₀M : Subgroup M := K₀.subgroupOf M
  let PM : Subgroup M := P.subgroupOf M
  let LM : Subgroup M := K₀M ⊔ SM
  have hLMeq : LM = L.subgroupOf M := by
    dsimp [LM, L, K₀M, SM]
    exact (Subgroup.subgroupOf_sup hK₀M hSM).symm
  letI : SM.Normal := by
    simpa [SM, S] using sigmaCore_normal M
  have hPMnormK₀M :
      PM ≤ Subgroup.normalizer (K₀M : Set M) := by
    have hsub : PM ≤
        (Subgroup.normalizer (K₀ : Set G)).subgroupOf M := by
      intro x hx
      exact hPnormK₀ hx
    dsimp [PM, K₀M] at hsub ⊢
    rwa [Subgroup.subgroupOf_normalizer_eq hK₀M] at hsub
  have hdisK₀MSM : Disjoint K₀M SM := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [natCard_subgroupOf_eq hK₀M,
      natCard_subgroupOf_eq hSM]
    exact hcopK₀S
  have hcopSMPM : Nat.Coprime (Nat.card SM) (Nat.card PM) := by
    rw [natCard_subgroupOf_eq hSM,
      natCard_subgroupOf_eq hPM]
    exact hcopSP
  have hPMp : IsPGroup p PM := by
    dsimp [PM]
    exact hP.isPGroup.comap_subtype
  letI : Group.IsNilpotent PM := hPMp.isNilpotent
  letI : IsSolvable PM := by infer_instance
  let q : M →* M ⧸ SM := QuotientGroup.mk' SM
  have hSMmap : SM.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff SM).mpr
    simpa [q, QuotientGroup.ker_mk']
  have hLMmap : LM.map q = K₀M.map q := by
    dsimp [LM]
    rw [Subgroup.map_sup, hSMmap, sup_bot_eq]
  have hquotCent :
      centralizerWithin (K₀M.map q) (PM.map q) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    rcases hz.1 with ⟨k, hkK₀M, hkz⟩
    have hkCent :
        ((k : M) : G) ∈ centralizerWithin K₀ P := by
      refine ⟨hkK₀M, ?_⟩
      intro a haP
      let aM : M := ⟨a, hPM haP⟩
      have haPM : aM ∈ PM := haP
      have hcommQ := hz.2 (q aM)
        (Subgroup.mem_map_of_mem q haPM)
      have hqone : q ⁅aM, k⁆ = 1 := by
        rw [map_commutatorElement]
        apply commutatorElement_eq_one_iff_mul_comm.mpr
        simpa only [hkz] using hcommQ
      have hcommSM : ⁅aM, k⁆ ∈ SM :=
        (QuotientGroup.eq_one_iff (⁅aM, k⁆ : M)).mp hqone
      have hcommK₀M : ⁅aM, k⁆ ∈ K₀M :=
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          hPMnormK₀M)
          (Subgroup.commutator_mem_commutator haPM hkK₀M)
      have hcommOne : ⁅aM, k⁆ = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hdisK₀MSM]
        exact ⟨hcommK₀M, hcommSM⟩
      exact congrArg Subtype.val
        (commutatorElement_eq_one_iff_mul_comm.mp hcommOne)
    have hkbot : ((k : M) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hcentK₀P]
      exact hkCent
    have hkone : k = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp hkbot)
    apply Subgroup.mem_bot.mpr
    rw [← hkz, hkone, map_one]
  have hmapCent :=
    map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
      (N := SM) (Y := LM) (R := PM) le_sup_right hcopSMPM
  rw [hLMmap, hquotCent] at hmapCent
  have hcentLM : centralizerWithin LM PM = ⊥ := by
    have hker : centralizerWithin LM PM ≤ SM := by
      have hm := (Subgroup.map_eq_bot_iff
        (centralizerWithin LM PM)).mp hmapCent
      simpa [q, QuotientGroup.ker_mk'] using hm
    apply le_antisymm _ bot_le
    intro x hx
    have hxAmbient :
        ((x : M) : G) ∈ centralizerWithin S P := by
      refine ⟨hker hx, ?_⟩
      intro a haP
      let aM : M := ⟨a, hPM haP⟩
      have haPM : aM ∈ PM := haP
      exact congrArg Subtype.val (hx.2 aM haPM)
    have hxbot : ((x : M) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hregP]
      simpa [S] using hxAmbient
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (Subgroup.mem_bot.mp hxbot))

  let F₀ : Subgroup G := P ⊔ L
  let LF : Subgroup F₀ := L.subgroupOf F₀
  let PF : Subgroup F₀ := P.subgroupOf F₀
  have hF₀M : F₀ ≤ M := sup_le hPM hLM
  have hLFnormal : LF.Normal := by
    dsimp [LF, F₀]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hPnormL
  have hcomp : LF.IsComplement' PF := by
    simpa [LF, PF, F₀] using
      subgroupOf_sup_isComplement_10_11 hPnormL hdisLP
  have hPFprime : (Nat.card PF).Prime := by
    rw [natCard_subgroupOf_eq
      (show P ≤ F₀ from le_sup_left), hP.card_eq, pow_one]
    exact Fact.out
  have hsolF₀ : IsSolvable F₀ :=
    mFT_sol (sub_mmax_proper hM hF₀M)
  have hcentLF : centralizerWithin LF PF = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    let xM : M := ⟨((x : F₀) : G), hF₀M x.2⟩
    have hxLM : xM ∈ LM := by
      rw [hLMeq]
      exact hx.1
    have hxCent : xM ∈ centralizerWithin LM PM := by
      refine ⟨hxLM, ?_⟩
      intro aM haPM
      let aF : F₀ :=
        ⟨((aM : M) : G),
          (show P ≤ F₀ by
            dsimp [F₀]
            exact le_sup_left) haPM⟩
      have haPF : aF ∈ PF := haPM
      apply Subtype.ext
      exact congrArg (fun y : F₀ => (y : G))
        (hx.2 aF haPF)
    have hxbot : xM ∈ (⊥ : Subgroup M) := by
      rw [← hcentLM]
      exact hxCent
    have hxMOne : xM = 1 := Subgroup.mem_bot.mp hxbot
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun z : M ↦ (z : G)) hxMOne
  have hnilLF : Group.IsNilpotent LF :=
    Submission.OddOrder.BG.Section03.prime_Frobenius_sol_kernel_nil
      hcomp hLFnormal hsolF₀ hPFprime hcentLF
  let eLF : LF ≃* L :=
    Subgroup.subgroupOfEquivOfLe
      (show L ≤ F₀ from le_sup_right)
  have hnilL : Group.IsNilpotent L :=
    (Group.isNilpotent_congr eLF).mp hnilLF
  letI : Group.IsNilpotent L := hnilL

  let SL : Subgroup L := S.subgroupOf L
  let K₀L : Subgroup L := K₀.subgroupOf L
  have hcompSL : SL.IsComplement' K₀L := by
    simpa [SL, K₀L, L] using
      subgroupOf_sup_isComplement_10_11 hK₀normS hdisK₀S.symm
  have hSLnormal : SL.Normal := by
    dsimp [SL, L]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hK₀normS
  have hK₀LHall : IsHall (sigmaPrimes M)ᶜ K₀L := by
    constructor
    · rw [natCard_subgroupOf_eq
        (show K₀ ≤ L from le_sup_left)]
      exact hK₀sigma'
    · rw [hcompSL.index_eq_card]
      rw [natCard_subgroupOf_eq
        (show S ≤ L from le_sup_right)]
      simpa only [compl_compl] using hSpi
  have hK₀Lnormal : K₀L.Normal := by
    rw [hall_eq_piCore_of_isNilpotent_10_11 hK₀LHall]
    infer_instance
  have hcentral : K₀ ≤ Subgroup.centralizer (S : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    let kL : L := ⟨k,
      (show K₀ ≤ L by
        dsimp [L]
        exact le_sup_left) hk⟩
    let sL : L := ⟨s,
      (show S ≤ L by
        dsimp [L]
        exact le_sup_right) hs⟩
    have hkK₀L : kL ∈ K₀L := hk
    have hsSL : sL ∈ SL := hs
    have hc := Subgroup.commute_of_normal_of_disjoint
      K₀L SL hK₀Lnormal hSLnormal hcompSL.disjoint.symm
      kL sL hkK₀L hsSL
    exact congrArg Subtype.val hc.eq.symm

  let D : Subgroup G := (_root_.commutator M).map M.subtype
  let Y : Subgroup G := centralizerWithin K₀ S ⊓ D
  have hK₀D : K₀ ≤ D := by
    dsimp [D]
    rw [M.map_subtype_commutator]
    exact Subgroup.commutator_mono hKM hPM
  have hK₀Y : K₀ ≤ Y := by
    dsimp [Y]
    exact le_inf (le_inf le_rfl hcentral) hK₀D
  have hcycNormal :=
    sub'cent_sigma_cyclic hM hK₀M hK₀sigma'
  change IsCyclic Y ∧ (Y.subgroupOf M).Normal at hcycNormal
  rcases hcycNormal with ⟨hYcyc, hYnormal⟩
  have hK₀cyc : IsCyclic K₀ := by
    letI : IsCyclic Y := hYcyc
    exact Subgroup.isCyclic_of_le hK₀Y
  refine ⟨hcentral, hK₀cyc, ?_⟩
  have hYM : Y ≤ M :=
    (inf_le_left.trans
      (centralizerWithin_le_left K₀ S)).trans hK₀M
  let YM : Subgroup M := Y.subgroupOf M
  let K₀M' : Subgroup M := K₀.subgroupOf M
  have hK₀M'YM : K₀M' ≤ YM :=
    Subgroup.subgroupOf_mono M hK₀Y
  have hYMcyc : IsCyclic YM := by
    letI : IsCyclic Y := hYcyc
    let eYM : YM ≃* Y := Subgroup.subgroupOfEquivOfLe hYM
    exact isCyclic_of_injective eYM.toMonoidHom eYM.injective
  let K₀YM : Subgroup YM := K₀M'.subgroupOf YM
  have hchar : K₀YM.Characteristic := by
    letI : IsCyclic YM := hYMcyc
    exact subgroup_characteristic_of_isCyclic_10_11 K₀YM
  letI : YM.Normal := by simpa [YM] using hYnormal
  letI : K₀YM.Characteristic := hchar
  have hnormalMap : (K₀YM.map YM.subtype).Normal := by
    infer_instance
  change
    ((K₀M'.subgroupOf YM).map YM.subtype).Normal at hnormalMap
  rw [Subgroup.map_subgroupOf_eq_of_le hK₀M'YM] at hnormalMap
  exact hnormalMap

/-- The source's local assertion `sigmaMHnil`: a prime common to
`sigma(M)` and `sigma(H)` can be neither an `alpha(M)`-prime nor compatible
with nilpotence of the sigma core of `M`, unless `M` and `H` are conjugate. -/
private theorem common_sigma_prime_forces
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom)
    {p : ℕ} (hpM : p ∈ sigmaPrimes M) (hpH : p ∈ sigmaPrimes H) :
    p ∉ alphaPrimes M ∧ ¬ Group.IsNilpotent (sigmaCore M) := by
  classical
  letI : Fact p.Prime := ⟨hpM.1⟩
  let P : Sylow p M := Classical.choice Sylow.nonempty
  obtain ⟨S, hS⟩ := sigma_Sylow_G hM hpM P
  let Q : Sylow p H := Classical.choice Sylow.nonempty
  obtain ⟨T, hT⟩ := sigma_Sylow_G hH hpH Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  let e : G ≃* G := MulAut.conj g
  have hST : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
    change MulAut.conj g • (S : Subgroup G) = (T : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  let PG : Subgroup G := ambientSylow M P
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le _
  have hPGmap : PG.map e.toMonoidHom = ambientSylow H Q := by
    dsimp only [PG]
    rw [← hS, ← hT]
    exact hST
  constructor
  · intro hpAlpha
    have hRankPG : HasElementaryAbelianRankAtLeast p 3 PG := by
      simpa only [PG] using sylow_has_rank_three_of_mem_alpha hpAlpha P
    have hPGp : IsPGroup p PG := by
      dsimp [PG, ambientSylow]
      exact P.isPGroup'.map M.subtype
    have hPGuniq : PG ∈ minSimple_uniq_max_groups (G := G) :=
      rank3_Uniqueness (mFT_pgroup_proper PG hPGp)
        ⟨p, Fact.out, hRankPG⟩
    have hPGfamily :
        minSimple_max_groups_of (G := G) (PG : Set G) = {M} :=
      def_uniq_mmax hPGuniq hM hPGM
    have hPGmapH : PG.map e.toMonoidHom ≤ H := by
      rw [hPGmap]
      exact Subgroup.map_subtype_le _
    have htransport := def_uniq_mmaxJ e hPGfamily
    have hEq : H = M.map e.toMonoidHom :=
      eq_uniq_mmax htransport hH hPGmapH
    exact hnotconj g hEq
  · intro hnil
    let C : Subgroup M := (sigmaCore M).subgroupOf M
    have hPpi : IsPiNumber (sigmaPrimes M) (Nat.card P) :=
      P.isPGroup'.isPiNumber_natCard hpM
    have hPC : (P : Subgroup M) ≤ C := by
      apply isPiNumber_le_normal_isHall
        (hNnormal := by simpa [C] using sigmaCore_normal M)
        (hNHall := by simpa [C] using Msigma_Hall hM)
        hPpi
    letI : C.Normal := by
      simpa [C] using sigmaCore_normal M
    letI : Group.IsNilpotent (sigmaCore M) := hnil
    letI : Group.IsNilpotent C := by
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M)).symm
    let PC : Sylow p C := P.subtype hPC
    have hPCnormal : (PC : Subgroup C).Normal := by infer_instance
    letI : (PC : Subgroup C).Characteristic :=
      PC.characteristic_of_normal hPCnormal
    have hPnormal : (P : Subgroup M).Normal := by
      have hmapNormal : ((PC : Subgroup C).map C.subtype).Normal := by
        infer_instance
      simpa [PC, Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hPC] using hmapNormal
    have hPGnormal : (PG.subgroupOf M).Normal := by
      change ((((P : Subgroup M).map M.subtype).comap M.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      exact hPnormal
    have hPGne : PG ≠ ⊥ := by
      simpa [PG] using sigma_Sylow_neq_bot hM hpM P
    have hNormPG : Subgroup.normalizer (PG : Set G) = M :=
      mmax_normal hM hPGM hPGnormal hPGne
    have hMmapH : M.map e.toMonoidHom ≤ H := by
      calc
        M.map e.toMonoidHom =
            (Subgroup.normalizer (PG : Set G)).map e.toMonoidHom := by
              rw [hNormPG]
        _ = Subgroup.normalizer (PG.map e.toMonoidHom : Set G) :=
          Subgroup.map_equiv_normalizer_eq PG e
        _ = Subgroup.normalizer (ambientSylow H Q : Set G) := by
          rw [hPGmap]
        _ ≤ H := norm_sigma_Sylow hpH Q
    have hMmapMax :
        M.map e.toMonoidHom ∈ minSimple_max_groups (G := G) :=
      (mmaxJ M e).mpr hM
    have hEq : M.map e.toMonoidHom = H :=
      eq_mmax hMmapMax hH hMmapH
    exact hnotconj g hEq.symm

/-- `BGsection10.v: sigma_disjoint`, assertion (a), prime-set form. -/
theorem alphaPrimes_disjoint_sigmaPrimes
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom) :
    Disjoint (alphaPrimes M) (sigmaPrimes H) := by
  rw [Set.disjoint_left]
  intro p hpAlpha hpSigma
  exact (common_sigma_prime_forces hM hH hnotconj
    (alpha_sub_sigma hM hpAlpha) hpSigma).1 hpAlpha

/-- `BGsection10.v: sigma_disjoint`, assertion (a), subgroup form. -/
theorem alphaCore_inf_sigmaCore_eq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom) :
    alphaCore M ⊓ sigmaCore H = ⊥ := by
  apply Subgroup.inf_eq_bot_of_coprime
  apply Nat.coprime_of_dvd
  intro p hp hpAlphaCard hpSigmaCard
  have hpAlpha : p ∈ alphaPrimes M :=
    alphaCore_isPiNumber M hp hpAlphaCard
  have hpSigma : p ∈ sigmaPrimes H :=
    sigmaCore_isPiNumber H hp hpSigmaCard
  exact Set.disjoint_left.mp
    (alphaPrimes_disjoint_sigmaPrimes hM hH hnotconj) hpAlpha hpSigma

/-- `BGsection10.v: sigma_disjoint`, assertion (b), prime-set form. -/
theorem sigmaPrimes_disjoint_sigmaPrimes_of_nilpotent
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom)
    (hnil : Group.IsNilpotent (sigmaCore M)) :
    Disjoint (sigmaPrimes M) (sigmaPrimes H) := by
  rw [Set.disjoint_left]
  intro p hpM hpH
  exact (common_sigma_prime_forces hM hH hnotconj hpM hpH).2 hnil

/-- `BGsection10.v: sigma_disjoint` (Bender--Glauberman Lemma 10.12), in
the same three-part shape as the source theorem. -/
theorem sigma_disjoint
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom) :
    alphaCore M ⊓ sigmaCore H = ⊥ ∧
      Disjoint (alphaPrimes M) (sigmaPrimes H) ∧
      (Group.IsNilpotent (sigmaCore M) →
        sigmaCore M ⊓ sigmaCore H = ⊥ ∧
          Disjoint (sigmaPrimes M) (sigmaPrimes H)) := by
  refine ⟨alphaCore_inf_sigmaCore_eq_bot hM hH hnotconj,
    alphaPrimes_disjoint_sigmaPrimes hM hH hnotconj, ?_⟩
  intro hnil
  exact ⟨sigmaCore_inf_sigmaCore_eq_bot_of_nilpotent hM hH hnotconj hnil,
    sigmaPrimes_disjoint_sigmaPrimes_of_nilpotent hM hH hnotconj hnil⟩

end

end Submission.OddOrder.BG.Section10
