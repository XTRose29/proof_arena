import Submission.OddOrder.BG.Section15.Tau2P2TypeSignalizer

/-!
# Bender--Glauberman Section 15: the non-F-type signalizer base

This module proves Theorem 15.9 from `BGsection15.v`.
-/

namespace Submission.OddOrder.BG.Section15

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section11
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

private theorem hall_of_le_hall_of_hall_15_9
    {A B C : Subgroup G} {pi rho : Set ℕ}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (hA : IsHall pi (A.subgroupOf B))
    (hB : IsHall rho (B.subgroupOf C))
    (hpi : pi ⊆ rho) :
    IsHall pi (A.subgroupOf C) := by
  constructor
  · simpa only [MathlibSupport.natCard_subgroupOf_eq (hAB.trans hBC),
      MathlibSupport.natCard_subgroupOf_eq hAB] using
      hA.isPiNumber_card
  · rw [← Subgroup.relIndex_mul_index
      (show A.subgroupOf C ≤ B.subgroupOf C from fun _ hx ↦ hAB hx)]
    apply IsPiNumber.mul
    · rw [Subgroup.relIndex_subgroupOf (H := A) hBC]
      change IsPiNumber piᶜ (A.subgroupOf B).index
      exact hA.isPiNumber_index
    · exact hB.isPiNumber_index.mono
        (Set.compl_subset_compl.mpr hpi)

private theorem hall_complement_card_mul_eq_15_9
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsHall pi A) (hB : IsHall piᶜ B) :
    Nat.card B * Nat.card A = Nat.card K := by
  have hcopAB : Nat.Coprime (Nat.card A) (Nat.card B) :=
    hA.isPiNumber_card.coprime_compl hB.isPiNumber_card
  have hBindexPi : IsPiNumber pi B.index := by
    simpa only [compl_compl] using hB.isPiNumber_index
  have hcopIndex : Nat.Coprime B.index A.index :=
    hBindexPi.coprime_compl hA.isPiNumber_index
  have hAcard_dvd_Bindex : Nat.card A ∣ B.index := by
    apply hcopAB.dvd_of_dvd_mul_left
    rw [B.card_mul_index]
    exact A.card_subgroup_dvd_card
  have hBindex_dvd_Acard : B.index ∣ Nat.card A := by
    apply hcopIndex.dvd_of_dvd_mul_right
    rw [A.card_mul_index]
    exact B.index_dvd_card
  have hAcard : Nat.card A = B.index :=
    Nat.dvd_antisymm hAcard_dvd_Bindex hBindex_dvd_Acard
  rw [hAcard, Nat.mul_comm, B.index_mul_card]

private theorem isSylowSubgroupOf_of_hall_15_9
    {pi : Set ℕ} {p : ℕ} [Fact p.Prime]
    {R U M : Subgroup G}
    (hUM : U ≤ M)
    (hHall : IsHall pi (U.subgroupOf M))
    (hpPi : p ∈ pi)
    (hR : IsSylowSubgroupOf p R U) :
    IsSylowSubgroupOf p R M := by
  have hRp : IsPGroup p R := hR.isPGroup
  obtain ⟨P, hRP⟩ := hR
  have hRU : R ≤ U := by
    rw [hRP]
    exact Subgroup.map_subtype_le (P : Subgroup U)
  have hRM : R ≤ M := hRU.trans hUM
  have hRsubU : R.subgroupOf U = (P : Subgroup U) := by
    rw [hRP]
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective P
  have hpRindexU : ¬ p ∣ R.relIndex U := by
    change ¬ p ∣ (R.subgroupOf U).index
    rw [hRsubU]
    exact P.not_dvd_index
  have hpUindexM : ¬ p ∣ U.relIndex M := by
    change ¬ p ∣ (U.subgroupOf M).index
    intro hpIndex
    exact hHall.isPiNumber_index Fact.out hpIndex hpPi
  have hpRindexM : ¬ p ∣ R.relIndex M := by
    rw [← Subgroup.relIndex_mul_relIndex R U M hRU hUM]
    exact (Fact.out : p.Prime).not_dvd_mul hpRindexU hpUindexM
  let RM : Subgroup M := R.subgroupOf M
  have hRMp : IsPGroup p RM :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
  let S : Sylow p M := hRMp.toSylow hpRindexM
  have hSco : (S : Subgroup M) = RM :=
    IsPGroup.toSylow_coe hRMp hpRindexM
  refine ⟨S, ?_⟩
  rw [hSco, Subgroup.map_subgroupOf_eq_of_le hRM]

private theorem exists_elementaryAbelian_le_ambientSylow_15_9
    {H Q : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hQH : IsSylowSubgroupOf p Q H)
    (hRank : HasElementaryAbelianRankAtLeast p n H) :
    ∃ A : Subgroup G, A ≤ Q ∧ IsElementaryAbelianOfRank p n A := by
  classical
  rcases hQH with ⟨P, hQP⟩
  rcases hRank with ⟨A, hAH, hA⟩
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p n AH :=
    hA.subgroupOf hAH
  obtain ⟨R, hAHR⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H R P
  let B : Subgroup H := AH.map (MulAut.conj h).toMonoidHom
  have hRB :
      (R : Subgroup H).map (MulAut.conj h).toMonoidHom =
        (P : Subgroup H) := by
    change MulAut.conj h • (R : Subgroup H) = (P : Subgroup H)
    rw [← Sylow.coe_subgroup_smul, hh]
  have hBP : B ≤ (P : Subgroup H) :=
    (Subgroup.map_mono hAHR).trans_eq hRB
  let BG : Subgroup G := B.map H.subtype
  refine ⟨BG, ?_, ?_⟩
  · rw [hQP]
    exact Subgroup.map_mono hBP
  · exact
      (hAHrank.map_of_injective (MulAut.conj h).toMonoidHom
        (MulAut.conj h).injective).map_of_injective
          H.subtype H.subtype_injective

private theorem pSubgroups_centralize_of_nilpotent_15_9
    {H A B : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hAp : IsPGroup p A) (hBq : IsPGroup q B)
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hnil : Group.IsNilpotent H) :
    A ≤ Subgroup.centralizer (B : Set G) := by
  let AH : Subgroup H := A.subgroupOf H
  let BH : Subgroup H := B.subgroupOf H
  have hAHp : IsPGroup p AH :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  have hBHq : IsPGroup q BH :=
    hBq.of_equiv (Subgroup.subgroupOfEquivOfLe hBH).symm
  obtain ⟨S, hAHS⟩ := hAHp.exists_le_sylow
  obtain ⟨T, hBHT⟩ := hBHq.exists_le_sylow
  letI : Group.IsNilpotent H := hnil
  letI : (S : Subgroup H).Normal := by infer_instance
  letI : (T : Subgroup H).Normal := by infer_instance
  have hcop : Nat.Coprime (Nat.card (S : Subgroup H))
      (Nat.card (T : Subgroup H)) :=
    IsPGroup.coprime_card_of_ne p q hpq
      (S : Subgroup H) (T : Subgroup H) S.isPGroup' T.isPGroup'
  have hdis : Disjoint (S : Subgroup H) (T : Subgroup H) :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hcommBot :
      ⁅(S : Subgroup H), (T : Subgroup H)⁆ = (⊥ : Subgroup H) := by
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf
        (H₁ := (S : Subgroup H)) (H₂ := (T : Subgroup H))).trans
          hdis.le_bot
    · exact bot_le
  have hcentST : (S : Subgroup H) ≤
      Subgroup.centralizer ((T : Subgroup H) : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  let aH : H := ⟨a, hAH ha⟩
  let bH : H := ⟨b, hBH hb⟩
  have haS : aH ∈ (S : Subgroup H) :=
    hAHS (show aH ∈ AH from ha)
  have hbT : bH ∈ (T : Subgroup H) :=
    hBHT (show bH ∈ BH from hb)
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp (hcentST haS) bH hbT)

private theorem subgroup_le_normal_isHall_15_9
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

private theorem nilpotent_normal_le_fittingWithin_15_9
    {K H : Subgroup G} (hKH : K ≤ H)
    (hKnormal : (K.subgroupOf H).Normal)
    (hKnil : Group.IsNilpotent K) :
    K ≤ fittingWithin H := by
  let KH : Subgroup H := K.subgroupOf H
  let eKH : KH ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  letI : KH.Normal := hKnormal
  letI : Group.IsNilpotent KH :=
    Group.nilpotent_of_mulEquiv eKH.symm
  have hcore : KH ≤ fittingCore H :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono hcore

/-- If the signalizer base of `x` is not of type F, then it is of type P2;
the original sigma-maximal overgroup is of type F and has the required
cyclic Frobenius complement. -/
theorem nonFtype_signalizer_base
    {M : Subgroup G} {x : G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hx : x ∈ sigmaCore M)
    (hx1 : x ≠ 1)
    (hcent : ¬ elementCentralizer x ≤ M)
    (hnotF : elementNormalizer15 x ∉
      typeFMaximalSubgroups (G := G)) :
    NonFTypeSignalizerBaseConclusion M x := by
  classical
  let N : Subgroup G := elementNormalizer15 x
  have hell : sigmaLength x = 1 := Msigma_ell1 hM hx hx1
  have hMmem : M ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G) :=
    ⟨hM, Subgroup.zpowers_le.mpr hx⟩
  obtain ⟨y, hyCent, hyM⟩ := SetLike.not_le_iff_exists.mp hcent
  have hyComm : Commute y x :=
    (Subgroup.mem_centralizer_iff.mp hyCent x
      (Subgroup.mem_zpowers x)).symm
  have hconjugateSet :
      conjugateSet y (Subgroup.zpowers x : Set G) =
        (Subgroup.zpowers x : Set G) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwy : w * y = y * w :=
        Subgroup.mem_centralizer_iff.mp hyCent w hw
      have heq : y * w * y⁻¹ = w := by
        rw [← hwy]
        group
      simpa [conjugateSet, MulAut.conj_apply, heq] using hw
    · intro hz
      refine ⟨z, hz, ?_⟩
      have hzy : z * y = y * z :=
        Subgroup.mem_centralizer_iff.mp hyCent z hz
      change y * z * y⁻¹ = z
      rw [← hzy]
      group
  let My : Subgroup G := M.map (MulAut.conj y).toMonoidHom
  have hMymem : My ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G) := by
    change M.map (MulAut.conj y).toMonoidHom ∈
      sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)
    rw [← hconjugateSet]
    exact (sigma_mmaxJ M (Subgroup.zpowers x : Set G) y).mpr hMmem
  have hMyne : M ≠ My := by
    intro hEq
    apply hyM
    rw [← norm_mmax hM]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    simpa [My] using hEq.symm
  have hlarge : 1 <
      (sigmaMaximalOvergroups
        (Subgroup.zpowers x : Set G)).ncard :=
    (Set.one_lt_ncard).2 ⟨M, hMmem, My, hMymem, hMyne⟩
  have hLarge := (FT_signalizer_context hell).large hlarge
  have hNmax : N ∈ minSimple_max_groups (G := G) := by
    simpa [N] using hLarge.base_maximal
  have hNP2 : N ∈ typeP2MaximalSubgroups (G := G) := by
    change ftSignalizerBase x ∈ typeP2MaximalSubgroups (G := G)
    rcases hLarge.base_type with hNF | hNP2
    · exact (hnotF hNF).elim
    · exact hNP2
  have hLocal := hLarge.overgroup_context hMmem
  let C : Subgroup G := M ⊓ N
  have hCM : C ≤ M := inf_le_left
  have hCN : C ≤ N := inf_le_right
  letI : IsSolvable N := mmax_sol hNmax
  have hCsol : IsSolvable C :=
    isSolvable_of_injective (Subgroup.inclusion hCN)
      (Subgroup.inclusion_injective hCN)
  have hHallCN :
      IsHall (sigmaPrimes N)ᶜ (C.subgroupOf N) := by
    simpa [C, N] using hLocal.hall_intersection
  obtain ⟨K, hKC, hHallKC⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      hCsol (kappaPrimes N)
  have hKN : K ≤ N := hKC.trans hCN
  have hKM : K ≤ M := hKC.trans hCM
  have hHallKN : IsHall (kappaPrimes N) (K.subgroupOf N) :=
    hall_of_le_hall_of_hall_15_9 hKC hCN hHallKC
      hHallCN
      (kappa_sigma' N)
  obtain ⟨U, hUC, hHallUC⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      hCsol (sigmaKappaPrimes N)ᶜ
  have hUN : U ≤ N := hUC.trans hCN
  have hUM : U ≤ M := hUC.trans hCM
  have hHallUN :
      IsHall (sigmaKappaPrimes N)ᶜ (U.subgroupOf N) := by
    apply hall_of_le_hall_of_hall_15_9 hUC hCN hHallUC
      hHallCN
    intro p hp hpSigma
    exact hp (Or.inl hpSigma)
  have hCpi : IsPiNumber (sigmaPrimes N)ᶜ (Nat.card C) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hCN] using
      hHallCN.isPiNumber_card
  have hHallKSK :
      IsHall (sigmaKappaPrimes N) (K.subgroupOf C) := by
    constructor
    · exact hHallKC.isPiNumber_card.mono fun _ hp ↦ Or.inr hp
    · intro p hpPrime hpIndex hpSK
      rcases hpSK with hpSigma | hpKappa
      · exact hCpi hpPrime
          (hpIndex.trans (K.subgroupOf C).index_dvd_card) hpSigma
      · exact hHallKC.isPiNumber_index hpPrime hpIndex hpKappa
  have hprod : (C : Set G) = (U : Set G) * (K : Set G) := by
    let UC : Subgroup C := U.subgroupOf C
    let KC : Subgroup C := K.subgroupOf C
    have hcopCard : (Nat.card UC).Coprime (Nat.card KC) := by
      simpa [UC, KC] using
        (hHallKSK.isPiNumber_card.coprime_compl
          hHallUC.isPiNumber_card).symm
    have hdis : Disjoint UC KC :=
      Subgroup.disjoint_of_coprime_natCard hcopCard
    have hcompC : UC.IsComplement' KC :=
      Subgroup.isComplement'_of_card_mul_and_disjoint
        (by simpa [UC, KC] using
          hall_complement_card_mul_eq_15_9 hHallKSK hHallUC) hdis
    apply Set.Subset.antisymm
    · intro e he
      obtain ⟨⟨u, k⟩, huk⟩ := hcompC.2 ⟨e, he⟩
      refine ⟨(u : C), u.property, (k : C), k.property, ?_⟩
      exact congrArg Subtype.val huk
    · rintro _ ⟨u, hu, k, hk, rfl⟩
      exact C.mul_mem (hUC hu) (hKC hk)
  have hCompl : KappaComplement N U K :=
    { U_le_M := hUN
      hall_U := hHallUN
      K_le_M := hKN
      hall_K := hHallKN
      product_is_group := ⟨C, hprod⟩ }
  have hPstruct := Ptype_structure hNP2.1 hKN hHallKN
  have hKprime : (Nat.card K).Prime :=
    (hPstruct.typeP2 hNP2).card_K_prime
  have hKne : K ≠ ⊥ := by
    intro hKbot
    exact hKprime.ne_one (Subgroup.card_eq_one.mpr hKbot)
  obtain ⟨r, hrOrder⟩ := exists_prime_mem_primeSupport_orderOf hx1
  letI : Fact r.Prime := ⟨hrOrder.1⟩
  have hrTauN : r ∈ tau2Primes N := by
    simpa [N] using hLarge.x_tau2 hrOrder.1 hrOrder.2
  have hrSigmaM : r ∈ sigmaPrimes M :=
    hLocal.tau2_subset_sigma hrTauN
  have hrNotKappaN : r ∉ kappaPrimes N := by
    intro hrKappa
    rcases kappa_tau13 hrKappa with hrTau1 | hrTau3
    · exact (tau2'1 N hrTau1) hrTauN
    · exact (tau3'2 N hrTauN) hrTau3
  have hrSKcompl : r ∈ (sigmaKappaPrimes N)ᶜ := by
    intro hrSK
    rcases hrSK with hrSigma | hrKappa
    · exact hrTauN.2.1 hrSigma
    · exact hrNotKappaN hrKappa
  let S : Sylow r U := Classical.choice Sylow.nonempty
  let R : Subgroup G := ambientSylow U S
  have hRU : R ≤ U := Subgroup.map_subtype_le (S : Subgroup U)
  have hR_U : IsSylowSubgroupOf r R U := ⟨S, rfl⟩
  have hR_N : IsSylowSubgroupOf r R N :=
    isSylowSubgroupOf_of_hall_15_9 hUN hHallUN hrSKcompl hR_U
  obtain ⟨A, hAR, hArank⟩ :=
    exists_elementaryAbelian_le_ambientSylow_15_9 hR_N hrTauN.2.2.1
  have hRnoncyclic : ¬ IsCyclic R := by
    intro hRcyclic
    letI : IsCyclic R := hRcyclic
    exact hArank.not_isCyclic hrOrder.1 (Subgroup.isCyclic_of_le hAR)
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hRnoncyclic
    rw [hRbot]
    infer_instance
  have hRM : R ≤ M := hRU.trans hUM
  have hNRM : Subgroup.normalizer (R : Set G) ≤ M :=
    norm_noncyclic_sigma hM hrSigmaM hR_U.isPGroup hRM hRnoncyclic
  obtain ⟨L, hLmax, hCKL⟩ :=
    mmax_exists (Subgroup.centralizer (K : Set G))
      (mFT_cent_proper K hKne)
  have hLmem : L ∈ minSimple_max_groups_of (G := G)
      (Subgroup.centralizer (K : Set G) : Set G) := ⟨hLmax, hCKL⟩
  have hP2signal := P2type_signalizer hNP2 hCompl hLmem hR_U
    (show M ∈ minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (R : Set G) : Set G) from ⟨hM, hNRM⟩)
  have hMF : M ∈ typeFMaximalSubgroups (G := G) := hP2signal.1
  have hSigmaNil : Group.IsNilpotent (sigmaCore M) :=
    notP1type_Msigma_nil (Or.inl hMF)
  let q := Nat.card K
  letI : Fact q.Prime := ⟨by simpa [q] using hKprime⟩
  have hKq : IsPGroup q K :=
    (isElementaryAbelianOfRank_one_of_card_eq_prime
      (p := q) (S := K) (by simp [q])).isPGroup
  have hqKappaN : q ∈ kappaPrimes N := by
    apply hHallKN.isPiNumber_card (Fact.out : q.Prime)
    simpa [q, MathlibSupport.natCard_subgroupOf_eq hKN]
  have hrq : r ≠ q := by
    intro hrq
    exact hrNotKappaN (hrq ▸ hqKappaN)
  have hRr : IsPGroup r R := hR_U.isPGroup
  have hRMs : R ≤ sigmaCore M := by
    let RM : Subgroup M := R.subgroupOf M
    let SM : Subgroup M := (sigmaCore M).subgroupOf M
    have hRMpi : IsPiNumber (sigmaPrimes M) (Nat.card RM) := by
      simpa [RM, MathlibSupport.natCard_subgroupOf_eq hRM] using
        hRr.isPiNumber_natCard hrSigmaM
    have hle : RM ≤ SM :=
      subgroup_le_normal_isHall_15_9
        (show SM.Normal from by simpa [SM] using sigmaCore_normal M)
        (by simpa [SM] using Msigma_Hall hM) hRMpi
    intro z hz
    let zM : M := ⟨z, hRM hz⟩
    exact hle (show zM ∈ RM from hz)
  have hKnotMs : ¬ K ≤ sigmaCore M := by
    intro hKMs
    have hRcentK : R ≤ Subgroup.centralizer (K : Set G) :=
      pSubgroups_centralize_of_nilpotent_15_9 hrq hRr hKq
        hRMs hKMs hSigmaNil
    have hctx := kappa_compl_context hNmax hCompl
    obtain ⟨kK, hkK1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
    have hRbot : R ≤ ⊥ := by
      intro z hzR
      let zU : U := ⟨z, hRU hzR⟩
      have hcomm : (kK : G) * z = z * kK := by
        exact (Subgroup.mem_centralizer_iff.mp
          (hRcentK hzR) (kK : G) kK.property)
      have hfix : (kK : G) * z * (kK : G)⁻¹ = z := by
        rw [hcomm]
        simp
      have hz1 : zU = 1 := hctx.U_K_semiregular kK hkK1 zU hfix
      exact congrArg (fun u : U ↦ (u : G)) hz1
    exact hRne (le_bot_iff.mp hRbot)
  have hqNotSigmaM : q ∉ sigmaPrimes M := by
    intro hqSigma
    apply hKnotMs
    let KM : Subgroup M := K.subgroupOf M
    let SM : Subgroup M := (sigmaCore M).subgroupOf M
    have hKMpi : IsPiNumber (sigmaPrimes M) (Nat.card KM) := by
      simpa [KM, MathlibSupport.natCard_subgroupOf_eq hKM] using
        hKq.isPiNumber_natCard hqSigma
    have hle : KM ≤ SM :=
      subgroup_le_normal_isHall_15_9
        (show SM.Normal from by simpa [SM] using sigmaCore_normal M)
        (by simpa [SM] using Msigma_Hall hM) hKMpi
    intro z hz
    let zM : M := ⟨z, hKM hz⟩
    exact hle (show zM ∈ KM from hz)
  have hKsigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) :=
    hKq.isPiNumber_natCard hqNotSigmaM
  obtain ⟨E, hKE, hEM, hHallE⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hKM (mmax_sol hM) (sigmaPrimes M)ᶜ hKsigmaCompl
  obtain ⟨⟨E₁, hE₁E, hHallE₁⟩, ⟨E₃, hE₃E, hHallE₃⟩⟩ :=
    ex_tau13_compl hEM hHallE
  obtain ⟨E₂, hE₂E, hHallE₂, hComplE⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  have hE₂bot : E₂ = ⊥ := by
    by_contra hE₂ne
    have hnotTauM :
        ¬ IsPiNumber (tau2Primes M)ᶜ (Nat.card M) := by
      intro hTauM
      have hE₂compl :
          IsPiNumber (tau2Primes M)ᶜ (Nat.card E₂) :=
        hTauM.of_dvd (Subgroup.card_dvd_of_le (hE₂E.trans hEM))
      have hE₂pi : IsPiNumber (tau2Primes M) (Nat.card E₂) := by
        simpa [MathlibSupport.natCard_subgroupOf_eq hE₂E] using
          hHallE₂.isPiNumber_card
      have hcardOne : Nat.card E₂ = 1 := by
        exact Nat.eq_one_of_dvd_coprimes
          (hE₂pi.coprime_compl hE₂compl) dvd_rfl dvd_rfl
      exact hE₂ne (Subgroup.card_eq_one.mp hcardOne)
    have hTauN := (tau2_P2type_signalizer hNP2 hCompl hLmem hR_U
      (show M ∈ minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (R : Set G) : Set G) from ⟨hM, hNRM⟩)
      hnotTauM).M_tau2_complement
    have hrR : r ∣ Nat.card R :=
      hRr.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hRne (Subgroup.card_eq_one.mp hcard))
    have hrN : r ∣ Nat.card N :=
      hrR.trans (Subgroup.card_dvd_of_le (hRU.trans hUN))
    exact hTauN hrOrder.1 hrN hrTauN
  have hSigmaFit : sigmaCore M ≤ fittingWithin M :=
    nilpotent_normal_le_fittingWithin_15_9 (sigmaCore_le M)
      (sigmaCore_normal M) hSigmaNil
  have hyFix : y * x * y⁻¹ = x := by
    rw [hyComm.eq]
    simp
  have hxMeet : x ∈ nonTIFittingIntersection M y := by
    refine ⟨hSigmaFit hx, ?_⟩
    exact ⟨x, hSigmaFit hx, by simpa [conjugateSubgroup15,
      MulAut.conj_apply] using hyFix⟩
  have hMeetNe : nonTIFittingIntersection M y ≠ ⊥ := by
    intro hbot
    exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxMeet))
  have hE₃bot : E₃ = ⊥ := by
    have hs := (nonTI_Fitting_structure hM hyM hMeetNe).sigma_complement_structure hComplE
    exact (Classical.choice hs).E₃_eq_bot
  have hComplCtx := sigma_compl_context hM hComplE
  have hEeqE₁ : E = E₁ := by
    have htop : E₁.subgroupOf E = ⊤ := by
      simpa [hE₂bot, hE₃bot] using
        hComplCtx.E₃₂_E₁_sdprod.2.2.2.sup_eq_top
    exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hE₁E
  have hEcyclic : IsCyclic E := by
    rw [hEeqE₁]
    exact hComplCtx.E₁_cyclic
  have hSigmaNe : sigmaCore M ≠ ⊥ := Msigma_neq1 hM
  have hEne : E ≠ ⊥ := fun hEbot ↦ hKne (by
    apply le_bot_iff.mp
    simpa [hEbot] using hKE)
  have hsd := sdprod_sigma hM hEM hHallE
  have hFrob : IsFrobeniusDecomposition
      ((sigmaCore M).subgroupOf M) (E.subgroupOf M) := by
    refine
      { isComplement := hsd.2.2.2
        kernel_normal := hsd.2.2.1
        kernel_ne_bot := ?_
        complement_ne_bot := ?_
        fixedPointFree := ?_ }
    · intro hbot
      apply hSigmaNe
      have hdis : Disjoint (sigmaCore M) M :=
        Subgroup.subgroupOf_eq_bot.mp hbot
      have hinf : sigmaCore M ⊓ M = ⊥ := disjoint_iff.mp hdis
      simpa [inf_eq_left.mpr (sigmaCore_le M)] using hinf
    · intro hbot
      apply hEne
      have hdis : Disjoint E M := Subgroup.subgroupOf_eq_bot.mp hbot
      have hinf : E ⊓ M = ⊥ := disjoint_iff.mp hdis
      simpa [inf_eq_left.mpr hEM] using hinf
    · intro z hz1 k hkfix
      by_contra hk1
      have hzE : (z : M) ∈ E.subgroupOf M := z.property
      have hzE₁ : (z : G) ∈ E₁ := by
        rw [← hEeqE₁]
        exact hzE
      have hzG1 : (z : G) ≠ 1 := by
        intro hz
        apply hz1
        apply Subtype.ext
        apply Subtype.ext
        exact hz
      obtain ⟨s, hsOrder⟩ :=
        exists_prime_mem_primeSupport_orderOf hzG1
      letI : Fact s.Prime := ⟨hsOrder.1⟩
      have hsTau1 : s ∈ tau1Primes M := by
        apply hHallE₁.isPiNumber_card hsOrder.1
        have hsE₁ : s ∣ Nat.card E₁ :=
          hsOrder.2.trans (E₁.orderOf_dvd_natCard hzE₁)
        simpa only [MathlibSupport.natCard_subgroupOf_eq hE₁E] using hsE₁
      have hzM : (z : G) ∈ M := hEM hzE
      have hsM : s ∣ Nat.card M :=
        hsOrder.2.trans (M.orderOf_dvd_natCard hzM)
      have hsNotKappa : s ∉ kappaPrimes M :=
        hMF.2 hsOrder.1 hsM
      obtain ⟨Z, hZline, hZz⟩ :=
        exists_rankOneLineIn_zpowers hsOrder
      have hZM : Z ≤ M :=
        hZz.trans (Subgroup.zpowers_le.mpr (hE₁E.trans hEM hzE₁))
      have hfixG : (z : G) * (k : G) * (z : G)⁻¹ = (k : G) := by
        exact congrArg (fun a : M ↦ (a : G)) hkfix
      have hcommzk : Commute (z : G) (k : G) := by
        rw [Commute]
        calc
          (z : G) * (k : G) =
              ((z : G) * (k : G) * (z : G)⁻¹) * (z : G) := by group
          _ = (k : G) * (z : G) := by rw [hfixG]
      have hkCentZ : (k : G) ∈ centralizerWithin (sigmaCore M) Z := by
        refine ⟨k.property, ?_⟩
        intro a haZ
        have haPow : a ∈ Subgroup.zpowers (z : G) := hZz haZ
        rcases haPow with ⟨n, rfl⟩
        exact (hcommzk.zpow_left n).eq
      have hcentNe : centralizerWithin (sigmaCore M) Z ≠ ⊥ := by
        intro hbot
        apply hk1
        apply Subtype.ext
        apply Subtype.ext
        have hkbot : (k : G) ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact hkCentZ
        exact Subgroup.mem_bot.mp hkbot
      exact hsNotKappa ⟨Or.inl hsTau1, Z, ⟨hZM, hZline⟩, hcentNe⟩
  exact ⟨
    { M_typeF := hMF
      normalizer_typeP2 := by simpa [N] using hNP2
      complement := E
      complement_le := hEM
      complement_hall := hHallE
      complement_cyclic := hEcyclic
      frobenius := hFrob }⟩

end

end Submission.OddOrder.BG.Section15
