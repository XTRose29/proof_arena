import Submission.OddOrder.BG.Section01.PLengthOneFunctorial
import Submission.OddOrder.BG.Section03.OddSemidirectZGroupPLength
import Submission.OddOrder.BG.Section04.RankTwoCoprimeCommutatorCentralProduct
import Submission.OddOrder.BG.Section10.SigmaNormalizerRankTwo
import Submission.OddOrder.BG.Section10.SigmaTransitivity
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.PElementCyclic
import Submission.OddOrder.MathlibSupport.SolvablePrimeComplement

/-!
# Elementary control at a sigma-complement prime

This file ports the block of `BGsection10.v` from Lemma 10.5, part 2,
through Corollary 10.7(e).  The statements use subgroup maps for the source
notation `Q :^ x`; thus that conjugate is
`Q.map (MulAut.conj x⁻¹).toMonoidHom`.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

universe u

private theorem omegaOneCenterAmbient_ne_bot_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) :
    omegaOneCenterAmbient p P ≠ ⊥ := by
  letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne
  let Z : Subgroup P := Subgroup.center P
  have hZne : Z ≠ ⊥ := by
    letI : Group.IsNilpotent P := hPp.isNilpotent
    exact Group.IsNilpotent.center_ne_bot P
  have hZp : IsPGroup p Z := hPp.to_subgroup Z
  have hZcard : Nat.card Z ≠ 1 :=
    (Z.one_lt_card_iff_ne_bot.mpr hZne).ne'
  have hOmegaNe : omegaOne p Z ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hZp hZcard
  have hCenterOmegaNe :
      Submission.OddOrder.BG.Section05.omegaOneCenter p P ≠ ⊥ := by
    dsimp [Submission.OddOrder.BG.Section05.omegaOneCenter, Z]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (omegaOne p (Subgroup.center P))
      (Subgroup.center P).subtype_injective)).mpr hOmegaNe
  dsimp [omegaOneCenterAmbient]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
    (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
    P.subtype_injective)).mpr hCenterOmegaNe

private theorem isPGroup_le_normal_isHall
    {K : Type*} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} [Fact p.Prime]
    {P H : Subgroup K} (hp : p ∈ pi)
    (hPp : IsPGroup p P) (hHnormal : H.Normal)
    (hHall : IsHall pi H) : P ≤ H := by
  letI : H.Normal := hHnormal
  let q : K →* K ⧸ H := QuotientGroup.mk' H
  have hmapPp : IsPGroup p (P.map q) := hPp.map q
  have hmapCard : Nat.card (P.map q) = 1 := by
    rcases hmapPp.card_eq_or_dvd with hOne | hpMap
    · exact hOne
    · exfalso
      have hpQuot : p ∣ Nat.card (K ⧸ H) :=
        hpMap.trans (P.map q).card_subgroup_dvd_card
      have hpIndex : p ∣ H.index := by
        simpa only [H.index_eq_card] using hpQuot
      exact hHall.isPiNumber_index Fact.out hpIndex hp
  have hmapBot : P.map q = ⊥ := Subgroup.card_eq_one.mp hmapCard
  have hker : P ≤ q.ker := (Subgroup.map_eq_bot_iff P).mp hmapBot
  simpa [q, QuotientGroup.ker_mk'] using hker

private theorem pPrimeCore_isPrimeComplement_of_mulEquiv
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B)
    (h : IsPrimeComplement p (pPrimeCore p A)) :
    IsPrimeComplement p (pPrimeCore p B) := by
  rw [← map_pPrimeCore_eq_mulEquiv (p := p) e]
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h.1
  · obtain ⟨n, hn⟩ := h.2
    exact ⟨n,
      (Subgroup.index_map_equiv (pPrimeCore p A) e).trans hn⟩

private theorem map_conj_map_conj
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_inv_map_conj
    {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj]
  simpa only [inv_mul_cancel] using map_conj_one H

private theorem map_conj_eq_self_of_centralizer
    {G : Type*} [Group G] (H : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.centralizer (H : Set G)) :
    H.map (MulAut.conj c).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer (H : Set G) hc)

/-! ### Bender--Glauberman Lemma 10.5, part 2 -/

/-- `BGsection10.v: sigma'1Elem_sub_p2Elem`.

A rank-one elementary-abelian subgroup whose normalizer is contained in a
maximal subgroup at a sigma-complement prime extends to rank two. -/
theorem sigma'1Elem_sub_p2Elem
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M X : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (hX : IsElementaryAbelianOfRank p 1 X)
    (hNXM : Subgroup.normalizer (X : Set G) ≤ M) :
    ∃ A : Subgroup G, IsElementaryAbelianOfRank p 2 A ∧ X ≤ A := by
  classical
  have hXM : X ≤ M := Subgroup.le_normalizer.trans hNXM
  let XM : Subgroup M := X.subgroupOf M
  have hXMp : IsPGroup p XM := hX.isPGroup.comap_subtype
  obtain ⟨P, hXMP⟩ := hXMp.exists_le_sylow
  let PG : Subgroup G := ambientSylow M P
  have hXPG : X ≤ PG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXMP
  have hPGp : IsPGroup p PG := P.isPGroup'.map M.subtype
  let T : Subgroup G := omegaOneCenterAmbient p PG
  have hTchar :
      Subgroup.normalizer (PG : Set G) ≤
        Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg t ht
    let R : Subgroup PG :=
      Submission.OddOrder.BG.Section05.omegaOneCenter p PG
    haveI : R.Characteristic := by
      dsimp [R]
      infer_instance
    exact characteristic_map_subtype_invariant_under_normalizer
      PG (Subgroup.normalizer (PG : Set G)) R le_rfl g hg t ht
  have hPGne : PG ≠ ⊥ := by
    intro hbot
    have hXbot : X = ⊥ := le_bot_iff.mp (hXPG.trans_eq hbot)
    exact hX.ne_bot hXbot
  have hTne : T ≠ ⊥ := by
    simpa [T] using omegaOneCenterAmbient_ne_bot_of_isPGroup hPGp hPGne
  have hTnotleX : ¬ T ≤ X := by
    intro hTX
    have hTcardDvd : Nat.card T ∣ p := by
      simpa [hX.card_eq] using Subgroup.card_dvd_of_le hTX
    have hTcard : Nat.card T = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hTcardDvd).resolve_left
        (fun hcard ↦ hTne (Subgroup.card_eq_one.mp hcard))
    have hTXeq : T = X :=
      Subgroup.eq_of_le_of_card_ge hTX (by simpa [hX.card_eq, hTcard])
    have hNormPGX : Subgroup.normalizer (PG : Set G) ≤
        Subgroup.normalizer (X : Set G) := by simpa [hTXeq] using hTchar
    exact hpSigma ⟨Fact.out, P, by simpa [PG] using hNormPGX.trans hNXM⟩
  obtain ⟨t, htT, htX⟩ := Set.not_subset.mp hTnotleX
  have htPG : t ∈ PG :=
    (omegaOneCenterAmbient_le_centerWithin p PG htT).1
  have htne : t ≠ 1 := fun ht ↦ htX (ht ▸ X.one_mem)
  have htpow : t ^ p = 1 := by
    rcases htT with ⟨z, hz, hzt⟩
    subst t
    have hzpow :=
      Submission.OddOrder.BG.Section05.omegaOneCenter_pow_eq_one
        (G := PG) p ⟨z, hz⟩
    exact congrArg Subtype.val (congrArg Subtype.val hzpow)
  have htorder : orderOf t = p := by
    have hdvd : orderOf t ∣ p := orderOf_dvd_of_pow_eq_one htpow
    exact ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left
      (by simpa [orderOf_eq_one_iff] using htne)
  let XP : Subgroup PG := X.subgroupOf PG
  let tP : PG := ⟨t, htPG⟩
  let ZP : Subgroup PG := Subgroup.zpowers tP
  have hXPcard : Nat.card XP = p := by
    calc
      Nat.card XP = Nat.card X :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hXPG
      _ = p := by simpa using hX.card_eq
  have hZPcard : Nat.card ZP = p := by
    calc
      Nat.card ZP = Nat.card (ZP.map PG.subtype) :=
        (Subgroup.card_map_of_injective PG.subtype_injective).symm
      _ = Nat.card (Subgroup.zpowers t) := by
        congr 1
        simpa [ZP, tP] using MonoidHom.map_zpowers PG.subtype tP
      _ = p := by rw [Nat.card_zpowers, htorder]
  have hXP : IsElementaryAbelianOfRank p 1 XP :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXPcard
  have hZP : IsElementaryAbelianOfRank p 1 ZP :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hZPcard
  have htCenter : tP ∈ Subgroup.center PG := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (mem_centerWithin.mp
      (omegaOneCenterAmbient_le_centerWithin p PG htT)).2 y y.property
  have hZPCenter : ZP ≤ Subgroup.center PG :=
    Subgroup.zpowers_le.mpr htCenter
  have hdis : Disjoint XP ZP := by
    rw [disjoint_iff]
    by_contra hne
    have hcardNe : Nat.card (XP ⊓ ZP : Subgroup PG) ≠ 1 :=
      fun hcard ↦ hne (Subgroup.card_eq_one.mp hcard)
    have hdiv : Nat.card (XP ⊓ ZP : Subgroup PG) ∣ p := by
      simpa [hZPcard] using
        Subgroup.card_dvd_of_le (inf_le_right : XP ⊓ ZP ≤ ZP)
    have hcard : Nat.card (XP ⊓ ZP : Subgroup PG) = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv).resolve_left hcardNe
    have hinf : XP ⊓ ZP = ZP :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard, hZPcard])
    have htXP : tP ∈ XP := by
      have : tP ∈ XP ⊓ ZP := by
        rw [hinf]
        exact Subgroup.mem_zpowers tP
      exact this.1
    exact htX (show t ∈ X from htXP)
  have hcomm : ∀ x ∈ XP, ∀ z ∈ ZP, Commute x z := by
    intro x _ z hz
    exact Subgroup.mem_center_iff.mp (hZPCenter hz) x
  let AP : Subgroup PG := XP ⊔ ZP
  have hAP : IsElementaryAbelianOfRank p 2 AP := by
    simpa [AP] using
      isElementaryAbelianOfRank_sup_of_disjoint_of_commute
        hPGp hXP hZP hdis hcomm
  let A : Subgroup G := AP.map PG.subtype
  have hA : IsElementaryAbelianOfRank p 2 A := by
    dsimp [A]
    exact hAP.map_of_injective PG.subtype PG.subtype_injective
  refine ⟨A, hA, ?_⟩
  have hXPmap : XP.map PG.subtype = X := by
    simpa [XP] using Subgroup.map_subgroupOf_eq_of_le hXPG
  rw [← hXPmap]
  exact Subgroup.map_mono (show XP ≤ AP by exact le_sup_left)

/-! ### Bender--Glauberman Theorem 10.6 -/

private theorem isPLengthOne_of_no_rank_three
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (hsol : IsSolvable H) (hodd : Odd (Nat.card H))
    (hRank : ¬ ∃ E : Subgroup H,
      IsElementaryAbelianOfRank p 3 E) :
    IsPLengthOne p H := by
  classical
  have hquotPrime : IsPPrimeSubgroup p
      (⊤ : Subgroup (H ⧸ pPrimePCore p H)) :=
    (rank2_der1_complement hsol hodd hRank).2.2
  have hnotFinal : ¬ p ∣ Nat.card (H ⧸ pPrimePCore p H) := by
    rw [IsPPrimeSubgroup, Subgroup.card_top] at hquotPrime
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hquotPrime
  have hnotTwoStep :
      ¬ p ∣ Nat.card ((H ⧸ pPrimeCore p H) ⧸
        pCore p (H ⧸ pPrimeCore p H)) := by
    rw [Nat.card_congr (pPrimePCoreQuotientEquiv p H).toEquiv]
    exact hnotFinal
  have hnotIndex :
      ¬ p ∣ (pCore p (H ⧸ pPrimeCore p H)).index := by
    rw [Subgroup.index_eq_card]
    exact hnotTwoStep
  let P : Sylow p (H ⧸ pPrimeCore p H) :=
    pCore_isPGroup.toSylow hnotIndex
  exact ⟨P, rfl⟩

/-- `BGsection10.v: mFT_proper_plength1`, Bender--Glauberman Theorem 10.6.

Every proper subgroup of the minimal simple odd-order counterexample has
`p`-length at most one. -/
theorem mFT_proper_plength1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] {H : Subgroup G} (hH : H < ⊤) :
    IsPLengthOne p H := by
  classical
  obtain ⟨M, hM, hHM⟩ := mmax_exists H hH
  have hMpl : IsPLengthOne p M := by
    letI : IsSolvable M := mmax_sol hM
    by_cases hpAlpha : p ∈ alphaPrimes M
    · let A : Subgroup M := (alphaCore M).subgroupOf M
      have hAnormal : A.Normal := by
        simpa [A] using alphaCore_normal M
      letI : A.Normal := hAnormal
      have hHall : IsHall (alphaPrimes M) A := by
        simpa [A] using Malpha_Hall hM
      obtain ⟨K, hAK⟩ := hHall.exists_right_complement
      have hcopAK : Nat.Coprime (Nat.card A) (Nat.card K) := by
        rw [← hAK.symm.index_eq_card]
        exact hHall.coprime_card_index
      have hAder : A ≤ _root_.commutator M := by
        have hmap : A.map M.subtype ≤
            (_root_.commutator M).map M.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le (alphaCore_le M)]
          exact (Malpha_sub_Msigma hM).trans (Msigma_der1 hM)
        exact (Subgroup.map_le_map_iff_of_injective
          M.subtype_injective).mp hmap
      letI : IsSolvable A := inferInstance
      have hperfect : ⁅A, K⁆ = A :=
        (coprime_der1_sdprod hAK
          (by rw [A.normalizer_eq_top]; exact le_top)
          hcopAK hAder).1

      let D : Subgroup M := _root_.commutator M
      have hMne : M ≠ ⊥ := mmax_neq1 hM
      letI : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hMne
      have hDneTop : D ≠ ⊤ := by
        exact (IsSolvable.commutator_lt_top_of_nontrivial M).ne
      have hquotNe : Nat.card (M ⧸ D) ≠ 1 := by
        rw [← D.index_eq_card]
        exact (ne_of_gt (Subgroup.one_lt_index_of_ne_top hDneTop))
      obtain ⟨q, hq, hqAb⟩ := Nat.exists_prime_and_dvd hquotNe
      letI : Fact q.Prime := ⟨hq⟩
      have hqSigma : q ∉ sigmaPrimes M := by
        exact der1_quo_sigma' hM (by simpa [D] using hqAb)
      have hqAlpha : q ∉ alphaPrimes M :=
        fun hqa ↦ hqSigma (alpha_sub_sigma hM hqa)
      have hqKindex : ¬ q ∣ K.index := by
        rw [hAK.index_eq_card]
        intro hqA
        exact hqAlpha (hHall.isPiNumber_card hq hqA)
      let QK : Sylow q K := Classical.choice Sylow.nonempty
      let QM0 : Subgroup M := (QK : Subgroup K).map K.subtype
      have hQM0p : IsPGroup q QM0 := QK.isPGroup'.map K.subtype
      have hQM0index : ¬ q ∣ QM0.index := by
        dsimp [QM0]
        rw [Subgroup.index_map_subtype]
        exact hq.not_dvd_mul QK.not_dvd_index hqKindex
      let QM : Sylow q M := hQM0p.toSylow hQM0index
      have hqM : q ∣ Nat.card M := by
        have hqDindex : q ∣ D.index := by
          simpa [D.index_eq_card] using hqAb
        exact hqDindex.trans D.index_dvd_card
      have hQMne : (QM : Subgroup M) ≠ ⊥ := by
        intro hbot
        apply QM.not_dvd_index
        simpa [hbot] using hqM
      obtain ⟨x, hxOmega, hxne, _hxNotUnique, hZ⟩ :=
        cent1_sigma'_Zgroup hM hqSigma QM hQMne
      let KG : Subgroup G := K.map M.subtype
      have hQMKG : ambientSylow M QM ≤ KG := by
        change QM0.map M.subtype ≤ K.map M.subtype
        exact Subgroup.map_mono (Subgroup.map_subtype_le (QK : Subgroup K))
      have hxKG : x ∈ KG :=
        hQMKG ((omegaOneCenterAmbient_le_centerWithin q
          (ambientSylow M QM) hxOmega).1)
      let R0 : Subgroup G := Subgroup.zpowers x
      have hR0KG : R0 ≤ KG := Subgroup.zpowers_le.mpr hxKG
      have hxpow : x ^ q = 1 := by
        rcases hxOmega with ⟨z, hz, hzx⟩
        subst x
        have hzpow :=
          Submission.OddOrder.BG.Section05.omegaOneCenter_pow_eq_one
            (G := ambientSylow M QM) q ⟨z, hz⟩
        exact congrArg Subtype.val (congrArg Subtype.val hzpow)
      have hxorder : orderOf x = q := by
        have hdvd : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one hxpow
        exact ((Nat.dvd_prime hq).mp hdvd).resolve_left
          (by simpa [orderOf_eq_one_iff] using hxne)
      have hR0prime : (Nat.card R0).Prime := by
        simpa [R0, Nat.card_zpowers, hxorder] using hq
      have hKGleM : KG ≤ M := by
        exact (Subgroup.map_subtype_le K)
      have hKGlocal : KG.subgroupOf M = K := by
        dsimp [KG]
        exact Subgroup.comap_map_eq_self_of_injective
          M.subtype_injective K
      have hcompJ :
          ((alphaCore M).subgroupOf M).IsComplement'
            (KG.subgroupOf M) := by
        simpa [A, hKGlocal] using hAK
      have hperfectG : ⁅alphaCore M, KG⁆ = alphaCore M := by
        calc
          ⁅alphaCore M, KG⁆ = (⁅A, K⁆).map M.subtype := by
            rw [Subgroup.map_commutator,
              Subgroup.map_subgroupOf_eq_of_le (alphaCore_le M)]
          _ = A.map M.subtype := by rw [hperfect]
          _ = alphaCore M := Subgroup.map_subgroupOf_eq_of_le (alphaCore_le M)
      have hcopG : Nat.Coprime (Nat.card (alphaCore M)) (Nat.card KG) := by
        have hAcard : Nat.card A = Nat.card (alphaCore M) := by
          simpa only [A] using
            Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
              (alphaCore_le M)
        have hKGcard : Nat.card KG = Nat.card K := by
          dsimp only [KG]
          exact Subgroup.card_map_of_injective M.subtype_injective
        rw [← hAcard, hKGcard]
        exact hcopAK
      have hApl : IsPLengthOne p (alphaCore M) := by
        have hplComm :=
          odd_sdprod_Zgroup_cent_prime_plength1_of_subgroup
            (p := p) M (alphaCore M) KG R0
            (alphaCore_le M) hKGleM hcompJ
            hcopG (mFT_odd M) hR0KG hR0prime hZ
        rwa [hperfectG] at hplComm
      have hAplLocal : IsPLengthOne p A := by
        exact isPLengthOne_of_mulEquiv hApl
          (Subgroup.subgroupOfEquivOfLe (alphaCore_le M)).symm
      let U : Subgroup M := pElementGenerated p M
      have hUA : U ≤ A := by
        rw [pElementGenerated_le_iff]
        intro x hx
        let C : Subgroup M := Subgroup.zpowers x
        have hCp : IsPGroup p C := hx.zpowers_isPGroup
        exact (isPGroup_le_normal_isHall hpAlpha hCp hAnormal hHall)
          (Subgroup.mem_zpowers x)
      have hUplSub : IsPLengthOne p (U.subgroupOf A) :=
        plength1S (U.subgroupOf A) hAplLocal
      have hUpl : IsPLengthOne p U := by
        exact isPLengthOne_of_mulEquiv hUplSub
          (Subgroup.subgroupOfEquivOfLe hUA)
      have hgenU : pElementGenerated p U = ⊤ := by
        have hmap : (pElementGenerated p U).map U.subtype = U := by
          apply le_antisymm (Subgroup.map_subtype_le _)
          change pElementGenerated p M ≤
            (pElementGenerated p U).map U.subtype
          rw [pElementGenerated_le_iff]
          intro x hx
          let xU : U := ⟨x, isPElement_subset_pElementGenerated hx⟩
          have hxU : IsPElement p xU :=
            IsPElement.of_map_of_injective U.subtype
              U.subtype_injective hx
          exact ⟨xU, isPElement_subset_pElementGenerated hxU, rfl⟩
        apply (Subgroup.map_injective (f := U.subtype) U.subtype_injective)
        rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      apply p_elt_gen_length1.mpr
      change IsPrimeComplement p (pPrimeCore p U)
      let W : Subgroup U := pElementGenerated p U
      have hHallW : IsPrimeComplement p (pPrimeCore p W) := by
        simpa only [W] using p_elt_gen_length1.mp hUpl
      let e : W ≃* U :=
        (MulEquiv.subgroupCongr (by simpa only [W] using hgenU)).trans
          Subgroup.topEquiv
      exact pPrimeCore_isPrimeComplement_of_mulEquiv e hHallW
    · apply isPLengthOne_of_no_rank_three (mmax_sol hM) (mFT_odd M)
      rintro ⟨E, hE⟩
      apply hpAlpha
      exact ⟨Fact.out, E.map M.subtype, Subgroup.map_subtype_le E,
        hE.map_of_injective M.subtype M.subtype_injective⟩
  have hHplLocal : IsPLengthOne p (H.subgroupOf M) :=
    plength1S (H.subgroupOf M) hMpl
  exact isPLengthOne_of_mulEquiv hHplLocal
    (Subgroup.subgroupOfEquivOfLe hHM)

/-! ### Bender--Glauberman Corollary 10.7(a--b) -/

/-- `BGsection10.v: mFT_Sylow_der1`, Corollary 10.7(a), second part. -/
theorem mFT_Sylow_der1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (P : Subgroup G) ≤
      (_root_.commutator
        (Subgroup.normalizer ((P : Subgroup G) : Set G))).map
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).subtype := by
  classical
  let N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  by_cases hPbot : (P : Subgroup G) = ⊥
  · rw [hPbot]
    exact bot_le
  have hPproper : (P : Subgroup G) < ⊤ :=
    mFT_pgroup_proper (P : Subgroup G) P.isPGroup'
  have hNproper : N < ⊤ := by
    simpa [N] using mFT_norm_proper (P : Subgroup G) hPbot hPproper
  obtain ⟨M, hM, hNM⟩ := mmax_exists N hNproper
  have hPM : (P : Subgroup G) ≤ M := P.le_normalizer.trans hNM
  let PM : Sylow p M := P.subtype hPM
  have hPMmap : (PM : Subgroup M).map M.subtype = (P : Subgroup G) := by
    dsimp only [PM]
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPM]
  have hpSigma : p ∈ sigmaPrimes M := by
    refine ⟨Fact.out, PM, ?_⟩
    simpa only [ambientSylow, hPMmap] using hNM
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hSnormal : S.Normal := by
    simpa [S] using sigmaCore_normal M
  have hSHall : IsHall (sigmaPrimes M) S := by
    simpa [S] using Msigma_Hall hM
  have hPMS : (PM : Subgroup M) ≤ S :=
    isPGroup_le_normal_isHall hpSigma PM.isPGroup' hSnormal hSHall
  have hSder : S ≤ _root_.commutator M := by
    have hmapped : S.map M.subtype ≤
        (_root_.commutator M).map M.subtype := by
      simpa only [S,
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] using
        Msigma_der1 hM
    exact (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp hmapped
  have hPMder : (PM : Subgroup M) ≤ _root_.commutator M :=
    hPMS.trans hSder
  have hplM : IsPLengthOne p M :=
    mFT_proper_plength1 p (mmax_proper hM)
  have hlocal := plength1_Sylow_sub_der1 PM hplM hPMder
  let U : Subgroup M :=
    Subgroup.normalizer ((PM : Subgroup M) : Set M)
  let UG : Subgroup G := U.map M.subtype
  have hUGN : UG ≤ N := by
    calc
      U.map M.subtype ≤
          Subgroup.normalizer
            ((PM : Subgroup M).map M.subtype : Set G) :=
        (PM : Subgroup M).le_normalizer_map M.subtype
      _ = N := by rw [hPMmap]
  have hPUGder : (P : Subgroup G) ≤ ⁅UG, UG⁆ := by
    calc
      (P : Subgroup G) = (PM : Subgroup M).map M.subtype := hPMmap.symm
      _ ≤ ⁅U, U⁆.map M.subtype :=
        Subgroup.map_mono hlocal
      _ = ⁅UG, UG⁆ := by
        dsimp only [UG]
        rw [Subgroup.map_commutator]
  calc
    (P : Subgroup G) ≤ ⁅UG, UG⁆ := hPUGder
    _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hUGN hUGN
    _ = (_root_.commutator N).map N.subtype :=
      N.map_subtype_commutator.symm

/-- `BGsection10.v: mFT_Sylow_sdprod_commg`, Corollary 10.7(a), first part.

The semidirect-product hypothesis is expressed intrinsically in the full
normalizer, while the conclusion is mapped back to the ambient group. -/
theorem mFT_Sylow_sdprod_commg
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (V : Subgroup G)
    (hVN : V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hcomp :
      ((P : Subgroup G).subgroupOf
        (Subgroup.normalizer ((P : Subgroup G) : Set G))).IsComplement'
      (V.subgroupOf
        (Subgroup.normalizer ((P : Subgroup G) : Set G)))) :
    ⁅(P : Subgroup G), V⁆ = (P : Subgroup G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let K : Subgroup N := (P : Subgroup G).subgroupOf N
  let W : Subgroup N := V.subgroupOf N
  have hcompKW : K.IsComplement' W := by simpa [N, K, W] using hcomp
  let PN : Sylow p N := P.subtype P.le_normalizer
  have hPNK : (PN : Subgroup N) = K := by
    dsimp only [PN, K, N]
    rw [Sylow.coe_subtype]
  letI : K.Normal := by
    dsimp only [K, N]
    exact (P : Subgroup G).normal_in_normalizer
  have hKp : IsPGroup p K := by
    dsimp only [K]
    exact P.isPGroup'.comap_subtype
  letI : Group.IsNilpotent K := hKp.isNilpotent
  have hKcopIndex : (Nat.card K).Coprime K.index := by
    rw [← hPNK]
    exact PN.card_coprime_index
  have hKWcop : (Nat.card K).Coprime (Nat.card W) := by
    rw [← hcompKW.symm.index_eq_card]
    exact hKcopIndex
  have hKder : K ≤ _root_.commutator N := by
    have hmapped : K.map N.subtype ≤
        (_root_.commutator N).map N.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le P.le_normalizer]
      exact mFT_Sylow_der1 P
    exact (Subgroup.map_le_map_iff_of_injective
      N.subtype_injective).mp hmapped
  have hWnormK : W ≤ Subgroup.normalizer (K : Set N) := by
    rw [K.normalizer_eq_top]
    exact le_top
  have hcommKW : ⁅K, W⁆ = K :=
    (coprime_der1_sdprod hcompKW hWnormK hKWcop hKder).1
  have hKmap : K.map N.subtype = (P : Subgroup G) := by
    dsimp only [K, N]
    exact Subgroup.map_subgroupOf_eq_of_le P.le_normalizer
  have hWmap : W.map N.subtype = V := by
    dsimp only [W, N]
    exact Subgroup.map_subgroupOf_eq_of_le hVN
  calc
    ⁅(P : Subgroup G), V⁆ =
        ⁅K.map N.subtype, W.map N.subtype⁆ := by rw [hKmap, hWmap]
    _ = ⁅K, W⁆.map N.subtype := by rw [Subgroup.map_commutator]
    _ = K.map N.subtype := by rw [hcommKW]
    _ = (P : Subgroup G) := hKmap

/-- `BGsection10.v: mFT_rank2_Sylow_cprod`, Corollary 10.7(b). -/
theorem mFT_rank2_Sylow_cprod
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E)
    (hPnoncomm : ¬ IsMulCommutative P) :
    ∃ S C : Subgroup G,
      ¬ IsMulCommutative S ∧
      Nat.card S = p ^ 3 ∧
      Monoid.exponent S ∣ p ∧
      C ≤ Subgroup.centralizer (S : Set G) ∧
      S ⊔ C = (P : Subgroup G) ∧
      IsCyclic C ∧
      (omegaOne p C).map C.subtype =
        (Subgroup.center S).map S.subtype := by
  classical
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hPbot
    apply hPnoncomm
    apply isMulCommutative_iff.mpr
    intro a b
    apply Subtype.ext
    have ha : (a : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hPbot]
      exact a.property
    have hb : (b : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hPbot]
      exact b.property
    simp [ha, hb]
  let N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let K : Subgroup N := (P : Subgroup G).subgroupOf N
  let PN : Sylow p N := P.subtype P.le_normalizer
  have hPNK : (PN : Subgroup N) = K := by
    dsimp only [PN, K, N]
    rw [Sylow.coe_subtype]
  letI : K.Normal := by
    dsimp only [K, N]
    exact (P : Subgroup G).normal_in_normalizer
  have hKcop : (Nat.card K).Coprime K.index := by
    rw [← hPNK]
    exact PN.card_coprime_index
  obtain ⟨W, hcompKW⟩ := K.exists_right_complement'_of_coprime hKcop
  let V : Subgroup G := W.map N.subtype
  have hVN : V ≤ N := Subgroup.map_subtype_le W
  have hVsub : V.subgroupOf N = W := by
    change (W.map N.subtype).comap N.subtype = W
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective W
  have hcompV : K.IsComplement' (V.subgroupOf N) := by
    rw [hVsub]
    exact hcompKW
  have hperfect : ⁅(P : Subgroup G), V⁆ = (P : Subgroup G) :=
    mFT_Sylow_sdprod_commg P V hVN hcompV
  have hpKindex : ¬ p ∣ K.index := by
    rw [← hPNK]
    exact PN.not_dvd_index
  have hpW : ¬ p ∣ Nat.card W := by
    rw [← hcompKW.symm.index_eq_card]
    exact hpKindex
  have hVcard : Nat.card V = Nat.card W :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hpV : Nat.Coprime p (Nat.card V) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by rwa [hVcard])
  obtain ⟨_hp3, hcases⟩ :=
    rankTwo_coprime_commutator_cprod
      (P : Subgroup G) V P.isPGroup' (mFT_odd (P : Subgroup G))
      hPne hRank hperfect hpV (mFT_odd V)
  rcases hcases.resolve_left hPnoncomm with
    ⟨S, C, hSnoncomm, hScard, hSexp, hCcent, hSC, hCcyc, hOmega⟩
  have hSP : S ≤ (P : Subgroup G) := by
    rw [← hSC]
    exact le_sup_left
  have hSp : IsPGroup p S := P.isPGroup'.to_le hSP
  have hSextra : IsExtraspecial S :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hSp hScard hSnoncomm
  refine ⟨S, C, hSnoncomm, hScard, hSexp, hCcent, hSC, hCcyc, ?_⟩
  calc
    (omegaOne p C).map C.subtype =
        (_root_.commutator S).map S.subtype := hOmega
    _ = (Subgroup.center S).map S.subtype := by
      rw [hSextra.toIsSpecial.commutator_eq_center]

/-! ### Bender--Glauberman Corollary 10.7(c--e) -/

/-- `BGsection10.v: mFT_sub_Sylow_trans`, Corollary 10.7(c). -/
theorem mFT_sub_Sylow_trans
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {Q : Subgroup G} {x : G}
    (hQP : Q ≤ (P : Subgroup G))
    (hQxP :
      Q.map (MulAut.conj x⁻¹).toMonoidHom ≤ (P : Subgroup G)) :
    ∃ y : G, y ∈ Subgroup.normalizer (P : Set G) ∧
      Q.map (MulAut.conj x⁻¹).toMonoidHom =
        Q.map (MulAut.conj y⁻¹).toMonoidHom := by
  classical
  by_cases hPbot : (P : Subgroup G) = ⊥
  · have hQbot : Q = ⊥ := bot_unique (hPbot ▸ hQP)
    subst Q
    refine ⟨1, ?_, ?_⟩ <;> simp
  have hPproper : (P : Subgroup G) < ⊤ :=
    mFT_pgroup_proper (P : Subgroup G) P.isPGroup'
  have hNPproper : Subgroup.normalizer (P : Set G) < ⊤ :=
    mFT_norm_proper (P : Subgroup G) hPbot hPproper
  obtain ⟨M, hM, hNPM⟩ :=
    mmax_exists (Subgroup.normalizer (P : Set G)) hNPproper
  have hPM : (P : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans hNPM
  let PM : Sylow p M := P.subtype hPM
  have hPMambient : ambientSylow M PM = (P : Subgroup G) := by
    dsimp only [PM, ambientSylow]
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPM]
  have hpSigma : p ∈ sigmaPrimes M := by
    refine ⟨Fact.out, PM, ?_⟩
    rw [hPMambient]
    exact hNPM
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  have hQM : Q ≤ M := hQP.trans hPM
  have hQxM : Q.map (MulAut.conj x⁻¹).toMonoidHom ≤ M :=
    hQxP.trans hPM
  obtain ⟨c, hc, u, hu, hxu⟩ :=
    (sigma_group_trans hM hpSigma hQp).1 x hQM hQxM
  have hQxQu :
      Q.map (MulAut.conj x⁻¹).toMonoidHom =
        Q.map (MulAut.conj u⁻¹).toMonoidHom := by
    calc
      Q.map (MulAut.conj x⁻¹).toMonoidHom =
          Q.map (MulAut.conj (c * u)⁻¹).toMonoidHom := by rw [hxu]
      _ = Q.map (MulAut.conj (u⁻¹ * c⁻¹)).toMonoidHom := by
        rw [mul_inv_rev]
      _ = (Q.map (MulAut.conj c⁻¹).toMonoidHom).map
          (MulAut.conj u⁻¹).toMonoidHom :=
        (map_conj_map_conj Q c⁻¹ u⁻¹).symm
      _ = Q.map (MulAut.conj u⁻¹).toMonoidHom := by
        rw [map_conj_eq_self_of_centralizer Q
          ((Subgroup.centralizer (Q : Set G)).inv_mem hc)]
  have hQuP : Q.map (MulAut.conj u⁻¹).toMonoidHom ≤
      (P : Subgroup G) := by
    rw [← hQxQu]
    exact hQxP
  let QM : Subgroup M := Q.subgroupOf M
  have hQMPM : QM ≤ (PM : Subgroup M) := by
    intro q hq
    change (q : G) ∈ (P : Subgroup G)
    exact hQP (show (q : G) ∈ Q from hq)
  let uM : M := ⟨u, hu⟩
  have hQuPM : ∀ q ∈ (QM : Set M),
      (MulAut.conj uM⁻¹).toMonoidHom q ∈ PM := by
    intro q hq
    change (MulAut.conj u⁻¹).toMonoidHom (q : G) ∈
      (P : Subgroup G)
    have hqQ : (q : G) ∈ Q := hq
    exact hQuP
      (Subgroup.mem_map_of_mem (MulAut.conj u⁻¹).toMonoidHom hqQ)
  letI : IsSolvable M := mmax_sol hM
  have hpl : IsPLengthOne p M :=
    mFT_proper_plength1 p (mmax_proper hM)
  obtain ⟨cM, hcM, yM, hyM, huy⟩ :=
    plength1_Sylow_trans PM hpl (QM : Set M)
      hQMPM uM hQuPM
  have hcMG : (cM : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    let qM : M := ⟨q, hQM hq⟩
    have hqQM : qM ∈ QM := hq
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp hcM) qM hqQM)
  have hyG : (yM : G) ∈ Subgroup.normalizer (P : Set G) := by
    have hyMap : (yM : G) ∈
        Subgroup.normalizer (ambientSylow M PM : Set G) := by
      change (yM : G) ∈ Subgroup.normalizer
        ((PM : Subgroup M).map M.subtype : Set G)
      apply Subgroup.le_normalizer_map M.subtype
      exact ⟨yM, hyM, rfl⟩
    rwa [hPMambient] at hyMap
  have huyG : u = (cM : G) * (yM : G) :=
    congrArg Subtype.val huy
  have hQuQy :
      Q.map (MulAut.conj u⁻¹).toMonoidHom =
        Q.map (MulAut.conj (yM : G)⁻¹).toMonoidHom := by
    calc
      Q.map (MulAut.conj u⁻¹).toMonoidHom =
          Q.map (MulAut.conj ((cM : G) * (yM : G))⁻¹).toMonoidHom := by
        rw [huyG]
      _ = Q.map
          (MulAut.conj ((yM : G)⁻¹ * (cM : G)⁻¹)).toMonoidHom := by
        rw [mul_inv_rev]
      _ = (Q.map (MulAut.conj (cM : G)⁻¹).toMonoidHom).map
          (MulAut.conj (yM : G)⁻¹).toMonoidHom :=
        (map_conj_map_conj Q (cM : G)⁻¹ (yM : G)⁻¹).symm
      _ = Q.map (MulAut.conj (yM : G)⁻¹).toMonoidHom := by
        rw [map_conj_eq_self_of_centralizer Q
          ((Subgroup.centralizer (Q : Set G)).inv_mem hcMG)]
  exact ⟨yM, hyG, hQxQu.trans hQuQy⟩

/-- `BGsection10.v: mFT_subnorm_Sylow`, Corollary 10.7(d). -/
theorem mFT_subnorm_Sylow
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {Q : Subgroup G}
    (hQP : Q ≤ (P : Subgroup G)) :
    ∃ S : Sylow p (Subgroup.normalizer (Q : Set G)),
      ambientSylow (Subgroup.normalizer (Q : Set G)) S =
        (P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) := by
  classical
  let NQ : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hQNQ : Q ≤ NQ := Subgroup.le_normalizer
  let QN : Subgroup NQ := Q.subgroupOf NQ
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  have hQNp : IsPGroup p QN := hQp.comap_subtype
  obtain ⟨S, hQNS⟩ := hQNp.exists_le_sylow
  let SG : Subgroup G := (S : Subgroup NQ).map NQ.subtype
  have hQSG : Q ≤ SG := by
    change Q ≤ (S : Subgroup NQ).map NQ.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hQNQ]
    exact Subgroup.map_mono hQNS
  have hSGp : IsPGroup p SG := S.isPGroup'.map NQ.subtype
  obtain ⟨T, hSGT⟩ := hSGp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T P
  have hTg :
      (T : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (P : Subgroup G) := by
    change ((g • T : Sylow p G) : Subgroup G) = (P : Subgroup G)
    exact congrArg (fun U : Sylow p G ↦ (U : Subgroup G)) hg
  have hSGgP : SG.map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) :=
    (Subgroup.map_mono hSGT).trans_eq hTg
  have hQgP : Q.map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) := (Subgroup.map_mono hQSG).trans hSGgP
  obtain ⟨y, hyP, hQgy⟩ :=
    mFT_sub_Sylow_trans (G := G) P
      (Q := Q) (x := g⁻¹) hQP (by simpa using hQgP)
  let k : G := y * g
  have hQk : Q.map (MulAut.conj k).toMonoidHom = Q := by
    calc
      Q.map (MulAut.conj k).toMonoidHom =
          (Q.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj y).toMonoidHom := by
        simpa [k] using (map_conj_map_conj Q g y).symm
      _ = (Q.map (MulAut.conj y⁻¹).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by
        have hQgy' :
            Q.map (MulAut.conj g).toMonoidHom =
              Q.map (MulAut.conj y⁻¹).toMonoidHom := by
          simpa only [inv_inv] using hQgy
        exact congrArg
          (fun R : Subgroup G ↦
            R.map (MulAut.conj y).toMonoidHom) hQgy'
      _ = Q := by
        simpa only [inv_inv] using map_conj_inv_map_conj Q y⁻¹
  have hkNQ : k ∈ NQ := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hQk
  have hSGkP : SG.map (MulAut.conj k).toMonoidHom ≤
      (P : Subgroup G) := by
    calc
      SG.map (MulAut.conj k).toMonoidHom =
          (SG.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj y).toMonoidHom := by
        simpa [k] using (map_conj_map_conj SG g y).symm
      _ ≤ (P : Subgroup G).map (MulAut.conj y).toMonoidHom :=
        Subgroup.map_mono hSGgP
      _ = (P : Subgroup G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyP
  let kN : NQ := ⟨k, hkNQ⟩
  let S' : Sylow p NQ := kN • S
  have hS'ambient :
      (S' : Subgroup NQ).map NQ.subtype =
        SG.map (MulAut.conj k).toMonoidHom := by
    change ((S : Subgroup NQ).map
        (MulAut.conj kN).toMonoidHom).map NQ.subtype =
      ((S : Subgroup NQ).map NQ.subtype).map
        (MulAut.conj k).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun f : NQ →* G ↦ (S : Subgroup NQ).map f)
    ext z
    rfl
  have hS'P : (S' : Subgroup NQ).map NQ.subtype ≤
      (P : Subgroup G) := by
    rw [hS'ambient]
    exact hSGkP
  let PN : Subgroup NQ :=
    ((P : Subgroup G) ⊓ NQ).subgroupOf NQ
  have hPNp : IsPGroup p PN :=
    (P.isPGroup'.to_le inf_le_left).comap_subtype
  have hS'PN : (S' : Subgroup NQ) ≤ PN := by
    intro z hz
    change (z : G) ∈ (P : Subgroup G) ⊓ NQ
    exact ⟨hS'P (Subgroup.mem_map_of_mem NQ.subtype hz), z.property⟩
  have hPNeq : PN = (S' : Subgroup NQ) :=
    S'.is_maximal' hPNp hS'PN
  refine ⟨S', ?_⟩
  change (S' : Subgroup NQ).map NQ.subtype =
    (P : Subgroup G) ⊓ NQ
  rw [← hPNeq]
  exact Subgroup.map_subgroupOf_eq_of_le inf_le_right

/-- `BGsection10.v: mFT_Sylow_normalS`, Corollary 10.7(e). -/
theorem mFT_Sylow_normalS
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {Q R : Subgroup G}
    (hRp : IsPGroup p R)
    (hQPR : Q ≤ (P : Subgroup G) ⊓ R)
    (hQnormal :
      (Q.subgroupOf (Subgroup.normalizer (P : Set G))).Normal) :
    (Q.subgroupOf (Subgroup.normalizer (R : Set G))).Normal := by
  classical
  let NP : Subgroup G := Subgroup.normalizer (P : Set G)
  let NR : Subgroup G := Subgroup.normalizer (R : Set G)
  let NQ : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hQP : Q ≤ (P : Subgroup G) := hQPR.trans inf_le_left
  have hQR : Q ≤ R := hQPR.trans inf_le_right
  have hQNP : Q ≤ NP := hQP.trans Subgroup.le_normalizer
  have hNPQ : NP ≤ NQ :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQNP).mp hQnormal
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hSg : (S : Subgroup G).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup G) := by
    change ((g • S : Sylow p G) : Subgroup G) = (P : Subgroup G)
    exact congrArg (fun U : Sylow p G ↦ (U : Subgroup G)) hg
  have hRgP : R.map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) := (Subgroup.map_mono hRS).trans_eq hSg
  have hQgP : Q.map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) := (Subgroup.map_mono hQR).trans hRgP
  have hQNR : Q ≤ NR := hQR.trans Subgroup.le_normalizer
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQNR).mpr
  intro y hy
  have hyInv : y⁻¹ ∈ NR := NR.inv_mem hy
  have hRy : R.map (MulAut.conj y⁻¹).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyInv
  have hQgyP :
      Q.map (MulAut.conj (g * y⁻¹)).toMonoidHom ≤
        (P : Subgroup G) := by
    calc
      Q.map (MulAut.conj (g * y⁻¹)).toMonoidHom =
          (Q.map (MulAut.conj y⁻¹).toMonoidHom).map
            (MulAut.conj g).toMonoidHom :=
        (map_conj_map_conj Q y⁻¹ g).symm
      _ ≤ (R.map (MulAut.conj y⁻¹).toMonoidHom).map
          (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (Subgroup.map_mono hQR)
      _ = R.map (MulAut.conj g).toMonoidHom := by rw [hRy]
      _ ≤ (P : Subgroup G) := hRgP
  obtain ⟨t, htP, hQt⟩ :=
    mFT_sub_Sylow_trans (G := G) P
      (Q := Q) (x := g⁻¹) hQP (by simpa using hQgP)
  obtain ⟨z, hzP, hQz⟩ :=
    mFT_sub_Sylow_trans (G := G) P
      (Q := Q) (x := y * g⁻¹) hQP
      (by simpa only [mul_inv_rev, inv_inv] using hQgyP)
  have hQt' : Q.map (MulAut.conj g).toMonoidHom =
      Q.map (MulAut.conj t⁻¹).toMonoidHom := by simpa using hQt
  have hQz' : Q.map (MulAut.conj (g * y⁻¹)).toMonoidHom =
      Q.map (MulAut.conj z⁻¹).toMonoidHom := by
    simpa only [mul_inv_rev, inv_inv] using hQz
  have htQ : t ∈ NQ := hNPQ htP
  have hzQ : z ∈ NQ := hNPQ hzP
  have hQg : Q.map (MulAut.conj g).toMonoidHom = Q :=
    hQt'.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp (NQ.inv_mem htQ))
  have hQgy : Q.map (MulAut.conj (g * y⁻¹)).toMonoidHom = Q :=
    hQz'.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp (NQ.inv_mem hzQ))
  have hgQ : g ∈ NQ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hQg
  have hgyQ : g * y⁻¹ ∈ NQ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hQgy
  have hyInvQ : y⁻¹ ∈ NQ := by
    simpa [mul_assoc] using NQ.mul_mem (NQ.inv_mem hgQ) hgyQ
  simpa using NQ.inv_mem hyInvQ

end Submission.OddOrder.BG.Section10
