import Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement
import Submission.OddOrder.BG.Section06.PProdCoprime
import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.BG.Section10.SigmaElementaryControl
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.FittingNilpotent
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall
import Submission.OddOrder.MathlibSupport.NilpotentCentralizer
import Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment
import Submission.OddOrder.MathlibSupport.PiCore
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow
import Submission.OddOrder.MathlibSupport.SolvableHallContainment
import Submission.OddOrder.MathlibSupport.SylowIntersection

/-!
# Bender--Glauberman Section 10: the beta Hall structure

This file ports the block of `BGsection10.v` from Lemma 10.8 through
Corollary 10.9(b).  The beta core is first shown to be a Hall subgroup, and
the derived quotient by that core is then shown to be nilpotent.  Those two
facts give the centralizer and non-unique-normalizer consequences used in
the remainder of Section 10.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

noncomputable section

universe u

/-! ### Local prime-core adapters -/

/-- The ambient prime-set core, restricted to its defining subgroup, is the
ordinary group-level `piCore` of that subgroup. -/
private theorem primeSetCore_subgroupOf_eq_piCore
    {K : Type u} [Group K] [Finite K]
    (pi : Set ℕ) (X : Subgroup K) :
    (primeSetCore pi X).subgroupOf X = piCore pi X := by
  let A : Subgroup K := primeSetCore pi X
  have hAX : A ≤ X := primeSetCore_le pi X
  apply le_antisymm
  · apply le_piCore
    · simpa [A] using primeSetCore_normal pi X
    · rw [natCard_subgroupOf_eq hAX]
      simpa [A] using primeSetCore_isPiNumber pi X
  · intro x hx
    change (x : K) ∈ A
    have hmapNormal :
        (((piCore pi X).map X.subtype).subgroupOf X).Normal := by
      change (((piCore pi X).map X.subtype).comap X.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
      infer_instance
    have hmapPi : IsPiNumber pi
        (Nat.card ((piCore pi X).map X.subtype)) := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact piCore_isPiNumber pi
    have hmapCore : (piCore pi X).map X.subtype ≤ A := by
      dsimp only [A]
      rw [primeSetCore]
      exact le_sSup ⟨Subgroup.map_subtype_le _, hmapNormal, hmapPi⟩
    exact hmapCore (Subgroup.mem_map_of_mem X.subtype hx)

/-- A `pi`-subgroup is an `r'`-subgroup when `r` is outside `pi`. -/
private theorem isPPrimeSubgroup_of_isPiNumber_not_mem
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {A : Subgroup K} {r : ℕ} [Fact r.Prime]
    (hA : IsPiNumber pi (Nat.card A)) (hr : r ∉ pi) :
    IsPPrimeSubgroup r A := by
  rw [IsPPrimeSubgroup]
  exact (Fact.out : r.Prime).coprime_iff_not_dvd.mpr fun hrA ↦
    hr (hA Fact.out hrA)

/-- Restricting a normal prime complement to an arbitrary subgroup leaves
the prime-complement core Hall in that subgroup. -/
private theorem pPrimeCore_isPrimeComplement_of_subgroup
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime]
    (hHall : IsPrimeComplement p (pPrimeCore p K))
    (S : Subgroup K) :
    IsPrimeComplement p (pPrimeCore p S) := by
  let O : Subgroup K := pPrimeCore p K
  let J : Subgroup S := O.comap S.subtype
  have hJprime : IsPPrimeSubgroup p J := by
    rw [IsPPrimeSubgroup]
    exact (pPrimeCore_coprime_card (G := K) (p := p)).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective O S.subtype
        S.subtype_injective)
  have hJnormal : J.Normal := by
    dsimp [J, O]
    infer_instance
  have hJcore : J ≤ pPrimeCore p S :=
    le_pPrimeCore hJprime hJnormal
  have hJindex : J.index ∣ O.index := by
    rw [show J.index = O.relIndex S.subtype.range by
      simpa [J] using Subgroup.index_comap O S.subtype]
    exact O.relIndex_dvd_index_of_normal S.subtype.range
  obtain ⟨n, hn⟩ := hHall.exists_index_eq_pow
  have hindexDvd : (pPrimeCore p S).index ∣ p ^ n :=
    (Subgroup.index_dvd_of_le hJcore).trans (hJindex.trans (hn ▸ dvd_rfl))
  obtain ⟨m, _hmn, hm⟩ :=
    (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hindexDvd
  exact ⟨(pPrimeCore_coprime_card (G := S) (p := p)).symm,
    ⟨m, hm⟩⟩

/-- A normal Hall `p'`-core descends through a quotient by a subgroup that
it contains. -/
private theorem pPrimeCore_isPrimeComplement_quotient_of_le
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime]
    {N : Subgroup K} [N.Normal]
    (hN : N ≤ pPrimeCore p K)
    (hHall : IsPrimeComplement p (pPrimeCore p K)) :
    IsPrimeComplement p (pPrimeCore p (K ⧸ N)) := by
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  let O : Subgroup K := pPrimeCore p K
  let Obar : Subgroup (K ⧸ N) := O.map q
  have hObarPrime : IsPPrimeSubgroup p Obar := by
    rw [IsPPrimeSubgroup]
    exact (pPrimeCore_coprime_card (G := K) (p := p)).coprime_dvd_right
      (Subgroup.card_map_dvd O q)
  have hObarNormal : Obar.Normal := by
    dsimp [Obar, O, q]
    infer_instance
  have hObarCore : Obar ≤ pPrimeCore p (K ⧸ N) :=
    le_pPrimeCore hObarPrime hObarNormal
  have hObarIndex : Obar.index = O.index := by
    dsimp [Obar, q]
    exact O.index_map_eq (QuotientGroup.mk'_surjective N) (by
      simpa only [QuotientGroup.ker_mk'] using hN)
  obtain ⟨n, hn⟩ := hHall.exists_index_eq_pow
  have hindexDvd : (pPrimeCore p (K ⧸ N)).index ∣ p ^ n := by
    rw [← hn, ← hObarIndex]
    exact Subgroup.index_dvd_of_le hObarCore
  obtain ⟨m, _hmn, hm⟩ :=
    (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hindexDvd
  exact ⟨(pPrimeCore_coprime_card (G := K ⧸ N) (p := p)).symm,
    ⟨m, hm⟩⟩

/-- A subgroup lying in every `r'`-core for `r ∉ pi` lies in the
`pi`-core. -/
private theorem le_piCore_of_le_pPrimeCores
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {A : Subgroup K}
    (hA : ∀ r : ℕ, r.Prime → r ∉ pi → A ≤ pPrimeCore r K) :
    A ≤ piCore pi K := by
  let N : Subgroup K := Subgroup.normalClosure (A : Set K)
  have hAN : A ≤ N := Subgroup.le_normalClosure
  have hNpi : IsPiNumber pi (Nat.card N) := by
    intro r hr hrN
    letI : Fact r.Prime := ⟨hr⟩
    by_contra hrPi
    have hNcore : N ≤ pPrimeCore r K := by
      dsimp only [N]
      exact Subgroup.normalClosure_le_normal (hA r hr hrPi)
    have hrCore : r ∣ Nat.card (pPrimeCore r K) :=
      hrN.trans (Subgroup.card_dvd_of_le hNcore)
    exact ((hr.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := K) (p := r))) hrCore)
  exact hAN.trans (le_piCore (by infer_instance) hNpi)

/-- A `p`-subgroup lies in a normal `pi`-Hall subgroup when `p ∈ pi`. -/
private theorem isPGroup_le_normal_isHall
    {K : Type u} [Group K] [Finite K]
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

/-- A quotient of a subgroup by the restriction of an ambient normal
subgroup is canonically its image in the ambient quotient. -/
private def subgroupQuotientEquivImage
    {K : Type u} [Group K] (B D : Subgroup K) [B.Normal] :
    (D ⧸ B.subgroupOf D) ≃* D.map (QuotientGroup.mk' B) := by
  letI : (B.subgroupOf D).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : B.Normal) D
  exact QuotientGroup.liftEquiv (B.subgroupOf D)
    ((QuotientGroup.mk' B).subgroupMap_surjective D) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- Prime complements are invariant under group isomorphism. -/
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

private instance betaCore_subgroupOf_normal
    {G : Type u} [Group G] [Finite G] {M : Subgroup G} :
    ((betaCore M).subgroupOf M).Normal := by
  simpa using betaCore_normal M

private instance betaCore_subgroupOf_commutator_normal
    {G : Type u} [Group G] [Finite G] {M : Subgroup G} :
    (((betaCore M).subgroupOf M).subgroupOf
      (_root_.commutator M)).Normal :=
  Subgroup.Normal.subgroupOf
    (inferInstance : ((betaCore M).subgroupOf M).Normal)
    (_root_.commutator M)

/-- If a Sylow subgroup of a normal subgroup has Sylow image in a
nilpotent quotient, adjoining the quotient kernel makes it normal in the
ambient group. -/
private theorem normal_sup_of_sylow_quotient_nilpotent
    {K : Type u} [Group K] [Finite K]
    {q : ℕ} [Fact q.Prime]
    {B D X : Subgroup K} [B.Normal] [D.Normal]
    (hBD : B ≤ D) (_hXD : X ≤ D)
    (hX : IsSylowSubgroupOf q X D)
    (hnil : Group.IsNilpotent (D ⧸ B.subgroupOf D)) :
    (B ⊔ X).Normal := by
  let pi : K →* K ⧸ B := QuotientGroup.mk' B
  let Dbar : Subgroup (K ⧸ B) := D.map pi
  letI : Dbar.Normal := by
    dsimp [Dbar, pi]
    exact Subgroup.Normal.map (inferInstance : D.Normal)
      (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)
  letI : Group.IsNilpotent Dbar := by
    letI : Group.IsNilpotent (D ⧸ B.subgroupOf D) := hnil
    simpa [Dbar, pi] using
      Group.nilpotent_of_mulEquiv
        (subgroupQuotientEquivImage B D)
  obtain ⟨P, hXP⟩ := hX
  let Q : Sylow q Dbar :=
    P.mapSurjective (pi.subgroupMap_surjective D)
  have hXmap :
      X.map pi = (Q : Subgroup Dbar).map Dbar.subtype := by
    rw [hXP]
    change
      ((P : Subgroup D).map D.subtype).map pi =
        ((P.mapSurjective (pi.subgroupMap_surjective D) :
          Sylow q Dbar) : Subgroup Dbar).map Dbar.subtype
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    apply congrArg
      (fun f : D →* K ⧸ B => (P : Subgroup D).map f)
    ext d
    rfl
  have hQcore : (Q : Subgroup Dbar) = pCore q Dbar :=
    (pCore_eq_sylow_of_isNilpotent Q).symm
  have hXmapNormal : (X.map pi).Normal := by
    rw [hXmap, hQcore]
    infer_instance
  have hcomapNormal : ((X.map pi).comap pi).Normal :=
    hXmapNormal.comap pi
  simpa [pi, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] using
    hcomapNormal

/-- Local adapter for MathComp's `subHall_Sylow`: a Sylow subgroup of a
Hall subgroup is already Sylow in the ambient finite group. -/
private theorem exists_sylow_eq_map_of_sylow_hall
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := by
    dsimp [S]
    exact P.isPGroup'.map A.subtype
  have hpAindex : ¬p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- Every Sylow subgroup of `M` has elementary-abelian rank at least three
at a prime in `alpha(M)`. -/
private theorem sylow_has_rank_three_of_mem_alpha
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p M) :
    HasElementaryAbelianRankAtLeast p 3
      ((P : Subgroup M).map M.subtype) := by
  classical
  rcases hpAlpha with ⟨_hp, E, hEM, hE⟩
  let EM : Subgroup M := E.subgroupOf M
  have hEMrank : IsElementaryAbelianOfRank p 3 EM :=
    hE.subgroupOf hEM
  obtain ⟨Q, hEMQ⟩ := hEMrank.isPGroup.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q P
  let C : Subgroup M :=
    EM.map (MulAut.conj m).toMonoidHom
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
  let CG : Subgroup G := C.map M.subtype
  exact ⟨CG, Subgroup.map_mono hCP,
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- A finite `{p,q}`-group with normal Sylow subgroups at both supported
primes is nilpotent. -/
private theorem isNilpotent_of_two_prime_normal_sylows
    {K : Type u} [Group K] [Finite K]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P Q : Subgroup K}
    (hKpi : IsPiNumber ({p, q} : Set ℕ) (Nat.card K))
    (hPp : IsPGroup p P) (hpIndex : ¬p ∣ P.index)
    (hPnormal : P.Normal)
    (hQq : IsPGroup q Q) (hqIndex : ¬q ∣ Q.index)
    (hQnormal : Q.Normal) : Group.IsNilpotent K := by
  have hPF : P ≤ fittingCore K :=
    nilpotent_normal_le_fittingCore hPnormal hPp.isNilpotent
  have hQF : Q ≤ fittingCore K :=
    nilpotent_normal_le_fittingCore hQnormal hQq.isNilpotent
  let R : Subgroup K := P ⊔ Q
  have hRtop : R = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro r hr hrIndex
    have hrK : r ∈ ({p, q} : Set ℕ) :=
      hKpi hr (hrIndex.trans R.index_dvd_card)
    rcases (by simpa only [Set.mem_insert_iff,
      Set.mem_singleton_iff] using hrK) with rfl | rfl
    · exact hpIndex (hrIndex.trans
        (Subgroup.index_dvd_of_le
          (show P ≤ R from le_sup_left)))
    · exact hqIndex (hrIndex.trans
        (Subgroup.index_dvd_of_le
          (show Q ≤ R from le_sup_right)))
  have htopF : (⊤ : Subgroup K) ≤ fittingCore K := by
    rw [← hRtop]
    exact sup_le hPF hQF
  have hfit : fittingCore K = ⊤ := top_unique htopF
  have htopNil : Group.IsNilpotent (⊤ : Subgroup K) := by
    rw [← hfit]
    infer_instance
  letI : Group.IsNilpotent (⊤ : Subgroup K) := htopNil
  exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv

/-- Transport a Sylow subgroup through a multiplicative equivalence. -/
private noncomputable def sylowMapMulEquiv
    {K L : Type u} [Group K] [Finite K] [Group L] [Finite L]
    {p : ℕ} [Fact p.Prime] (e : K ≃* L) (P : Sylow p K) :
    Sylow p L :=
  let Q : Subgroup L := (P : Subgroup K).map e.toMonoidHom
  (P.isPGroup'.map e.toMonoidHom).toSylow (by
    dsimp [Q]
    rw [Subgroup.index_map_equiv]
    exact P.not_dvd_index)

@[simp]
private theorem coe_sylowMapMulEquiv
    {K L : Type u} [Group K] [Finite K] [Group L] [Finite L]
    {p : ℕ} [Fact p.Prime] (e : K ≃* L) (P : Sylow p K) :
    (sylowMapMulEquiv e P : Subgroup L) =
      (P : Subgroup K).map e.toMonoidHom := rfl

/-! ### Bender--Glauberman Lemma 10.8 -/

/-- `BGsection10.v: Mbeta_der1`. -/
theorem Mbeta_der1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    betaCore M ≤ (_root_.commutator M).map M.subtype :=
  (Mbeta_sub_Msigma hM).trans (Msigma_der1 hM)

/-- `BGsection10.v: beta_max_pdiv`, Lemma 10.8(c). -/
theorem beta_max_pdiv
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpBeta : p ∉ betaPrimes M) :
    IsPrimeComplement p
        (pPrimeCore p (_root_.commutator M)) ∧
      IsPrimeComplement p
        (pPrimeCore p ((sigmaCore M).subgroupOf M)) ∧
      ∀ {q : ℕ}, q.Prime →
        q ∣ Nat.card (M ⧸ pPrimeCore p M) → q ≤ p := by
  classical
  have hnotAll : ¬ ∀ P : Sylow p M,
      ¬ IsNarrow p (⊤ : Subgroup P) := by
    intro hAll
    exact hpBeta ⟨Fact.out, hAll⟩
  push_neg at hnotAll
  obtain ⟨P, hPnarrow⟩ := hnotAll
  have hbase := narrow_der1_complement_max_pdiv
    (hodd := mFT_odd M) (hsol := mmax_sol hM) P hPnarrow
    (fun _ ↦ mFT_proper_plength1 p (mmax_proper hM))
  refine ⟨hbase.1, ?_, hbase.2⟩
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hSD : S ≤ _root_.commutator M := by
    have hmapped : S.map M.subtype ≤
        (_root_.commutator M).map M.subtype := by
      simpa only [S,
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] using
        Msigma_der1 hM
    exact (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp hmapped
  let SD : Subgroup (_root_.commutator M) :=
    S.subgroupOf (_root_.commutator M)
  have hSDcomp : IsPrimeComplement p (pPrimeCore p SD) :=
    pPrimeCore_isPrimeComplement_of_subgroup hbase.1 SD
  simpa only [S] using
    pPrimeCore_isPrimeComplement_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hSD) hSDcomp

/-- `BGsection10.v: Mbeta_Hall`, Lemma 10.8(a), first part. -/
theorem Mbeta_Hall
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsHall (betaPrimes M) ((betaCore M).subgroupOf M) := by
  classical
  let B : Subgroup M := (betaCore M).subgroupOf M
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hBnormal : B.Normal := by
    simpa [B] using betaCore_normal M
  have hSnormal : S.Normal := by
    simpa [S] using sigmaCore_normal M
  letI : B.Normal := hBnormal
  letI : S.Normal := hSnormal
  have hSHall : IsHall (sigmaPrimes M) S := by
    simpa [S] using Msigma_Hall hM
  have hBcore : B = piCore (betaPrimes M) M := by
    simpa [B, betaCore] using
      primeSetCore_subgroupOf_eq_piCore (betaPrimes M) M
  have hquotBetaCompl :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card (M ⧸ S)) := by
    rw [← S.index_eq_card]
    apply hSHall.isPiNumber_index.mono
    intro r hrNotSigma
    change r ∉ betaPrimes M
    intro hrBeta
    exact hrNotSigma (beta_sub_sigma hM hrBeta)
  have hmapPiCore :
      (piCore (betaPrimes M) S).map S.subtype =
        piCore (betaPrimes M) M :=
    map_piCore_eq_of_quotient_isPiNumber hquotBetaCompl
  constructor
  · rw [natCard_subgroupOf_eq (betaCore_le M)]
    exact betaCore_isPiNumber M
  · intro p hp hpIndex
    show p ∈ (betaPrimes M)ᶜ
    intro hpBeta
    letI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p M := Classical.choice Sylow.nonempty
    have hPS : (P : Subgroup M) ≤ S :=
      isPGroup_le_normal_isHall
        (beta_sub_sigma hM hpBeta) P.isPGroup' hSnormal hSHall
    let PS : Subgroup S := (P : Subgroup M).subgroupOf S
    have hPSPi : PS ≤ piCore (betaPrimes M) S := by
      apply le_piCore_of_le_pPrimeCores
      intro r hr hrNotBeta
      letI : Fact r.Prime := ⟨hr⟩
      have hPSp : IsPGroup p PS := by
        dsimp [PS]
        exact P.isPGroup'.comap_subtype
      have hPSBeta : IsPiNumber (betaPrimes M) (Nat.card PS) :=
        hPSp.isPiNumber_natCard hpBeta
      have hPSprime : IsPPrimeSubgroup r PS :=
        isPPrimeSubgroup_of_isPiNumber_not_mem hPSBeta hrNotBeta
      exact isPPrimeSubgroup_le_normal_primeComplement
        (hHnormal := by infer_instance)
        (beta_max_pdiv hM hrNotBeta).2.1 hPSprime
    have hmapped := Subgroup.map_mono hPSPi (f := S.subtype)
    have hPSmap : PS.map S.subtype = (P : Subgroup M) := by
      simpa [PS] using Subgroup.map_subgroupOf_eq_of_le hPS
    rw [hPSmap, hmapPiCore, ← hBcore] at hmapped
    exact P.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hmapped))

/-- `BGsection10.v: Mbeta_Hall_G`, Lemma 10.8(a), second part. -/
theorem Mbeta_Hall_G
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsHall (betaPrimes M) (betaCore M) := by
  let B : Subgroup M := (betaCore M).subgroupOf M
  have hBHall : IsHall (betaPrimes M) B := by
    simpa [B] using Mbeta_Hall hM
  have hMindexSigma : IsPiNumber (sigmaPrimes M)ᶜ M.index :=
    (Msigma_Hall_G hM).isPiNumber_index.of_dvd
      (Subgroup.index_dvd_of_le (sigmaCore_le M))
  have hMindexBeta : IsPiNumber (betaPrimes M)ᶜ M.index :=
    hMindexSigma.mono (by
      intro p hpNotSigma
      change p ∉ betaPrimes M
      intro hpBeta
      exact hpNotSigma (beta_sub_sigma hM hpBeta))
  constructor
  · exact betaCore_isPiNumber M
  · rw [← Subgroup.map_subgroupOf_eq_of_le (betaCore_le M),
      Subgroup.index_map_subtype]
    exact hBHall.isPiNumber_index.mul hMindexBeta

/-! ### The beta quotient of the derived subgroup -/

/-- `BGsection10.v: Mbeta_quo_nil`, Lemma 10.8(b). -/
theorem Mbeta_quo_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Group.IsNilpotent
      (_root_.commutator M ⧸
        ((betaCore M).subgroupOf M).subgroupOf
          (_root_.commutator M)) := by
  classical
  let B0 : Subgroup M := (betaCore M).subgroupOf M
  let D : Subgroup M := _root_.commutator M
  have hB0D : B0 ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  let B : Subgroup D := B0.subgroupOf D
  have hB0normal : B0.Normal := by
    simpa [B0] using betaCore_normal M
  letI : B0.Normal := hB0normal
  have hBnormal : B.Normal := by
    dsimp [B]
    infer_instance
  letI : B.Normal := hBnormal
  let Q := D ⧸ B
  have hBHallD : IsHall (betaPrimes M) B := by
    constructor
    · dsimp [B]
      rw [natCard_subgroupOf_eq hB0D]
      exact (Mbeta_Hall hM).isPiNumber_card
    · change IsPiNumber (betaPrimes M)ᶜ (B0.relIndex D)
      exact (Mbeta_Hall hM).isPiNumber_index.of_dvd
        (Subgroup.relIndex_dvd_index_of_le hB0D)
  have hQbetaPrime :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card Q) := by
    rw [← B.index_eq_card]
    exact hBHallD.isPiNumber_index
  apply
    ((Group.isNilpotent_of_finite_tfae (G := Q)).out 3 0 rfl rfl).mp
  intro q hq P
  letI : Fact q.Prime := hq
  have hPcore :
      (P : Subgroup Q) ≤ piCore ({q} : Set ℕ) Q := by
    apply le_piCore_of_le_pPrimeCores
    intro r hr hrNotQ
    letI : Fact r.Prime := ⟨hr⟩
    by_cases hrBeta : r ∈ betaPrimes M
    · have hrCard : ¬r ∣ Nat.card Q := by
        intro hrQ
        exact hQbetaPrime hr hrQ hrBeta
      have htopPrime :
          IsPPrimeSubgroup r (⊤ : Subgroup Q) := by
        rw [IsPPrimeSubgroup]
        simpa using hr.coprime_iff_not_dvd.mpr hrCard
      have htopCore :
          (⊤ : Subgroup Q) ≤ pPrimeCore r Q :=
        le_pPrimeCore htopPrime (by infer_instance)
      exact le_top.trans htopCore
    · have hBprime : IsPPrimeSubgroup r B :=
        isPPrimeSubgroup_of_isPiNumber_not_mem
          hBHallD.isPiNumber_card hrBeta
      have hBcore : B ≤ pPrimeCore r D :=
        isPPrimeSubgroup_le_normal_primeComplement
          (hHnormal := by infer_instance)
          (beta_max_pdiv hM hrBeta).1 hBprime
      have hcoreHallQ :
          IsPrimeComplement r (pPrimeCore r Q) := by
        simpa [Q] using
          pPrimeCore_isPrimeComplement_quotient_of_le hBcore
            (beta_max_pdiv hM hrBeta).1
      have hPpi :
          IsPiNumber ({q} : Set ℕ) (Nat.card (P : Subgroup Q)) :=
        P.isPGroup'.isPiNumber_natCard (Set.mem_singleton q)
      have hPprime : IsPPrimeSubgroup r (P : Subgroup Q) :=
        isPPrimeSubgroup_of_isPiNumber_not_mem hPpi hrNotQ
      exact isPPrimeSubgroup_le_normal_primeComplement
        (hHnormal := by infer_instance) hcoreHallQ hPprime
  have hcoreP : IsPGroup q (piCore ({q} : Set ℕ) Q) :=
    isPGroup_of_isPiNumber_singleton
      (piCore_isPiNumber ({q} : Set ℕ))
  have hcoreEq : piCore ({q} : Set ℕ) Q = (P : Subgroup Q) :=
    P.is_maximal' hcoreP hPcore
  rw [← hcoreEq]
  infer_instance

/-- `BGsection10.v: beta'_der1_nil`, Corollary 10.9(a).

Every beta-complement subgroup of the derived subgroup of `M` is
nilpotent. -/
theorem beta'_der1_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hHbetaPrime :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card H))
    (hHD : H ≤ (_root_.commutator M).map M.subtype) :
    Group.IsNilpotent H := by
  classical
  let D : Subgroup M := _root_.commutator M
  let B0 : Subgroup M := (betaCore M).subgroupOf M
  have hB0D : B0 ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  let B : Subgroup D := B0.subgroupOf D
  have hB0normal : B0.Normal := by
    simpa [B0] using betaCore_normal M
  letI : B0.Normal := hB0normal
  have hBnormal : B.Normal := by
    dsimp [B]
    infer_instance
  letI : B.Normal := hBnormal
  have hHM : H ≤ M :=
    hHD.trans (Subgroup.map_subtype_le D)
  let HM : Subgroup M := H.subgroupOf M
  have hHMD : HM ≤ D := by
    intro x hx
    change (x : G) ∈ H at hx
    obtain ⟨y, hy, hyx⟩ := hHD hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  let HD : Subgroup D := HM.subgroupOf D
  have hBcard :
      IsPiNumber (betaPrimes M) (Nat.card B) := by
    dsimp [B]
    rw [natCard_subgroupOf_eq hB0D]
    exact (Mbeta_Hall hM).isPiNumber_card
  have hHDcard :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card HD) := by
    dsimp [HD]
    rw [natCard_subgroupOf_eq hHMD]
    dsimp [HM]
    rw [natCard_subgroupOf_eq hHM]
    exact hHbetaPrime
  have hdis : Disjoint B HD :=
    Subgroup.disjoint_of_coprime_natCard
      (hBcard.coprime_compl hHDcard)
  let Q := D ⧸ B
  let qD : D →* Q := QuotientGroup.mk' B
  let f : HD →* Q := qD.comp HD.subtype
  have hfinj : Function.Injective f := by
    rw [← f.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hfx : f x = 1 := f.mem_ker.mp hx
    change qD (HD.subtype x) = 1 at hfx
    have hxB : (HD.subtype x : D) ∈ B :=
      (QuotientGroup.eq_one_iff (HD.subtype x)).mp hfx
    have hxHD : (HD.subtype x : D) ∈ HD := x.property
    have hxBot : (HD.subtype x : D) ∈ (⊥ : Subgroup D) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hxB, hxHD⟩
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxBot
  letI : Group.IsNilpotent Q := by
    simpa [Q, D, B, B0] using Mbeta_quo_nil hM
  let R : Subgroup Q := f.range
  letI : Group.IsNilpotent R := inferInstance
  let eHD : HD ≃* R := MulEquiv.ofBijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hfinj,
      f.rangeRestrict_surjective⟩
  have hHDnil : Group.IsNilpotent HD :=
    Group.nilpotent_of_mulEquiv eHD.symm
  letI : Group.IsNilpotent HD := hHDnil
  let eHM : HD ≃* HM :=
    Subgroup.subgroupOfEquivOfLe hHMD
  have hHMnil : Group.IsNilpotent HM :=
    Group.nilpotent_of_mulEquiv eHM
  letI : Group.IsNilpotent HM := hHMnil
  let eH : HM ≃* H :=
    Subgroup.subgroupOfEquivOfLe hHM
  exact Group.nilpotent_of_mulEquiv eH

/-- Intrinsic form of `beta'_der1_nil` for subgroups of the maximal
subgroup `M`. -/
private theorem betaPrime_subgroup_der1_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {Y : Subgroup M}
    (hYbetaPrime :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card Y))
    (hYD : Y ≤ _root_.commutator M) :
    Group.IsNilpotent Y := by
  let YG : Subgroup G := Y.map M.subtype
  have hYGbetaPrime :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card YG) := by
    dsimp [YG]
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hYbetaPrime
  have hYGD :
      YG ≤ (_root_.commutator M).map M.subtype := by
    dsimp [YG]
    exact Subgroup.map_mono hYD
  letI : Group.IsNilpotent YG :=
    beta'_der1_nil hM hYGbetaPrime hYGD
  exact Group.nilpotent_of_mulEquiv
    (Y.equivMapOfInjective M.subtype M.subtype_injective).symm

/-- The `{p,q}`-Hall subgroup used in Corollary 10.9(a) can be chosen
nilpotent.  This is the long local construction in the middle of the Coq
proof of `beta'_cent_Sylow`. -/
private theorem exists_betaPair_hall_nilpotent
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpBeta : p ∉ betaPrimes M)
    (hqBeta : q ∉ betaPrimes M)
    {X : Subgroup M} (hXq : IsPGroup q X)
    (hposition :
      (p ≠ q ∧ X ≤ _root_.commutator M) ∨
        p < q) :
    ∃ W : Subgroup M,
      X ≤ W ∧
      W ≤ X ⊔ _root_.commutator M ∧
      IsHall ({p, q} : Set ℕ)
        (W.subgroupOf
          (X ⊔ _root_.commutator M)) ∧
      Group.IsNilpotent W := by
  classical
  let D : Subgroup M := _root_.commutator M
  let XM : Subgroup M := X
  let J : Subgroup M := XM ⊔ D
  have hXMq : IsPGroup q XM := by simpa [XM] using hXq
  have hXMpair :
      IsPiNumber ({p, q} : Set ℕ) (Nat.card XM) :=
    hXMq.isPiNumber_natCard (by simp)
  have hsolJ : IsSolvable J := by
    letI : IsSolvable M := mmax_sol hM
    exact isSolvable_subgroup_of_isSolvable J
  obtain ⟨W, hXW, hWJ, hWHall⟩ :=
    exists_ambient_isHall_ge_of_isSolvable
      (G := M) (K := J) (A := XM) le_sup_left hsolJ
      ({p, q} : Set ℕ) hXMpair
  have hWpair :
      IsPiNumber ({p, q} : Set ℕ) (Nat.card W) := by
    rw [← natCard_subgroupOf_eq hWJ]
    exact hWHall.isPiNumber_card
  have hWbetaPrime :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card W) := by
    intro r hr hrW
    have hrPair : r = p ∨ r = q := by
      simpa using hWpair hr hrW
    rcases hrPair with rfl | rfl
    · exact hpBeta
    · exact hqBeta
  refine ⟨W, hXW, hWJ, hWHall, ?_⟩
  rcases hposition with ⟨_hpq, hXD⟩ | hpq
  · have hXMD : XM ≤ D := by simpa [XM, D] using hXD
    have hWD : W ≤ D := by
      apply hWJ.trans
      dsimp [J]
      exact sup_le hXMD le_rfl
    exact betaPrime_subgroup_der1_nil hM hWbetaPrime hWD
  · let O : Subgroup M := pPrimeCore p M
    let C : Subgroup W := O.subgroupOf W
    have hCnormal : C.Normal := by
      dsimp [C, O]
      infer_instance
    letI : C.Normal := hCnormal
    have hCq : IsPGroup q C := by
      apply isPGroup_of_isPiNumber_singleton
      intro r hr hrC
      have hrW : r ∣ Nat.card W :=
        hrC.trans C.card_subgroup_dvd_card
      have hrPair : r = p ∨ r = q := by
        simpa using hWpair hr hrW
      have hrO : r ∣ Nat.card O :=
        hrC.trans
          (Subgroup.card_comap_dvd_of_injective O W.subtype
            W.subtype_injective)
      have hpNotO : ¬p ∣ Nat.card O := by
        apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
        simpa only [O] using
          (pPrimeCore_coprime_card (G := M) (p := p))
      rcases hrPair with rfl | rfl
      · exact (hpNotO hrO).elim
      · simp
    have hQleC (Q : Sylow q W) : (Q : Subgroup W) ≤ C := by
      let qo : M →* M ⧸ O := QuotientGroup.mk' O
      let f : W →* M ⧸ O := qo.comp W.subtype
      let Qbar : Subgroup (M ⧸ O) := (Q : Subgroup W).map f
      have hQbarq : IsPGroup q Qbar := Q.isPGroup'.map f
      have hQbarCard : Nat.card Qbar = 1 := by
        rcases hQbarq.card_eq_or_dvd with hOne | hqBar
        · exact hOne
        · exfalso
          have hqQuot : q ∣ Nat.card (M ⧸ O) :=
            hqBar.trans Qbar.card_subgroup_dvd_card
          have hqp : q ≤ p := by
            simpa [O] using
              (beta_max_pdiv hM hpBeta).2.2
                (Fact.out : q.Prime) hqQuot
          exact (Nat.not_le_of_gt hpq) hqp
      have hQbarBot : Qbar = ⊥ :=
        Subgroup.card_eq_one.mp hQbarCard
      have hQker : (Q : Subgroup W) ≤ f.ker :=
        (Subgroup.map_eq_bot_iff (Q : Subgroup W)).mp hQbarBot
      intro x hx
      change (x : M) ∈ O
      have hxker := hQker hx
      have hxone : f x = 1 := f.mem_ker.mp hxker
      change qo (x : M) = 1 at hxone
      exact (QuotientGroup.eq_one_iff (x : M)).mp hxone
    let Q0 : Sylow q W := Classical.choice Sylow.nonempty
    have hQ0C : (Q0 : Subgroup W) ≤ C := hQleC Q0
    have hCeq : C = (Q0 : Subgroup W) :=
      Q0.is_maximal' hCq hQ0C
    have hCindex : ¬q ∣ C.index := by
      rw [hCeq]
      exact Q0.not_dvd_index

    let I : Subgroup W := D.subgroupOf W
    have hInormal : I.Normal := by
      dsimp [I, D]
      infer_instance
    letI : I.Normal := hInormal
    let qD : M →* M ⧸ D := QuotientGroup.mk' D
    have hDmap : D.map qD = ⊥ := by
      apply (Subgroup.map_eq_bot_iff D).mpr
      rw [QuotientGroup.ker_mk']
    have hJmap : J.map qD = XM.map qD := by
      dsimp [J]
      rw [Subgroup.map_sup, hDmap, sup_bot_eq]
    have hWmap : W.map qD ≤ XM.map qD := by
      calc
        W.map qD ≤ J.map qD := Subgroup.map_mono hWJ
        _ = XM.map qD := hJmap
    have hWmapq : IsPGroup q (W.map qD) :=
      (hXMq.map qD).to_le hWmap
    have hWIq : IsPGroup q (W ⧸ I) := by
      simpa [I, qD] using
        hWmapq.of_equiv
          (subgroupQuotientEquivImage D W).symm

    let IW : Subgroup M := I.map W.subtype
    have hIWD : IW ≤ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hIbetaPrime :
        IsPiNumber (betaPrimes M)ᶜ (Nat.card I) :=
      hWbetaPrime.of_dvd I.card_subgroup_dvd_card
    have hIWbetaPrime :
        IsPiNumber (betaPrimes M)ᶜ (Nat.card IW) := by
      dsimp [IW]
      rw [Subgroup.card_map_of_injective W.subtype_injective]
      exact hIbetaPrime
    letI : Group.IsNilpotent IW :=
      betaPrime_subgroup_der1_nil hM hIWbetaPrime hIWD
    let eI : I ≃* IW :=
      I.equivMapOfInjective W.subtype W.subtype_injective
    letI : Group.IsNilpotent I :=
      Group.nilpotent_of_mulEquiv eI.symm

    have hpIindex : ¬p ∣ I.index := by
      intro hpIndex
      have hpQuot : p ∣ Nat.card (W ⧸ I) := by
        simpa only [I.index_eq_card] using hpIndex
      have hpq' : p = q := Set.mem_singleton_iff.mp
        (hWIq.isPiNumber_natCard (Set.mem_singleton q)
          (Fact.out : p.Prime) hpQuot)
      exact (Nat.ne_of_lt hpq) hpq'
    let PI : Sylow p I := Classical.choice Sylow.nonempty
    have hpcoreEq : pCore p I = (PI : Subgroup I) :=
      pCore_eq_sylow_of_isNilpotent PI
    have hpcoreIndex : ¬p ∣ (pCore p I).index := by
      rw [hpcoreEq]
      exact PI.not_dvd_index
    let P0 : Subgroup W := (pCore p I).map I.subtype
    have hP0p : IsPGroup p P0 := by
      dsimp [P0]
      exact pCore_isPGroup.map I.subtype
    have hP0index : ¬p ∣ P0.index := by
      dsimp [P0]
      rw [Subgroup.index_map_subtype]
      exact (Fact.out : p.Prime).not_dvd_mul
        hpcoreIndex hpIindex
    have hP0normal : P0.Normal := by
      dsimp [P0]
      infer_instance
    letI : P0.Normal := hP0normal
    exact isNilpotent_of_two_prime_normal_sylows
      hWpair hP0p hP0index hP0normal hCq hCindex hCnormal

/-! ### Bender--Glauberman Corollary 10.9 -/

/-- Homomorphisms preserve elementwise centralizing relations between
subgroups. -/
private theorem map_le_centralizer_map
    {K L : Type*} [Group K] [Group L]
    {f : K →* L} {A B : Subgroup K}
    (h : A ≤ Subgroup.centralizer (B : Set K)) :
    A.map f ≤ Subgroup.centralizer (B.map f : Set L) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  simpa only [map_mul] using congrArg f
    (Subgroup.mem_centralizer_iff.mp (h ha) b hb)

/-- The first two conclusions of the source proof of
`beta'_cent_Sylow`, extracted from its nilpotent Hall subgroup. -/
private theorem betaCent_a1_a2_from_hall
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q)
    (X W : Subgroup M)
    (hXq : IsPGroup q X)
    (hXW : X ≤ W)
    (hWJ : W ≤ X ⊔ _root_.commutator M)
    (hWHall : IsHall ({p, q} : Set ℕ)
      (W.subgroupOf (X ⊔ _root_.commutator M)))
    (hWnil : Group.IsNilpotent W) :
    (∃ PS : Sylow p ((sigmaCore M).subgroupOf M),
      X ≤ Subgroup.centralizer
        ((((PS : Subgroup ((sigmaCore M).subgroupOf M)).map
          ((sigmaCore M).subgroupOf M).subtype) : Subgroup M) : Set M)) ∧
    (p ∈ alphaPrimes M →
      centralizerWithin M (X.map M.subtype) ∈
        minSimple_uniq_max_groups (G := G)) := by
  classical
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  let D : Subgroup M := _root_.commutator M
  let J : Subgroup M := X ⊔ D
  change (∃ PS : Sylow p S, X ≤ Subgroup.centralizer
      (((PS : Subgroup S).map S.subtype : Subgroup M) : Set M)) ∧ _
  have hSD : S ≤ D := by
    intro x hx
    change (x : G) ∈ sigmaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Msigma_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  have hSJ : S ≤ J := hSD.trans le_sup_right
  have hXJ : X ≤ J := le_sup_left
  have hWJ' : W ≤ J := by simpa only [J, D] using hWJ
  have hWHall' : IsHall ({p, q} : Set ℕ) (W.subgroupOf J) := by
    simpa only [J, D] using hWHall
  let WJ : Subgroup J := W.subgroupOf J
  let XJ : Subgroup J := X.subgroupOf J
  have hXJWJ : XJ ≤ WJ := by
    intro x hx
    change (x : M) ∈ W
    exact hXW hx
  let XWJ : Subgroup WJ := XJ.subgroupOf WJ
  letI : Group.IsNilpotent W := hWnil
  let eWJ : WJ ≃* W := Subgroup.subgroupOfEquivOfLe hWJ'
  letI : Group.IsNilpotent WJ :=
    Group.nilpotent_of_mulEquiv eWJ.symm
  let eXJ : XJ ≃* X := Subgroup.subgroupOfEquivOfLe hXJ
  have hXJq : IsPGroup q XJ := hXq.of_equiv eXJ.symm
  let eXWJ : XWJ ≃* XJ := Subgroup.subgroupOfEquivOfLe hXJWJ
  have hXWJq : IsPGroup q XWJ := hXJq.of_equiv eXWJ.symm
  have ha1 : ∃ PS : Sylow p S, X ≤ Subgroup.centralizer
      (((PS : Subgroup S).map S.subtype : Subgroup M) : Set M) := by
    let R : Sylow p WJ := Classical.choice Sylow.nonempty
    have hRcore : (R : Subgroup WJ) = pCore p WJ :=
      (pCore_eq_sylow_of_isNilpotent R).symm
    have hXWJlePrime : XWJ ≤ pPrimeCore p WJ :=
      hXWJq.le_pCore_of_isNilpotent |>.trans
        (pCore_le_pPrimeCore_of_ne (G := WJ) (p := p) (q := q) hpq)
    have hPrimeCentCore : pPrimeCore p WJ ≤
        Subgroup.centralizer (pCore p WJ : Set WJ) :=
      Subgroup.le_centralizer_iff.mp
        (pCore_le_centralizer_pPrimeCore (G := WJ) p)
    have hXWJcentR : XWJ ≤
        Subgroup.centralizer ((R : Subgroup WJ) : Set WJ) := by
      simpa only [hRcore] using
        hXWJlePrime.trans hPrimeCentCore
    obtain ⟨T, hT⟩ := exists_sylow_eq_map_of_sylow_hall
      (Fact.out : p.Prime) hWHall' (by simp) R
    have hXJcentT : XJ ≤
        Subgroup.centralizer ((T : Subgroup J) : Set J) := by
      rw [hT]
      have hm := map_le_centralizer_map
        (f := WJ.subtype) hXWJcentR
      simpa only [XWJ,
        Subgroup.map_subgroupOf_eq_of_le hXJWJ] using hm
    have hSnormal : S.Normal := by
      simpa only [S] using sigmaCore_normal M
    letI : S.Normal := hSnormal
    let SJ : Subgroup J := S.subgroupOf J
    letI : SJ.Normal := by
      dsimp only [SJ]
      infer_instance
    let PJ : Sylow p SJ := normalIntersectionSylow T SJ
    have hPJleT :
        (PJ : Subgroup SJ).map SJ.subtype ≤ (T : Subgroup J) := by
      dsimp only [PJ]
      rw [map_normalIntersectionSylow_eq_inf]
      exact inf_le_left
    have hXJcentPJ : XJ ≤ Subgroup.centralizer
        (((PJ : Subgroup SJ).map SJ.subtype : Subgroup J) : Set J) :=
      hXJcentT.trans (Subgroup.centralizer_le hPJleT)
    have hXcentPJ : X ≤ Subgroup.centralizer
        ((((PJ : Subgroup SJ).map SJ.subtype).map J.subtype :
          Subgroup M) : Set M) := by
      have hm := map_le_centralizer_map
        (f := J.subtype) hXJcentPJ
      simpa only [XJ,
        Subgroup.map_subgroupOf_eq_of_le hXJ] using hm
    let eSJ : SJ ≃* S := Subgroup.subgroupOfEquivOfLe hSJ
    let PS : Sylow p S :=
      PJ.mapSurjective (f := eSJ.toMonoidHom) eSJ.surjective
    have hPSmap : (PS : Subgroup S).map S.subtype =
        ((PJ : Subgroup SJ).map SJ.subtype).map J.subtype := by
      change (((PJ.mapSurjective (f := eSJ.toMonoidHom)
        eSJ.surjective : Sylow p S) : Subgroup S).map S.subtype) = _
      rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
      apply congrArg
        (fun f : SJ →* M => (PJ : Subgroup SJ).map f)
      ext x
      rfl
    exact ⟨PS, by rw [hPSmap]; exact hXcentPJ⟩
  refine ⟨ha1, ?_⟩
  intro hpAlpha
  rcases ha1 with ⟨PS, hPScent⟩
  have hSHall : IsHall (sigmaPrimes M) S := by
    simpa only [S] using Msigma_Hall hM
  obtain ⟨PM, hPM⟩ := exists_sylow_eq_map_of_sylow_hall
    (Fact.out : p.Prime) hSHall (alpha_sub_sigma hM hpAlpha) PS
  let PG : Subgroup G := (PM : Subgroup M).map M.subtype
  have hPGM : PG ≤ M := Subgroup.map_subtype_le _
  have hXcentPM : X ≤
      Subgroup.centralizer ((PM : Subgroup M) : Set M) := by
    rw [hPM]
    exact hPScent
  have hXGcentPG : X.map M.subtype ≤
      Subgroup.centralizer (PG : Set G) :=
    map_le_centralizer_map (f := M.subtype) hXcentPM
  have hPGC : PG ≤ centralizerWithin M (X.map M.subtype) :=
    le_inf hPGM (Subgroup.le_centralizer_iff.mp hXGcentPG)
  have hPGrank : HasElementaryAbelianRankAtLeast p 3 PG := by
    simpa only [PG] using
      sylow_has_rank_three_of_mem_alpha hpAlpha PM
  have hPGuniq : PG ∈ minSimple_uniq_max_groups (G := G) :=
    rank3_Uniqueness (lt_of_le_of_lt hPGM (mmax_proper hM))
      ⟨p, Fact.out, hPGrank⟩
  exact uniq_mmaxS hPGC
    (lt_of_le_of_lt
      (centralizerWithin_le_left M (X.map M.subtype))
      (mmax_proper hM)) hPGuniq

/-- The Frattini--focal conclusion of the source proof of
`beta'_cent_Sylow`, extracted from the same nilpotent Hall subgroup. -/
private theorem betaCent_a3_from_hall
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q)
    (hpBeta : p ∉ betaPrimes M)
    (X W : Subgroup M)
    (hXW : X ≤ W)
    (hWJ : W ≤ X ⊔ _root_.commutator M)
    (hWHall : IsHall ({p, q} : Set ℕ)
      (W.subgroupOf (X ⊔ _root_.commutator M)))
    (hWnil : Group.IsNilpotent W)
    (hXsyl : IsSylowSubgroupOf q X (_root_.commutator M)) :
    ∃ PD : Sylow p (_root_.commutator M),
      (PD : Subgroup (_root_.commutator M)).map
          (_root_.commutator M).subtype ≤
        (_root_.commutator (Subgroup.normalizer (X : Set M))).map
          (Subgroup.normalizer (X : Set M)).subtype := by
  classical
  let D : Subgroup M := _root_.commutator M
  let J : Subgroup M := X ⊔ D
  let U : Subgroup M := Subgroup.normalizer (X : Set M)
  change ∃ PD : Sylow p D,
    (PD : Subgroup D).map D.subtype ≤
      (_root_.commutator U).map U.subtype
  have hWJ' : W ≤ J := by simpa only [J, D] using hWJ
  have hWHall' : IsHall ({p, q} : Set ℕ) (W.subgroupOf J) := by
    simpa only [J, D] using hWHall
  have hXsyl' : IsSylowSubgroupOf q X D := by
    simpa only [D] using hXsyl
  let B0 : Subgroup M := (betaCore M).subgroupOf M
  have hB0D : B0 ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  have hB0normal : B0.Normal := by
    simpa [B0] using betaCore_normal M
  letI : B0.Normal := hB0normal
  have hDnormal : D.Normal := by
    dsimp only [D]
    infer_instance
  letI : D.Normal := hDnormal
  obtain ⟨PX, hX_eq⟩ := hXsyl'
  have hXD : X ≤ D := by
    rw [hX_eq]
    exact Subgroup.map_subtype_le _
  let N : Subgroup M := B0 ⊔ X
  have hNnormal : N.Normal := by
    dsimp only [N]
    exact normal_sup_of_sylow_quotient_nilpotent
      (B := B0) (D := D) (X := X) hB0D hXD
      ⟨PX, hX_eq⟩ (by
        simpa [B0, D] using Mbeta_quo_nil hM)
  letI : N.Normal := hNnormal
  have hND : N ≤ D := by
    dsimp only [N]
    exact sup_le hB0D hXD
  let ND : Subgroup D := N.subgroupOf D
  have hPXND : (PX : Subgroup D) ≤ ND := by
    intro x hx
    change (x : M) ∈ N
    have hxX : (x : M) ∈ X := by
      rw [hX_eq]
      exact Subgroup.mem_map_of_mem D.subtype hx
    exact (show X ≤ N from by
      dsimp only [N]
      exact le_sup_right) hxX
  let XND : Sylow q ND := PX.subtype hPXND
  let eND : ND ≃* N := Subgroup.subgroupOfEquivOfLe hND
  let XN : Sylow q N :=
    XND.mapSurjective (f := eND.toMonoidHom) eND.surjective
  have hXNmap : (XN : Subgroup N).map N.subtype = X := by
    simp only [XN, Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : N.subtype.comp eND.toMonoidHom =
        D.subtype.comp ND.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map]
    dsimp only [XND]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hPXND]
    exact hX_eq.symm
  have hfrattini : U ⊔ N = ⊤ := by
    simpa [U, hXNmap] using XN.normalizer_sup_eq_top
  have hXU : X ≤ U := by
    dsimp only [U]
    exact Subgroup.le_normalizer
  have hBU : B0 ⊔ U = ⊤ := by
    apply top_unique
    rw [← hfrattini]
    apply sup_le
    · exact le_sup_right
    · dsimp only [N]
      exact sup_le le_sup_left (hXU.trans le_sup_right)
  have hJD : J = D := by
    dsimp only [J]
    exact sup_eq_right.mpr hXD
  have hWD : W ≤ D := by
    simpa only [hJD] using hWJ'
  have hWHallD : IsHall ({p, q} : Set ℕ)
      (W.subgroupOf D) := by
    rw [← hJD]
    exact hWHall'
  let WD : Subgroup D := W.subgroupOf D
  have hWDHall : IsHall ({p, q} : Set ℕ) WD := by
    simpa only [WD] using hWHallD
  let eWD : WD ≃* W := Subgroup.subgroupOfEquivOfLe hWD
  letI : Group.IsNilpotent W := hWnil
  letI : Group.IsNilpotent WD :=
    Group.nilpotent_of_mulEquiv eWD.symm
  let PW : Sylow p WD := Classical.choice Sylow.nonempty
  obtain ⟨PD, hPD⟩ := exists_sylow_eq_map_of_sylow_hall
    (Fact.out : p.Prime) hWDHall (by simp) PW
  have hPXWD : (PX : Subgroup D) ≤ WD := by
    intro x hx
    change (x : M) ∈ W
    apply hXW
    rw [hX_eq]
    exact Subgroup.mem_map_of_mem D.subtype hx
  let QW : Sylow q WD := PX.subtype hPXWD
  have hdis : Disjoint (PW : Subgroup WD) (QW : Subgroup WD) :=
    IsPGroup.disjoint_of_ne p q hpq _ _
      PW.isPGroup' QW.isPGroup'
  have hcomm := Subgroup.commute_of_normal_of_disjoint
    (PW : Subgroup WD) (QW : Subgroup WD)
    (by infer_instance) (by infer_instance) hdis
  let P0 : Subgroup M := (PD : Subgroup D).map D.subtype
  have hP0cent : P0 ≤ Subgroup.centralizer (X : Set M) := by
    rintro _ ⟨xd, hxd, rfl⟩
    rw [hPD] at hxd
    rcases hxd with ⟨xw, hxw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yd : D := ⟨y, hXD hy⟩
    have hyd : yd ∈ (PX : Subgroup D) := by
      have hyMap : y ∈ (PX : Subgroup D).map D.subtype := by
        rw [← hX_eq]
        exact hy
      rcases hyMap with ⟨z, hz, hzy⟩
      have hzyd : z = yd := by
        apply Subtype.ext
        simpa [yd] using hzy
      exact hzyd ▸ hz
    let yw : WD := ⟨yd, hXW hy⟩
    have hyw : yw ∈ (QW : Subgroup WD) := by
      dsimp only [QW]
      rw [Sylow.coe_subtype]
      exact hyd
    have hc := congrArg (fun z : WD => (((z : D) : M)))
      (hcomm xw yw hxw hyw).eq.symm
    simpa [yw, yd] using hc
  have hP0U : P0 ≤ U := by
    dsimp only [U]
    exact hP0cent.trans
      (Subgroup.centralizer_le_normalizer (X : Set M))
  have hB0beta : IsPiNumber (betaPrimes M) (Nat.card B0) := by
    simpa [B0] using (Mbeta_Hall hM).isPiNumber_card
  have hP0p : IsPGroup p P0 := by
    dsimp only [P0]
    exact PD.isPGroup'.map D.subtype
  have hP0betaCompl :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card P0) :=
    hP0p.isPiNumber_natCard
      (show p ∈ (betaPrimes M)ᶜ from hpBeta)
  have hcop : (Nat.card B0).Coprime (Nat.card P0) :=
    hB0beta.coprime_compl hP0betaCompl
  have hfocal : P0 ⊓ _root_.commutator M = P0 ⊓ ⁅U, U⁆ :=
    Section06.pprod_focal_coprime
      (K := B0) (U := U) (H := P0) hBU hP0U hcop
  have hP0D : P0 ≤ _root_.commutator M := by
    change (PD : Subgroup D).map D.subtype ≤ D
    exact Subgroup.map_subtype_le _
  have hP0derU : P0 ≤ ⁅U, U⁆ := by
    intro x hx
    have hxleft : x ∈ P0 ⊓ _root_.commutator M :=
      ⟨hx, hP0D hx⟩
    rw [hfocal] at hxleft
    exact hxleft.2
  have hUder : (_root_.commutator U).map U.subtype = ⁅U, U⁆ := by
    rw [map_commutator_eq, U.range_subtype]
  refine ⟨PD, ?_⟩
  rw [hUder]
  exact hP0derU

/-- `BGsection10.v: beta'_cent_Sylow`, Corollary 10.9(a).

The source subgroup `X \le M` is represented intrinsically as a subgroup
of `M`.  The three conclusions respectively give a centralized Sylow
subgroup of the sigma core, uniqueness of `C_M(X)` at an alpha prime, and
a Sylow subgroup of `M'` contained in `N_M(X)'`. -/
theorem beta'_cent_Sylow
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpBeta : p ∉ betaPrimes M)
    (hqBeta : q ∉ betaPrimes M)
    {X : Subgroup M}
    (hXq : IsPGroup q X)
    (hposition :
      (p ≠ q ∧ X ≤ _root_.commutator M) ∨ p < q) :
    (∃ PS : Sylow p ((sigmaCore M).subgroupOf M),
      X ≤ Subgroup.centralizer
        ((((PS : Subgroup ((sigmaCore M).subgroupOf M)).map
          ((sigmaCore M).subgroupOf M).subtype) : Subgroup M) : Set M)) ∧
    (p ∈ alphaPrimes M →
      centralizerWithin M (X.map M.subtype) ∈
        minSimple_uniq_max_groups (G := G)) ∧
    (IsSylowSubgroupOf q X (_root_.commutator M) →
      ∃ PD : Sylow p (_root_.commutator M),
        (PD : Subgroup (_root_.commutator M)).map
            (_root_.commutator M).subtype ≤
          (_root_.commutator
              (Subgroup.normalizer (X : Set M))).map
            (Subgroup.normalizer (X : Set M)).subtype) := by
  classical
  have hpq : p ≠ q := hposition.elim
    (fun h ↦ h.1) (fun h ↦ Nat.ne_of_lt h)
  obtain ⟨W, hXW, hWJ, hWHall, hWnil⟩ :=
    exists_betaPair_hall_nilpotent hM hpBeta hqBeta hXq hposition
  have h12 := betaCent_a1_a2_from_hall
    hM hpq X W hXq hXW hWJ hWHall hWnil
  refine ⟨h12.1, h12.2, ?_⟩
  intro hXsyl
  exact betaCent_a3_from_hall
    hM hpq hpBeta X W hXW hWJ hWHall hWnil hXsyl

/-- `BGsection10.v: nonuniq_norm_Sylow_pprod`, Corollary 10.9(b).

If two distinct maximal subgroups contain the normalizer of an ambient
Sylow subgroup, their intersection together with the beta core generates
`M`, and the alpha and beta prime sets of `M` coincide. -/
theorem nonuniq_norm_Sylow_pprod
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hne : H ≠ M)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p G)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H ⊓ M) :
    betaCore M ⊔ (H ⊓ M) = M ∧
      alphaPrimes M = betaPrimes M := by
  classical
  have hSM : (S : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans (hN.trans inf_le_right)
  have hSH : (S : Subgroup G) ≤ H :=
    Subgroup.le_normalizer.trans (hN.trans inf_le_left)
  let SM : Sylow p M := S.subtype hSM
  have hSMmap : (SM : Subgroup M).map M.subtype =
      (S : Subgroup G) := by
    dsimp only [SM]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSM]
  have hpSigma : p ∈ sigmaPrimes M := by
    refine ⟨Fact.out, SM, ?_⟩
    simpa only [ambientSylow, hSMmap] using
      hN.trans inf_le_right
  have hpNotAlpha : p ∉ alphaPrimes M := by
    intro hpAlpha
    have hRankSM :=
      sylow_has_rank_three_of_mem_alpha hpAlpha SM
    have hRankS : HasElementaryAbelianRankAtLeast p 3
        (S : Subgroup G) := by
      simpa only [hSMmap] using hRankSM
    have hSuniq : (S : Subgroup G) ∈
        minSimple_uniq_max_groups (G := G) :=
      rank3_Uniqueness
        (mFT_pgroup_proper (S : Subgroup G) S.isPGroup')
        ⟨p, Fact.out, hRankS⟩
    have hSfamily :
        minSimple_max_groups_of (G := G) ((S : Subgroup G) : Set G) =
          {M} :=
      def_uniq_mmax hSuniq hM hSM
    have hHM : H = M := eq_uniq_mmax hSfamily hH hSH
    exact hne hHM
  have hpNotBeta : p ∉ betaPrimes M := fun hpBeta ↦
    hpNotAlpha (beta_sub_alpha M hpBeta)

  let S0 : Subgroup M := (sigmaCore M).subgroupOf M
  have hS0normal : S0.Normal := by
    simpa [S0] using sigmaCore_normal M
  have hS0Hall : IsHall (sigmaPrimes M) S0 := by
    simpa [S0] using Msigma_Hall hM
  have hSMS0 : (SM : Subgroup M) ≤ S0 :=
    isPGroup_le_normal_isHall hpSigma SM.isPGroup'
      hS0normal hS0Hall
  have hS0der : S0 ≤ _root_.commutator M := by
    have hmapped : S0.map M.subtype ≤
        (_root_.commutator M).map M.subtype := by
      simpa only [S0,
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] using
        Msigma_der1 hM
    exact (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp hmapped
  have hSMder : (SM : Subgroup M) ≤ _root_.commutator M :=
    hSMS0.trans hS0der

  let B0 : Subgroup M := (betaCore M).subgroupOf M
  let D : Subgroup M := _root_.commutator M
  have hB0D : B0 ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  have hB0normal : B0.Normal := by
    simpa [B0] using betaCore_normal M
  letI : B0.Normal := hB0normal
  have hDnormal : D.Normal := by
    dsimp only [D]
    infer_instance
  letI : D.Normal := hDnormal
  have hSMder' : (SM : Subgroup M) ≤ D := by
    simpa only [D] using hSMder
  let SD : Sylow p D := SM.subtype hSMder'
  have hSDmap : (SD : Subgroup D).map D.subtype =
      (SM : Subgroup M) := by
    dsimp only [SD]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSMder']
  have hSMsylD : IsSylowSubgroupOf p (SM : Subgroup M) D :=
    ⟨SD, hSDmap.symm⟩
  let N0 : Subgroup M := B0 ⊔ (SM : Subgroup M)
  have hN0normal : N0.Normal := by
    dsimp only [N0]
    exact normal_sup_of_sylow_quotient_nilpotent
      (B := B0) (D := D) (X := (SM : Subgroup M))
      hB0D hSMder' hSMsylD (by
        simpa [B0, D] using Mbeta_quo_nil hM)
  letI : N0.Normal := hN0normal
  have hSMN0 : (SM : Subgroup M) ≤ N0 := by
    dsimp only [N0]
    exact le_sup_right
  let SN : Sylow p N0 := SM.subtype hSMN0
  have hSNmap : (SN : Subgroup N0).map N0.subtype =
      (SM : Subgroup M) := by
    dsimp only [SN]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSMN0]
  let U : Subgroup M :=
    Subgroup.normalizer ((SM : Subgroup M) : Set M)
  have hUN0 : U ⊔ N0 = ⊤ := by
    simpa [U, hSNmap] using SN.normalizer_sup_eq_top
  have hSMU : (SM : Subgroup M) ≤ U := by
    dsimp only [U]
    exact Subgroup.le_normalizer
  have hBU : B0 ⊔ U = ⊤ := by
    apply top_unique
    rw [← hUN0]
    apply sup_le
    · exact le_sup_right
    · dsimp only [N0]
      exact sup_le le_sup_left (hSMU.trans le_sup_right)
  let HM : Subgroup M := H.subgroupOf M
  have hUHM : U ≤ HM := by
    intro x hx
    change (x : G) ∈ H
    have hxMap : (x : G) ∈ U.map M.subtype :=
      ⟨x, hx, rfl⟩
    have hUGnormalizer : U.map M.subtype ≤
        Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      calc
        U.map M.subtype ≤ Subgroup.normalizer
            ((SM : Subgroup M).map M.subtype : Set G) :=
          (SM : Subgroup M).le_normalizer_map M.subtype
        _ = Subgroup.normalizer ((S : Subgroup G) : Set G) := by
          rw [hSMmap]
    exact (hN (hUGnormalizer hxMap)).1
  have hBHM : B0 ⊔ HM = ⊤ := by
    apply top_unique
    rw [← hBU]
    exact sup_le le_sup_left (hUHM.trans le_sup_right)
  have hBmap : B0.map M.subtype = betaCore M := by
    dsimp only [B0]
    exact Subgroup.map_subgroupOf_eq_of_le (betaCore_le M)
  have hHMmap : HM.map M.subtype = H ⊓ M := by
    dsimp only [HM]
    exact Subgroup.subgroupOf_map_subtype H M
  have htopMap : (⊤ : Subgroup M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hprod : betaCore M ⊔ (H ⊓ M) = M := by
    calc
      betaCore M ⊔ (H ⊓ M) =
          B0.map M.subtype ⊔ HM.map M.subtype := by
        rw [hBmap, hHMmap]
      _ = (B0 ⊔ HM).map M.subtype :=
        (Subgroup.map_sup B0 HM M.subtype).symm
      _ = (⊤ : Subgroup M).map M.subtype := by rw [hBHM]
      _ = M := htopMap

  refine ⟨hprod, Set.Subset.antisymm ?_ (beta_sub_alpha M)⟩
  intro q hqAlpha
  by_contra hqBeta
  letI : Fact q.Prime := ⟨hqAlpha.1⟩
  have hqp : q ≠ p := by
    intro hqp
    subst q
    exact hpNotAlpha hqAlpha
  have hcent := (beta'_cent_Sylow
    (p := q) (q := p) hM hqBeta hpNotBeta SM.isPGroup'
      (Or.inl ⟨hqp, hSMder⟩)).2.1 hqAlpha
  let C : Subgroup G :=
    centralizerWithin M ((SM : Subgroup M).map M.subtype)
  have hCuniq : C ∈ minSimple_uniq_max_groups (G := G) := by
    simpa only [C] using hcent
  have hCM : C ≤ M := by
    dsimp only [C]
    exact centralizerWithin_le_left M
      ((SM : Subgroup M).map M.subtype)
  have hCH : C ≤ H := by
    dsimp only [C, centralizerWithin]
    calc
      M ⊓ Subgroup.centralizer
            (((SM : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤
          Subgroup.centralizer
            (((SM : Subgroup M).map M.subtype : Subgroup G) : Set G) :=
        inf_le_right
      _ ≤ Subgroup.normalizer
            (((SM : Subgroup M).map M.subtype : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _
      _ = Subgroup.normalizer ((S : Subgroup G) : Set G) := by
        rw [hSMmap]
      _ ≤ H := hN.trans inf_le_left
  have hCfamily :
      minSimple_max_groups_of (G := G) (C : Set G) = {M} :=
    def_uniq_mmax hCuniq hM hCM
  have hHM : H = M := eq_uniq_mmax hCfamily hH hCH
  exact hne hHM

end

end Submission.OddOrder.BG.Section10
