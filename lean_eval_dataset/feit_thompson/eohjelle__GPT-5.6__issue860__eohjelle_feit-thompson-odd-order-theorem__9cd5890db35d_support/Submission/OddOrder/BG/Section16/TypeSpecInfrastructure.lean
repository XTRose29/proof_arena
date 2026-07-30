import Submission.OddOrder.BG.Section16.TypesAndSupport
import Submission.OddOrder.BG.Section16.SummaryABC

/-!
# Infrastructure for the Section 16 type specification

This dependency-first module collects the subgroup, Hall, Sylow, and
semidirect-product transports used by the proof identifying `FTtype` with the
five semantic type predicates.  They are intentionally accessible to the
later proof phases rather than hidden as file-local implementation details.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

namespace TypeSpecInternal

theorem secondDerived_le_derived16 (M : Subgroup G) :
    secondDerivedWithin M ≤ derivedWithin M := by
  change (_root_.commutator (derivedWithin M)).map
      (derivedWithin M).subtype ≤ derivedWithin M
  exact Subgroup.map_subtype_le _

theorem isHall_subgroupOf_intermediate16
    {A B : Subgroup G} (hAB : A ≤ B) {pi : Set ℕ}
    (hA : IsHall pi A) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · simpa [MathlibSupport.natCard_subgroupOf_eq hAB] using
      hA.isPiNumber_card
  · exact hA.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hAB)

/-- Restrict a Hall subgroup through one stage of an ambient subgroup chain. -/
theorem isHall_subgroupOf_chain16
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C) {pi : Set ℕ}
    (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · simpa [MathlibSupport.natCard_subgroupOf_eq hAB,
      MathlibSupport.natCard_subgroupOf_eq (hAB.trans hBC)] using
      hA.isPiNumber_card
  · apply hA.isPiNumber_index.of_dvd
    have hACBC : A.subgroupOf C ≤ B.subgroupOf C :=
      Subgroup.subgroupOf_mono C hAB
    have hdvd := Subgroup.relIndex_dvd_index_of_le hACBC
    rw [Subgroup.relIndex_subgroupOf (H := A) hBC] at hdvd
    exact hdvd

theorem hall_of_le_hall_of_hall16
    {A B C : Subgroup G} {pi rho : Set ℕ}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (hA : IsHall pi (A.subgroupOf B))
    (hB : IsHall rho (B.subgroupOf C))
    (hpi : pi ⊆ rho) :
    IsHall pi (A.subgroupOf C) := by
  constructor
  · simpa [MathlibSupport.natCard_subgroupOf_eq hAB,
      MathlibSupport.natCard_subgroupOf_eq (hAB.trans hBC)] using
      hA.isPiNumber_card
  · have hACBC : A.subgroupOf C ≤ B.subgroupOf C :=
      Subgroup.subgroupOf_mono C hAB
    rw [← Subgroup.relIndex_mul_index hACBC]
    apply IsPiNumber.mul
    · rw [Subgroup.relIndex_subgroupOf (H := A) hBC]
      exact hA.isPiNumber_index
    · exact IsPiNumber.mono (pi := rhoᶜ) (rho := piᶜ)
        (fun _ hpNotRho hpPi ↦ hpNotRho (hpi hpPi))
        hB.isPiNumber_index

theorem semidirect_left_isHall_compl16
    {N H K : Subgroup G} {pi : Set ℕ}
    (hsd : IsInternalSemidirectProductIn N H K)
    (hH : IsHall pi (H.subgroupOf K)) :
    IsHall piᶜ (N.subgroupOf K) := by
  constructor
  · rw [← hsd.2.2.2.index_eq_card]
    exact hH.isPiNumber_index
  · rw [hsd.2.2.2.symm.index_eq_card]
    simpa only [compl_compl] using hH.isPiNumber_card

theorem semidirect_right_eq_bot_iff_left_eq_ambient16
    {A B K : Subgroup G}
    (h : IsInternalSemidirectProductIn A B K) :
    B = ⊥ ↔ A = K := by
  constructor
  · intro hB
    apply le_antisymm h.1
    have hsup := h.2.2.2.sup_eq_top
    rw [hB, Subgroup.bot_subgroupOf, sup_bot_eq] at hsup
    exact Subgroup.subgroupOf_eq_top.mp hsup
  · intro hA
    have hcomp := h.2.2.2
    rw [hA, Subgroup.subgroupOf_self] at hcomp
    have hBsub : B.subgroupOf K = ⊥ :=
      Subgroup.isComplement'_top_left.mp hcomp
    have hdisjoint : Disjoint B K :=
      Subgroup.subgroupOf_eq_bot.mp hBsub
    apply le_antisymm
    · exact (le_inf le_rfl h.2.1).trans hdisjoint.le_bot
    · exact bot_le

theorem exists_sylow_eq_map_of_sylow_hall16
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp only [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

theorem exists_ambient_sylow_eq_of_sylow_hall16
    {K H : Subgroup G} {pi : Set ℕ} {p : ℕ}
    (hp : p.Prime) (hKH : K ≤ H)
    (hKHall : IsHall pi (K.subgroupOf H))
    (hpPi : p ∈ pi) (P : Sylow p K) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype =
        (P : Subgroup K).map K.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let KH : Subgroup H := K.subgroupOf H
  let e : K ≃* KH := (Subgroup.subgroupOfEquivOfLe hKH).symm
  let PKH : Sylow p KH :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall16 hp hKHall hpPi PKH
  refine ⟨Q, ?_⟩
  rw [hQ, Subgroup.map_map]
  simp only [PKH, Sylow.coe_mapSurjective, Subgroup.map_map]
  apply congrArg (fun f : K →* G ↦ (P : Subgroup K).map f)
  ext x
  rfl

theorem not_rankTwo_of_cyclic_sylow16
    {H P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPH : IsSylowSubgroupOf p P H) (hcyc : IsCyclic P) :
    ¬ HasElementaryAbelianRankAtLeast p 2 H := by
  rintro ⟨A, hAH, hA⟩
  obtain ⟨Q, hQP⟩ := hPH
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p 2 AH := hA.subgroupOf hAH
  obtain ⟨S, hAHS⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  let B : Subgroup H := AH.map (MulAut.conj x).toMonoidHom
  have hBQ : B ≤ (Q : Subgroup H) := by
    have hSQ :
        (S : Subgroup H).map (MulAut.conj x).toMonoidHom =
          (Q : Subgroup H) := by
      change MulAut.conj x • (S : Subgroup H) = (Q : Subgroup H)
      rw [← Sylow.coe_subgroup_smul, hx]
    exact (Subgroup.map_mono hAHS).trans_eq hSQ
  let BG : Subgroup G := B.map H.subtype
  have hBGP : BG ≤ P := by
    rw [hQP]
    exact Subgroup.map_mono hBQ
  have hBG : IsElementaryAbelianOfRank p 2 BG :=
    (hAHrank.map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).map_of_injective
        H.subtype H.subtype_injective
  letI : IsCyclic P := hcyc
  let eBG : BG.subgroupOf P ≃* BG :=
    Subgroup.subgroupOfEquivOfLe hBGP
  have hcycBGsub : IsCyclic (BG.subgroupOf P) := by infer_instance
  have hcycBG : IsCyclic BG := eBG.isCyclic.mp hcycBGsub
  exact hBG.not_isCyclic Fact.out hcycBG

theorem characteristic_map_subtype_le_normalizer16
    {K : Type*} [Group K] (S : Subgroup K)
    (R : Subgroup S) [R.Characteristic] :
    Subgroup.normalizer (S : Set K) ≤
      Subgroup.normalizer (R.map S.subtype : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set K) :=
      (Subgroup.normalizer (S : Set K)).inv_mem hg
    have h := characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using h

theorem normalizer_le_normalizer_ambientSylow_of_isNilpotent16
    {U : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnil : Group.IsNilpotent U) (S : Sylow p U) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (ambientSylow U S : Set G) := by
  letI : Group.IsNilpotent U := hnil
  have hSnormal : (S : Subgroup U).Normal := by infer_instance
  have hScore : pCore p U = (S : Subgroup U) := by
    apply le_antisymm (pCore_le_sylow S)
    exact le_pCore S.isPGroup' hSnormal
  rw [ambientSylow, ← hScore]
  exact characteristic_map_subtype_le_normalizer16 U (pCore p U)

theorem derivedWithin_le16_final (M : Subgroup G) :
    derivedWithin M ≤ M := by
  exact Subgroup.map_subtype_le _

theorem derivedWithin_normal16
    (M : Subgroup G) : ((derivedWithin M).subgroupOf M).Normal := by
  unfold derivedWithin
  rw [M.map_subtype_commutator]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.commutator_le_self M)).2
  exact Subgroup.normalizer_commutator_ge_left M M

theorem normal_restrict16
    {N L K : Subgroup G}
    (hN : (N.subgroupOf K).Normal)
    (hNL : N ≤ L) (hLK : L ≤ K) :
    (N.subgroupOf L).Normal := by
  have hNK : N ≤ K := hNL.trans hLK
  have hKnormN : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).1 hN
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2
    (hLK.trans hKnormN)

theorem sylow_of_nilpotent_semidirect_sigma_complement16
    {M U : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (_hnil : Group.IsNilpotent U)
    (hsd : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M))
    (hSigmaDer : sigmaCore M = derivedWithin M)
    (hFHall : IsHall (primeSupport (Nat.card (Fitting_core M)))
      ((Fitting_core M).subgroupOf (derivedWithin M)))
    (hpNotF : p ∉ primeSupport (Nat.card (Fitting_core M)))
    (hpU : p ∣ Nat.card U) (S : Sylow p U) :
    IsSylowSubgroupOf p (ambientSylow U S) M := by
  let pi := primeSupport (Nat.card (Fitting_core M))
  have hUHallD : IsHall piᶜ (U.subgroupOf (derivedWithin M)) := by
    constructor
    · rw [← hsd.2.2.2.symm.index_eq_card]
      exact hFHall.isPiNumber_index
    · rw [hsd.2.2.2.index_eq_card]
      simpa only [compl_compl] using hFHall.isPiNumber_card
  have hpPiCompl : p ∈ piᶜ := hpNotF
  obtain ⟨Q, hQ⟩ := exists_ambient_sylow_eq_of_sylow_hall16
    Fact.out hsd.2.1 hUHallD hpPiCompl S
  have hDerM : derivedWithin M ≤ M := derivedWithin_le16_final M
  have hDerHallM : IsHall (sigmaPrimes M)
      ((derivedWithin M).subgroupOf M) := by
    simpa [hSigmaDer] using Msigma_Hall hM
  have hpDer : p ∣ Nat.card (derivedWithin M) :=
    hpU.trans (Subgroup.card_dvd_of_le hsd.2.1)
  have hpSigmaCard : p ∣ Nat.card (sigmaCore M) := by
    simpa [hSigmaDer] using hpDer
  have hpSigma : p ∈ sigmaPrimes M :=
    sigmaCore_isPiNumber M Fact.out hpSigmaCard
  obtain ⟨R, hR⟩ := exists_ambient_sylow_eq_of_sylow_hall16
    Fact.out hDerM hDerHallM hpSigma Q
  exact ⟨R, (hR.trans hQ).symm⟩

theorem iterated_semidirect_complement_isHall16
    {M U K : Subgroup G}
    (_hM : M ∈ minSimple_max_groups (G := G))
    (hSigmaHall : IsHall (sigmaPrimes M)
      ((sigmaCore M).subgroupOf M))
    (hKHall : IsHall (kappaPrimes M) (K.subgroupOf M))
    (hFcoreEq : Fitting_core M = sigmaCore M)
    (hFU : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M))
    (hDK : IsInternalSemidirectProductIn (derivedWithin M) K M) :
    IsHall (sigmaKappaPrimes M)ᶜ (U.subgroupOf M) := by
  have hDerM : derivedWithin M ≤ M := hDK.1
  have hUM : U ≤ M := hFU.2.1.trans hDerM
  have hFDerSub :
      (Fitting_core M).subgroupOf M ≤
        (derivedWithin M).subgroupOf M :=
    Subgroup.subgroupOf_mono M hFU.1
  have hFrelDer :
      ((Fitting_core M).subgroupOf M).relIndex
          ((derivedWithin M).subgroupOf M) = Nat.card U := by
    rw [Subgroup.relIndex_subgroupOf hDerM]
    change ((Fitting_core M).subgroupOf (derivedWithin M)).index = _
    rw [hFU.2.2.2.symm.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq hFU.2.1]
  have hUdvdFindex :
      Nat.card U ∣ ((Fitting_core M).subgroupOf M).index := by
    rw [← hFrelDer]
    exact Subgroup.relIndex_dvd_index_of_le hFDerSub
  have hUrelDer :
      (U.subgroupOf M).relIndex
          ((derivedWithin M).subgroupOf M) =
        Nat.card (Fitting_core M) := by
    rw [Subgroup.relIndex_subgroupOf hDerM]
    change (U.subgroupOf (derivedWithin M)).index = _
    rw [hFU.2.2.2.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq hFU.1]
  have hDerIndex :
      ((derivedWithin M).subgroupOf M).index = Nat.card K := by
    rw [hDK.2.2.2.symm.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq hDK.2.1]
  have hUindex : (U.subgroupOf M).index =
      Nat.card (Fitting_core M) * Nat.card K := by
    calc
      (U.subgroupOf M).index =
          (U.subgroupOf M).relIndex
              ((derivedWithin M).subgroupOf M) *
            ((derivedWithin M).subgroupOf M).index :=
        (Subgroup.relIndex_mul_index
          (Subgroup.subgroupOf_mono M hFU.2.1)).symm
      _ = Nat.card (Fitting_core M) * Nat.card K := by
        rw [hUrelDer, hDerIndex]
  constructor
  · rw [MathlibSupport.natCard_subgroupOf_eq hUM]
    intro p hp hpU
    refine fun hpSigmaKappa ↦ ?_
    rcases hpSigmaKappa with hpSigma | hpKappa
    · have hpFindex :
          p ∣ ((Fitting_core M).subgroupOf M).index :=
        hpU.trans hUdvdFindex
      have hpSigmaIndex :
          p ∣ ((sigmaCore M).subgroupOf M).index := by
        simpa [hFcoreEq] using hpFindex
      exact hSigmaHall.isPiNumber_index hp hpSigmaIndex hpSigma
    · have hpKindex : p ∣ (K.subgroupOf M).index := by
        rw [hDK.2.2.2.index_eq_card,
          MathlibSupport.natCard_subgroupOf_eq hDK.1]
        exact hpU.trans (Subgroup.card_dvd_of_le hFU.2.1)
      exact hKHall.isPiNumber_index hp hpKindex hpKappa
  · intro p hp hpIndex
    rw [hUindex] at hpIndex
    have hpSigmaKappa : p ∈ sigmaKappaPrimes M := by
      rcases hp.dvd_mul.mp hpIndex with hpF | hpK
      · left
        have hpSigmaCard : p ∣ Nat.card (sigmaCore M) := by
          simpa [hFcoreEq] using hpF
        exact sigmaCore_isPiNumber M hp hpSigmaCard
      · right
        have hpK' : p ∣ Nat.card (K.subgroupOf M) := by
          simpa [MathlibSupport.natCard_subgroupOf_eq hDK.2.1] using hpK
        exact hKHall.isPiNumber_card hp hpK'
    simpa only [compl_compl] using hpSigmaKappa

theorem sigmaFixedPointGenerated_le_complement16
    {M U K : Subgroup G}
    (_hM : M ∈ minSimple_max_groups (G := G))
    (_hCompl : KappaComplement M U K) :
    sigmaFixedPointGenerated M U ≤ U := by
  rw [sigmaFixedPointGenerated]
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨x, _hxSigma, _hx1, hy⟩
  exact centralizerWithin_le_left U (Subgroup.zpowers x) hy

theorem sigma_fixedPointGenerated_contains_centralizer16
    {M U : Subgroup G} {x : G}
    (hx : x ∈ subgroupNonidentity (sigmaCore M)) :
    elementCentralizerWithin U x ≤ sigmaFixedPointGenerated M U := by
  intro y hy
  rw [sigmaFixedPointGenerated]
  exact Subgroup.subset_closure ⟨x, hx.1, hx.2, hy⟩

theorem sigmaFixedPointGenerated_normal_in_complement16
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    ((sigmaFixedPointGenerated M U).subgroupOf U).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (sigmaFixedPointGenerated_le_complement16 hM hCompl)).2
  rw [sigmaFixedPointGenerated]
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro u hu y ⟨x, hxSigma, hx1, hyCent⟩
  have hMnormSigma :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).1
      (sigmaCore_normal M)
  have hxSigma' : u * x * u⁻¹ ∈ sigmaCore M :=
    (Subgroup.le_normalizer_iff.mp hMnormSigma)
      u (hCompl.U_le_M hu) x hxSigma
  have hx1' : u * x * u⁻¹ ≠ 1 := by
    intro heq
    apply hx1
    simpa [mul_assoc] using
      congrArg (fun z ↦ u⁻¹ * z * u) heq
  apply Subgroup.subset_closure
  refine ⟨u * x * u⁻¹, hxSigma', hx1', ?_⟩
  refine mem_centralizerWithin.mpr ⟨?_, ?_⟩
  · exact U.mul_mem (U.mul_mem hu
      (centralizerWithin_le_left U (Subgroup.zpowers x) hyCent))
        (U.inv_mem hu)
  · intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hyx : Commute y x :=
      ((mem_centralizerWithin.mp hyCent).2 x
        (Subgroup.mem_zpowers x)).symm
    exact ((hyx.conj u).zpow_right n).eq.symm

noncomputable def semidirectQuotientEquiv16
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    K ⧸ N.subgroupOf K ≃* H := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact hsd.2.2.2.symm.QuotientMulEquiv.trans
    (Subgroup.subgroupOfEquivOfLe hsd.2.1)

theorem semidirect_quotient_commutative16
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    IsMulCommutative (K ⧸ N.subgroupOf K) ↔ IsMulCommutative H := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  let e := semidirectQuotientEquiv16 hsd
  constructor
  · intro hQ
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.symm.injective
    simpa only [map_mul] using
      (isMulCommutative_iff.mp hQ (e.symm x) (e.symm y))
  · intro hH
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    simpa only [map_mul] using
      (isMulCommutative_iff.mp hH (e x) (e y))

theorem semidirect_quotient_card16
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    Nat.card (K ⧸ N.subgroupOf K) = Nat.card H := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact Nat.card_congr (semidirectQuotientEquiv16 hsd).toEquiv

theorem semidirect_quotient_exponent16
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    Monoid.exponent (K ⧸ N.subgroupOf K) = Monoid.exponent H := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact Monoid.exponent_eq_of_mulEquiv (semidirectQuotientEquiv16 hsd)

theorem cyclic_of_typeP_complement16
    {M U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hTypeP : of_typeP M U W W₁ W₂ defW) :
    IsCyclic W₁ :=
  hTypeP.1.1

/-- Cauchy's theorem, expressed as an ambient elementary-abelian line. -/
theorem exists_rankOneLineIn_of_primeSupport16
    {K : Subgroup G} {p : ℕ}
    (hpK : p ∈ primeSupport (Nat.card K)) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElementaryAbelianOfRank p 1 P := by
  letI : Fact p.Prime := ⟨hpK.1⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := K) p hpK.2
  let P : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardP : Nat.card P = p := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Nat.card_zpowers, hx]
  exact ⟨P, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardP⟩

theorem cyclic_Hall_complement_rank_one16
    {M K : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hHall : IsHall (primeSupport (Nat.card K)) (K.subgroupOf M))
    (hcyc : IsCyclic K)
    (hpK : p ∈ primeSupport (Nat.card K)) :
    HasElementaryAbelianRankAtLeast p 1 M ∧
      ¬ HasElementaryAbelianRankAtLeast p 2 M := by
  letI : Fact p.Prime := ⟨hpK.1⟩
  obtain ⟨X, hXK, hX⟩ := exists_rankOneLineIn_of_primeSupport16 hpK
  have hXM : X ≤ M := hXK.trans hKM
  refine ⟨⟨X, hXM, hX⟩, ?_⟩
  let KM : Subgroup M := K.subgroupOf M
  let S : Sylow p KM := default
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_map_of_sylow_hall16
    hpK.1 hHall hpK S
  let P : Subgroup G := (Q : Subgroup M).map M.subtype
  have hPsyl : IsSylowSubgroupOf p P M := ⟨Q, rfl⟩
  have hPK : P ≤ K := by
    intro z hz
    rcases hz with ⟨zM, hzQ, rfl⟩
    rw [hQ] at hzQ
    rcases hzQ with ⟨zK, hzS, hzK⟩
    exact hzK ▸ zK.2
  letI : IsCyclic K := hcyc
  have hPcyc : IsCyclic P := Subgroup.isCyclic_of_le hPK
  exact not_rankTwo_of_cyclic_sylow16 hPsyl hPcyc

theorem typeP_complement_isKappaNumber16
    {M U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hTypeP : of_typeP M U W W₁ W₂ defW) :
    IsPiNumber (kappaPrimes M) (Nat.card W₁) := by
  rcases hTypeP with
    ⟨⟨hW₁cyc, ⟨hW₁M, hHallW₁⟩, hW₁ne, hDerived⟩,
      _, _, ⟨_, hW₂ne, hW₂F, _, hcentralizer⟩, _⟩
  intro p hp hpW₁
  have hpW₁' : p ∈ primeSupport (Nat.card W₁) := ⟨hp, hpW₁⟩
  have hrank := cyclic_Hall_complement_rank_one16
    hM hW₁M hHallW₁ hW₁cyc hpW₁'
  have hpDer : ¬ p ∣ Nat.card (derivedWithin M) := by
    intro hpD
    have hpIndex : p ∣ (W₁.subgroupOf M).index := by
      rw [hDerived.2.2.2.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hDerived.1]
      exact hpD
    exact hHallW₁.isPiNumber_index hp hpIndex hpW₁'
  have hpSigma : p ∉ sigmaPrimes M := by
    intro hpSigma
    have hpSigmaCard : p ∣ Nat.card (sigmaCore M) := by
      have hpSupport : p ∈ primeSupport (Nat.card (sigmaCore M)) := by
        rw [pi_Msigma hM]
        exact hpSigma
      exact hpSupport.2
    exact hpDer (hpSigmaCard.trans
      (Subgroup.card_dvd_of_le (Msigma_der1 hM)))
  have hpDerComm : ¬ p ∣ Nat.card (_root_.commutator M) := by
    rw [derivedWithin,
      Subgroup.card_map_of_injective M.subtype_injective] at hpDer
    exact hpDer
  have hpTau1 : p ∈ tau1Primes M :=
    ⟨hp, hpSigma, hrank.1, hrank.2, hpDerComm⟩
  obtain ⟨X, hXW₁, hXline⟩ :=
    exists_rankOneLineIn_of_primeSupport16 hpW₁'
  have hW₂central : W₂ ≤ centralizerWithin (sigmaCore M) X := by
    intro z hzW₂
    refine ⟨(Fcore_sub_Msigma hM) (hW₂F hzW₂), ?_⟩
    intro y hyX
    have hyW₁ := hXW₁ hyX
    by_cases hy1 : y = 1
    · subst y
      simp
    · have hz : z ∈ elementCentralizerWithin (derivedWithin M) y := by
        rw [hcentralizer y ⟨hyW₁, hy1⟩]
        exact hzW₂
      exact hz.2 y (Subgroup.mem_zpowers y)
  have hcentNe : centralizerWithin (sigmaCore M) X ≠ ⊥ := by
    intro hbot
    apply hW₂ne
    exact le_bot_iff.mp (hW₂central.trans_eq hbot)
  exact ⟨Or.inl hpTau1, X, ⟨hXW₁.trans hW₁M, hXline⟩, hcentNe⟩

theorem normalizer_nilpotent_complement_le_maximal16
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hnil : Group.IsNilpotent U)
    (hUDer : U ≤ derivedWithin M)
    (_hKnorm : K ≤ Subgroup.normalizer (U : Set G))
    (hsd : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M))
    (hSigmaDer : sigmaCore M = derivedWithin M)
    (hFHall : IsHall (primeSupport (Nat.card (Fitting_core M)))
      ((Fitting_core M).subgroupOf (derivedWithin M)))
    (hUne : U ≠ ⊥) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  have hcardU : 1 < Nat.card U := U.one_lt_card_iff_ne_bot.mpr hUne
  obtain ⟨p, hp, hpU⟩ := Nat.exists_prime_and_dvd hcardU.ne'
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p U := default
  let P : Subgroup G := ambientSylow U S
  have hPUDer : P ≤ derivedWithin M :=
    (Subgroup.map_subtype_le (S : Subgroup U)).trans hUDer
  have hpNotF : p ∉ primeSupport (Nat.card (Fitting_core M)) := by
    intro hpF
    have hpIndex : p ∣
        ((Fitting_core M).subgroupOf (derivedWithin M)).index := by
      rw [hsd.2.2.2.symm.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hsd.2.1]
      exact hpU
    exact hFHall.isPiNumber_index hp hpIndex hpF
  have hpSigma : p ∈ sigmaPrimes M := by
    have hpDer : p ∣ Nat.card (derivedWithin M) :=
      hpU.trans (Subgroup.card_dvd_of_le hUDer)
    rw [← hSigmaDer] at hpDer
    exact sigmaCore_isPiNumber M hp hpDer
  have hPsylowM : IsSylowSubgroupOf p P M := by
    exact sylow_of_nilpotent_semidirect_sigma_complement16
      hM hnil hsd hSigmaDer hFHall hpNotF hpU S
  have hnormUP :
      Subgroup.normalizer (U : Set G) ≤
        Subgroup.normalizer (P : Set G) := by
    exact normalizer_le_normalizer_ambientSylow_of_isNilpotent16
      hnil S
  obtain ⟨Q, hQP⟩ := hPsylowM
  intro g hg
  have hgP : g ∈ Subgroup.normalizer (P : Set G) := hnormUP hg
  have hnormQ :
      Subgroup.normalizer (P : Set G) ≤ M := by
    rw [hQP]
    exact norm_sigma_Sylow hpSigma Q
  exact hnormQ hgP

theorem kappaComplement_of_typeP_notP116
    {M U W₁ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hW₁Hall : IsHall (kappaPrimes M) (W₁.subgroupOf M))
    (hW₁ : IsCyclic W₁ ∧
      (W₁ ≤ M ∧
        IsHall (primeSupport (Nat.card W₁)) (W₁.subgroupOf M)) ∧
      W₁ ≠ ⊥ ∧
      IsInternalSemidirectProductIn (derivedWithin M) W₁ M)
    (hU : Group.IsNilpotent U ∧
      U ≤ derivedWithin M ∧
      W₁ ≤ Subgroup.normalizer (U : Set G) ∧
      IsInternalSemidirectProductIn (Fitting_core M) U
        (derivedWithin M))
    (hFcoreEq : Fitting_core M = sigmaCore M)
    (_hnotP1 : M ∉ typeP1MaximalSubgroups (G := G)) :
    KappaComplement M U W₁ := by
  have hUleM : U ≤ M := hU.2.1.trans (derivedWithin_le16_final M)
  have hHallU : IsHall (sigmaKappaPrimes M)ᶜ (U.subgroupOf M) := by
    exact iterated_semidirect_complement_isHall16
      hM (Msigma_Hall hM) hW₁Hall hFcoreEq hU.2.2.2 hW₁.2.2.2
  have hProduct : ∃ E : Subgroup G,
      (E : Set G) = (U : Set G) * (W₁ : Set G) := by
    exact ⟨U ⊔ W₁,
      Subgroup.coe_mul_of_right_le_normalizer_left U W₁ hU.2.2.1⟩
  exact
    { U_le_M := hUleM
      hall_U := hHallU
      K_le_M := hW₁.2.1.1
      hall_K := hW₁Hall
      product_is_group := hProduct }

/-- Facts common to all semantic type-P decompositions.  Keeping this result
available avoids repeating the expensive Hall-complement analysis in later
type and support phases. -/
structure TypePFacts16
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  typeP : M ∈ typePMaximalSubgroups (G := G)
  W₁_hall_kappa :
    IsHall (kappaPrimes M) (W₁.subgroupOf M)
  partner_eq : pTypePartner M W₁ = W₂
  typeP1_iff : M ∈ typeP1MaximalSubgroups (G := G) ↔
    U = ⊥ ∨ Subgroup.normalizer (U : Set G) ≤ M
  sigma_eq_derived_cases : sigmaCore M = derivedWithin M →
    (Fitting_core M = sigmaCore M ↔ U = ⊥) ∧
      (fittingCoreQuotientAbelian M ↔ IsMulCommutative U)

theorem typePFacts16
    {M U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hTypeP : of_typeP M U W W₁ W₂ defW) :
    TypePFacts16 M U W W₁ W₂ defW := by
  classical
  rcases hTypeP with
    ⟨hW₁, hU, hcore, hW₂, hTI⟩
  have hW₁kappa := typeP_complement_isKappaNumber16 hM
    (show of_typeP M U W W₁ W₂ defW from
      ⟨hW₁, hU, hcore, hW₂, hTI⟩)
  have hMP : M ∈ typePMaximalSubgroups (G := G) := by
    have hcard : 1 < Nat.card W₁ :=
      W₁.one_lt_card_iff_ne_bot.mpr hW₁.2.2.1
    obtain ⟨p, hp, hpW₁⟩ := Nat.exists_prime_and_dvd hcard.ne'
    exact (PtypeP hM).2 ⟨p, hW₁kappa hp hpW₁⟩
  obtain ⟨K, hKM, hHallK⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM) (kappaPrimes M)
  obtain ⟨Mstar, hEmbedK⟩ := Ptype_embedding hMP hKM hHallK
  have hcardW₁K : Nat.card W₁ = Nat.card K := by
    have hIndexW₁ : ((derivedWithin M).subgroupOf M).index =
        Nat.card W₁ := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hW₁.2.1.1] using
        hW₁.2.2.2.2.2.2.symm.index_eq_card
    have hIndexK : ((derivedWithin M).subgroupOf M).index =
        Nat.card K := by
      simpa only [derivedWithin,
          MathlibSupport.natCard_subgroupOf_eq hKM] using
        hEmbedK.derived_sdprod.2.2.2.symm.index_eq_card
    exact hIndexW₁.symm.trans hIndexK
  have hW₁HallKappa :
      IsHall (kappaPrimes M) (W₁.subgroupOf M) := by
    constructor
    · simpa [MathlibSupport.natCard_subgroupOf_eq hW₁.2.1.1] using
        hW₁kappa
    · have hindexEq : (W₁.subgroupOf M).index =
          (K.subgroupOf M).index := by
        apply Nat.eq_of_mul_eq_mul_right
          (Nat.card_pos (α := W₁.subgroupOf M))
        calc
          (W₁.subgroupOf M).index * Nat.card (W₁.subgroupOf M) =
              Nat.card M := (W₁.subgroupOf M).index_mul_card
          _ = (K.subgroupOf M).index * Nat.card (K.subgroupOf M) :=
            (K.subgroupOf M).index_mul_card.symm
          _ = (K.subgroupOf M).index * Nat.card (W₁.subgroupOf M) := by
            rw [MathlibSupport.natCard_subgroupOf_eq hW₁.2.1.1,
              MathlibSupport.natCard_subgroupOf_eq hKM, hcardW₁K]
      simpa [hindexEq] using hHallK.isPiNumber_index
  obtain ⟨V, hCompl⟩ := ex_kappa_compl hM hW₁.2.1.1 hW₁HallKappa
  have hSummary := BGsummaryC hM hCompl hW₁.2.2.1
  have hPartner : pTypePartner M W₁ = W₂ := by
    obtain ⟨x, hx1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hW₁.2.2.1
    have hxW₁ : (x : G) ∈ W₁ := x.property
    have hx1G : (x : G) ≠ 1 := fun hx ↦ hx1 (Subtype.ext hx)
    apply le_antisymm
    · intro z hz
      have hzDer : z ∈ derivedWithin M :=
        (Msigma_der1 hM) (centralizerWithin_le_left _ _ hz)
      have hzCent : z ∈ elementCentralizerWithin (derivedWithin M) x := by
        refine mem_centralizerWithin.mpr ⟨hzDer, ?_⟩
        intro a ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact (mem_centralizerWithin.mp hz).2 (x ^ n)
          (W₁.zpow_mem hxW₁ n)
      rw [hW₂.2.2.2.2 x ⟨hxW₁, hx1G⟩] at hzCent
      exact hzCent
    · intro z hz
      refine mem_centralizerWithin.mpr
        ⟨(Fcore_sub_Msigma hM) (hW₂.2.2.1 hz), ?_⟩
      intro x' hx'
      by_cases hx'1 : x' = 1
      · subst x'
        simp
      · have hzCent : z ∈
            elementCentralizerWithin (derivedWithin M) x' := by
          rw [hW₂.2.2.2.2 x' ⟨hx', hx'1⟩]
          exact hz
        exact hzCent.2 x' (Subgroup.mem_zpowers x')
  have hP1iff : M ∈ typeP1MaximalSubgroups (G := G) ↔
      U = ⊥ ∨ Subgroup.normalizer (U : Set G) ≤ M := by
    constructor
    · intro hP1
      by_cases hUbot : U = ⊥
      · exact Or.inl hUbot
      · right
        have hsigmaDer := Msigma_eq_der1 hM hP1
        have hFcoreHallDerived : IsHall
            (primeSupport (Nat.card (Fitting_core M)))
            ((Fitting_core M).subgroupOf (derivedWithin M)) :=
          isHall_subgroupOf_chain16
            (Fitting_structure hM).Fcore_le_derived
            (derivedWithin_le16_final M) (Fcore_Hall M)
        exact normalizer_nilpotent_complement_le_maximal16
          hM hU.1 hU.2.1 hU.2.2.1 hU.2.2.2
            hsigmaDer hFcoreHallDerived hUbot
    · intro hcase
      rcases hcase with hUbot | hnorm
      · have hSigmaKappa : IsPiNumber (sigmaKappaPrimes M)
            (Nat.card M) := by
          have hFDer : Fitting_core M = derivedWithin M :=
            (semidirect_right_eq_bot_iff_left_eq_ambient16
              hU.2.2.2).1 hUbot
          rw [← hW₁.2.2.2.2.2.2.card_mul]
          have hFpi : IsPiNumber (sigmaPrimes M)
              (Nat.card (Fitting_core M)) :=
            (sigmaCore_isPiNumber M).of_dvd
              (Subgroup.card_dvd_of_le (Fcore_sub_Msigma hM))
          rw [← hFDer]
          simpa only [sigmaKappaPrimes,
              MathlibSupport.natCard_subgroupOf_eq (Fcore_sub M),
              MathlibSupport.natCard_subgroupOf_eq hW₁.2.1.1] using
            (hFpi.mono Set.subset_union_left).mul
              (hW₁kappa.mono (Set.subset_union_right))
        exact ⟨hMP, hSigmaKappa⟩
      · by_contra hnotP1
        have hFcoreEq : Fitting_core M = sigmaCore M :=
          (Fcore_eq_Msigma hM).2
            (notP1type_Msigma_nil (Or.inr ⟨hMP, hnotP1⟩))
        have hComplU : KappaComplement M U W₁ :=
          kappaComplement_of_typeP_notP116
            hM hW₁HallKappa hW₁ hU hFcoreEq hnotP1
        exact (BGsummaryC hM hComplU hW₁.2.2.1).normalizer_U_not_le hnorm
  have hSigmaCases : sigmaCore M = derivedWithin M →
      (Fitting_core M = sigmaCore M ↔ U = ⊥) ∧
        (fittingCoreQuotientAbelian M ↔ IsMulCommutative U) := by
    intro hSigmaDer
    have hsd : IsInternalSemidirectProductIn
        (Fitting_core M) U (derivedWithin M) := hU.2.2.2
    constructor
    · constructor
      · intro hEq
        exact (semidirect_right_eq_bot_iff_left_eq_ambient16 hsd).2
          (hEq.trans hSigmaDer)
      · intro hUbot
        have hEqDer :=
          (semidirect_right_eq_bot_iff_left_eq_ambient16 hsd).1 hUbot
        exact hEqDer.trans hSigmaDer.symm
    · unfold fittingCoreQuotientAbelian
      rw [hSigmaDer]
      change
        ((_root_.commutator (derivedWithin M)).map
            (derivedWithin M).subtype ≤ Fitting_core M) ↔
          IsMulCommutative U
      rw [Subgroup.map_le_iff_le_comap]
      change (_root_.commutator (derivedWithin M) ≤
          (Fitting_core M).subgroupOf (derivedWithin M)) ↔
        IsMulCommutative U
      letI : ((Fitting_core M).subgroupOf (derivedWithin M)).Normal :=
        hsd.2.2.1
      rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
      exact semidirect_quotient_commutative16 hsd
  exact
    { typeP := hMP
      W₁_hall_kappa := hW₁HallKappa
      partner_eq := hPartner
      typeP1_iff := hP1iff
      sigma_eq_derived_cases := hSigmaCases }

end TypeSpecInternal

end

end Submission.OddOrder.BG.Section16
