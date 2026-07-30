import Submission.OddOrder.BG.Section16.SummaryABC
import Submission.OddOrder.BG.Section16.SummaryDE
import Submission.OddOrder.BG.Section16.SummaryI
import Submission.OddOrder.BG.Section16.SupportZero

/-!
# Bender--Glauberman Section 16: summary II

This module packages the support, fusion, centralizer, and Frobenius conclusions
of Bender--Glauberman Theorem II.  Its conclusion records contain subgroup
witnesses, so they live in `Type` and the final result is a noncomputable
definition.
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

/-! ## Public conclusion records -/

/-- The elements of `X` whose full centralizer escapes `M`. -/
def outerExceptionalSet (M : Subgroup G) (X : Set G) : Set G :=
  {x : G | x ∈ X ∧ ¬ elementCentralizer x ≤ M}

/-- The Frobenius-complement data in clause (iii). -/
structure BGSummaryIIFrobeniusData (M : Subgroup G) : Type u where
  complement : Subgroup G
  complement_le : complement ≤ M
  frobenius :
    IsFrobeniusDecomposition
      ((Fitting_core M).subgroupOf M) (complement.subgroupOf M)
  complement_cyclic : IsCyclic complement

/-- The elementwise conclusions in clauses (ii) and (iii). -/
structure BGSummaryIIElementData
    (M : Subgroup G) (X : Set G) (x : G) : Type u where
  unique_maximal_centralizer :
    minSimple_max_groups_of (G := G) (elementCentralizer x : Set G) =
      {elementNormalizer15 x}
  type_one_or_two :
    FTtype (elementNormalizer15 x) = 1 ∨
      FTtype (elementNormalizer15 x) = 2
  fittingCore_complement :
    IsInternalSemidirectProductIn
      (Fitting_core (elementNormalizer15 x))
      (M ⊓ elementNormalizer15 x) (elementNormalizer15 x)
  centralizer_coprime : ∀ y ∈ X,
    Nat.Coprime
      (Nat.card (Fitting_core (elementNormalizer15 x)))
      (Nat.card (elementCentralizerWithin M y))
  support_not_support1 :
    x ∈ FTsupport (elementNormalizer15 x) \
      FTsupport1 (elementNormalizer15 x)
  centralizer_decomposition :
    IsInternalSemidirectProductIn
      (elementCentralizerWithin
        (Fitting_core (elementNormalizer15 x)) x)
      (elementCentralizerWithin M x) (elementCentralizer x)
  typeTwo_frobenius : FTtype (elementNormalizer15 x) = 2 →
    BGSummaryIIFrobeniusData M

/-- The Peterfalvi-facing form of Bender--Glauberman Theorem II. -/
structure BGSummaryIIConclusion (M : Subgroup G) (X : Set G) : Type u where
  exceptional_subset_support1 :
    outerExceptionalSet M X ⊆ FTsupport1 M
  fusion_control : ∀ x ∈ X, ∀ a : G,
    conjugateElement16 x a ∈ X →
      ∃ y : G, y ∈ M ∧
        conjugateElement16 x a = conjugateElement16 x y
  element_data : ∀ x ∈ outerExceptionalSet M X,
    BGSummaryIIElementData M X x

/-! ## General adapters -/

/-- Restrict a Summary-II package to a smaller support set. -/
private def restrictSummaryII
    {M : Subgroup G} {X Y : Set G}
    (hXY : X ⊆ Y) (hY : BGSummaryIIConclusion M Y) :
    BGSummaryIIConclusion M X :=
  { exceptional_subset_support1 := fun _ hx ↦
      hY.exceptional_subset_support1 ⟨hXY hx.1, hx.2⟩
    fusion_control := fun x hx a hxa ↦
      hY.fusion_control x (hXY hx) a (hXY hxa)
    element_data := fun x hx ↦
      let hxY : x ∈ outerExceptionalSet M Y := ⟨hXY hx.1, hx.2⟩
      let data := hY.element_data x hxY
      { unique_maximal_centralizer := data.unique_maximal_centralizer
        type_one_or_two := data.type_one_or_two
        fittingCore_complement := data.fittingCore_complement
        centralizer_coprime := fun y hy ↦
          data.centralizer_coprime y (hXY hy)
        support_not_support1 := data.support_not_support1
        centralizer_decomposition := data.centralizer_decomposition
        typeTwo_frobenius := data.typeTwo_frobenius } }

/-- A subgroup with `pi`-number order is contained in a normal `pi`-Hall
subgroup. -/
private theorem piSubgroup_le_normalHall16
    {K : Type*} [Group K] [Finite K] {pi : Set ℕ}
    {L N : Subgroup K}
    (hNnormal : N.Normal) (hNHall : IsHall pi N)
    (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcoprime : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have hqL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have hqIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have hqOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime hqL hqIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp hqOne)

private theorem orderOf_conjugateElement16 (x a : G) :
    orderOf (conjugateElement16 x a) = orderOf x :=
  orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective x

private theorem orderOf_isPrimeSupport_of_mem16
    {H : Subgroup G} {x : G} (hxH : x ∈ H) :
    IsPiNumber (primeSupport (Nat.card H)) (orderOf x) := by
  intro p hp hpOrder
  exact ⟨hp, hpOrder.trans (by
    simpa using orderOf_dvd_natCard (⟨x, hxH⟩ : H))⟩

/-- Detect membership in the sigma core from the order of an element of a
maximal subgroup. -/
private theorem mem_sigmaCore_of_order16
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hxM : x ∈ M)
    (hxPi : IsPiNumber (sigmaPrimes M) (orderOf x)) :
    x ∈ sigmaCore M := by
  let X : Subgroup G := Subgroup.zpowers x
  have hXM : X ≤ M := Subgroup.zpowers_le.mpr hxM
  have hXpi : IsPiNumber (sigmaPrimes M)
      (Nat.card (X.subgroupOf M)) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hXM]
    change IsPiNumber (sigmaPrimes M)
      (Nat.card (Subgroup.zpowers x))
    rw [Nat.card_zpowers]
    exact hxPi
  have hle : X.subgroupOf M ≤ (sigmaCore M).subgroupOf M :=
    piSubgroup_le_normalHall16
      (by simpa using sigmaCore_normal M) (Msigma_Hall hM) hXpi
  exact hle (show (⟨x, hxM⟩ : M) ∈ X.subgroupOf M from
    Subgroup.mem_zpowers x)

/-- Pull canonical-core membership back through conjugation. -/
private theorem mem_FTcore_of_conjugate16
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x a : G} (hxM : x ∈ M)
    (hxa : conjugateElement16 x a ∈ FTcore M) :
    x ∈ FTcore M := by
  have hxaSigma : conjugateElement16 x a ∈ sigmaCore M := by
    rw [← def_FTcore hM]
    exact hxa
  have hxaPi : IsPiNumber (sigmaPrimes M)
      (orderOf (conjugateElement16 x a)) :=
    (sigmaCore_isPiNumber M).of_dvd
      ((sigmaCore M).orderOf_dvd_natCard hxaSigma)
  rw [def_FTcore hM]
  apply mem_sigmaCore_of_order16 hM hxM
  rw [← orderOf_conjugateElement16 x a]
  exact hxaPi

/-! ## Support and fusion -/

/-- Conjugation cannot move an element of the mixed outer support into the
ordinary Dade support. -/
private theorem conjugate_not_mem_FTsupport16
    {M : Subgroup G} {x a : G}
    (hx : x ∈ FTsupport0 M \ FTsupport M) :
    conjugateElement16 x a ∉ FTsupport M := by
  intro hxa
  rcases hx.1 with hxSupport | hxMixed
  · exact hx.2 hxSupport
  · simp only [FTsupport, ftSupport, Set.mem_iUnion] at hxa
    rcases hxa with ⟨z, hz, hxaCentral⟩
    have hPi : IsPiNumber (primeSupport (Nat.card (FTder M)))
        (orderOf (conjugateElement16 x a)) :=
      orderOf_isPrimeSupport_of_mem16 hxaCentral.1.1
    apply hxMixed.2.1
    rw [← orderOf_conjugateElement16 x a]
    exact hPi

/-- The pointwise normalized-TI argument for the enlarged support. -/
private theorem support0_conjugator_mem16
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x a : G}
    (hx : x ∈ FTsupport0 M \ FTsupport1 M)
    (hxa : conjugateElement16 x a ∈ FTsupport0 M) :
    a ∈ M := by
  classical
  obtain ⟨U, K, hComplement⟩ := kappa_witness hM
  by_cases hxSupport : x ∈ FTsupport M
  · have hSupportsDifferent : FTsupport M ≠ FTsupport1 M := by
      intro hEq
      exact hx.2 (hEq ▸ hxSupport)
    have hTI :=
      (BGsummaryB hM hComplement).support_difference_normalizedTI
        hSupportsDifferent
    have hxaNotSupport1 :
        conjugateElement16 x a ∉ FTsupport1 M := by
      intro hxaOne
      have hxM : x ∈ M := (FTsupp0_sub M hx.1).1
      have hxNe : x ≠ 1 := by
        intro hxOne
        subst x
        exact hxaOne.2 (by simp [conjugateElement16])
      exact hx.2 ⟨mem_FTcore_of_conjugate16 hM hxM hxaOne.1, hxNe⟩
    have hxaSupport : conjugateElement16 x a ∈ FTsupport M := by
      by_contra hxaNotSupport
      have hOuter : conjugateElement16 x a ∈
          FTsupport0 M \ FTsupport M := ⟨hxa, hxaNotSupport⟩
      have hBack := conjugate_not_mem_FTsupport16
        (a := a⁻¹) hOuter
      apply hBack
      simpa [conjugateElement16, MulAut.conj_apply, mul_assoc] using hxSupport
    have hainv : a⁻¹ ∈ M := by
      apply ((isNormalizedTI_iff_mem_conj.mp hTI).2.2
        ⟨hxSupport, hx.2⟩ (by simp)).mp
      simpa [conjugateElement16, MulAut.conj_apply] using
        (show conjugateElement16 x a ∈
          FTsupport M \ FTsupport1 M from
            ⟨hxaSupport, hxaNotSupport1⟩)
    simpa using M.inv_mem hainv
  · have hKne : K ≠ ⊥ := by
      intro hKbot
      have hF : M ∈ typeFMaximalSubgroups (G := G) :=
        (trivg_kappa hM hComplement.K_le_M hComplement.hall_K).1 hKbot
      have hTypeOne : FTtype M = 1 := (FTtype_Fmax hM).1 hF
      exact hxSupport ((FTsupp0_type1 M hTypeOne) ▸ hx.1)
    have hTI :=
      (BGsummaryC hM hComplement hKne).outer_support_normalizedTI
    have hxaNotSupport : conjugateElement16 x a ∉ FTsupport M :=
      conjugate_not_mem_FTsupport16 ⟨hx.1, hxSupport⟩
    have hainv : a⁻¹ ∈ M := by
      apply ((isNormalizedTI_iff_mem_conj.mp hTI).2.2
        ⟨hx.1, hxSupport⟩ (by simp)).mp
      simpa [conjugateElement16, MulAut.conj_apply] using
        (show conjugateElement16 x a ∈
          FTsupport0 M \ FTsupport M from ⟨hxa, hxaNotSupport⟩)
    simpa using M.inv_mem hainv

/-! ## Coprimality for escaping centralizers -/

private theorem prime_mem_tau2_or_tau13_16
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpM : p ∈ primeSupport (Nat.card M))
    (hpNotSigma : p ∉ sigmaPrimes M) :
    p ∈ tau2Primes M ∨ p ∈ tau13Primes M := by
  letI : Fact p.Prime := ⟨hpM.1⟩
  obtain ⟨x, hxOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := M) p hpM.2
  let X : Subgroup G := (Subgroup.zpowers x).map M.subtype
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      Nat.card_zpowers, hxOrder]
  have hXrank : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hRankOne : HasElementaryAbelianRankAtLeast p 1 M :=
    ⟨X, Subgroup.map_subtype_le _, hXrank⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast p 2 M
  · left
    refine ⟨hpM.1, hpNotSigma, hRankTwo, ?_⟩
    intro hRankThree
    exact hpNotSigma (alpha_sub_sigma hM ⟨hpM.1, hRankThree⟩)
  · right
    by_cases hpDer : p ∣ Nat.card (_root_.commutator M)
    · exact Or.inr ⟨hpM.1, hpNotSigma, hRankOne, hRankTwo, hpDer⟩
    · exact Or.inl ⟨hpM.1, hpNotSigma, hRankOne, hRankTwo, hpDer⟩

/-- Under the Type-F signalizer hypotheses, every element of the enlarged
support belongs to the sigma core. -/
private theorem support0_mem_sigma_of_typeF16
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hF : M ∈ typeFMaximalSubgroups (G := G))
    (hTau : IsPiNumber (tau2Primes M)ᶜ (Nat.card M))
    {y : G} (hy : y ∈ FTsupport0 M) :
    y ∈ sigmaCore M := by
  classical
  have hTypeOne : FTtype M = 1 := (FTtype_Fmax hM).1 hF
  have hySupport : y ∈ FTsupport M := by
    rw [← FTsupp0_type1 M hTypeOne]
    exact hy
  simp only [FTsupport, ftSupport, Set.mem_iUnion] at hySupport
  rcases hySupport with ⟨t, htSupport1, hyCentral⟩
  have htSigma : t ∈ sigmaCore M := by
    rw [← def_FTcore hM]
    exact htSupport1.1
  have hyM : y ∈ M := by
    simpa [FTder, ftDerived, hTypeOne] using hyCentral.1.1
  have hyPi : IsPiNumber (sigmaPrimes M) (orderOf y) := by
    intro p hp hpOrder
    by_contra hpNotSigma
    have hpM : p ∈ primeSupport (Nat.card M) :=
      primeSupport_orderOf_mem_of_mem hyM ⟨hp, hpOrder⟩
    have hpNotTau : p ∉ tau2Primes M := hTau hp hpM.2
    have hpTau13 : p ∈ tau13Primes M :=
      (prime_mem_tau2_or_tau13_16 hM hpM hpNotSigma).resolve_left hpNotTau
    obtain ⟨P, hPline, hPcycle⟩ :=
      exists_rankOneLineIn_zpowers ⟨hp, hpOrder⟩
    have hPM : P ≤ M :=
      hPcycle.trans (Subgroup.zpowers_le.mpr hyM)
    have hCentralizerNe : centralizerWithin (sigmaCore M) P ≠ ⊥ := by
      intro hbot
      have htCentral : t ∈ centralizerWithin (sigmaCore M) P := by
        refine mem_centralizerWithin.mpr ⟨htSigma, ?_⟩
        intro z hzP
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hPcycle hzP)
        have hty : Commute t y :=
          hyCentral.1.2 t (Subgroup.mem_zpowers t)
        exact (hty.zpow_right n).symm.eq
      rw [hbot] at htCentral
      exact htSupport1.2 (Subgroup.mem_bot.mp htCentral)
    have hpKappa : p ∈ kappaPrimes M :=
      ⟨hpTau13, P, ⟨hPM, hPline⟩, hCentralizerNe⟩
    exact (hF.2 hp hpM.2) hpKappa
  exact mem_sigmaCore_of_order16 hM hyM hyPi

/-- Clause (ii)(c): the escaping normalizer's Fitting core is coprime to
centralizers inside the enlarged support. -/
private theorem escaping_fcore_coprime16
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hxSigma : x ∈ subgroupNonidentity (sigmaCore M))
    (hCentralizerEscapes : ¬ elementCentralizer x ≤ M)
    (hEsc : BGSummaryDEscapingCentralizer M x)
    {y : G} (hy : y ∈ FTsupport0 M) :
    Nat.Coprime
      (Nat.card (Fitting_core (elementNormalizer15 x)))
      (Nat.card (elementCentralizerWithin M y)) := by
  classical
  let N : Subgroup G := elementNormalizer15 x
  have hNmax : N ∈ minSimple_max_groups (G := G) := by
    rcases hEsc.normalizer_type with hNF | hNP2
    · exact hNF.1
    · exact hNP2.1.1
  have hCentralizerPi : IsPiNumber (sigmaPrimes N)ᶜ
      (Nat.card (elementCentralizerWithin M y)) := by
    by_contra hNotPi
    obtain ⟨q, hqCentralizer, hqSigmaN⟩ :=
      exists_primeSupport_inter_of_not_isPiNumber hNotPi
    have hqM : q ∈ primeSupport (Nat.card M) :=
      ⟨hqCentralizer.1, hqCentralizer.2.trans
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))⟩
    have hLength : sigmaLength x = 1 :=
      Msigma_ell1 hM hxSigma.1 hxSigma.2
    have hMover : M ∈
        sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) :=
      ⟨hM, Subgroup.zpowers_le.mpr hxSigma.1⟩
    have hLarge : 1 <
        (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard := by
      by_contra hNotLarge
      have hCardOne :
          (sigmaMaximalOvergroups
            (Subgroup.zpowers x : Set G)).ncard = 1 :=
        Nat.le_antisymm (Nat.le_of_not_gt hNotLarge)
          ((Set.ncard_pos).mpr ⟨M, hMover⟩)
      exact hCentralizerEscapes
        (cent1_sub_uniq_sigma_mmax hCardOne hMover)
    have hLargeContext := (FT_signalizer_context hLength).large hLarge
    have hBase : ftSignalizerBase x = N := rfl
    have hMNotComplement : ¬ IsPiNumber
        (sigmaPrimes (ftSignalizerBase x))ᶜ (Nat.card M) := by
      rw [hBase]
      intro hPi
      exact (hPi hqM.1 hqM.2) hqSigmaN
    obtain ⟨hMF, hTau⟩ :=
      non_disjoint_signalizer_Frobenius
        hLength hLarge hMover hMNotComplement
    have hySigma : y ∈ sigmaCore M :=
      support0_mem_sigma_of_typeF16 hM hMF hTau hy
    have hTypeM : FTtype M = 1 := (FTtype_Fmax hM).1 hMF
    have hCentralizerSigma : IsPiNumber (sigmaPrimes M)
        (Nat.card (elementCentralizerWithin M y)) := by
      apply isPiNumber_natCard_of_orderOf
      intro z hzCentralizer hzNe
      have hzSupport0 : z ∈ FTsupport0 M := by
        apply FTsupp_sub0 M
        simp only [FTsupport, ftSupport, Set.mem_iUnion]
        refine ⟨y, ⟨?_, (FTsupp0_sub M hy).2⟩, ⟨?_, hzNe⟩⟩
        · rw [def_FTcore hM]
          exact hySigma
        · simpa [FTder, ftDerived, hTypeM] using hzCentralizer
      have hzSigma : z ∈ sigmaCore M :=
        support0_mem_sigma_of_typeF16 hM hMF hTau hzSupport0
      exact (sigmaCore_isPiNumber M).of_dvd
        ((sigmaCore M).orderOf_dvd_natCard hzSigma)
    have hqSigmaM : q ∈ sigmaPrimes M :=
      hCentralizerSigma hqCentralizer.1 hqCentralizer.2
    obtain ⟨p, hpOrder⟩ :=
      exists_prime_mem_primeSupport_orderOf hxSigma.2
    have hpSigmaM : p ∈ sigmaPrimes M :=
      ((sigmaCore_isPiNumber M).of_dvd
        ((sigmaCore M).orderOf_dvd_natCard hxSigma.1))
          hpOrder.1 hpOrder.2
    have hxTauN : IsPiNumber (tau2Primes N) (orderOf x) := by
      simpa [hBase] using hLargeContext.x_tau2
    have hpTauN : p ∈ tau2Primes N :=
      hxTauN hpOrder.1 hpOrder.2
    have hNotConjugate : ¬ AreConjugateSubgroups M N :=
      not_conjugate_of_tau2_sigma hM hNmax hpSigmaM hpTauN
    have hNotConjugateMap : ∀ g : G,
        N ≠ M.map (MulAut.conj g).toMonoidHom := by
      intro g hEq
      exact hNotConjugate ⟨g, hEq⟩
    have hDisjoint : Disjoint (sigmaPrimes M) (sigmaPrimes N) :=
      sigma_partition hM hNmax hNotConjugateMap
    exact Set.disjoint_left.mp hDisjoint hqSigmaM hqSigmaN
  rw [hEsc.normalizer_Fcore_eq_sigma]
  exact (sigmaCore_isPiNumber N).coprime_compl hCentralizerPi

/-! ## Final assembly -/

/-- `BGsection16.v: BGsummaryII`, Bender--Glauberman Theorem II in the form
used by Peterfalvi. -/
noncomputable def BGsummaryII (M : Subgroup G) (X : Set G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hX : X = FTsupport M ∨ X = FTsupport0 M) :
    BGSummaryIIConclusion M X := by
  classical
  let summaryD : BGSummaryDConclusion M := BGsummaryD hM
  have hExceptional :
      outerExceptionalSet M (FTsupport0 M) ⊆ FTsupport1 M := by
    intro x hxOuter
    by_contra hxNotSupport1
    obtain ⟨a, haCentralizer, haNotM⟩ :=
      SetLike.not_le_iff_exists.mp hxOuter.2
    have hCommute : Commute a x :=
      (Subgroup.mem_centralizer_iff.mp haCentralizer x
        (Subgroup.mem_zpowers x)).symm
    have hConjugateFixed : conjugateElement16 x a = x := by
      change a * x * a⁻¹ = x
      calc
        a * x * a⁻¹ = x * a * a⁻¹ := by rw [hCommute.eq]
        _ = x := by simp
    have haM := support0_conjugator_mem16 hM
      (show x ∈ FTsupport0 M \ FTsupport1 M from
        ⟨hxOuter.1, hxNotSupport1⟩)
      (show conjugateElement16 x a ∈ FTsupport0 M by
        simpa [hConjugateFixed] using hxOuter.1)
    exact haNotM haM
  have hSupport0 : BGSummaryIIConclusion M (FTsupport0 M) := by
    refine
      { exceptional_subset_support1 := hExceptional
        fusion_control := ?_
        element_data := ?_ }
    · intro x hxSupport0 a hxaSupport0
      by_cases hxSupport1 : x ∈ FTsupport1 M
      · have hxSigma : x ∈ sigmaCore M := by
          rw [← def_FTcore hM]
          exact hxSupport1.1
        have hxaM : conjugateElement16 x a ∈ M :=
          (FTsupp0_sub M hxaSupport0).1
        have hxaCore : conjugateElement16 x a ∈ FTcore M := by
          have hBack :
              conjugateElement16 (conjugateElement16 x a) a⁻¹ ∈
                FTcore M := by
            simpa [conjugateElement16, MulAut.conj_apply, mul_assoc] using
              hxSupport1.1
          exact mem_FTcore_of_conjugate16 hM hxaM hBack
        have hxaSigma : conjugateElement16 x a ∈ sigmaCore M := by
          rw [← def_FTcore hM]
          exact hxaCore
        have hGlobal : conjugateElement16 x a ∈
            conjugacyClassWithin (⊤ : Subgroup G) x := by
          refine ⟨a⁻¹, by simp, ?_⟩
          simp [conjugateElement16, MulAut.conj_apply, mul_assoc]
        rcases summaryD.sigma_fusion hxSigma hxaSigma hGlobal with
          ⟨b, hbM, hb⟩
        exact ⟨b⁻¹, M.inv_mem hbM, by
          simpa [conjugateElement16, MulAut.conj_apply] using hb.symm⟩
      · exact ⟨a, support0_conjugator_mem16 hM
          ⟨hxSupport0, hxSupport1⟩ hxaSupport0, rfl⟩
    · intro x hxOuter
      have hxSupport1 : x ∈ FTsupport1 M := hExceptional hxOuter
      have hxSigma : x ∈ subgroupNonidentity (sigmaCore M) := by
        refine ⟨?_, hxSupport1.2⟩
        rw [← def_FTcore hM]
        exact hxSupport1.1
      let esc : BGSummaryDEscapingCentralizer M x :=
        summaryD.escaping_centralizer hxSigma hxOuter.2
      let N : Subgroup G := elementNormalizer15 x
      have hNmax : N ∈ minSimple_max_groups (G := G) := by
        rcases esc.normalizer_type with hNF | hNP2
        · exact hNF.1
        · exact hNP2.1.1
      have hTypeRange : FTtype N = 1 ∨ FTtype N = 2 := by
        rcases esc.normalizer_type with hNF | hNP2
        · exact Or.inl ((FTtype_Fmax hNF.1).1 hNF)
        · exact Or.inr ((FTtype_P2max hNP2.1.1).1 hNP2)
      have hFittingDecomposition : IsInternalSemidirectProductIn
          (Fitting_core N) (M ⊓ N) N := by
        rw [esc.normalizer_Fcore_eq_sigma]
        exact sdprod_sigma hNmax inf_le_right esc.intersection_hall
      have hBase : ftSignalizerBase x = N := rfl
      have hCentralizerDecomposition : IsInternalSemidirectProductIn
          (elementCentralizerWithin (Fitting_core N) x)
          (elementCentralizerWithin M x) (elementCentralizer x) := by
        rw [esc.normalizer_Fcore_eq_sigma]
        simpa [ftSignalizer, hBase] using
          (summaryD.signalizer hxSigma).centralizer_sdprod
      refine
        { unique_maximal_centralizer := esc.normalizer_unique
          type_one_or_two := hTypeRange
          fittingCore_complement := hFittingDecomposition
          centralizer_coprime := ?_
          support_not_support1 := esc.outer_support
          centralizer_decomposition := hCentralizerDecomposition
          typeTwo_frobenius := ?_ }
      · intro y hy
        exact escaping_fcore_coprime16 hM hxSigma hxOuter.2 esc hy
      · intro hTypeTwo
        have hNP2 : N ∈ typeP2MaximalSubgroups (G := G) :=
          (FTtype_P2max hNmax).2 hTypeTwo
        let typeP2Data : BGSummaryDTypeP2Case M := esc.typeP2_case hNP2
        have hFcoreSigma : Fitting_core M = sigmaCore M :=
          (Fcore_eq_Msigma hM).2
            (notP1type_Msigma_nil (Or.inl typeP2Data.typeF))
        exact
          { complement := typeP2Data.complement
            complement_le := typeP2Data.complement_le
            frobenius := by
              rw [hFcoreSigma]
              exact typeP2Data.frobenius
            complement_cyclic := typeP2Data.complement_cyclic }
  by_cases hOrdinary : X = FTsupport M
  · subst X
    exact restrictSummaryII (FTsupp_sub0 M) hSupport0
  · have hZero : X = FTsupport0 M := hX.resolve_left hOrdinary
    subst X
    exact hSupport0

end

end Submission.OddOrder.BG.Section16
