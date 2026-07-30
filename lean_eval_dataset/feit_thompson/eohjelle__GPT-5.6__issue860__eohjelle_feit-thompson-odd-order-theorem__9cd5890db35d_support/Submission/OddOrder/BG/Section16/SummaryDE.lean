import Submission.OddOrder.BG.Section16.TypesAndSupport
import Submission.OddOrder.BG.Section15.NonFTypeSignalizerBase
import Submission.OddOrder.BG.Section15.FittingCoreStructure
import Submission.OddOrder.BG.Section14.PartitionAndSignalizers
import Submission.OddOrder.BG.Section14.SigmaSupport
import Submission.OddOrder.BG.Section12.SigmaEmbedding
import Submission.OddOrder.MathlibSupport.SolvableHallContainment
import Submission.OddOrder.PF.Section02.ClassSupportPartition

/-!
# Bender--Glauberman Section 16: summaries D and E

This module packages the last two global summaries from `BGsection16.v` and
the maximal-subgroup transversal theorem between them.  The records below
spell out the nested conjunctions used by the source development.
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
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Public result interfaces -/

/-- The conjugates of `M` containing `x`. -/
def maximalConjugatesContaining (M : Subgroup G) (x : G) :
    Set (Subgroup G) :=
  {H | AreConjugateSubgroups M H ∧ x ∈ H}

/-- The signalizer assertions in clause (3) of summary D. -/
structure BGSummaryDSignalizerContext
    (M : Subgroup G) (x : G) : Prop where
  centralizer_hall :
    (Nat.card ((elementCentralizerWithin M x).subgroupOf
      (elementCentralizer x))).Coprime
        ((elementCentralizerWithin M x).subgroupOf
          (elementCentralizer x)).index
  centralizer_sdprod :
    IsInternalSemidirectProductIn (ftSignalizer x)
      (elementCentralizerWithin M x) (elementCentralizer x)
  transitive :
    ∀ {L H : Subgroup G},
      L ∈ maximalConjugatesContaining M x →
      H ∈ maximalConjugatesContaining M x →
      ∃ r : G, r ∈ ftSignalizer x ∧
        H = L.map (MulAut.conj r).toMonoidHom
  card_signalizer :
    Nat.card (ftSignalizer x) =
      (maximalConjugatesContaining M x).ncard

/-- The type-P2 branch at the end of summary D. -/
structure BGSummaryDTypeP2Case
    (M : Subgroup G) : Type u where
  typeF : M ∈ typeFMaximalSubgroups (G := G)
  complement : Subgroup G
  complement_le : complement ≤ M
  complement_hall :
    IsHall (sigmaPrimes M)ᶜ (complement.subgroupOf M)
  complement_cyclic : IsCyclic complement
  frobenius :
    IsFrobeniusDecomposition
      ((sigmaCore M).subgroupOf M) (complement.subgroupOf M)
  Fcore_not_normalizedTI :
    ¬ IsNormalizedTI (subgroupNonidentity (Fitting_core M)) ⊤ M

/-- Clause (4) of summary D when the element centralizer is not in `M`. -/
structure BGSummaryDEscapingCentralizer
    (M : Subgroup G) (x : G) : Type u where
  normalizer_unique :
    minSimple_max_groups_of (G := G)
      ((elementCentralizer x : Subgroup G) : Set G) =
        {elementNormalizer15 x}
  normalizer_Fcore_eq_sigma :
    Fitting_core (elementNormalizer15 x) =
      sigmaCore (elementNormalizer15 x)
  outer_support :
    x ∈ FTsupport (elementNormalizer15 x) \
      FTsupport1 (elementNormalizer15 x)
  normalizer_type :
    elementNormalizer15 x ∈
      typeFMaximalSubgroups (G := G) ∪
        typeP2MaximalSubgroups (G := G)
  intersection_hall :
    IsHall (sigmaPrimes (elementNormalizer15 x))ᶜ
      ((M ⊓ elementNormalizer15 x).subgroupOf
        (elementNormalizer15 x))
  typeP2_case :
    elementNormalizer15 x ∈ typeP2MaximalSubgroups (G := G) →
      BGSummaryDTypeP2Case M

/-- The four clauses of `BGsummaryD`. -/
structure BGSummaryDConclusion (M : Subgroup G) : Type u where
  sigma_fusion :
    ∀ {x : G}, x ∈ sigmaCore M →
      ∀ {y : G}, y ∈ sigmaCore M →
        y ∈ conjugacyClassWithin (⊤ : Subgroup G) x →
          y ∈ conjugacyClassWithin M x
  conjugate_intersection :
    ∀ g : G, g ∉ M →
      (sigmaCore M ⊓ conjugateSubgroup15 M g =
          sigmaCore M ⊓ conjugateSubgroup15 (sigmaCore M) g) ∧
        IsCyclic
          (sigmaCore M ⊓ conjugateSubgroup15 M g : Subgroup G)
  signalizer :
    ∀ {x : G}, x ∈ subgroupNonidentity (sigmaCore M) →
      BGSummaryDSignalizerContext M x
  escaping_centralizer :
    ∀ {x : G}, x ∈ subgroupNonidentity (sigmaCore M) →
      ¬ elementCentralizer x ≤ M →
        BGSummaryDEscapingCentralizer M x

/-- The source assertions bundled by `mmax_transversalP`. -/
structure MmaxTransversalSpec (U : Subgroup G) : Prop where
  subset_maximal :
    mmax_transversal U ⊆ minSimple_max_groups (G := G)
  representative :
    ∀ {M : Subgroup G}, M ∈ minSimple_max_groups (G := G) →
      ∃ N ∈ mmax_transversal U,
        AreConjugateSubgroupsWithin U M N
  conjugacy_injective :
    ∀ {M N : Subgroup G},
      M ∈ mmax_transversal U →
      N ∈ mmax_transversal U →
      AreConjugateSubgroupsWithin U M N → M = N

/-- The three clauses of `BGsummaryE`. -/
structure BGSummaryEConclusion (G : Type u)
    [Group G] [Finite G] [IsMinSimpleOddGroup G] : Prop where
  support_card :
    ∀ {M : Subgroup G}, M ∈ minSimple_max_groups (G := G) →
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover M)).ncard =
        (Nat.card (sigmaCore M) - 1) * M.index
  prime_sigma :
    ∀ {p : ℕ}, p ∈ primeSupport (Nat.card G) →
      ∃ M : Subgroup G,
        M ∈ minSimple_max_groups (G := G) ∧
          p ∈ sigmaPrimes M
  sigma_disjoint :
    ∀ {M H : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      H ∈ minSimple_max_groups (G := G) →
      ¬ AreConjugateSubgroups M H →
        Disjoint (sigmaPrimes M) (sigmaPrimes H)
  support_partition :
    IsSetPartition (pTypeSupportCover (G := G))
      (⋃₀ (pTypeSupportCover (G := G)))
  cover_eq_nonidentity_of_no_typeP :
    typePMaximalSubgroups (G := G) = ∅ →
      ⋃₀ (pTypeSupportCover (G := G)) = nonidentitySet G
  exceptional_partition :
    ∀ {M K : Subgroup G},
      M ∈ typePMaximalSubgroups (G := G) →
      K ≤ M →
      IsHall (kappaPrimes M) (K.subgroupOf M) →
      IsSetPartition
        {pTypeExceptionalSupport M K,
          ⋃₀ (pTypeSupportCover (G := G))}
        (nonidentitySet G)

/-! ## Hall and semidirect-product adapters -/

private theorem hall_complement
    {K : Type*} [Group K] [Finite K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsHall pi A) (hAB : A.IsComplement' B) :
    IsHall piᶜ B := by
  constructor
  · rw [← hAB.symm.index_eq_card]
    exact hA.isPiNumber_index
  · rw [hAB.index_eq_card]
    simpa using hA.isPiNumber_card

private theorem piSubgroup_le_normalHall
    {K : Type*} [Group K] [Finite K]
    {pi : Set ℕ} {A H : Subgroup K}
    (hHnormal : H.Normal) (hH : IsHall pi H)
    (hA : IsPiNumber pi (Nat.card A)) :
    A ≤ H := by
  letI : H.Normal := hHnormal
  have hcop : (Nat.card A).Coprime H.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpIndex
    exact hH.isPiNumber_index hp hpIndex (hA hp hpA)
  intro x hx
  let q : K →* K ⧸ H := QuotientGroup.mk' H
  have horderA : orderOf (q x) ∣ Nat.card A :=
    (orderOf_map_dvd q x).trans (A.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (q x) ∣ H.index := by
    simpa only [H.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderA horderIndex
  apply (QuotientGroup.eq_one_iff x).mp
  simpa [q] using orderOf_eq_one_iff.mp horderOne

private theorem bot_signalizer_product (H : Subgroup G) :
    IsInternalSemidirectProductIn ⊥ H H := by
  refine ⟨bot_le, le_rfl, inferInstance, ?_⟩
  simpa using
    (Subgroup.isComplement'_bot_left.mpr rfl :
      (⊥ : Subgroup H).IsComplement' ⊤)

/-! ## Conjugate intersections and signalizer support -/

private theorem sigmaCore_intersection_conjugate
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) (g : G) :
    sigmaCore M ⊓ conjugateSubgroup15 M g =
      sigmaCore M ⊓ conjugateSubgroup15 (sigmaCore M) g := by
  let Mg : Subgroup G := conjugateSubgroup15 M g
  let T : Subgroup G := sigmaCore M ⊓ Mg
  let Sg : Subgroup G := sigmaCore Mg
  have hMg : Mg ∈ minSimple_max_groups (G := G) := by
    simpa [Mg, conjugateSubgroup15] using
      (mmaxJ M (MulAut.conj g)).mpr hM
  have hTMg : T ≤ Mg := inf_le_right
  have hTpiM : IsPiNumber (sigmaPrimes M) (Nat.card T) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le inf_le_left)
  have hTpiMg : IsPiNumber (sigmaPrimes Mg)
      (Nat.card (T.subgroupOf Mg)) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hTMg]
    have hPrimes : sigmaPrimes Mg = sigmaPrimes M := by
      dsimp [Mg, conjugateSubgroup15]
      exact sigmaPrimes_conj M g
    rw [hPrimes]
    exact hTpiM
  have hTleSgSub : T.subgroupOf Mg ≤ Sg.subgroupOf Mg :=
    piSubgroup_le_normalHall
      (by simpa [Sg] using sigmaCore_normal Mg)
      (Msigma_Hall hMg) hTpiMg
  have hTleSg : T ≤ Sg := by
    intro x hx
    let xMg : Mg := ⟨x, hTMg hx⟩
    exact hTleSgSub (show xMg ∈ T.subgroupOf Mg from hx)
  have hT : T = sigmaCore M ⊓ Sg := by
    apply le_antisymm
    · exact le_inf inf_le_left hTleSg
    · intro x hx
      exact ⟨hx.1, sigmaCore_le Mg hx.2⟩
  calc
    sigmaCore M ⊓ conjugateSubgroup15 M g = T := rfl
    _ = sigmaCore M ⊓ Sg := hT
    _ = sigmaCore M ⊓ conjugateSubgroup15 (sigmaCore M) g := by
      change sigmaCore M ⊓ sigmaCore
          (M.map (MulAut.conj g).toMonoidHom) =
        sigmaCore M ⊓
          (sigmaCore M).map (MulAut.conj g).toMonoidHom
      rw [sigmaCore_conj]

private theorem tau2_element_mem_FTder
    {x : G}
    (hN : elementNormalizer15 x ∈ minSimple_max_groups (G := G))
    (hType : elementNormalizer15 x ∈
      typeFMaximalSubgroups (G := G) ∪
        typeP2MaximalSubgroups (G := G))
    (hxN : x ∈ elementNormalizer15 x)
    (hxTau : IsPiNumber
      (tau2Primes (elementNormalizer15 x)) (orderOf x)) :
    x ∈ FTder (elementNormalizer15 x) := by
  let N : Subgroup G := elementNormalizer15 x
  by_cases htype : FTtype N = 1
  · simpa [FTder, ftDerived, N, htype] using hxN
  · have hNP2 : N ∈ typeP2MaximalSubgroups (G := G) := by
      rcases hType with hNF | hNP2
      · exact (htype ((FTtype_Fmax hN).mp hNF)).elim
      · exact hNP2
    obtain ⟨K, hKN, hHallK⟩ :=
      MathlibSupport.exists_ambient_isHall_of_isSolvable
        (mmax_sol hN) (kappaPrimes N)
    obtain ⟨U, hCompl⟩ := ex_kappa_compl hN hKN hHallK
    have hKne : K ≠ ⊥ := by
      intro hKbot
      exact hNP2.1.2 ((trivg_kappa hN hKN hHallK).mp hKbot)
    have hstructure := kappa_structure hN hCompl
    have hderived := hstructure.derived_decomposition hKne
    let A : Subgroup G := Subgroup.zpowers x
    have hAN : A ≤ N := Subgroup.zpowers_le.mpr hxN
    let D : Subgroup G := sigmaCore N ⊔ U
    have hDnormal : (D.subgroupOf N).Normal := by
      simpa [D] using hstructure.sigmaU_K_sdprod.2.2.1
    have hDHall : IsHall (kappaPrimes N)ᶜ (D.subgroupOf N) := by
      simpa [D] using hall_complement hHallK
        hstructure.sigmaU_K_sdprod.2.2.2.symm
    have htauCompl : tau2Primes N ⊆ (kappaPrimes N)ᶜ := by
      intro p hpTau hpKappa
      rcases kappa_tau13 hpKappa with hpTau1 | hpTau3
      · exact tau2'1 N hpTau1 hpTau
      · exact tau3'2 N hpTau hpTau3
    have hApi : IsPiNumber (kappaPrimes N)ᶜ
        (Nat.card (A.subgroupOf N)) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hAN]
      simpa [A, Nat.card_zpowers] using hxTau.mono htauCompl
    have hADsub : A.subgroupOf N ≤ D.subgroupOf N :=
      piSubgroup_le_normalHall hDnormal hDHall hApi
    have hAD : A ≤ D := by
      intro a ha
      let aN : N := ⟨a, hAN ha⟩
      exact hADsub (show aN ∈ A.subgroupOf N from ha)
    have hxDerived : x ∈ derivedWithin N :=
      (sup_le hderived.1 hderived.2.1)
        (hAD (Subgroup.mem_zpowers x))
    simpa [FTder, ftDerived, N, htype] using hxDerived

private theorem large_signalizer_outer_support
    {x : G} (hx1 : x ≠ 1)
    (hLarge : FTSignalizerLargeContext x
      (ftSignalizerBase x) (ftSignalizer x)) :
    x ∈ FTsupport (elementNormalizer15 x) \
      FTsupport1 (elementNormalizer15 x) := by
  let N : Subgroup G := elementNormalizer15 x
  have hbase : ftSignalizerBase x = N := rfl
  have hNmax : N ∈ minSimple_max_groups (G := G) := by
    simpa [hbase] using hLarge.base_maximal
  have hType : N ∈
      typeFMaximalSubgroups (G := G) ∪
        typeP2MaximalSubgroups (G := G) := by
    simpa [hbase] using hLarge.base_type
  have hxTau : IsPiNumber (tau2Primes N) (orderOf x) := by
    simpa [hbase] using hLarge.x_tau2
  have hxCentSelf : x ∈ elementCentralizer x := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl x).zpow_left n).eq
  have hxN : x ∈ N := hLarge.centralizer_le_base hxCentSelf
  have hxDer : x ∈ FTder N :=
    tau2_element_mem_FTder hNmax hType hxN hxTau
  obtain ⟨⟨r, hrR⟩, hr1sub⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hLarge.signalizer_ne_bot
  have hr1 : r ≠ 1 := fun hr ↦ hr1sub (Subtype.ext hr)
  have hrSigma : r ∈ sigmaCore N := by
    simpa [ftSignalizer, hbase] using hrR.1
  have hrCore : r ∈ FTcore N := by
    rw [def_FTcore hNmax]
    exact hrSigma
  have hrSupport1 : r ∈ FTsupport1 N := ⟨hrCore, hr1⟩
  have hrx : Commute r x :=
    (hrR.2 x (Subgroup.mem_zpowers x)).symm
  have hxCent : x ∈ elementCentralizerWithin (FTder N) r := by
    refine ⟨hxDer, ?_⟩
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact hrx.zpow_left n
  have hxSupport : x ∈ FTsupport N := by
    simp only [FTsupport, ftSupport, Set.mem_iUnion]
    exact ⟨r, hrSupport1, ⟨hxCent, hx1⟩⟩
  have hxNotSupport1 : x ∉ FTsupport1 N := by
    intro hxSupport1
    have hxSigma : x ∈ sigmaCore N := by
      rw [← def_FTcore hNmax]
      exact hxSupport1.1
    have hxSigmaPi : IsPiNumber (sigmaPrimes N) (orderOf x) :=
      (sigmaCore_isPiNumber N).of_dvd
        ((sigmaCore N).orderOf_dvd_natCard hxSigma)
    have hxSigmaCompl : IsPiNumber (sigmaPrimes N)ᶜ (orderOf x) :=
      hxTau.mono fun _ hpTau ↦ hpTau.2.1
    have hxOrder : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (hxSigmaPi.coprime_compl hxSigmaCompl) dvd_rfl dvd_rfl
    exact hx1 (orderOf_eq_one_iff.mp hxOrder)
  exact ⟨hxSupport, hxNotSupport1⟩

private theorem conjugatesContaining_eq_sigmaOvergroups
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hxM : x ∈ sigmaCore M) (hx1 : x ≠ 1) :
    maximalConjugatesContaining M x =
      sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) := by
  classical
  ext H
  change (AreConjugateSubgroups M H ∧ x ∈ H) ↔
    H ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)
  constructor
  · rintro ⟨⟨g, rfl⟩, hxConj⟩
    let Mg : Subgroup G := M.map (MulAut.conj g).toMonoidHom
    let A : Subgroup G := Subgroup.zpowers x
    have hMg : Mg ∈ minSimple_max_groups (G := G) := by
      simpa [Mg] using (mmaxJ M (MulAut.conj g)).mpr hM
    have hAMg : A ≤ Mg := by
      simpa [A, Mg] using Subgroup.zpowers_le.mpr hxConj
    have hxPiM : IsPiNumber (sigmaPrimes M) (orderOf x) :=
      (sigmaCore_isPiNumber M).of_dvd
        ((sigmaCore M).orderOf_dvd_natCard hxM)
    have hApi : IsPiNumber (sigmaPrimes Mg)
        (Nat.card (A.subgroupOf Mg)) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hAMg]
      have hPrimes : sigmaPrimes Mg = sigmaPrimes M := by
        dsimp [Mg]
        exact sigmaPrimes_conj M g
      rw [hPrimes]
      simpa [A, Nat.card_zpowers] using hxPiM
    have hAleSigmaSub : A.subgroupOf Mg ≤
        (sigmaCore Mg).subgroupOf Mg :=
      piSubgroup_le_normalHall
        (by simpa using sigmaCore_normal Mg)
        (Msigma_Hall hMg) hApi
    refine ⟨hMg, ?_⟩
    intro y hy
    let yMg : Mg := ⟨y, hAMg hy⟩
    exact hAleSigmaSub (show yMg ∈ A.subgroupOf Mg from hy)
  · rintro ⟨hH, hxHcore⟩
    have hxSigmaH : x ∈ sigmaCore H :=
      hxHcore (Subgroup.mem_zpowers x)
    refine ⟨?_, sigmaCore_le H hxSigmaH⟩
    by_contra hnotConj
    have hnotConj' : ∀ g : G,
        H ≠ M.map (MulAut.conj g).toMonoidHom := by
      intro g hEq
      exact hnotConj ⟨g, hEq⟩
    have hdisjoint : Disjoint (sigmaPrimes M) (sigmaPrimes H) :=
      sigma_partition hM hH hnotConj'
    have hxPiM : IsPiNumber (sigmaPrimes M) (orderOf x) :=
      (sigmaCore_isPiNumber M).of_dvd
        ((sigmaCore M).orderOf_dvd_natCard hxM)
    have hxPiH : IsPiNumber (sigmaPrimes H) (orderOf x) :=
      (sigmaCore_isPiNumber H).of_dvd
        ((sigmaCore H).orderOf_dvd_natCard hxSigmaH)
    obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd
      (fun h ↦ hx1 (orderOf_eq_one_iff.mp h))
    exact (Set.disjoint_left.mp hdisjoint)
      (hxPiM hp hpOrder) (hxPiH hp hpOrder)

/-! ## The four fields of summary D -/

private theorem summaryD_sigma_fusion
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    ∀ {x : G}, x ∈ sigmaCore M →
      ∀ {y : G}, y ∈ sigmaCore M →
        y ∈ conjugacyClassWithin (⊤ : Subgroup G) x →
          y ∈ conjugacyClassWithin M x := by
  intro x hx y hy hyConj
  rcases hyConj with ⟨a, _, rfl⟩
  have hHallSelf : IsHall (sigmaPrimes M)
      ((sigmaCore M).subgroupOf (sigmaCore M)) := by
    constructor
    · rw [MathlibSupport.natCard_subgroupOf_eq le_rfl]
      exact sigmaCore_isPiNumber M
    · simpa using (IsPiNumber.one : IsPiNumber (sigmaPrimes M)ᶜ 1)
  have hxa : (MulAut.conj a⁻¹) x ∈ sigmaCore M := by
    simpa [MulAut.conj_apply, mul_assoc] using hy
  obtain ⟨b, hb, hconj⟩ :=
    sigma_Hall_tame hM le_rfl hHallSelf hx hxa
  refine ⟨b⁻¹, M.inv_mem hb.1, ?_⟩
  simpa [MulAut.conj_apply, mul_assoc] using hconj.symm

private theorem summaryD_conjugate_intersection
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    ∀ g : G, g ∉ M →
      (sigmaCore M ⊓ conjugateSubgroup15 M g =
          sigmaCore M ⊓ conjugateSubgroup15 (sigmaCore M) g) ∧
        IsCyclic
          (sigmaCore M ⊓ conjugateSubgroup15 M g : Subgroup G) := by
  intro g hg
  obtain ⟨E, hEM, hHallE⟩ := ex_sigma_compl hM
  have hEmbedding := sigma_compl_embedding hM hEM hHallE
  exact ⟨sigmaCore_intersection_conjugate hM g,
    (hEmbedding.2.2 g hg).1⟩

private theorem summaryD_signalizer
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hx : x ∈ subgroupNonidentity (sigmaCore M)) :
    BGSummaryDSignalizerContext M x := by
  have hell : sigmaLength x = 1 := Msigma_ell1 hM hx.1 hx.2
  have hctx := FT_signalizer_context hell
  have hMmem : M ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G) :=
    ⟨hM, Subgroup.zpowers_le.mpr hx.1⟩
  have hsd : IsInternalSemidirectProductIn (ftSignalizer x)
      (elementCentralizerWithin M x) (elementCentralizer x) := by
    by_cases hmore : 1 <
        (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard
    · have hlarge := hctx.large hmore
      have hCMbase :
          elementCentralizerWithin (M ⊓ ftSignalizerBase x) x =
            elementCentralizerWithin M x := by
        apply le_antisymm
        · intro y hy
          exact ⟨hy.1.1, hy.2⟩
        · intro y hy
          exact ⟨⟨hy.1, hlarge.centralizer_le_base hy.2⟩, hy.2⟩
      simpa [hCMbase] using
        (hlarge.overgroup_context hMmem).centralizer_sdprod
    · have hcard :
          (sigmaMaximalOvergroups
            (Subgroup.zpowers x : Set G)).ncard = 1 := by
        exact Nat.le_antisymm (Nat.le_of_not_gt hmore)
          ((Set.ncard_pos).mpr ⟨M, hMmem⟩)
      have hRbot : ftSignalizer x = ⊥ := hctx.small_signalizer hmore
      have hcent : elementCentralizer x ≤ M :=
        cent1_sub_uniq_sigma_mmax hcard hMmem
      have hCM : elementCentralizerWithin M x =
          elementCentralizer x := by
        apply le_antisymm inf_le_right
        intro y hy
        exact ⟨hcent hy, hy⟩
      simpa [hRbot, hCM] using
        bot_signalizer_product (elementCentralizer x)
  have hfamily := conjugatesContaining_eq_sigmaOvergroups
    hM hx.1 hx.2
  refine
    { centralizer_hall := ?_
      centralizer_sdprod := hsd
      transitive := ?_
      card_signalizer := ?_ }
  · exact (hall_complement hctx.basic.R_hall hsd.2.2.2).coprime_card_index
  · intro L H hL hH
    rw [hfamily] at hL hH
    exact hctx.basic.transitive hL hH
  · rw [hfamily]
    exact hctx.basic.card_eq

private noncomputable def summaryD_typeP2_case
    {M : Subgroup G} {x : G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hx : x ∈ subgroupNonidentity (sigmaCore M))
    (hcentNot : ¬ elementCentralizer x ≤ M)
    (hNP2 : elementNormalizer15 x ∈
      typeP2MaximalSubgroups (G := G)) :
    BGSummaryDTypeP2Case M := by
  let N : Subgroup G := elementNormalizer15 x
  have hnotF : N ∉ typeFMaximalSubgroups (G := G) := by
    simpa [N] using hNP2.1.2
  have hbaseFacts := nonFtype_signalizer_base
    hM hx.1 hx.2 hcentNot hnotF
  have hSigmaNilM : Group.IsNilpotent (sigmaCore M) := by
    have hnilSub : Group.IsNilpotent ((sigmaCore M).subgroupOf M) :=
      Frobenius_sol_kernel_nil hbaseFacts.frobenius (mmax_sol hM)
    exact (Group.isNilpotent_congr
      (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M))).mp hnilSub
  have hFcoreM : Fitting_core M = sigmaCore M :=
    (Fcore_eq_Msigma hM).mpr hSigmaNilM
  have hnotTI :
      ¬ IsNormalizedTI (subgroupNonidentity (Fitting_core M)) ⊤ M := by
    intro hTI
    obtain ⟨y, hyCent, hyM⟩ := SetLike.not_le_iff_exists.mp hcentNot
    have hxFcore : x ∈ subgroupNonidentity (Fitting_core M) :=
      ⟨hFcoreM.symm ▸ hx.1, hx.2⟩
    have hyWithin : y ∈
        centralizerWithin (⊤ : Subgroup G) (Subgroup.zpowers x) :=
      ⟨Subgroup.mem_top y, hyCent⟩
    exact hyM (hTI.centralizerWithin_zpowers_le hxFcore hyWithin)
  exact
    { typeF := hbaseFacts.M_typeF
      complement := hbaseFacts.complement
      complement_le := hbaseFacts.complement_le
      complement_hall := hbaseFacts.complement_hall
      complement_cyclic := hbaseFacts.complement_cyclic
      frobenius := hbaseFacts.frobenius
      Fcore_not_normalizedTI := hnotTI }

private noncomputable def summaryD_escaping_centralizer
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hx : x ∈ subgroupNonidentity (sigmaCore M))
    (hcentNot : ¬ elementCentralizer x ≤ M) :
    BGSummaryDEscapingCentralizer M x := by
  have hell : sigmaLength x = 1 := Msigma_ell1 hM hx.1 hx.2
  have hctx := FT_signalizer_context hell
  have hMmem : M ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G) :=
    ⟨hM, Subgroup.zpowers_le.mpr hx.1⟩
  have hmore : 1 <
      (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard := by
    by_contra hnot
    have hcard :
        (sigmaMaximalOvergroups
          (Subgroup.zpowers x : Set G)).ncard = 1 := by
      exact Nat.le_antisymm (Nat.le_of_not_gt hnot)
        ((Set.ncard_pos).mpr ⟨M, hMmem⟩)
    exact hcentNot (cent1_sub_uniq_sigma_mmax hcard hMmem)
  have hlarge := hctx.large hmore
  let N : Subgroup G := elementNormalizer15 x
  have hbase : ftSignalizerBase x = N := rfl
  have hNmax : N ∈ minSimple_max_groups (G := G) := by
    simpa [hbase] using hlarge.base_maximal
  have hType : N ∈
      typeFMaximalSubgroups (G := G) ∪
        typeP2MaximalSubgroups (G := G) := by
    simpa [hbase] using hlarge.base_type
  have hxTau : IsPiNumber (tau2Primes N) (orderOf x) := by
    simpa [hbase] using hlarge.x_tau2
  have hSigmaNil : Group.IsNilpotent (sigmaCore N) := by
    obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd
      (fun h ↦ hx.2 (orderOf_eq_one_iff.mp h))
    exact tau2_Msigma_nil hNmax (hxTau hp hpOrder)
  have hFcoreEq : Fitting_core N = sigmaCore N :=
    (Fcore_eq_Msigma hNmax).mpr hSigmaNil
  have hOuter : x ∈ FTsupport N \ FTsupport1 N :=
    large_signalizer_outer_support hx.2 hlarge
  have hHall : IsHall (sigmaPrimes N)ᶜ
      ((M ⊓ N).subgroupOf N) := by
    change IsHall (sigmaPrimes (ftSignalizerBase x))ᶜ
      ((M ⊓ ftSignalizerBase x).subgroupOf (ftSignalizerBase x))
    exact (hlarge.overgroup_context hMmem).hall_intersection
  refine
    { normalizer_unique := ?_
      normalizer_Fcore_eq_sigma := hFcoreEq
      outer_support := hOuter
      normalizer_type := hType
      intersection_hall := hHall
      typeP2_case := ?_ }
  · simpa [N, hbase] using hlarge.centralizer_maximal
  · intro hNP2
    exact summaryD_typeP2_case hM hx hcentNot hNP2

/-- `BGsection16.v: BGsummaryD`, Bender--Glauberman summary D. -/
noncomputable def BGsummaryD
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    BGSummaryDConclusion M :=
  { sigma_fusion := summaryD_sigma_fusion hM
    conjugate_intersection := summaryD_conjugate_intersection hM
    signalizer := summaryD_signalizer hM
    escaping_centralizer := summaryD_escaping_centralizer hM }

/-! ## Maximal-subgroup transversal -/

/-- `BGsection16.v: mmax_transversalP`. -/
theorem mmax_transversalP :
    MmaxTransversalSpec (⊤ : Subgroup G) :=
  { subset_maximal := mmax_transversal_subset ⊤
    representative := by
      intro M hM
      exact exists_mem_mmax_transversal_conjugate ⊤ M hM
    conjugacy_injective := by
      intro M N hM hN hMN
      exact mmax_transversal_conjugate_injective ⊤ hM hN hMN }

/-! ## Partition adapters and summary E -/

private theorem merge_partition_blocks
    {C D : Set G} {P : Set (Set G)}
    (hpart : IsSetPartition ({C} ∪ P) D)
    (hCnot : C ∉ P) (hPne : P.Nonempty) :
    IsSetPartition {C, ⋃₀ P} D := by
  have hCdis : Disjoint C (⋃₀ P) := by
    rw [Set.disjoint_sUnion_right]
    intro B hB
    exact hpart.2.1 (Or.inl rfl) (Or.inr hB)
      (fun hCB ↦ hCnot (hCB.symm ▸ hB))
  have hCne : C ≠ (∅ : Set G) := by
    intro hC
    exact hpart.2.2 (Or.inl hC.symm)
  have hUnionNe : ⋃₀ P ≠ (∅ : Set G) := by
    obtain ⟨B, hB⟩ := hPne
    have hBne : B ≠ (∅ : Set G) := by
      intro hB0
      exact hpart.2.2 (Or.inr (hB0 ▸ hB))
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hBne
    intro hUnion
    have hxUnion : x ∈ ⋃₀ P := Set.mem_sUnion_of_mem hx hB
    rw [hUnion] at hxUnion
    simpa using hxUnion
  refine ⟨?_, ?_, ?_⟩
  · calc
      ⋃₀ {C, ⋃₀ P} = C ∪ ⋃₀ P := by simp
      _ = ⋃₀ ({C} ∪ P) := by simp
      _ = D := hpart.1
  · intro A hA B hB hAB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hCdis
    · exact hCdis.symm
    · exact (hAB rfl).elim
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hCne, Ne.symm hUnionNe⟩

private theorem partition_of_subfamily
    {P Q : Set (Set G)} {D : Set G}
    (hpart : IsSetPartition P D) (hQP : Q ⊆ P) :
    IsSetPartition Q (⋃₀ Q) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro A hA B hB hAB
    exact hpart.2.1 (hQP hA) (hQP hB) hAB
  · exact fun hzero ↦ hpart.2.2 (hQP hzero)

/-- `BGsection16.v: BGsummaryE`, Bender--Glauberman summary E. -/
theorem BGsummaryE : BGSummaryEConclusion G := by
  classical
  refine
    { support_card := fun hM ↦ card_class_support_sigma hM
      prime_sigma := fun hp ↦ sigma_mmax_exists hp
      sigma_disjoint := ?_
      support_partition := ?_
      cover_eq_nonidentity_of_no_typeP := ?_
      exceptional_partition := ?_ }
  · intro M H hM hH hnot
    apply sigma_partition hM hH
    intro g hconj
    exact hnot ⟨g, hconj⟩
  · by_cases hPempty : typePMaximalSubgroups (G := G) = ∅
    · exact ⟨rfl, ((mFT_partition (G := G)).1 hPempty).2⟩
    · obtain ⟨M, hMP⟩ :
          (typePMaximalSubgroups (G := G)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hPempty
      obtain ⟨K, hKM, hHallK⟩ :=
        MathlibSupport.exists_ambient_isHall_of_isSolvable
          (mmax_sol hMP.1) (kappaPrimes M)
      apply partition_of_subfamily
        ((mFT_partition (G := G)).2 M K hMP hKM hHallK).1
      intro A hA
      exact Or.inr hA
  · intro hPempty
    exact ((mFT_partition (G := G)).1 hPempty).1
  · intro M K hMP hKM hHallK
    have hfull := (mFT_partition (G := G)).2 M K hMP hKM hHallK
    have hcoverNonempty : (pTypeSupportCover (G := G)).Nonempty := by
      refine ⟨classSupportWithin (⊤ : Subgroup G) (sigmaCover M), ?_⟩
      exact ⟨M, hMP.1, rfl⟩
    exact merge_partition_blocks hfull.1 hfull.2 hcoverNonempty

end

end Submission.OddOrder.BG.Section16
