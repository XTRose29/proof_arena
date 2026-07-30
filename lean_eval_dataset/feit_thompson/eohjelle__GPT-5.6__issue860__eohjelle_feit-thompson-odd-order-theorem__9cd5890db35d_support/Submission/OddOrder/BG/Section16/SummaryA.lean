import Submission.OddOrder.BG.Section16.TypesAndSupport
import Submission.OddOrder.BG.Section15.FittingCoreStructure
import Submission.OddOrder.BG.Section15.NonTIFittingAndSignalizer
import Submission.OddOrder.BG.Section14.PTypeStructure
import Submission.OddOrder.BG.Section14.PTypeEmbedding
import Submission.OddOrder.BG.Section14.PartitionAndSignalizers
import Submission.OddOrder.BG.Section12.SigmaNilpotent
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.PF.Section03.InternalDirectProduct
import Mathlib.GroupTheory.Exponent

/-!
# Bender--Glauberman Section 16: summary A

This phase states and proves the eight conclusions collected in summary A,
together with the type-selected derived-subgroup decomposition used by the
later Section 16 summaries.
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

/-- `B` is a complement to `A` inside the ambient subgroup `M`. -/
def IsComplementIn (A B M : Subgroup G) : Prop :=
  A ≤ M ∧ B ≤ M ∧
    (A.subgroupOf M).IsComplement' (B.subgroupOf M)

/-- The fixed-point-free conclusion in summary A(4). -/
def IsFixedPointFreeOn (U K : Subgroup G) : Prop :=
  ∀ {k : G}, k ∈ K → k ≠ 1 →
    centralizerWithin U (Subgroup.zpowers k) = ⊥

/-- The eight numbered clauses of `BGsummaryA`. -/
structure BGSummaryA (M U K : Subgroup G) : Prop where
  sigmaCore_normal : ((sigmaCore M).subgroupOf M).Normal
  sigmaCore_hall_M :
    IsHall (sigmaPrimes M) ((sigmaCore M).subgroupOf M)
  sigmaCore_hall_G : IsHall (sigmaPrimes M) (sigmaCore M)
  K_hall : IsHall (kappaPrimes M) (K.subgroupOf M)
  K_cyclic : IsCyclic K
  U_complements_sigma_K :
    IsComplementIn (sigmaCore M ⊔ K) U M
  K_normalizes_U : K ≤ Subgroup.normalizer (U : Set G)
  sigma_U_normal : ((sigmaCore M ⊔ U).subgroupOf M).Normal
  U_normal_UK : (U.subgroupOf (U ⊔ K)).Normal
  sigma_U_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M) U
      (sigmaCore M ⊔ U)
  sigmaU_K_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M ⊔ U) K M
  fixed_point_free : IsFixedPointFreeOn U K
  partner_ne_bot : pTypePartner M K ≠ ⊥
  centralizer_direct : ∀ {k : G}, k ∈ K → k ≠ 1 →
    IsInternalDirectProductIn K (pTypePartner M K)
      (elementCentralizerWithin M k)
  Fcore_ne_bot : Fitting_core M ≠ ⊥
  Fcore_le_sigma : Fitting_core M ≤ sigmaCore M
  sigma_le_derived : sigmaCore M ≤ derivedWithin M
  derived_lt : derivedWithin M < M
  Fcore_normal_derived :
    ((Fitting_core M).subgroupOf (derivedWithin M)).Normal
  derived_mod_Fcore_nilpotent :
    letI : ((Fitting_core M).subgroupOf (derivedWithin M)).Normal :=
      Fcore_normal_derived
    Group.IsNilpotent
      (derivedWithin M ⧸
        (Fitting_core M).subgroupOf (derivedWithin M))
  secondDerived_le_fitting : secondDerivedWithin M ≤ fittingWithin M
  Fcore_join_centralizer :
    Fitting_core M ⊔ centralizerWithin M (Fitting_core M) =
      fittingWithin M
  fitting_le_derived_of_K_ne_bot :
    K ≠ ⊥ → fittingWithin M ≤ derivedWithin M
  nonnilpotent_case : Fitting_core M ≠ sigmaCore M →
    U = ⊥ ∧
      IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M ∧
      (Nat.card K).Prime

/-! ## Assembly lemmas -/

/-- The two nested semidirect decompositions attached to a kappa complement
also exhibit `U` as a complement to `sigmaCore M ⊔ K` inside `M`. -/
private theorem complement_sigma_join_kappa
    {M U K : Subgroup G}
    (hCompl : KappaComplement M U K)
    (hctx : KappaComplementContext M U K) :
    IsComplementIn (sigmaCore M ⊔ K) U M := by
  classical
  let S : Subgroup G := sigmaCore M
  let A : Subgroup G := S ⊔ K
  have hSM : S ≤ M := by
    simpa [S] using sigmaCore_le M
  have hKM : K ≤ M := hCompl.K_le_M
  have hUM : U ≤ M := hCompl.U_le_M
  have hAM : A ≤ M := sup_le hSM hKM
  refine ⟨by simpa [A, S] using hAM, hUM, ?_⟩

  have hSigma : IsPiNumber (sigmaPrimes M) (Nat.card S) := by
    simpa [S] using sigmaCore_isPiNumber M
  have hKappa : IsPiNumber (kappaPrimes M) (Nat.card K) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
      hCompl.hall_K.isPiNumber_card
  have hKappaCompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) :=
    hKappa.mono (kappa_sigma' M)
  have hSK : Disjoint S K :=
    Subgroup.disjoint_of_coprime_natCard
      (hSigma.coprime_compl hKappaCompl)
  have hMnormalizesS : M ≤ Subgroup.normalizer (S : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mp
    simpa [S] using sigmaCore_normal M
  have hKnormalizesS : K ≤ Subgroup.normalizer (S : Set G) :=
    hKM.trans hMnormalizesS
  have hAcard : Nat.card A = Nat.card S * Nat.card K := by
    have hcard := natCard_sup_eq_mul_of_disjoint_of_le_normalizer
      hSK.symm hKnormalizesS
    calc
      Nat.card A = Nat.card (K ⊔ S : Subgroup G) := by
        simp only [A, sup_comm]
      _ = Nat.card K * Nat.card S := hcard
      _ = Nat.card S * Nat.card K := Nat.mul_comm _ _

  have hUKcard : Nat.card U * Nat.card K = Nat.card (U ⊔ K : Subgroup G) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq le_sup_left,
      MathlibSupport.natCard_subgroupOf_eq le_sup_right] using
      hctx.U_K_sdprod.2.2.2.card_mul
  have hMcard : Nat.card S * Nat.card (U ⊔ K : Subgroup G) = Nat.card M := by
    simpa only [S, MathlibSupport.natCard_subgroupOf_eq hSM,
      MathlibSupport.natCard_subgroupOf_eq hctx.U_sup_K_le_M] using
      hctx.sigma_UK_sdprod.2.2.2.card_mul
  have hProductCard :
      Nat.card (A.subgroupOf M) * Nat.card (U.subgroupOf M) =
        Nat.card M := by
    rw [MathlibSupport.natCard_subgroupOf_eq hAM,
      MathlibSupport.natCard_subgroupOf_eq hUM, hAcard]
    calc
      (Nat.card S * Nat.card K) * Nat.card U =
          Nat.card S * (Nat.card U * Nat.card K) := by ac_rfl
      _ = Nat.card S * Nat.card (U ⊔ K : Subgroup G) := by
        rw [hUKcard]
      _ = Nat.card M := hMcard

  have hA_pi : IsPiNumber (sigmaKappaPrimes M) (Nat.card A) := by
    rw [hAcard]
    exact
      (hSigma.mono (fun _ hp ↦ Or.inl hp)).mul
        (hKappa.mono (fun _ hp ↦ Or.inr hp))
  have hU_pi : IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hUM] using
      hCompl.hall_U.isPiNumber_card
  have hCoprime :
      Nat.Coprime (Nat.card (A.subgroupOf M))
        (Nat.card (U.subgroupOf M)) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hAM,
      MathlibSupport.natCard_subgroupOf_eq hUM] using
      hA_pi.coprime_compl hU_pi
  simpa only [A, S] using
    Subgroup.isComplement'_of_coprime hProductCard hCoprime

omit [Finite G] [IsMinSimpleOddGroup G] in
/-- Semiregularity of the kappa-complement action has the centralizer form
used by summary A. -/
private theorem centralizer_zpowers_eq_bot
    {U K : Subgroup G}
    (hreg : IsSemiregularConjugation U K)
    {k : G} (hkK : k ∈ K) (hk1 : k ≠ 1) :
    centralizerWithin U (Subgroup.zpowers k) = ⊥ := by
  apply le_bot_iff.mp
  intro u hu
  have hku : k * u = u * k :=
    Subgroup.mem_centralizer_iff.mp hu.2 k (Subgroup.mem_zpowers k)
  have hfixed : k * u * k⁻¹ = u := by
    calc
      k * u * k⁻¹ = u * k * k⁻¹ := by rw [hku]
      _ = u := by simp
  let kK : K := ⟨k, hkK⟩
  let uU : U := ⟨u, hu.1⟩
  have hkK_ne : kK ≠ 1 := by
    intro h
    exact hk1 (congrArg Subtype.val h)
  have huU : uU = 1 := hreg kK hkK_ne uU hfixed
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val huU)

/-! ## Summary A -/

/-- `BGsection16.v: BGsummaryA`. -/
theorem BGsummaryA
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    BGSummaryA M U K := by
  classical
  have hctx : KappaComplementContext M U K :=
    kappa_compl_context hM hCompl
  have hkappa : KappaStructure M U K := kappa_structure hM hCompl
  have hcore : FCoreStructure M := Fcore_structure hM
  have hfit : FittingStructure M := Fitting_structure hM
  have hTypeP (hKne : K ≠ ⊥) :
      M ∈ typePMaximalSubgroups (G := G) := by
    refine ⟨hM, ?_⟩
    intro hF
    exact hKne
      ((trivg_kappa hM hCompl.K_le_M hCompl.hall_K).2 hF)

  have hKnormalizesU : K ≤ Subgroup.normalizer (U : Set G) :=
    hctx.U_K_sdprod.2.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        hctx.U_K_sdprod.1).mp hctx.U_K_sdprod.2.2.1)

  have hPartner : pTypePartner M K ≠ ⊥ := by
    by_cases hKbot : K = ⊥
    · subst K
      have hPartnerBot :
          pTypePartner M (⊥ : Subgroup G) = sigmaCore M := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          refine ⟨hx, ?_⟩
          intro y hy
          rw [Subgroup.mem_bot.mp hy]
          simp
      rw [hPartnerBot]
      exact Msigma_neq1 hM
    · simpa [pTypePartner, pTypeCentralizer] using
        (Ptype_structure (hTypeP hKbot) hCompl.K_le_M
          hCompl.hall_K).Kstar_ne_bot

  have hCentralizers : ∀ {k : G}, k ∈ K → k ≠ 1 →
      IsInternalDirectProductIn K (pTypePartner M K)
        (elementCentralizerWithin M k) := by
    intro k hkK hk1
    have hKne : K ≠ ⊥ := by
      intro hKbot
      subst K
      exact hk1 (Subgroup.mem_bot.mp hkK)
    have hP := Ptype_structure (hTypeP hKne) hCompl.K_le_M
      hCompl.hall_K
    obtain ⟨Mstar, hemb⟩ :=
      Ptype_embedding (hTypeP hKne) hCompl.K_le_M hCompl.hall_K
    have hcent := hemb.cyclicStructure.centralizer_left hkK hk1
    have hJoinNormalizer :
        pTypeJoin M K = normalizerWithin M K := by
      have htop := hP.normalizer_direct.complement.sup_eq_top
      have hmapped := congrArg
        (Subgroup.map (normalizerWithin M K).subtype) htop
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hP.normalizer_direct.left_le,
        Subgroup.map_subgroupOf_eq_of_le hP.normalizer_direct.right_le,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapped
      simpa [pTypeJoin, pTypePartner] using hmapped
    change IsInternalDirectProductIn K (pTypePartner M K)
      (centralizerWithin M (Subgroup.zpowers k))
    rw [hcent, hJoinNormalizer]
    simpa [pTypePartner, pTypeCentralizer] using hP.normalizer_direct

  have hExceptional : Fitting_core M ≠ sigmaCore M →
      U = ⊥ ∧
        IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M ∧
        (Nat.card K).Prime := by
    intro hCoreNe
    let q := Nat.card (pTypePartner M K)
    have hSigmaSolvable : IsSolvable (sigmaCore M) := by
      letI : IsSolvable M := mmax_sol hM
      exact isSolvable_of_injective
        (Subgroup.inclusion (sigmaCore_le M))
        (Subgroup.inclusion_injective (sigmaCore_le M))
    obtain ⟨D, hDsigma, hHallD⟩ :=
      MathlibSupport.exists_ambient_isHall_of_isSolvable
        hSigmaSolvable
        ({q} : Set ℕ)ᶜ
    have hn := hcore.nonnilpotent
      hCompl.K_le_M hCompl.hall_K hCoreNe hDsigma
      (by simpa [q, pTypePartner, kappaCentralizer] using hHallD)
    have hUbot : U = ⊥ :=
      (trivg_kappa_compl hM hCompl).2 hn.typeP1
    have hTI :
        IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M := by
      by_contra hNotTI
      rcases nonTI_Fitting_facts hM hNotTI with hF | hP1
      · have hKbot :=
          (trivg_kappa hM hCompl.K_le_M hCompl.hall_K).2 hF
        have hcardK : Nat.card K = 1 := Subgroup.card_eq_one.mpr hKbot
        exact hn.card_K_prime.ne_one hcardK
      · exact hCoreNe hP1.2.1
    exact ⟨hUbot, hTI, hn.card_K_prime⟩

  exact
    { sigmaCore_normal := sigmaCore_normal M
      sigmaCore_hall_M := Msigma_Hall hM
      sigmaCore_hall_G := Msigma_Hall_G hM
      K_hall := hCompl.hall_K
      K_cyclic := hkappa.K_cyclic
      U_complements_sigma_K := complement_sigma_join_kappa hCompl hctx
      K_normalizes_U := hKnormalizesU
      sigma_U_normal := hkappa.sigmaU_K_sdprod.2.2.1
      U_normal_UK := hctx.U_K_sdprod.2.2.1
      sigma_U_sdprod := hkappa.sigma_U_sdprod
      sigmaU_K_sdprod := hkappa.sigmaU_K_sdprod
      fixed_point_free := by
        intro k hkK hk1
        exact centralizer_zpowers_eq_bot hctx.U_K_semiregular hkK hk1
      partner_ne_bot := hPartner
      centralizer_direct := hCentralizers
      Fcore_ne_bot := hcore.Fcore_ne_bot
      Fcore_le_sigma := hcore.Fcore_le_sigma
      sigma_le_derived := hcore.sigma_le_derived
      derived_lt := hcore.derived_lt
      Fcore_normal_derived := hfit.Fcore_normal_derived
      derived_mod_Fcore_nilpotent := hfit.derived_mod_Fcore_nilpotent
      secondDerived_le_fitting := hfit.secondDerived_le_fitting
      Fcore_join_centralizer := hfit.Fcore_join_centralizer
      fitting_le_derived_of_K_ne_bot := fun hKne ↦
        hfit.typeP_fitting_le_derived (hTypeP hKne)
      nonnilpotent_case := hExceptional }

/-! ## The type-selected derived subgroup -/

/-- The source variant of Lemma 16.1(e):
`sigmaCore M ><| U = M^(FTtype M != 1)`. -/
theorem sdprod_FTder
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    IsInternalSemidirectProductIn (sigmaCore M) U (FTder M) := by
  classical
  have hkappa : KappaStructure M U K := kappa_structure hM hCompl
  by_cases hKbot : K = ⊥
  · have hF : M ∈ typeFMaximalSubgroups (G := G) :=
      (trivg_kappa hM hCompl.K_le_M hCompl.hall_K).1 hKbot
    have htype : FTtype M = 1 := by
      simp [FTtype, ftType, hF.2]
    have hSigmaUEq : sigmaCore M ⊔ U = M := by
      have hSubTop :
          (sigmaCore M ⊔ U).subgroupOf M = ⊤ := by
        have hsup :=
          hkappa.sigmaU_K_sdprod.2.2.2.sup_eq_top
        simpa [hKbot] using hsup
      exact le_antisymm hkappa.sigmaU_K_sdprod.1
        (Subgroup.subgroupOf_eq_top.mp hSubTop)
    simpa [FTder, ftDerived, htype, hSigmaUEq] using
      hkappa.sigma_U_sdprod
  · have hNotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) := by
      intro hPi
      exact hKbot
        ((trivg_kappa hM hCompl.K_le_M hCompl.hall_K).2 ⟨hM, hPi⟩)
    have htype : FTtype M ≠ 1 := by
      unfold FTtype ftType
      rw [if_neg hNotPi]
      split_ifs <;> omega
    simpa [FTder, ftDerived, htype] using
      hkappa.derived_decomposition hKbot

end

end Submission.OddOrder.BG.Section16
