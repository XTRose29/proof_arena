import Submission.OddOrder.BG.Section16.SummaryABC
import Submission.OddOrder.BG.Section16.SummaryDE
import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.BG.Section16.TypesAndSupport
import Submission.OddOrder.PF.Section05.CoherenceExtension
import Submission.OddOrder.PF.Section05.OrthogonalIntegralSpan
import Submission.OddOrder.PF.Section05.SubcoherentProperties
import Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence
import Submission.OddOrder.PF.Section08.FTSupportPartition
import Submission.OddOrder.PF.Section08.FTTypeContexts
import Submission.OddOrder.PF.Section09.PTypeFCoreKernel
import Submission.OddOrder.PF.Section09.PTypeGaloisAction
import Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure
import Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore
import Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer

/-!
# Peterfalvi Section 9: the canonical P-type core context

This module fixes the subgroup and character-family context used throughout
Peterfalvi (9.11).  It also packages the subgroup transports, normality facts,
index calculations, degree bound, and support inclusion needed by the later
core-bound phases.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open CategoryTheory Limits
open scoped BigOperators Classical IsMulCommutative Pointwise commutatorElement

universe u v w

local instance (priority := 10) pTypeCoreContextFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! ## Canonical subgroups and source family -/

/-- Source `HU = M'`, regarded as a subgroup of the maximal-subgroup type. -/
abbrev pTypeCoreDerived
    {G : Type u} [Group G] (M : Subgroup G) : Subgroup M :=
  pTypeHUInMaximal M (derivedWithin M)

/-- Source `H = M_F`, regarded as a subgroup of `HU`. -/
abbrev pTypeCoreFitting
    {G : Type u} [Group G] (M : Subgroup G) :
    Subgroup (pTypeCoreDerived M) :=
  pTypeHInDerived M (derivedWithin M) (Fitting_core M)

/-- The selected F-core kernel `H₀`, regarded as a subgroup of `HU`. -/
abbrev pTypeCoreKernel
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Subgroup (pTypeCoreDerived M) :=
  pTypeH0InDerived M (derivedWithin M) (Ptype_Fcore_kernel ctx)

/-- Source `H₀C' = H₀ ⟨C'⟩`, formed inside `HU`. -/
def pTypeCoreKernelDerivedComplement
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Subgroup (pTypeCoreDerived M) :=
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D

/-- The literal source family `S_(H₀C')` attached to a Type-P context. -/
def pTypeCoreFamilyOfContext
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Finset (ClassFunction M ℂ) :=
  seqIndD (k := ℂ) (pTypeCoreDerived M) (pTypeCoreFitting M)
    (pTypeCoreKernelDerivedComplement ctx)

/-- The abstract source family `S_Y = seqIndD HU H Y`. -/
def pTypeCoreFamily
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H Y : Subgroup HU) :
    Finset (ClassFunction M ℂ) :=
  seqIndD (k := ℂ) HU H Y

/-!
The remaining declarations are intentionally exported from a named internal
namespace.  They are implementation infrastructure for the later core phases,
not additional source-facing API.
-/

namespace PTypeCoreContextInternal

/-! ## Subgroup transport and containment -/

/-- Derived subgroups are monotone with respect to ambient subgroup inclusion. -/
theorem pTypeCore_derivedWithin_mono
    {G : Type u} [Group G]
    {A B : Subgroup G} (hAB : A ≤ B) :
    derivedWithin A ≤ derivedWithin B := by
  rw [derivedWithin, A.map_subtype_commutator,
    derivedWithin, B.map_subtype_commutator]
  exact Subgroup.commutator_mono hAB hAB

/-- Mapping a complement derived subgroup through an inclusion agrees with
forming the derived subgroup first and then restricting it. -/
theorem pTypeCoreDerivedComplementInMaximal_eq_derivedWithin_subgroupOf
    {G : Type u} [Group G]
    {M U : Subgroup G} (hUM : U ≤ M) :
    pTypeDerivedComplementInMaximal (Subgroup.inclusion hUM) =
      (derivedWithin U).subgroupOf M := by
  unfold pTypeDerivedComplementInMaximal derivedWithin
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    exact ⟨u, hu, congrArg Subtype.val hux⟩
  · rintro ⟨u, hu, hux⟩
    exact ⟨u, hu, Subtype.ext hux⟩

/-- The source containment `H₀C' ≤ H₀U'`. -/
theorem pTypeCoreKernelDerivedComplement_le_H0UPrime
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    pTypeCoreKernelDerivedComplement ctx ≤
      pTypeH0DerivedComplementInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let Cₐ : Subgroup G := D.C.map U.subtype
  have hCU : Cₐ ≤ U := Subgroup.map_subtype_le D.C
  have hderCU : derivedWithin Cₐ ≤ derivedWithin U :=
    pTypeCore_derivedWithin_mono hCU
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  have hCPrimeUPrime :
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU ≤
        ((derivedWithin U).subgroupOf M).subgroupOf HU := by
    rw [Submission.OddOrder.PF.internal.pTypeDerivedComplementInMaximal_eq_derivedWithin_map]
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M hderCU)
  have hUPrimeEq :
      pTypeDerivedComplementInMaximal (U.subgroupOf M).subtype =
        (derivedWithin U).subgroupOf M := by
    exact
      (internal.pTypeDerivedComplementInMaximal_eq_subgroupOf
        hUM).symm.trans
          (internal.pTypeDerivedComplementInMaximal_eq_derivedWithin_subgroupOf
            hUM)
  change
    pTypeH0InDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) ⊔
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU ≤
      pTypeH0InDerived M (derivedWithin M)
          (Ptype_Fcore_kernel ctx) ⊔
        (pTypeDerivedComplementInMaximal
          (U.subgroupOf M).subtype).subgroupOf HU
  apply sup_le le_sup_left
  rw [hUPrimeEq]
  exact hCPrimeUPrime.trans le_sup_right

/-- The source containment `H₀C' ≤ H₀C`. -/
theorem pTypeCoreKernelDerivedComplement_le_H0C
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    pTypeCoreKernelDerivedComplement ctx ≤
      pTypeH0CInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U W₁
        (Ptype_factor_action ctx facts) := by
  let D := Ptype_factor_action ctx facts
  have hderived :
      pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype) ≤
        D.C.map U.subtype := by
    rintro _ ⟨c, _hc, rfl⟩
    exact ⟨(c : U), c.property, rfl⟩
  exact sup_le_sup le_rfl
    (Subgroup.subgroupOf_mono (pTypeCoreDerived M)
      (Subgroup.subgroupOf_mono M hderived))

/-- If `C = U'`, the two unprimed kernel bounds are equal. -/
theorem pTypeCoreH0C_eq_H0UPrime_of_C_eq_commutator
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hC : (Ptype_factor_action ctx facts).C =
      _root_.commutator U) :
    pTypeH0CInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U W₁
        (Ptype_factor_action ctx facts) =
      pTypeH0DerivedComplementInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  have hCmap : D.C.map U.subtype = derivedWithin U := by
    rw [hC]
    rfl
  have hUPrimeEq :
      pTypeDerivedComplementInMaximal (U.subgroupOf M).subtype =
        (derivedWithin U).subgroupOf M := by
    exact
      (internal.pTypeDerivedComplementInMaximal_eq_subgroupOf
        hUM).symm.trans
          (internal.pTypeDerivedComplementInMaximal_eq_derivedWithin_subgroupOf
            hUM)
  change
    pTypeH0InDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) ⊔
        ((D.C.map U.subtype).subgroupOf M).subgroupOf HU =
      pTypeH0InDerived M (derivedWithin M)
          (Ptype_Fcore_kernel ctx) ⊔
        (pTypeDerivedComplementInMaximal
          (U.subgroupOf M).subtype).subgroupOf HU
  congr 1
  rw [hUPrimeEq, hCmap]

/-! ## Normality and commutator control -/

/-- The canonical Fitting subgroup is normal in `HU`. -/
theorem pTypeCoreH_normal
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeCoreFitting M).Normal := by
  exact Submission.OddOrder.PF.internal.pTypeHInDerived_normal ctx

/-- The unprimed kernel bound `H₀C` is normal in `HU`. -/
theorem pTypeCoreH0C_normal
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁
      (Ptype_factor_action ctx facts)).Normal :=
  Submission.OddOrder.PF.internal.pTypeH0CInDerived_normal ctx facts

/-- The canonical subgroup `HC` is normal in `HU`. -/
theorem pTypeCoreHC_normal
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)).Normal := by
  simpa only [pTypeHCInDerived, pTypeCInDerived] using
    (show (pTypeHInDerived M (derivedWithin M) (Fitting_core M) ⊔
      pTypeCInDerived M (derivedWithin M) U W₁
        (Ptype_factor_action ctx facts)).Normal from
      Submission.OddOrder.PF.internal.pTypeHCInDerived_normal ctx facts)

/-- The derived-complement kernel bound `H₀C'` is normal in `HU`. -/
theorem pTypeCoreH0CPrime_normal
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeCoreKernelDerivedComplement ctx).Normal := by
  dsimp only [pTypeCoreKernelDerivedComplement]
  exact Submission.OddOrder.PF.internal.pTypeH0CPrimeInDerived_normal
    ctx (Ptype_Fcore_factor_facts ctx)

/-- The canonical action kernel centralizes the Fitting core modulo `H₀`. -/
theorem pTypeCore_commutator_C_H_le_H0
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeCoreFitting M
    let H₀ := pTypeCoreKernel ctx
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    ⁅C, H⁆ ≤ H₀ := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀ := pTypeCoreKernel ctx
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let Hₐ := Fitting_core M
  let H₀a := Ptype_Fcore_kernel ctx
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  have hUnormH : U ≤ Subgroup.normalizer (Hₐ : Set G) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  have hUnormH₀ : U ≤ Subgroup.normalizer (H₀a : Set G) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Ptype_Fcore_kernel_le_M ctx)).mp
          (Ptype_Fcore_kernel_normal_M ctx))
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hxC : (((x : HU) : M) : G) ∈ D.C.map U.subtype := hx
  obtain ⟨a, ha, hax⟩ := hxC
  let yH : Hₐ := ⟨(((y : HU) : M) : G), hy⟩
  have haKer : a ∈ (ptypeFCoreAction ctx).ker := by
    change a ∈ ((ptypeFCoreAction ctx).ker : Set U)
    simpa only [D, Ptype_factor_action_C] using ha
  have haKer' : a ∈
      (subgroupConjugationFactorHom H₀a Hₐ U
        hUnormH hUnormH₀).ker := by
    simpa only [ptypeFCoreAction] using haKer
  have hcomm : ⁅(a : G), (yH : G)⁆ ∈ H₀a :=
    (mem_ker_subgroupConjugationFactorHom_iff
      H₀a Hₐ U hUnormH hUnormH₀ a).mp haKer'
        (yH : G) yH.property
  change ⁅(((x : HU) : M) : G),
    (((y : HU) : M) : G)⁆ ∈ H₀a
  rw [← hax]
  exact hcomm

/-- The quotient `HC/H₀C'` is abelian. -/
theorem pTypeCore_commutator_HC_le_H0CPrime
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
    _root_.commutator HC ≤ H₀CPrime.subgroupOf HC := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  let Hₐ := Fitting_core M
  let H₀a := Ptype_Fcore_kernel ctx
  change _root_.commutator HC ≤ H₀CPrime.subgroupOf HC
  letI : (H₀a.subgroupOf Hₐ).Normal :=
    Ptype_Fcore_kernel_normal_Fcore ctx
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    (ptypeFCoreFactor_elementary ctx).commutative
  letI : H₀CPrime.Normal := pTypeCoreH0CPrime_normal ctx facts
  have hHcomm : _root_.commutator Hₐ ≤ H₀a.subgroupOf Hₐ :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (ptypeFCoreFactor ctx))
  have hHH : ⁅H, H⁆ ≤ H₀CPrime := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    let xH : Hₐ := ⟨(((x : HU) : M) : G), hx⟩
    let yH : Hₐ := ⟨(((y : HU) : M) : G), hy⟩
    have hxyComm : ⁅xH, yH⁆ ∈ _root_.commutator Hₐ := by
      change ⁅xH, yH⁆ ∈ ⁅(⊤ : Subgroup Hₐ), ⊤⁆
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top xH) (Subgroup.mem_top yH)
    have hleft : pTypeCoreKernel ctx ≤ H₀CPrime := by
      exact le_sup_left
    apply hleft
    change ⁅(((x : HU) : M) : G),
      (((y : HU) : M) : G)⁆ ∈ H₀a
    have hxyH₀ : ((⁅xH, yH⁆ : Hₐ) : G) ∈ H₀a :=
      hHcomm hxyComm
    change ⁅(xH : G), (yH : G)⁆ ∈ H₀a at hxyH₀
    simpa only [xH, yH] using hxyH₀
  have hCH : ⁅C, H⁆ ≤ H₀CPrime := by
    exact (pTypeCore_commutator_C_H_le_H0 ctx facts).trans le_sup_left
  have hHC : ⁅H, C⁆ ≤ H₀CPrime := by
    rw [Subgroup.commutator_comm]
    exact hCH
  have hCC : ⁅C, C⁆ ≤ H₀CPrime := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hxC : (((x : HU) : M) : G) ∈ D.C.map U.subtype := hx
    have hyC : (((y : HU) : M) : G) ∈ D.C.map U.subtype := hy
    obtain ⟨a, ha, hax⟩ := hxC
    obtain ⟨b, hb, hby⟩ := hyC
    let aC : D.C := ⟨a, ha⟩
    let bC : D.C := ⟨b, hb⟩
    have habComm : ⁅aC, bC⁆ ∈ _root_.commutator D.C := by
      change ⁅aC, bC⁆ ∈ ⁅(⊤ : Subgroup D.C), ⊤⁆
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top aC) (Subgroup.mem_top bC)
    have hright :
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU ≤
          H₀CPrime := by
      exact le_sup_right
    apply hright
    change ⁅(((x : HU) : M) : G),
        (((y : HU) : M) : G)⁆ ∈
      pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)
    refine ⟨⁅aC, bC⁆, habComm, ?_⟩
    rw [map_commutatorElement]
    change ⁅(a : G), (b : G)⁆ =
      ⁅(((x : HU) : M) : G), (((y : HU) : M) : G)⁆
    exact congrArg₂ (fun x y : G ↦ ⁅x, y⁆) hax hby
  have hHsup : ⁅H, H ⊔ C⁆ ≤ H₀CPrime :=
    commutator_sup_le_of_normal hHH hHC
  have hCsup : ⁅C, H ⊔ C⁆ ≤ H₀CPrime :=
    commutator_sup_le_of_normal hCH hCC
  have hsupH : ⁅H ⊔ C, H⁆ ≤ H₀CPrime := by
    rw [Subgroup.commutator_comm]
    exact hHsup
  have hsupC : ⁅H ⊔ C, C⁆ ≤ H₀CPrime := by
    rw [Subgroup.commutator_comm]
    exact hCsup
  have hHCcomm : ⁅HC, HC⁆ ≤ H₀CPrime := by
    change ⁅H ⊔ C, H ⊔ C⁆ ≤ H₀CPrime
    exact commutator_sup_le_of_normal hsupH hsupC
  intro z hz
  change (z : HU) ∈ H₀CPrime
  apply hHCcomm
  rw [← HC.map_subtype_commutator]
  exact ⟨z, hz, rfl⟩

/-! ## Canonical index calculations -/

/-- The source identity `[M : HU] = q`. -/
theorem pTypeCore_index_eq_q
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeCoreDerived M).index =
      (Ptype_factor_action ctx facts).q := by
  have houter : IsInternalSemidirectProductIn
      (derivedWithin M) W₁ M := ctx.typeP.1.2.2.2
  calc
    (pTypeCoreDerived M).index = Nat.card (W₁.subgroupOf M) :=
      houter.2.2.2.symm.index_eq_card
    _ = Nat.card W₁ := natCard_subgroupOf_eq houter.2.1
    _ = (Ptype_factor_action ctx facts).q := by
      rw [Ptype_factor_action_q]

/-- Restrict a complement decomposition to a subgroup containing its left
factor. -/
theorem pTypeCore_isComplement_subgroupOf_of_left_le
    {A : Type u} [Group A]
    {N C T : Subgroup A}
    (hNC : N.IsComplement' C) (hNT : N ≤ T) :
    (N.subgroupOf T).IsComplement'
      ((C ⊓ T).subgroupOf T) :=
  Submission.OddOrder.PF.internal.pTypeIsComplement_subgroupOf_of_left_le hNC hNT

/-- In a complement decomposition, an intermediate ambient index is the
corresponding relative index in the complement. -/
theorem pTypeCore_index_eq_relIndex_of_complement
    {A : Type u} [Group A] [Finite A]
    {N C T : Subgroup A}
    (hNC : N.IsComplement' C) (hNT : N ≤ T) :
    T.index = T.relIndex C :=
  Submission.OddOrder.PF.internal.pTypeIndex_eq_relIndex_of_isComplement_of_left_le hNC hNT

/-- Intersecting `N ⊔ C` with the two complementary factors recovers `N`
and `C`. -/
theorem pTypeCore_inf_sup_eq_of_complement
    {A : Type u} [Group A]
    (H U N C : Subgroup A) [N.Normal]
    (hHU : H.IsComplement' U) (hNH : N ≤ H) (hCU : C ≤ U) :
    H ⊓ (N ⊔ C) = N ∧ U ⊓ (N ⊔ C) = C := by
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, c, hc, hnc⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hx.2
      have hcH : c ∈ H := by
        have hcEq : c = n⁻¹ * x := by
          rw [← hnc]
          simp
        rw [hcEq]
        exact H.mul_mem (H.inv_mem (hNH hn)) hx.1
      have hcOne : c = 1 := by
        apply Subgroup.mem_bot.mp
        exact hHU.disjoint.le_bot ⟨hcH, hCU hc⟩
      have hxEq : x = n := by
        rw [← hnc, hcOne, mul_one]
      exact hxEq.symm ▸ hn
    · intro n hn
      exact ⟨hNH hn, (show N ≤ N ⊔ C from le_sup_left) hn⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, c, hc, hnc⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hx.2
      have hnU : n ∈ U := by
        have hnEq : n = x * c⁻¹ := by
          rw [← hnc]
          simp
        rw [hnEq]
        exact U.mul_mem hx.1 (U.inv_mem (hCU hc))
      have hnOne : n = 1 := by
        apply Subgroup.mem_bot.mp
        exact hHU.disjoint.le_bot ⟨hNH hn, hnU⟩
      have hxEq : x = c := by
        rw [← hnc, hnOne, one_mul]
      exact hxEq.symm ▸ hc
    · intro c hc
      exact ⟨hCU hc, (show C ≤ N ⊔ C from le_sup_right) hc⟩

/-- The canonical copies of `H` and `U` are complementary inside `HU`. -/
theorem pTypeCoreH_isComplement_U
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeCoreFitting M).IsComplement'
      (pTypeUInDerived M (derivedWithin M) U) := by
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  let eHU : pTypeCoreDerived M ≃* derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hDerM
  have hmapped :=
    Submission.OddOrder.PF.internal.pTypeIsComplement_map_mulEquiv
      ctx.typeP.2.1.2.2.2.2.2.2 eHU.symm
  have hmapH :
      ((Fitting_core M).subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom =
        pTypeCoreFitting M := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hx
      let h : (Fitting_core M).subgroupOf (derivedWithin M) :=
        ⟨eHU x, hx⟩
      exact ⟨h, h.property, by
        apply Subtype.ext
        rfl⟩
  have hmapU :
      (U.subgroupOf (derivedWithin M)).map eHU.symm.toMonoidHom =
        pTypeUInDerived M (derivedWithin M) U := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      let a : U.subgroupOf (derivedWithin M) := ⟨eHU x, hx⟩
      exact ⟨a, a.property, by
        apply Subtype.ext
        rfl⟩
  simpa only [hmapH, hmapU] using hmapped

/-- The canonical identity `[HU : HC] = |U/C|`. -/
theorem pTypeCore_HC_index_eq_factorCard
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    HC.index = pTypeActionFactorCard D := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H : Subgroup HU := pTypeCoreFitting M
  let C : Subgroup HU :=
    pTypeCInDerived M (derivedWithin M) U W₁ D
  let UHU : Subgroup HU :=
    pTypeUInDerived M (derivedWithin M) U
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := pTypeCoreH_normal ctx
  letI : D.C.Normal := D.C_normal
  have hcomp : H.IsComplement' UHU :=
    pTypeCoreH_isComplement_U ctx
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hCder : D.C.map U.subtype ≤ derivedWithin M :=
    (Subgroup.map_subtype_le D.C).trans hUder
  have hCU : C ≤ UHU := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Subgroup.map_subtype_le D.C))
  have hHHC : H ≤ HC := le_sup_left
  have hindexRel : HC.index = HC.relIndex UHU :=
    pTypeCore_index_eq_relIndex_of_complement hcomp hHHC
  have hinter := pTypeCore_inf_sup_eq_of_complement
    H UHU H C hcomp le_rfl hCU
  have hHCcap : HC.subgroupOf UHU = C.subgroupOf UHU := by
    ext x
    change (x : HU) ∈ H ⊔ C ↔ (x : HU) ∈ C
    constructor
    · intro hx
      have hxInf : (x : HU) ∈ UHU ⊓ (H ⊔ C) :=
        ⟨x.property, hx⟩
      rw [hinter.2] at hxInf
      exact hxInf
    · exact fun hx ↦
        (show C ≤ H ⊔ C from le_sup_right) hx
  have hUHU : U.subgroupOf M ≤ HU := by
    intro x hx
    exact hUder hx
  have hcardUHU : Nat.card UHU = Nat.card U := by
    calc
      Nat.card UHU = Nat.card (U.subgroupOf M) :=
        natCard_subgroupOf_eq hUHU
      _ = Nat.card U := natCard_subgroupOf_eq hUM
  have hDCM : D.C.map U.subtype ≤ M := hCder.trans hDerM
  have hDCHU : (D.C.map U.subtype).subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  have hcardC : Nat.card C = Nat.card D.C := by
    calc
      Nat.card C = Nat.card ((D.C.map U.subtype).subgroupOf M) :=
        natCard_subgroupOf_eq hDCHU
      _ = Nat.card (D.C.map U.subtype) :=
        natCard_subgroupOf_eq hDCM
      _ = Nat.card D.C :=
        Subgroup.card_map_of_injective U.subtype_injective
  have hcardCsub : Nat.card (C.subgroupOf UHU) = Nat.card D.C :=
    (natCard_subgroupOf_eq hCU).trans hcardC
  have hleft : (C.subgroupOf UHU).index * Nat.card D.C =
      Nat.card U := by
    calc
      (C.subgroupOf UHU).index * Nat.card D.C =
          (C.subgroupOf UHU).index *
            Nat.card (C.subgroupOf UHU) := by rw [hcardCsub]
      _ = Nat.card UHU := (C.subgroupOf UHU).index_mul_card
      _ = Nat.card U := hcardUHU
  have hright : D.C.index * Nat.card D.C = Nat.card U :=
    D.C.index_mul_card
  have hindexC : (C.subgroupOf UHU).index = D.C.index :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := D.C))
      (hleft.trans hright.symm)
  calc
    HC.index = HC.relIndex UHU := hindexRel
    _ = (HC.subgroupOf UHU).index := rfl
    _ = (C.subgroupOf UHU).index := by rw [hHCcap]
    _ = D.C.index := hindexC
    _ = pTypeActionFactorCard D := rfl

/-! ## Character norms and the F-core interval -/

private instance pTypeCoreRepInjectiveGeneral
    {A : Type u} {k : Type v} [Group A] [Finite A] [Field k]
    [NeZero (Nat.card A : k)] (V : Rep.{w} k A) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

private instance pTypeCoreFDRepInjectiveGeneral
    {A : Type u} {k : Type v} [Group A] [Finite A] [Field k]
    [NeZero (Nat.card A : k)] (V : FDRep k A) : Injective V :=
  (forget₂ (FDRep k A) (Rep k A)).injective_of_map_injective inferInstance

private theorem pTypeCoreSimple_iff_end_rank_one_general
    {A : Type u} {k : Type v} [Group A] [Finite A] [Field k]
    [IsAlgClosed k] [NeZero (Nat.card A : k)] (V : FDRep k A) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ :=
      ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι ≠ 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ :=
          (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V :=
        (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

private theorem pTypeCoreSimple_iff_char_norm_one_general
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k] (V : FDRep k A) :
    Simple V ↔
      ∑ a : A, V.character a * V.character a⁻¹ = Nat.card A where
  mp h := by
    have : NeZero (Nat.card A : k) := by
      rw [← @Fintype.card_eq_nat_card A (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Nat.card A : k))
    have := invertibleOfNonzero (NeZero.ne (Fintype.card A : k))
    classical
    have hpair : ⅟(Nat.card A : k) •
        ∑ a, V.character a * V.character a⁻¹ = 1 := by
      simpa only [Nonempty.intro (Iso.refl V), ↓reduceIte,
        Fintype.card_eq_nat_card] using FDRep.char_orthonormal V V
    apply_fun (· * (Fintype.card A : k)) at hpair
    rwa [mul_comm, ← smul_eq_mul, smul_smul, Fintype.card_eq_nat_card,
      mul_invOf_self, smul_eq_mul, one_mul, one_mul] at hpair
  mpr h := by
    have : NeZero (Nat.card A : k) := by
      rw [← @Fintype.card_eq_nat_card A (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Fintype.card A : k))
    have := invertibleOfNonzero (NeZero.ne (Nat.card A : k))
    have eq := FDRep.scalar_product_char_eq_finrank_equivariant V V
    rw [h] at eq
    simp only [invOf_eq_inv, smul_eq_mul, inv_mul_cancel_of_invertible,
      Fintype.card_eq_nat_card] at eq
    rw [pTypeCoreSimple_iff_end_rank_one_general,
      ← Nat.cast_inj (R := k), ← eq, Nat.cast_one]

private def pTypeCoreCoefficientTransport
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Field k] [Field l]
    (sigma : k ≃+* l) (V : FDRep k A) : FDRep l A :=
  let b := Module.finBasis k V
  FDRep.of
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp
      (sigma.mapMatrix.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp V.ρ)))

@[simp] private theorem pTypeCoreCoefficientTransport_character
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Field k] [Field l]
    (sigma : k ≃+* l) (V : FDRep k A) (a : A) :
    (pTypeCoreCoefficientTransport sigma V).character a =
      sigma (V.character a) := by
  let b := Module.finBasis k V
  change LinearMap.trace l _
      (Matrix.toLinAlgEquiv'
        (sigma.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ a)))) =
    sigma (LinearMap.trace k V (V.ρ a))
  change LinearMap.trace l _
      (Matrix.toLin'
        (sigma.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ a)))) = _
  rw [Matrix.trace_toLin'_eq,
    LinearMap.trace_eq_matrix_trace k b,
    AddMonoidHom.map_trace]
  rfl

private theorem pTypeCoreCoefficientTransport_simple
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (V : FDRep k A) [Simple V] :
    Simple (pTypeCoreCoefficientTransport sigma V) := by
  rw [pTypeCoreSimple_iff_char_norm_one_general]
  have hV :=
    (pTypeCoreSimple_iff_char_norm_one_general V).mp (by infer_instance)
  simp only [pTypeCoreCoefficientTransport_character,
    ← map_mul, ← map_sum, hV]
  exact map_natCast sigma (Nat.card A)

private noncomputable def pTypeCoreMapCoefficient
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (chi : IrreducibleCharacter A k) :
    IrreducibleCharacter A l := by
  letI : Simple chi.representation := chi.representation_simple
  letI : Simple
      (pTypeCoreCoefficientTransport sigma chi.representation) :=
    pTypeCoreCoefficientTransport_simple sigma chi.representation
  exact IrreducibleCharacter.ofFDRep
    (pTypeCoreCoefficientTransport sigma chi.representation)

@[simp] private theorem pTypeCoreMapCoefficient_apply
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (chi : IrreducibleCharacter A k) (a : A) :
    pTypeCoreMapCoefficient sigma chi a = sigma (chi a) := by
  letI : Simple chi.representation := chi.representation_simple
  letI : Simple
      (pTypeCoreCoefficientTransport sigma chi.representation) :=
    pTypeCoreCoefficientTransport_simple sigma chi.representation
  simp only [pTypeCoreMapCoefficient,
    IrreducibleCharacter.ofFDRep_apply,
    pTypeCoreCoefficientTransport_character,
    IrreducibleCharacter.representation_character]

private theorem pTypeCoreMapRingHom_induce
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A] [Field k] [Field l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (K : Subgroup A) (f : ClassFunction K k) :
    ClassFunction.mapRingHom sigma.toRingHom (ClassFunction.induce K f) =
      ClassFunction.induce K
        (ClassFunction.mapRingHom sigma.toRingHom f) := by
  classical
  ext a
  rw [ClassFunction.mapRingHom_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula,
    map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y⁻¹ * a * y ∈ K
  · rw [dif_pos hy, dif_pos hy, ClassFunction.mapRingHom_apply]
  · rw [dif_neg hy, dif_neg hy, map_zero]

@[simp] private theorem pTypeCoreMapCoefficient_coe
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (chi : IrreducibleCharacter A k) :
    ClassFunction.mapRingHom sigma.toRingHom
        (chi : ClassFunction A k) =
      (pTypeCoreMapCoefficient sigma chi : ClassFunction A l) := by
  ext a
  simp

private theorem pTypeCoreMapRingHom_restrict
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Field k] [Field l]
    (sigma : k ≃+* l) (K : Subgroup A)
    (f : ClassFunction A k) :
    ClassFunction.mapRingHom sigma.toRingHom
        (ClassFunction.restrict K f) =
      ClassFunction.restrict K
        (ClassFunction.mapRingHom sigma.toRingHom f) := by
  ext x
  rfl

private theorem pTypeCore_characterPairing_mapRingEquiv
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A] [Field k] [Field l]
    (sigma : k ≃+* l) (f g : ClassFunction A k) :
    characterPairing
        (ClassFunction.mapRingHom sigma.toRingHom f)
        (ClassFunction.mapRingHom sigma.toRingHom g) =
      sigma (characterPairing f g) := by
  simp only [characterPairing, ClassFunction.mapRingHom_apply,
    map_mul, map_inv₀, map_natCast, map_sum]
  rfl

private theorem pTypeCoreMapCoefficient_finrank
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (chi : IrreducibleCharacter A k) :
    Module.finrank l
        (pTypeCoreMapCoefficient sigma chi).representation =
      Module.finrank k chi.representation := by
  apply Nat.cast_injective (R := l)
  simpa only [IrreducibleCharacter.apply_one_eq_finrank,
    map_natCast] using pTypeCoreMapCoefficient_apply sigma chi 1

private theorem pTypeCoreMapCoefficient_translationKernel
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (chi : IrreducibleCharacter A k) :
    ClassFunction.translationKernel
        (pTypeCoreMapCoefficient sigma chi : ClassFunction A l) =
      ClassFunction.translationKernel (chi : ClassFunction A k) := by
  ext a
  simp only [ClassFunction.mem_translationKernel_iff]
  constructor
  · intro ha x
    apply sigma.injective
    simpa only [pTypeCoreMapCoefficient_apply] using ha x
  · intro ha x
    simpa only [pTypeCoreMapCoefficient_apply] using
      congrArg sigma (ha x)

private theorem pTypeCoreMapCoefficient_isConstituent_restrict
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (K : Subgroup A)
    (s : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter K k)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict K (s : ClassFunction A k))) :
    (pTypeCoreMapCoefficient sigma theta).IsConstituent
      (ClassFunction.restrict K
        (pTypeCoreMapCoefficient sigma s : ClassFunction A l)) := by
  unfold IrreducibleCharacter.IsConstituent at htheta ⊢
  rw [← pTypeCoreMapCoefficient_coe sigma s,
    ← pTypeCoreMapCoefficient_coe sigma theta,
    ← pTypeCoreMapRingHom_restrict,
    pTypeCore_characterPairing_mapRingEquiv]
  exact sigma.map_ne_zero_iff.mpr htheta

private theorem pTypeCoreIsIrreducible_mapRingEquiv_iff
    {A : Type u} {k : Type v} {l : Type w}
    [Group A] [Fintype A]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (f : ClassFunction A k) :
    IsIrreducibleCharacter A l
        (ClassFunction.mapRingHom sigma.toRingHom f) ↔
      IsIrreducibleCharacter A k f := by
  constructor
  · intro h
    let chiL : IrreducibleCharacter A l :=
      ⟨ClassFunction.mapRingHom sigma.toRingHom f, h⟩
    let chiK : IrreducibleCharacter A k :=
      pTypeCoreMapCoefficient sigma.symm chiL
    have hchiK : (chiK : ClassFunction A k) = f := by
      ext a
      simp [chiK, chiL]
    rw [← hchiK]
    exact chiK.property
  · intro h
    let chiK : IrreducibleCharacter A k := ⟨f, h⟩
    let chiL : IrreducibleCharacter A l :=
      pTypeCoreMapCoefficient sigma chiK
    have hchiL : (chiL : ClassFunction A l) =
        ClassFunction.mapRingHom sigma.toRingHom f := by
      ext a
      simp [chiL, chiK]
    rw [← hchiL]
    exact chiL.property

private theorem pTypeCoreIsAlgClosedOfRingEquiv
    {k : Type v} {l : Type w} [Field k] [Field l]
    (sigma : k ≃+* l) [IsAlgClosed l] : IsAlgClosed k := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hdegree : Polynomial.degree (p.map sigma.toRingHom) ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := l)
      (p.map sigma.toRingHom) hdegree with ⟨z, hz⟩
  use sigma.symm z
  rw [Polynomial.IsRoot] at hz
  apply sigma.injective
  rw [map_zero, ← hz]
  clear hz hdegree hp hmp
  induction p using Polynomial.induction_on <;> simp_all

private theorem pTypeCore_induce_irreducible_of_inertia_le
    {A : Type u} [Group A] [Fintype A]
    (K : Subgroup A) [K.Normal]
    [Invertible (Nat.card K : ℂ)]
    (chi : IrreducibleCharacter K ℂ)
    (hI : ClassFunction.inertia K (chi : ClassFunction K ℂ) ≤ K) :
    IsIrreducibleCharacter A ℂ
      (ClassFunction.induce K (chi : ClassFunction K ℂ)) := by
  let k : Type u := ULift.{u} ℂ
  let sigma : k ≃+* ℂ := ULift.ringEquiv
  letI : CharZero k :=
    charZero_of_injective_ringHom
      (f := sigma.symm.toRingHom) sigma.symm.injective
  letI : IsAlgClosed k := pTypeCoreIsAlgClosedOfRingEquiv sigma
  let chiHigh : IrreducibleCharacter K k :=
    pTypeCoreMapCoefficient sigma.symm chi
  have hround : pTypeCoreMapCoefficient sigma chiHigh = chi := by
    apply IrreducibleCharacter.ext
    intro x
    simp only [chiHigh, pTypeCoreMapCoefficient_apply]
    exact sigma.apply_symm_apply _
  have hinertia :
      ClassFunction.inertia K (chiHigh : ClassFunction K k) =
        ClassFunction.inertia K (chi : ClassFunction K ℂ) := by
    ext a
    rw [ClassFunction.mem_inertia_iff, ClassFunction.mem_inertia_iff]
    constructor
    · intro ha
      apply ClassFunction.ext
      intro x
      have hx := congrArg (fun f : ClassFunction K k ↦ f x) ha
      change chiHigh ((MulAut.conjNormal a).symm x) = chiHigh x at hx
      rw [pTypeCoreMapCoefficient_apply,
        pTypeCoreMapCoefficient_apply] at hx
      exact sigma.symm.injective hx
    · intro ha
      apply ClassFunction.ext
      intro x
      have hx := congrArg (fun f : ClassFunction K ℂ ↦ f x) ha
      change chi ((MulAut.conjNormal a).symm x) = chi x at hx
      change chiHigh ((MulAut.conjNormal a).symm x) = chiHigh x
      rw [pTypeCoreMapCoefficient_apply,
        pTypeCoreMapCoefficient_apply]
      exact congrArg sigma.symm hx
  have hIHigh :
      ClassFunction.inertia K (chiHigh : ClassFunction K k) ≤ K := by
    rw [hinertia]
    exact hI
  letI : Invertible (Nat.card K : k) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := K)).ne')
  have hirrHigh : IsIrreducibleCharacter A k
      (ClassFunction.induce K (chiHigh : ClassFunction K k)) :=
    ClassFunction.inertia_Ind_irr K chiHigh hIHigh
  have hirrDown : IsIrreducibleCharacter A ℂ
      (ClassFunction.mapRingHom sigma.toRingHom
        (ClassFunction.induce K (chiHigh : ClassFunction K k))) :=
    (pTypeCoreIsIrreducible_mapRingEquiv_iff sigma _).mpr hirrHigh
  rw [pTypeCoreMapRingHom_induce,
    pTypeCoreMapCoefficient_coe, hround] at hirrDown
  exact hirrDown

/-- The inertia number agrees with the corresponding relative subgroup index. -/
theorem pTypeCore_inertiaIndex_eq_relIndex
    {A : Type u} [Group A] [Fintype A]
    (K : Subgroup A) [K.Normal]
    (f : ClassFunction K ℂ) :
    ClassFunction.inertiaIndex K f =
      K.relIndex (ClassFunction.inertia K f) := by
  let I := ClassFunction.inertia K f
  have hKI : K ≤ I := ClassFunction.le_inertia K f
  unfold ClassFunction.inertiaIndex
  apply Nat.div_eq_of_eq_mul_left (Nat.card_pos (α := K))
  change Nat.card I = (K.subgroupOf I).index * Nat.card K
  rw [← natCard_subgroupOf_eq hKI]
  exact (K.subgroupOf I).index_mul_card.symm

/-- Reducible induction from a normal subgroup of prime index has norm equal
to that index. -/
theorem pTypeCore_reducible_induce_norm_eq_primeIndex
    {A : Type u} [Group A] [Fintype A]
    (K : Subgroup A) [K.Normal]
    (hprime : K.index.Prime)
    (chi : IrreducibleCharacter K ℂ)
    (hred : ¬ IsIrreducibleCharacter A ℂ
      (ClassFunction.induce K (chi : ClassFunction K ℂ))) :
    characterPairing
        (ClassFunction.induce K (chi : ClassFunction K ℂ))
        (ClassFunction.induce K (chi : ClassFunction K ℂ)) =
      (K.index : ℂ) := by
  letI : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := K)).ne')
  let I := ClassFunction.inertia K (chi : ClassFunction K ℂ)
  have hKI : K ≤ I := ClassFunction.le_inertia K _
  have hdvd : K.relIndex I ∣ K.index :=
    Subgroup.relIndex_dvd_index_of_le hKI
  have hne : K.relIndex I ≠ 1 := by
    intro hone
    have hIK : I ≤ K := Subgroup.relIndex_eq_one.mp hone
    exact hred (pTypeCore_induce_irreducible_of_inertia_le K chi hIK)
  have hrel : K.relIndex I = K.index :=
    ((Nat.dvd_prime hprime).mp hdvd).resolve_left hne
  rw [ClassFunction.cfnorm_Ind_irr,
    pTypeCore_inertiaIndex_eq_relIndex, hrel]

/-- The quotient interval `H/H₀` has cardinality `p^q`. -/
theorem pTypeCore_H0_relIndex_H_eq_factorCard
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeCoreFitting M
    let H₀ := pTypeCoreKernel ctx
    H₀.relIndex H = D.p ^ D.q := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀ := pTypeCoreKernel ctx
  let H₀a := Ptype_Fcore_kernel ctx
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hH₀H : H₀a ≤ Fitting_core M :=
    (Ptype_Fcore_kernel_lt ctx).le
  have hH₀der : H₀a ≤ derivedWithin M :=
    hH₀H.trans hHder
  have hH₀M : H₀a ≤ M := hH₀der.trans hDerM
  have hH₀nested : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M hH₀H)
  have hHHU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro x hx
    exact hHder hx
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hcardH : Nat.card H = Nat.card (Fitting_core M) := by
    calc
      Nat.card H = Nat.card ((Fitting_core M).subgroupOf M) :=
        natCard_subgroupOf_eq hHHU
      _ = Nat.card (Fitting_core M) :=
        natCard_subgroupOf_eq (Fcore_sub M)
  have hcardH₀ : Nat.card H₀ = Nat.card H₀a := by
    calc
      Nat.card H₀ = Nat.card (H₀a.subgroupOf M) :=
        natCard_subgroupOf_eq hH₀HU
      _ = Nat.card H₀a := natCard_subgroupOf_eq hH₀M
  have hfactor : Nat.card (ptypeFCoreFactor ctx) = D.p ^ D.q := by
    simpa only [D, Ptype_factor_action_p,
      Ptype_factor_action_q] using facts.factor_card
  have hleft : H₀.relIndex H * Nat.card H₀ = Nat.card H := by
    change (H₀.subgroupOf H).index * Nat.card H₀ = Nat.card H
    rw [← natCard_subgroupOf_eq hH₀nested]
    exact (H₀.subgroupOf H).index_mul_card
  have hright : D.p ^ D.q * Nat.card H₀ = Nat.card H := by
    calc
      D.p ^ D.q * Nat.card H₀ =
          Nat.card (ptypeFCoreFactor ctx) *
            Nat.card (H₀a.subgroupOf (Fitting_core M)) := by
        rw [hfactor, hcardH₀,
          natCard_subgroupOf_eq hH₀H]
      _ = Nat.card (Fitting_core M) :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (H₀a.subgroupOf (Fitting_core M))).symm
      _ = Nat.card H := hcardH.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H₀))
    (hleft.trans hright.symm)

/-- Every character in the source reducible `H₀` layer has norm `q`. -/
theorem pTypeCore_reducibleLayer_norm_eq_q
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ pTypeReducibleLayer
      (pTypeCoreDerived M) (pTypeCoreFitting M)
      (pTypeCoreKernel ctx)) :
    characterPairing zeta zeta =
      ((Ptype_factor_action ctx facts).q : ℂ) := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀ := pTypeCoreKernel ctx
  letI : ((derivedWithin M).subgroupOf M).Normal := by
    unfold derivedWithin
    rw [M.map_subtype_commutator]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.commutator_le_self M)).2
    exact Subgroup.normalizer_commutator_ge_left M M
  rcases Finset.mem_filter.mp hzeta with ⟨hzetaLayer, hzetaRed⟩
  obtain ⟨chi, _hchi, rfl⟩ := seqIndP.mp hzetaLayer
  have hprime : HU.index.Prime := by
    rw [pTypeCore_index_eq_q ctx facts]
    exact D.q_prime
  simpa only [HU, D, pTypeCore_index_eq_q ctx facts] using
    pTypeCore_reducible_induce_norm_eq_primeIndex
      HU hprime chi hzetaRed

/-! ## Degree and support layers -/

/-- Restriction of an irreducible character to a finite subgroup has an
irreducible constituent. -/
theorem pTypeCore_exists_constituent_restrict
    {A : Type u} [Group A] [Fintype A]
    (K : Subgroup A) [Fintype K]
    (chi : IrreducibleCharacter A ℂ) :
    ∃ theta : IrreducibleCharacter K ℂ,
      theta.IsConstituent
        (ClassFunction.restrict K
          (chi : ClassFunction A ℂ)) := by
  let V : FDRep ℂ K :=
    FDRep.of (chi.representation.ρ.comp K.subtype)
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  letI : Nontrivial V :=
    inferInstanceAs (Nontrivial chi.representation)
  obtain ⟨theta, htheta⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial V
  refine ⟨theta, ?_⟩
  have hV : ClassFunction.ofRepresentation V.ρ =
      ClassFunction.restrict K
        (chi : ClassFunction A ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  rwa [hV] at htheta

/-- An irreducible character whose kernel contains the commutator subgroup is
linear. -/
theorem pTypeCore_linear_of_commutator_le_kernel
    {A : Type u} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hder : _root_.commutator A ≤
      ClassFunction.translationKernel
        (chi : ClassFunction A ℂ)) :
    pTypeIsLinearCharacter chi := by
  let rho := chi.representation.ρ
  have hder' : _root_.commutator A ≤ rho.ker := by
    rw [← Submission.OddOrder.PF.internal.pTypeGaloisTranslationKernel_irreducibleCharacter chi]
    exact hder
  let Q := A ⧸ rho.ker
  let sigmaQ : Representation ℂ Q chi.representation :=
    quotientKerRepresentation rho
  let q : A →* Q := QuotientGroup.mk' rho.ker
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder'
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible (sigmaQ.comp q) := by
    change Representation.IsIrreducible rho
    infer_instance
  letI : Representation.IsIrreducible sigmaQ :=
    representation_isIrreducible_of_comp sigmaQ q
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    sigmaQ

private abbrev pTypeCoreHCOfContext
    {G : Type u} [Group G] [Fintype G]
    [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    Subgroup (pTypeCoreDerived M) :=
  pTypeHCInDerived M (derivedWithin M) (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)

private abbrev pTypeCoreRestrictedFDRep
    {A : Type u} {k : Type v} [Group A] [Field k]
    (HC : Subgroup A) (s : IrreducibleCharacter A k) :
    FDRep k HC :=
  FDRep.of (s.representation.ρ.comp HC.subtype)

private theorem pTypeCoreRestrictedFDRep_character
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    (HC : Subgroup A) (s : IrreducibleCharacter A k) :
    ClassFunction.ofRepresentation
        (pTypeCoreRestrictedFDRep HC s).ρ =
      ClassFunction.restrict HC (s : ClassFunction A k) := by
  rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
    s.ofRepresentation_representation]

private theorem pTypeCore_restricted_kernel_le_constituent_sameUniverse
    {A k : Type u} [Group A] [Fintype A] [Field k] [CharZero k]
    (HC : Subgroup A) (s : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter HC k)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict HC (s : ClassFunction A k))) :
    (pTypeCoreRestrictedFDRep HC s).ρ.ker ≤
      theta.representation.ρ.ker := by
  apply FDRep.ker_le_irreducible_ker_of_isConstituent
  rwa [pTypeCoreRestrictedFDRep_character]

private theorem pTypeCore_subgroupOf_le_restricted_kernel
    {A : Type u} {k : Type v} [Group A] [Field k]
    (K HC : Subgroup A) (s : IrreducibleCharacter A k)
    (hsRho : K ≤ s.representation.ρ.ker) :
    K.subgroupOf HC ≤ (pTypeCoreRestrictedFDRep HC s).ρ.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  change s.representation.ρ ((x : HC) : A) = 1
  exact MonoidHom.mem_ker.mp (hsRho hx)

private theorem pTypeCore_constituent_kernel_generic
    {A : Type u} [Group A] [Fintype A]
    (K HC : Subgroup A)
    (s : IrreducibleCharacter A ℂ)
    (theta : IrreducibleCharacter HC ℂ)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict HC (s : ClassFunction A ℂ)))
    (hsK : K ≤ ClassFunction.translationKernel
      (s : ClassFunction A ℂ)) :
    K.subgroupOf HC ≤ ClassFunction.translationKernel
      (theta : ClassFunction HC ℂ) := by
  classical
  let k : Type u := ULift.{u} ℂ
  let sigma : k ≃+* ℂ := ULift.ringEquiv
  letI : CharZero k :=
    CharZero.of_addMonoidHom sigma.symm.toAddMonoidHom
      sigma.symm.map_one sigma.symm.injective
  letI : IsAlgClosed k := pTypeCoreIsAlgClosedOfRingEquiv sigma
  let sHigh : IrreducibleCharacter A k :=
    pTypeCoreMapCoefficient sigma.symm s
  let thetaHigh : IrreducibleCharacter HC k :=
    pTypeCoreMapCoefficient sigma.symm theta
  have hthetaHigh : thetaHigh.IsConstituent
      (ClassFunction.restrict HC
        (sHigh : ClassFunction A k)) :=
    pTypeCoreMapCoefficient_isConstituent_restrict
      sigma.symm HC s theta htheta
  have hsHigh : K ≤ ClassFunction.translationKernel
      (sHigh : ClassFunction A k) := by
    rw [pTypeCoreMapCoefficient_translationKernel]
    exact hsK
  have hsHighRho : K ≤ sHigh.representation.ρ.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter sHigh]
    exact hsHigh
  have hthetaHighRho : K.subgroupOf HC ≤
      thetaHigh.representation.ρ.ker :=
    (pTypeCore_subgroupOf_le_restricted_kernel
      K HC sHigh hsHighRho).trans
        (pTypeCore_restricted_kernel_le_constituent_sameUniverse
          HC sHigh thetaHigh hthetaHigh)
  have hthetaHighKernel : K.subgroupOf HC ≤
      ClassFunction.translationKernel
        (thetaHigh : ClassFunction HC k) := by
    rw [ClassFunction.translationKernel_irreducibleCharacter]
    exact hthetaHighRho
  rw [← pTypeCoreMapCoefficient_translationKernel sigma.symm theta]
  exact hthetaHighKernel

private theorem pTypeCore_constituent_linear
    {G : Type u} [Group G] [Fintype G]
    [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (s : IrreducibleCharacter (pTypeCoreDerived M) ℂ)
    (theta : IrreducibleCharacter
      (pTypeCoreHCOfContext ctx facts) ℂ)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict (pTypeCoreHCOfContext ctx facts)
        (s : ClassFunction (pTypeCoreDerived M) ℂ)))
    (hsPrime : pTypeCoreKernelDerivedComplement ctx ≤
      ClassFunction.translationKernel
        (s : ClassFunction (pTypeCoreDerived M) ℂ)) :
    pTypeIsLinearCharacter theta := by
  let HC := pTypeCoreHCOfContext ctx facts
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  have hthetaKernel : H₀CPrime.subgroupOf HC ≤
      ClassFunction.translationKernel
        (theta : ClassFunction HC ℂ) :=
    pTypeCore_constituent_kernel_generic H₀CPrime HC
      s theta htheta hsPrime
  exact pTypeCore_linear_of_commutator_le_kernel theta
    ((pTypeCore_commutator_HC_le_H0CPrime ctx facts).trans
      hthetaKernel)

private theorem pTypeCore_exists_linear_constituent
    {G : Type u} [Group G] [Fintype G]
    [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (s : IrreducibleCharacter (pTypeCoreDerived M) ℂ)
    (hsPrime : pTypeCoreKernelDerivedComplement ctx ≤
      ClassFunction.translationKernel
        (s : ClassFunction (pTypeCoreDerived M) ℂ)) :
    ∃ theta : IrreducibleCharacter
        (pTypeCoreHCOfContext ctx facts) ℂ,
      theta.IsConstituent
          (ClassFunction.restrict (pTypeCoreHCOfContext ctx facts)
            (s : ClassFunction (pTypeCoreDerived M) ℂ)) ∧
        pTypeIsLinearCharacter theta := by
  let HC := pTypeCoreHCOfContext ctx facts
  obtain ⟨theta, htheta⟩ :=
    pTypeCore_exists_constituent_restrict HC s
  exact ⟨theta, htheta,
    pTypeCore_constituent_linear ctx facts s theta htheta hsPrime⟩

private theorem pTypeCore_degree_le_index_of_linear_constituent
    {A : Type u} [Group A] [Fintype A]
    (K : Subgroup A)
    (s : IrreducibleCharacter A ℂ)
    (theta : IrreducibleCharacter K ℂ)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict K (s : ClassFunction A ℂ)))
    (hthetaLinear : pTypeIsLinearCharacter theta) :
    Module.finrank ℂ s.representation ≤ K.index := by
  classical
  let k : Type u := ULift.{u} ℂ
  let sigma : k ≃+* ℂ := ULift.ringEquiv
  letI : CharZero k :=
    CharZero.of_addMonoidHom sigma.symm.toAddMonoidHom
      sigma.symm.map_one sigma.symm.injective
  letI : IsAlgClosed k := pTypeCoreIsAlgClosedOfRingEquiv sigma
  let sHigh : IrreducibleCharacter A k :=
    pTypeCoreMapCoefficient sigma.symm s
  let thetaHigh : IrreducibleCharacter K k :=
    pTypeCoreMapCoefficient sigma.symm theta
  have hthetaHigh : thetaHigh.IsConstituent
      (ClassFunction.restrict K
        (sHigh : ClassFunction A k)) :=
    pTypeCoreMapCoefficient_isConstituent_restrict
      sigma.symm K s theta htheta
  have hthetaLinearHigh :
      Module.finrank k thetaHigh.representation = 1 := by
    unfold pTypeIsLinearCharacter at hthetaLinear
    rw [pTypeCoreMapCoefficient_finrank]
    exact hthetaLinear
  have hsInd : sHigh.IsConstituent
      (ClassFunction.induce K
        (thetaHigh : ClassFunction K k)) :=
    (thetaHigh.isConstituent_restrict_iff_induce K sHigh).mp
      hthetaHigh
  let V : FDRep k A :=
    FDRep.induceFromSubgroup K thetaHigh.representation
  have hVchar : ClassFunction.ofRepresentation V.ρ =
      ClassFunction.induce K
        (thetaHigh : ClassFunction K k) := by
    dsimp only [V]
    exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
      K thetaHigh.representation).trans
        (congrArg (ClassFunction.induce K)
          thetaHigh.ofRepresentation_representation)
  have hsV : sHigh.IsConstituent
      (ClassFunction.ofRepresentation V.ρ) := by
    rwa [hVchar]
  have hdegree : Module.finrank k sHigh.representation ≤
      Module.finrank k V :=
    FDRep.finrank_irreducible_le_of_isConstituent V sHigh hsV
  have hVdim : Module.finrank k V = K.index := by
    apply Nat.cast_injective (R := k)
    calc
      (Module.finrank k V : k) = V.character 1 :=
        (FDRep.char_one V).symm
      _ = ClassFunction.ofRepresentation V.ρ 1 := rfl
      _ = ClassFunction.induce K
          (thetaHigh : ClassFunction K k) 1 := by rw [hVchar]
      _ = (K.index : k) * thetaHigh 1 :=
        ClassFunction.induce_one K _
      _ = (K.index : k) := by
        rw [IrreducibleCharacter.apply_one_eq_finrank,
          hthetaLinearHigh]
        norm_num
  calc
    Module.finrank ℂ s.representation =
        Module.finrank k sHigh.representation :=
      (pTypeCoreMapCoefficient_finrank sigma.symm s).symm
    _ ≤ K.index := by
      rw [← hVdim]
      exact hdegree

private theorem pTypeCore_irreducible_degree_le_factorCard
    {G : Type u} [Group G] [instG : Fintype G]
    [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (s : IrreducibleCharacter (pTypeCoreDerived M) ℂ)
    (hsPrime : pTypeCoreKernelDerivedComplement ctx ≤
      ClassFunction.translationKernel
        (s : ClassFunction (pTypeCoreDerived M) ℂ)) :
    Module.finrank ℂ s.representation ≤
      pTypeActionFactorCard (Ptype_factor_action ctx facts) := by
  classical
  let D := Ptype_factor_action ctx facts
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  obtain ⟨theta, htheta, hthetaLinear⟩ :=
    pTypeCore_exists_linear_constituent ctx facts s hsPrime
  calc
    Module.finrank ℂ s.representation ≤ HC.index :=
      pTypeCore_degree_le_index_of_linear_constituent
        HC s theta htheta hthetaLinear
    _ = pTypeActionFactorCard D :=
      pTypeCore_HC_index_eq_factorCard ctx facts

/-- Every member of the canonical core family has degree at most `q * u`. -/
theorem pTypeCore_member_degree_le_q_mul_factorCard
    {G : Type u} [Group G] [instG : Fintype G]
    [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    {chi : ClassFunction M ℂ}
    (hchi : chi ∈ pTypeCoreFamilyOfContext ctx) :
    (chi 1).re ≤
      ((Ptype_factor_action ctx facts).q *
        pTypeActionFactorCard (Ptype_factor_action ctx facts) : ℕ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  have hchiData :
      ∃ s : IrreducibleCharacter HU ℂ,
        H₀CPrime ≤ ClassFunction.translationKernel
            (s : ClassFunction HU ℂ) ∧
          chi 1 = (HU.index : ℂ) * s 1 := by
    letI : Fintype G := pTypeCoreContextFintypeOfFinite G
    change chi ∈ seqIndD (k := ℂ) HU H H₀CPrime at hchi
    obtain ⟨s, hs, hsEq⟩ := seqIndP.mp hchi
    refine ⟨s, (mem_Iirr_kerD.mp hs).1, ?_⟩
    rw [hsEq, ClassFunction.induce_one]
  obtain ⟨s, hsPrime, hchiOne⟩ := hchiData
  have hsDegree : Module.finrank ℂ s.representation ≤
      pTypeActionFactorCard D :=
    pTypeCore_irreducible_degree_le_factorCard ctx facts s
      hsPrime
  rw [hchiOne,
    pTypeCore_index_eq_q ctx facts,
    IrreducibleCharacter.apply_one_eq_finrank]
  norm_num
  exact_mod_cast Nat.mul_le_mul_left (Fintype.card W₁) hsDegree

/-- The canonical family is contained in the explicit Section 8 Type-P
kernel layer.  In universe zero this recovers `FTtypePKernelLayer` by
`simpa [FTtypePKernelLayer, PrimeDadeHypothesis.signalizerInKernel]`. -/
theorem pTypeCoreFamily_sub_kernelLayer
    {G : Type u} [Group G] [instG : Fintype G]
    [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (hmaxM : M ∈ minSimple_max_groups (G := G))
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype5 : FTtype M ≠ 5) :
    let ctx := Ptype_Fcore_context hmaxM defW MtypeP notMtype5
    (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)) ⊆
      (↑(seqIndD (k := ℂ)
        ((derivedWithin M).subgroupOf M)
        (((FTcore M).subgroupOf M).subgroupOf
          ((derivedWithin M).subgroupOf M)) ⊥) :
        Set (ClassFunction M ℂ)) := by
  simp only
  let ctx := Ptype_Fcore_context hmaxM defW MtypeP notMtype5
  intro phi hphi
  let HU := pTypeCoreDerived M
  let HF : Subgroup HU := pTypeCoreFitting M
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  let HT : Subgroup HU :=
    ((FTcore M).subgroupOf M).subgroupOf HU
  have hFT : HF ≤ HT := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Fcore_sub_FTcore hmaxM))
  have hphiData :
      ∃ s : IrreducibleCharacter HU ℂ,
        H₀CPrime ≤ ClassFunction.translationKernel
            (s : ClassFunction HU ℂ) ∧
          ¬HF ≤ ClassFunction.translationKernel
            (s : ClassFunction HU ℂ) ∧
          phi = ClassFunction.induce HU
            (s : ClassFunction HU ℂ) := by
    letI : Fintype G := pTypeCoreContextFintypeOfFinite G
    change phi ∈ seqIndD (k := ℂ) HU HF H₀CPrime at hphi
    obtain ⟨s, hs, hsEq⟩ := seqIndP.mp hphi
    refine ⟨s, (mem_Iirr_kerD.mp hs).1,
      (mem_Iirr_kerD.mp hs).2, ?_⟩
    convert hsEq using 1 <;> try apply Subsingleton.elim
    ext x
    simp only [ClassFunction.induce_apply_formula]
    congr 1
    apply Finset.sum_congr
    · ext y
      simp
    · intro y _hy
      rfl
  obtain ⟨s, _hsPrime, hsNotF, hsEq⟩ := hphiData
  apply seqIndP.mpr
  refine ⟨s, (mem_Iirr_kerD.mpr ⟨bot_le, ?_⟩), hsEq⟩
  intro hsT
  exact hsNotF (hFT.trans hsT)

end PTypeCoreContextInternal

end

end Submission.OddOrder.PF
