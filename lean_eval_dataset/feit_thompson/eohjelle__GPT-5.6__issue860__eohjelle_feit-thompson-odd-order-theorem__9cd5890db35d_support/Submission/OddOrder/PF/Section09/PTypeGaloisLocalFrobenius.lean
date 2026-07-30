import Submission.OddOrder.PF.Section09.PTypeGaloisCharacterArithmetic
import Submission.OddOrder.PF.Section09.PTypeGaloisSubgroupAdapters

/-!
# Peterfalvi Section 9: the local Frobenius quotient in the Galois branch

This module constructs the canonical Frobenius decomposition of
`HU / H₀C`.  It then uses a linear character of the resulting kernel,
together with a nonprincipal character of the complementary `C`-factor, to
show that an entirely reducible `H₀C'` induction layer forces `C = ⊥`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open CategoryTheory
open scoped Classical IsMulCommutative Pointwise commutatorElement

noncomputable section

universe u

namespace PTypeGaloisLocalFrobeniusInternal

open PTypeGaloisCharacterArithmeticInternal
open PTypeGaloisSubgroupAdaptersInternal
open internal

/-! ## The canonical quotient -/

/-- The two canonical images in `HU / H₀C` are complementary and
nontrivial. -/
theorem pTypeGalois_localQuotient_algebra
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let UHU := pTypeUInDerived M (derivedWithin M) U
    letI : H.Normal := internal.pTypeHInDerived_normal ctx
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
    (H.map (QuotientGroup.mk' H₀C)).IsComplement'
        (UHU.map (QuotientGroup.mk' H₀C)) ∧
      H.map (QuotientGroup.mk' H₀C) ≠ ⊥ ∧
      UHU.map (QuotientGroup.mk' H₀C) ≠ ⊥ := by
  let D := Ptype_factor_action ctx facts
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
  have hH₀C : H₀C = H₀ ⊔ C := rfl
  letI : (H₀ ⊔ C).Normal := by
    rw [← hH₀C]
    infer_instance
  have hcomp : H.IsComplement' UHU :=
    pTypeHInDerived_isComplement_UInDerived ctx
  have hstrict : H₀ < H ∧ C < UHU :=
    pTypeH0_C_strict_in_derived ctx facts
  have hquotComp := pTypeIsComplement_quotient_sup
    H UHU H₀ C hcomp hstrict.1.le hstrict.2.le
  have hquotNe := pTypeQuotientSup_images_ne_bot
    H UHU H₀ C hcomp hstrict.1 hstrict.2
  simpa only [hH₀C] using ⟨hquotComp, hquotNe⟩

/-! ## Fixed points in the faithful finite-field action -/

/-- In the Galois model, an element outside the action kernel fixes only the
identity of the F-core factor. -/
theorem pTypeGalois_action_fixed_eq_one
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hGal : TypePGaloisConclusion D)
    (x : U) (h : Hbar) (hx : x ∉ D.C)
    (hfix : D.U_action x h = h) :
    h = 1 := by
  by_contra hh
  have hphi : hGal.phi (Additive.ofMul h) ≠ 0 := by
    intro hzero
    apply hh
    apply Additive.ofMul.injective
    apply hGal.phi.injective
    simpa using hzero
  have hcompat := hGal.phi_U_compatible h x
  rw [hfix] at hcompat
  have hpsi : (hGal.psi x : hGal.F) = 1 := by
    apply mul_left_cancel₀ hphi
    calc
      hGal.phi (Additive.ofMul h) * (hGal.psi x : hGal.F) =
          hGal.phi (Additive.ofMul h) := hcompat.symm
      _ = hGal.phi (Additive.ofMul h) * 1 := by rw [mul_one]
  apply hx
  rw [← hGal.psi_kernel]
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  simpa using hpsi

/-- The canonical quotient `HU / H₀C` is a Frobenius group in the Galois
alternative. -/
theorem pTypeGalois_localQuotient_frobenius
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : TypePGaloisConclusion (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let UHU := pTypeUInDerived M (derivedWithin M) U
    letI : H.Normal := internal.pTypeHInDerived_normal ctx
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
    IsFrobeniusDecomposition
      (H.map (QuotientGroup.mk' H₀C))
      (UHU.map (QuotientGroup.mk' H₀C)) := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
  let q : HU →* HU ⧸ H₀C := QuotientGroup.mk' H₀C
  have hH₀C : H₀C = H₀ ⊔ C := rfl
  letI : (H₀ ⊔ C).Normal := by
    rw [← hH₀C]
    infer_instance
  have hcomp : H.IsComplement' UHU :=
    pTypeHInDerived_isComplement_UInDerived ctx
  have hstrict : H₀ < H ∧ C < UHU :=
    pTypeH0_C_strict_in_derived ctx facts
  have halgebra := pTypeGalois_localQuotient_algebra ctx facts
  refine
    { isComplement := halgebra.1
      kernel_normal := Subgroup.Normal.map
        (inferInstance : H.Normal) q
        (QuotientGroup.mk'_surjective H₀C)
      kernel_ne_bot := halgebra.2.1
      complement_ne_bot := halgebra.2.2
      fixedPointFree := ?_ }
  intro r hr k hfix
  obtain ⟨v, hv⟩ := q.subgroupMap_surjective UHU r
  obtain ⟨h, hh⟩ := q.subgroupMap_surjective H k
  have hvq : q (v : HU) = (r : HU ⧸ H₀C) :=
    congrArg Subtype.val hv
  have hhq : q (h : HU) = (k : HU ⧸ H₀C) :=
    congrArg Subtype.val hh
  let u : U :=
    ⟨((((v : UHU) : HU) : M) : Gamma), v.property⟩
  let hF : Fitting_core M :=
    ⟨((((h : H) : HU) : M) : Gamma), h.property⟩
  let hbar : ptypeFCoreFactor ctx :=
    QuotientGroup.mk'
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) hF
  have huC : u ∉ D.C := by
    intro hu
    apply hr
    apply Subtype.ext
    change (r : HU ⧸ H₀C) = 1
    rw [← hvq]
    apply QuotientGroup.eq_one_iff (v : HU) |>.mpr
    rw [hH₀C]
    apply (show C ≤ H₀ ⊔ C from le_sup_right)
    change ((((v : UHU) : HU) : M) : Gamma) ∈ D.C.map U.subtype
    exact ⟨u, hu, rfl⟩
  have hqfix :
      q ((v : HU) * (h : HU) * (v : HU)⁻¹) = q (h : HU) := by
    calc
      q ((v : HU) * (h : HU) * (v : HU)⁻¹) =
          q (v : HU) * q (h : HU) * (q (v : HU))⁻¹ := by
        simp only [map_mul, map_inv]
      _ = (r : HU ⧸ H₀C) * (k : HU ⧸ H₀C) *
          (r : HU ⧸ H₀C)⁻¹ := by rw [hvq, hhq]
      _ = (k : HU ⧸ H₀C) := hfix
      _ = q (h : HU) := hhq.symm
  have hdiffN :
      ((v : HU) * (h : HU) * (v : HU)⁻¹)⁻¹ * (h : HU) ∈ H₀C :=
    QuotientGroup.eq.mp hqfix
  have hconjH : (v : HU) * (h : HU) * (v : HU)⁻¹ ∈ H :=
    (inferInstance : H.Normal).conj_mem
      (h : HU) h.property (v : HU)
  have hdiffH :
      ((v : HU) * (h : HU) * (v : HU)⁻¹)⁻¹ * (h : HU) ∈ H :=
    H.mul_mem (H.inv_mem hconjH) h.property
  have hinter := pTypeInf_sup_eq_of_isComplement
    H UHU H₀ C hcomp hstrict.1.le hstrict.2.le
  have hdiffH₀ :
      ((v : HU) * (h : HU) * (v : HU)⁻¹)⁻¹ * (h : HU) ∈ H₀ := by
    have hmem :
        ((v : HU) * (h : HU) * (v : HU)⁻¹)⁻¹ * (h : HU) ∈
          H ⊓ (H₀ ⊔ C) := ⟨hdiffH, by simpa [hH₀C] using hdiffN⟩
    rw [hinter.1] at hmem
    exact hmem
  have hactionFix : D.U_action u hbar = hbar := by
    change ptypeFCoreAction ctx u
        (QuotientGroup.mk'
          ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) hF) =
      QuotientGroup.mk'
        ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) hF
    rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk]
    apply QuotientGroup.eq.mpr
    change
      ((u : Gamma) * (hF : Gamma) * (u : Gamma)⁻¹)⁻¹ *
          (hF : Gamma) ∈ Ptype_Fcore_kernel ctx
    change
      ((u : Gamma) * (hF : Gamma) * (u : Gamma)⁻¹)⁻¹ *
          (hF : Gamma) ∈ Ptype_Fcore_kernel ctx at hdiffH₀
    exact hdiffH₀
  have hbarOne : hbar = 1 :=
    pTypeGalois_action_fixed_eq_one hGal u hbar huC hactionFix
  have hhH₀ : hF ∈
      (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M) :=
    QuotientGroup.eq_one_iff hF |>.mp hbarOne
  have hhN : (h : HU) ∈ H₀C := by
    rw [hH₀C]
    apply (show H₀ ≤ H₀ ⊔ C from le_sup_left)
    exact hhH₀
  have hqhOne : q (h : HU) = 1 :=
    QuotientGroup.eq_one_iff (h : HU) |>.mpr hhN
  apply Subtype.ext
  change (k : HU ⧸ H₀C) = 1
  rw [← hhq, hqhOne]

/-! ## The derived complement inside `HC` -/

/-- The derived subgroup of the action kernel's canonical complement copy
maps into the derived subgroup of `HC`. -/
theorem pTypeGalois_derived_C_le_commutator_HC
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let CPrime :=
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    CPrime.subgroupOf HC ≤ _root_.commutator HC := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  let iC : D.C →* HC :=
    { toFun := fun c ↦
        ⟨⟨⟨(c : Gamma), hUM (c : U).property⟩,
            hUder (c : U).property⟩, by
          change ⟨⟨(c : Gamma), hUM (c : U).property⟩,
              hUder (c : U).property⟩ ∈
            pTypeHInDerived M (derivedWithin M) (Fitting_core M) ⊔
              ((D.C.map U.subtype).subgroupOf M).subgroupOf HU
          have hcC : ⟨⟨(c : Gamma), hUM (c : U).property⟩,
                hUder (c : U).property⟩ ∈
              ((D.C.map U.subtype).subgroupOf M).subgroupOf HU := by
            change (c : Gamma) ∈ D.C.map U.subtype
            exact ⟨c, c.property, rfl⟩
          exact (show
            ((D.C.map U.subtype).subgroupOf M).subgroupOf HU ≤
              pTypeHInDerived M (derivedWithin M) (Fitting_core M) ⊔
                ((D.C.map U.subtype).subgroupOf M).subgroupOf HU
            from le_sup_right) hcC⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hmapComm : (_root_.commutator D.C).map iC ≤
      _root_.commutator HC := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  change CPrime.subgroupOf HC ≤ _root_.commutator HC
  intro x hx
  change ((((x : HC) : HU) : M) : Gamma) ∈
    pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype) at hx
  obtain ⟨d, hd, hdx⟩ := hx
  have hid : iC d ∈ _root_.commutator HC :=
    hmapComm ⟨d, hd, rfl⟩
  have hxd : x = iC d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hdx.symm
  rwa [hxd]

/-! ## A character detecting both quotient factors -/

private theorem subgroupOf_ne_bot_of_ne_bot
    {A : Type u} [Group A] {H J : Subgroup A}
    (hHJ : H ≤ J) (hH : H ≠ ⊥) : H.subgroupOf J ≠ ⊥ := by
  intro hbot
  apply hH
  apply le_bot_iff.mp
  intro x hx
  let xJ : J := ⟨x, hHJ hx⟩
  have hxSub : xJ ∈ H.subgroupOf J := hx
  rw [hbot] at hxSub
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp hxSub))

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

/-- If `C` is nontrivial, the two factors of `HC / H₀` provide a linear
irreducible character of `HC` which is nonprincipal on both `H` and `C`.
Its restriction to `H` is inflated from the canonical local Frobenius
kernel, so its inertia in `HU` lies in `HC`. -/
theorem pTypeGalois_exists_direct_product_character
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : TypePGaloisConclusion (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    C ≠ ⊥ →
      ∃ r : IrreducibleCharacter HC ℂ,
        pTypeIsLinearCharacter r ∧
        ClassFunction.inertia HC (r : ClassFunction HC ℂ) ≤ HC ∧
        H₀.subgroupOf HC ≤ ClassFunction.translationKernel
          (r : ClassFunction HC ℂ) ∧
        ¬ H.subgroupOf HC ≤ ClassFunction.translationKernel
          (r : ClassFunction HC ℂ) ∧
        ¬ C.subgroupOf HC ≤ ClassFunction.translationKernel
          (r : ClassFunction HC ℂ) := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let HHC := H.subgroupOf HC
  let CHC := C.subgroupOf HC
  let H₀HC := H₀.subgroupOf HC
  letI : IsSolvable M := mmax_sol ctx.maxM
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
  letI : HHC.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : H.Normal) HC
  letI : H₀HC.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : H₀.Normal) HC
  intro hCne
  have hH₀H : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Ptype_Fcore_kernel_lt ctx).le)
  have hCU : C ≤ UHU := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Subgroup.map_subtype_le D.C))
  have hHHC : H ≤ HC := le_sup_left
  have hCHC : C ≤ HC := le_sup_right
  have hcomp : H.IsComplement' UHU :=
    pTypeHInDerived_isComplement_UInDerived ctx
  have hinterHC := pTypeInf_sup_eq_of_isComplement
    H UHU H C hcomp le_rfl hCU
  have hUcap : (UHU ⊓ HC).subgroupOf HC = CHC := by
    ext x
    change (x : HU) ∈ UHU ∧ (x : HU) ∈ H ⊔ C ↔
      (x : HU) ∈ C
    constructor
    · intro hx
      have hxInf : (x : HU) ∈ UHU ⊓ (H ⊔ C) := hx
      rw [hinterHC.2] at hxInf
      exact hxInf
    · intro hx
      exact ⟨hCU hx, (show C ≤ H ⊔ C from le_sup_right) hx⟩
  have hcompHC : HHC.IsComplement' CHC := by
    have hrest := internal.pTypeIsComplement_subgroupOf_of_left_le
      hcomp hHHC
    rw [hUcap] at hrest
    exact hrest
  have hH₀HC_HHC : H₀HC ≤ HHC := by
    intro x hx
    exact hH₀H hx
  let qHC : HC →* HC ⧸ H₀HC := QuotientGroup.mk' H₀HC
  let Hq : Subgroup (HC ⧸ H₀HC) := HHC.map qHC
  let Cq : Subgroup (HC ⧸ H₀HC) := CHC.map qHC
  have hquotComp : Hq.IsComplement' Cq := by
    simpa only [Hq, Cq, qHC] using
      hcompHC.quotient_isComplement hH₀HC_HHC
  have hCHCne : CHC ≠ ⊥ :=
    subgroupOf_ne_bot_of_ne_bot hCHC hCne
  have hCqne : Cq ≠ ⊥ := by
    simpa only [Cq, qHC] using
      hcompHC.quotient_right_ne_bot hH₀HC_HHC hCHCne
  let qHU : HU →* HU ⧸ H₀C := QuotientGroup.mk' H₀C
  let Kq : Subgroup (HU ⧸ H₀C) := H.map qHU
  let Rq : Subgroup (HU ⧸ H₀C) := UHU.map qHU
  have hFrob : IsFrobeniusDecomposition Kq Rq := by
    simpa only [Kq, Rq, qHU] using
      pTypeGalois_localQuotient_frobenius ctx facts hGal
  let eHHC : HHC ≃* H := Subgroup.subgroupOfEquivOfLe hHHC
  let fH : H →* Hq :=
    (qHC.subgroupMap HHC).comp eHHC.symm.toMonoidHom
  let gH : H →* Kq := qHU.subgroupMap H
  have hfH : Function.Surjective fH := by
    exact (qHC.subgroupMap_surjective HHC).comp
      eHHC.symm.surjective
  have hgH : Function.Surjective gH :=
    qHU.subgroupMap_surjective H
  have hfHker : fH.ker = H₀.subgroupOf H := by
    ext x
    change fH x = 1 ↔ (x : H) ∈ H₀.subgroupOf H
    dsimp only [fH]
    change (qHC.subgroupMap HHC) (eHHC.symm x) = 1 ↔
      (x : H) ∈ H₀.subgroupOf H
    constructor
    · intro hx
      have hxval : qHC ((eHHC.symm x : HHC) : HC) = 1 :=
        congrArg Subtype.val hx
      change QuotientGroup.mk' H₀HC
          ((eHHC.symm x : HHC) : HC) = 1 at hxval
      have hxmem : ((eHHC.symm x : HHC) : HC) ∈ H₀HC :=
        (QuotientGroup.eq_one_iff _).mp hxval
      change (x : HU) ∈ H₀ at hxmem ⊢
      exact hxmem
    · intro hx
      apply Subtype.ext
      change qHC ((eHHC.symm x : HHC) : HC) = 1
      change QuotientGroup.mk' H₀HC
          ((eHHC.symm x : HHC) : HC) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      change (x : HU) ∈ H₀ at hx ⊢
      exact hx
  have hgHker : gH.ker = H₀.subgroupOf H := by
    dsimp only [gH]
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    ext x
    change (x : HU) ∈ H₀C ↔ (x : HU) ∈ H₀
    constructor
    · intro hx
      change (x : HU) ∈ H₀ ⊔ C at hx
      have hxInf : (x : HU) ∈ H ⊓ (H₀ ⊔ C) :=
        ⟨x.property, hx⟩
      have hinter := pTypeInf_sup_eq_of_isComplement
        H UHU H₀ C hcomp hH₀H hCU
      rw [hinter.1] at hxInf
      exact hxInf
    · intro hx
      change (x : HU) ∈ H₀ ⊔ C
      exact (show H₀ ≤ H₀ ⊔ C from le_sup_left) hx
  let eHK : Hq ≃* Kq :=
    internal.pTypeGaloisImageEquivOfCommonKernel
      (H₀.subgroupOf H) fH gH hfH hgH hfHker hgHker
  letI : Nontrivial Kq :=
    Kq.nontrivial_iff_ne_bot.mpr hFrob.kernel_ne_bot
  obtain ⟨iK, hiKlinear, hiKnon⟩ :=
    exists_nontrivial_linear_character_of_solvable (A := Kq)
  let iH : IrreducibleCharacter Hq ℂ :=
    internal.pTypeGaloisComapMulEquiv eHK iK
  have hiHlinear : pTypeIsLinearCharacter iH :=
    internal.pTypeIsLinearCharacter_comapMulEquiv eHK iK hiKlinear
  have hiHnon : iH ≠ IrreducibleCharacter.trivial :=
    internal.pTypeComapMulEquiv_ne_trivial eHK iK hiKnon
  letI : Nontrivial Cq := Cq.nontrivial_iff_ne_bot.mpr hCqne
  obtain ⟨jC, hjClinear, hjCnon⟩ :=
    exists_nontrivial_linear_character_of_solvable (A := Cq)
  have hcross : ⁅H, C⁆ ≤ H₀ := by
    rw [Subgroup.commutator_comm]
    exact pTypeGalois_commutator_C_H_le_H0 ctx facts
  have hcomm : ∀ x : Hq, ∀ y : Cq,
      Commute (x : HC ⧸ H₀HC) (y : HC ⧸ H₀HC) := by
    intro x y
    obtain ⟨x₀, hx₀⟩ := qHC.subgroupMap_surjective HHC x
    obtain ⟨y₀, hy₀⟩ := qHC.subgroupMap_surjective CHC y
    have hxq : qHC (x₀ : HC) = (x : HC ⧸ H₀HC) :=
      congrArg Subtype.val hx₀
    have hyq : qHC (y₀ : HC) = (y : HC ⧸ H₀HC) :=
      congrArg Subtype.val hy₀
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← hxq, ← hyq, ← map_commutatorElement]
    apply QuotientGroup.eq_one_iff (⁅(x₀ : HC), (y₀ : HC)⁆) |>.mpr
    change ⁅((x₀ : HC) : HU), ((y₀ : HC) : HU)⁆ ∈ H₀
    exact hcross (Subgroup.commutator_mem_commutator
      x₀.property y₀.property)
  let hdirect : IsInternalDirectProductIn Hq Cq
      (⊤ : Subgroup (HC ⧸ H₀HC)) :=
    pTypeInternalDirectProduct_top_of_complement_commute
      Hq Cq hquotComp hcomm
  let eQ : Hq × Cq ≃* HC ⧸ H₀HC :=
    hdirect.mulEquiv.trans Subgroup.topEquiv
  let rQ : IrreducibleCharacter (HC ⧸ H₀HC) ℂ :=
    internal.pTypeGaloisComapMulEquiv eQ.symm
      (internal.pTypeGaloisExternalProduct iH jC)
  have hrQlinear : pTypeIsLinearCharacter rQ := by
    apply internal.pTypeIsLinearCharacter_comapMulEquiv
    exact internal.pTypeIsLinearCharacter_externalProduct
      iH jC hiHlinear hjClinear
  have hqHC : Function.Surjective qHC :=
    QuotientGroup.mk'_surjective H₀HC
  let r : IrreducibleCharacter HC ℂ :=
    internal.pTypeGaloisInflateIrreducible qHC hqHC rQ
  have hrlinear : pTypeIsLinearCharacter r :=
    internal.pTypeIsLinearCharacter_inflate qHC hqHC rQ hrQlinear
  have hrQapply (z : HC ⧸ H₀HC) :
      rQ z = internal.pTypeGaloisExternalProduct iH jC (eQ.symm z) := by
    exact internal.pTypeGaloisComapMulEquiv_apply eQ.symm
      (internal.pTypeGaloisExternalProduct iH jC) z
  have hiHapply (z : Hq) : iH z = iK (eHK z) := by
    exact internal.pTypeGaloisComapMulEquiv_apply eHK iK z
  have heLeft (x : H) :
      eQ.symm (qHC (Subgroup.inclusion hHHC x)) = (fH x, 1) := by
    apply eQ.injective
    rw [eQ.apply_symm_apply]
    change qHC (Subgroup.inclusion hHHC x) =
      (fH x : HC ⧸ H₀HC) * 1
    rw [mul_one]
    rfl
  let gC : CHC →* Cq := qHC.subgroupMap CHC
  have hgC : Function.Surjective gC :=
    qHC.subgroupMap_surjective CHC
  have heRight (x : CHC) :
      eQ.symm (qHC (x : HC)) = (1, gC x) := by
    apply eQ.injective
    rw [eQ.apply_symm_apply]
    change qHC (x : HC) = 1 * (gC x : HC ⧸ H₀HC)
    rw [one_mul]
    rfl
  let thetaH : IrreducibleCharacter H ℂ :=
    internal.pTypeGaloisInflateIrreducible gH hgH iK
  have hthetaHlinear : pTypeIsLinearCharacter thetaH :=
    internal.pTypeIsLinearCharacter_inflate gH hgH iK hiKlinear
  have hthetaHnon : thetaH ≠ IrreducibleCharacter.trivial :=
    internal.pTypeGaloisInflate_ne_trivial gH hgH iK hiKnon
  have hrestrictH : ClassFunction.comap
      (Subgroup.inclusion hHHC) (r : ClassFunction HC ℂ) =
      (thetaH : ClassFunction H ℂ) := by
    ext x
    change r (Subgroup.inclusion hHHC x) = thetaH x
    rw [internal.pTypeGaloisInflateIrreducible_apply,
      internal.pTypeGaloisInflateIrreducible_apply]
    rw [hrQapply, heLeft, internal.pTypeGaloisExternalProduct_apply,
      internal.pTypeLinear_apply_one jC hjClinear, mul_one, hiHapply]
    rw [internal.pTypeGaloisImageEquivOfCommonKernel_apply]
  have hthetaCF : (thetaH : ClassFunction H ℂ) =
      ClassFunction.comap gH (iK : ClassFunction Kq ℂ) := by
    ext x
    exact internal.pTypeGaloisInflateIrreducible_apply gH hgH iK x
  have hHCeq : H ⊔ H₀C = HC := by
    change H ⊔ (H₀ ⊔ C) = H ⊔ C
    rw [← sup_assoc, sup_eq_left.mpr hH₀H]
  have hthetaInertia : ClassFunction.inertia H
      (thetaH : ClassFunction H ℂ) = HC := by
    rw [hthetaCF]
    simpa only [gH, hHCeq] using
      internal.pTypeInertia_inflated_FrobeniusKernel
        H₀C H UHU hFrob iK hiKnon
  have hrInertia : ClassFunction.inertia HC
      (r : ClassFunction HC ℂ) ≤ HC := by
    have hle : ClassFunction.inertia HC
        (r : ClassFunction HC ℂ) ≤
        ClassFunction.inertia H (thetaH : ClassFunction H ℂ) := by
      intro x hx
      rw [ClassFunction.mem_inertia_iff] at hx ⊢
      rw [← hrestrictH]
      ext h
      have hvalue := congrArg
        (fun phi : ClassFunction HC ℂ ↦
          phi (Subgroup.inclusion hHHC h)) hx
      simp only [ClassFunction.normalConjugate_apply,
        ClassFunction.comap_apply] at hvalue ⊢
      have harg :
          Subgroup.inclusion hHHC ((MulAut.conjNormal x).symm h) =
            (MulAut.conjNormal x).symm
              (Subgroup.inclusion hHHC h) := by
        apply Subtype.ext
        rfl
      rw [harg]
      exact hvalue
    calc
      ClassFunction.inertia HC (r : ClassFunction HC ℂ) ≤
          ClassFunction.inertia H (thetaH : ClassFunction H ℂ) := hle
      _ = HC := hthetaInertia
  have hrCF : (r : ClassFunction HC ℂ) =
      ClassFunction.comap qHC (rQ : ClassFunction (HC ⧸ H₀HC) ℂ) := by
    ext x
    exact internal.pTypeGaloisInflateIrreducible_apply qHC hqHC rQ x
  have hH₀ker : H₀HC ≤ ClassFunction.translationKernel
      (r : ClassFunction HC ℂ) := by
    rw [hrCF]
    have hkerq : H₀HC ≤ qHC.ker := by
      rw [QuotientGroup.ker_mk']
    exact hkerq.trans
      (ClassFunction.ker_le_translationKernel_comap qHC _)
  have hHnon : ¬ HHC ≤ ClassFunction.translationKernel
      (r : ClassFunction HC ℂ) := by
    intro hHker
    apply internal.pTypeLinear_ne_trivial_not_top_le_kernel
      thetaH hthetaHlinear hthetaHnon
    intro x _hx
    rw [← hrestrictH, ClassFunction.mem_translationKernel_iff]
    intro y
    change r (Subgroup.inclusion hHHC (x * y)) =
      r (Subgroup.inclusion hHHC y)
    rw [map_mul]
    have hxMem : Subgroup.inclusion hHHC x ∈ HHC := x.property
    exact hHker hxMem
      (Subgroup.inclusion hHHC y)
  let thetaC : IrreducibleCharacter CHC ℂ :=
    internal.pTypeGaloisInflateIrreducible gC hgC jC
  have hthetaClinear : pTypeIsLinearCharacter thetaC :=
    internal.pTypeIsLinearCharacter_inflate gC hgC jC hjClinear
  have hthetaCnon : thetaC ≠ IrreducibleCharacter.trivial :=
    internal.pTypeGaloisInflate_ne_trivial gC hgC jC hjCnon
  have hrestrictC : ClassFunction.comap
      CHC.subtype (r : ClassFunction HC ℂ) =
      (thetaC : ClassFunction CHC ℂ) := by
    ext x
    change r (x : HC) = thetaC x
    rw [internal.pTypeGaloisInflateIrreducible_apply,
      internal.pTypeGaloisInflateIrreducible_apply]
    calc
      rQ (qHC (x : HC)) =
          internal.pTypeGaloisExternalProduct iH jC
            (eQ.symm (qHC (x : HC))) := hrQapply _
      _ = internal.pTypeGaloisExternalProduct iH jC (1, gC x) := by
        rw [heRight]
      _ = iH 1 * jC (gC x) :=
        internal.pTypeGaloisExternalProduct_apply iH jC 1 (gC x)
      _ = jC (gC x) := by
        rw [internal.pTypeLinear_apply_one iH hiHlinear, one_mul]
  have hCnon : ¬ CHC ≤ ClassFunction.translationKernel
      (r : ClassFunction HC ℂ) := by
    intro hCker
    apply internal.pTypeLinear_ne_trivial_not_top_le_kernel
      thetaC hthetaClinear hthetaCnon
    intro x _hx
    rw [← hrestrictC, ClassFunction.mem_translationKernel_iff]
    intro y
    change r ((x * y : CHC) : HC) = r (y : HC)
    have hval : ((x * y : CHC) : HC) = (x : HC) * (y : HC) := rfl
    rw [hval]
    exact hCker x.property (y : HC)
  exact ⟨r, hrlinear, hrInertia, hH₀ker, hHnon, hCnon⟩

/-! ## The all-reducible contradiction -/

set_option maxHeartbeats 3000000

/-- The derived-complement kernel bound sits in `HC`, and restricting it to
`HC` distributes over its canonical two summands. -/
private theorem pTypeGalois_prime_kernel_geometry
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let CPrime :=
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    H₀CPrime ≤ HC ∧
      H₀CPrime.subgroupOf HC =
        H₀.subgroupOf HC ⊔ CPrime.subgroupOf HC := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  have hH₀H : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Ptype_Fcore_kernel_lt ctx).le)
  have hH₀C_HC : H₀C ≤ HC := by
    change H₀ ⊔ C ≤ H ⊔ C
    exact sup_le_sup hH₀H le_rfl
  have hPrimeHC : H₀CPrime ≤ HC :=
    (pTypeH0CPrimeInDerived_le_H0CInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U W₁ D).trans
        hH₀C_HC
  have hH₀HC : H₀ ≤ HC := le_sup_left.trans hPrimeHC
  have hCPrimeHC : CPrime ≤ HC := le_sup_right.trans hPrimeHC
  refine ⟨hPrimeHC, ?_⟩
  change (H₀ ⊔ CPrime).subgroupOf HC =
    H₀.subgroupOf HC ⊔ CPrime.subgroupOf HC
  exact Subgroup.subgroupOf_sup hH₀HC hCPrimeHC

/-- A linear character of `HC` kills the restricted derived-complement
summand. -/
private theorem pTypeGalois_CPrime_le_translationKernel_of_linear
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let CPrime :=
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    ∀ r : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter r →
      CPrime.subgroupOf HC ≤
        ClassFunction.translationKernel (r : ClassFunction HC ℂ) := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  intro r hrlinear
  exact (pTypeGalois_derived_C_le_commutator_HC ctx facts).trans
    (commutator_le_translationKernel_of_isLinear r hrlinear)

/-- Combining the two summand kernel bounds kills the whole `H₀C'`
subgroup inside `HC`. -/
private theorem pTypeGalois_H0CPrime_le_translationKernel_of_linear
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let CPrime :=
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    ∀ r : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter r →
      H₀.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) →
      H₀CPrime.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  intro r hrlinear hH₀ker
  have hPrimeSub : H₀CPrime.subgroupOf HC =
      H₀.subgroupOf HC ⊔ CPrime.subgroupOf HC :=
    (pTypeGalois_prime_kernel_geometry ctx facts).2
  rw [hPrimeSub]
  exact sup_le hH₀ker
    (pTypeGalois_CPrime_le_translationKernel_of_linear
      ctx facts r hrlinear)

/-- The linear direct-product character kills the whole `H₀C'` source
kernel, and that source kernel lies in `HC`. -/
private theorem pTypeGalois_prime_kernel_of_direct_linear_character
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    ∀ r : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter r →
      H₀.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) →
      H₀CPrime ≤ HC ∧
        H₀CPrime.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  intro r hrlinear hH₀ker
  exact ⟨(pTypeGalois_prime_kernel_geometry ctx facts).1,
    pTypeGalois_H0CPrime_le_translationKernel_of_linear
      ctx facts r hrlinear hH₀ker⟩

/-- Representation-kernel bounds are the defining two conditions for the
`Iirr_kerD` layer. -/
private theorem pTypeGalois_mem_Iirr_kerD_of_representation_kernel
    {G : Type u} [Group G] [Fintype G]
    (H K : Subgroup G) [H.Normal] [K.Normal]
    (s : IrreducibleCharacter G ℂ)
    (hK : K ≤ s.representation.ρ.ker)
    (hH : ¬ H ≤ s.representation.ρ.ker) :
    s ∈ Iirr_kerD (k := ℂ) H K := by
  rw [mem_Iirr_kerD]
  constructor
  · rw [internal.pTypeGaloisTranslationKernel_irreducibleCharacter s]
    exact hK
  · intro hsH
    apply hH
    rw [← internal.pTypeGaloisTranslationKernel_irreducibleCharacter s]
    exact hsH

/-- A constituent over `ℂ` embeds into the representation that realizes its
ambient character, without identifying the group and coefficient universes. -/
private theorem pTypeGalois_exists_injective_constituent_hom
    {G : Type u} [Group G] [Fintype G]
    (V : FDRep ℂ G) (chi : IrreducibleCharacter G ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V,
      Function.Injective
        (((forget₂ (FDRep ℂ G) (Rep ℂ G)).map f).hom) := by
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card G : ℂ) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction G ℂ) =
        (Module.finrank ℂ (chi.representation ⟶ V) : ℂ) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant
        chi.representation V
    have hcharV (g : G) :
        V.character g = _root_.Representation.character V.ρ g := rfl
    simpa only [characterPairing,
      ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character, invOf_eq_inv,
      smul_eq_mul, Fintype.card_eq_nat_card, hcharV] using hhom
  have hfin : Module.finrank ℂ (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hchi
    rw [hpair, hzero, Nat.cast_zero]
  obtain ⟨f, hf⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hfin)
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Mono f := CategoryTheory.mono_of_nonzero_from_simple hf
  refine ⟨f, ?_⟩
  exact (Rep.mono_iff_injective
    ((forget₂ (FDRep ℂ G) (Rep ℂ G)).map f)).mp inferInstance

/-- The representation kernel lies in the kernel of every irreducible
constituent, in the split-universe setting used here. -/
private theorem pTypeGalois_representationKernel_le_constituentKernel
    {G : Type u} [Group G] [Fintype G]
    (V : FDRep ℂ G) (chi : IrreducibleCharacter G ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ :=
    pTypeGalois_exists_injective_constituent_hom V chi hchi
  let fR := (forget₂ (FDRep ℂ G) (Rep ℂ G)).map f
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro x
  apply hf
  have hinter := _root_.Representation.IntertwiningMap.isIntertwining
    (ρ := ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj
      chi.representation).ρ)
    (σ := ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj V).ρ)
    (f := fR.hom) g x
  change fR.hom (chi.representation.ρ g x) =
    V.ρ g (fR.hom x) at hinter
  rw [MonoidHom.mem_ker.mp hg] at hinter
  simpa using hinter

set_option maxHeartbeats 8000000
/-- Reverse kernel transport for a constituent of induction, isolated from
the large dependent P-type context. -/
private theorem pTypeGalois_sub_ker_constituent_induce_mpr
    {G : Type u} [Group G] [Fintype G]
    (H A : Subgroup G) [H.Normal] [A.Normal]
    (hAH : A ≤ H)
    (chi : IrreducibleCharacter G ℂ)
    (psi : IrreducibleCharacter H ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.induce H (psi : ClassFunction H ℂ)))
    (hAchi : A ≤ chi.representation.ρ.ker) :
    A.subgroupOf H ≤ psi.representation.ρ.ker := by
  have hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G ℂ)) :=
    (psi.isConstituent_restrict_iff_induce H chi).mpr hchi
  let R : FDRep ℂ H :=
    FDRep.of (chi.representation.ρ.comp H.subtype)
  have hRchar : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict H (chi : ClassFunction G ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  have hpsiR : psi.IsConstituent
      (ClassFunction.ofRepresentation R.ρ) := by
    rwa [hRchar]
  have hkerRpsi : R.ρ.ker ≤ psi.representation.ρ.ker :=
    pTypeGalois_representationKernel_le_constituentKernel
      R psi hpsiR
  intro h hh
  apply hkerRpsi
  rw [MonoidHom.mem_ker]
  change chi.representation.ρ (h : G) = 1
  exact MonoidHom.mem_ker.mp (hAchi hh)

set_option maxHeartbeats 3000000

/-- The Frobenius inertia bound makes the induced character itself an
irreducible constituent. -/
private theorem pTypeGalois_exists_induced_irreducible_constituent
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    ∀ r : IrreducibleCharacter HC ℂ,
      ClassFunction.inertia HC (r : ClassFunction HC ℂ) ≤ HC →
      ∃ s : IrreducibleCharacter HU ℂ,
        (s : ClassFunction HU ℂ) =
            ClassFunction.induce HC (r : ClassFunction HC ℂ) ∧
          s.IsConstituent
            (ClassFunction.induce HC (r : ClassFunction HC ℂ)) := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r hrInertia
  have hIndIrr : IsIrreducibleCharacter HU ℂ
      (ClassFunction.induce HC (r : ClassFunction HC ℂ)) :=
    FrobeniusKernelInductionAux.irreducible_induce_of_inertia
      r hrInertia
  let s : IrreducibleCharacter HU ℂ :=
    ⟨ClassFunction.induce HC (r : ClassFunction HC ℂ), hIndIrr⟩
  letI : Invertible (Nat.card HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine ⟨s, rfl, ?_⟩
  unfold IrreducibleCharacter.IsConstituent
  change characterPairing (s : ClassFunction HU ℂ)
    (s : ClassFunction HU ℂ) ≠ 0
  rw [IrreducibleCharacter.characterPairing_self]
  exact one_ne_zero

set_option maxHeartbeats 8000000
/-- A constituent transports the prime kernel bound from the inducing
character. -/
private theorem pTypeGalois_constituent_prime_kernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    ∀ (r : IrreducibleCharacter HC ℂ)
        (s : IrreducibleCharacter HU ℂ),
      (s : ClassFunction HU ℂ) =
          ClassFunction.induce HC (r : ClassFunction HC ℂ) →
      H₀CPrime ≤ HC →
      H₀CPrime.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) →
      H₀CPrime ≤ s.representation.ρ.ker := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H₀CPrime.Normal :=
    internal.pTypeH0CPrimeInDerived_normal ctx facts
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r s hsInduce hPrimeHC hPrimeKer
  have hsPrimeKer : H₀CPrime ≤
      ClassFunction.translationKernel (s : ClassFunction HU ℂ) := by
    rw [hsInduce]
    exact ClassFunction.le_translationKernel_induce
      H₀CPrime HC hPrimeHC
        (r : ClassFunction HC ℂ) hPrimeKer
  rw [← internal.pTypeGaloisTranslationKernel_irreducibleCharacter s]
  exact hsPrimeKer

set_option maxHeartbeats 3000000

set_option maxHeartbeats 8000000
/-- A constituent cannot acquire the whole Fitting subgroup in its kernel
when the inducing character did not have it. -/
private theorem pTypeGalois_constituent_not_H_kernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    ∀ (r : IrreducibleCharacter HC ℂ)
        (s : IrreducibleCharacter HU ℂ),
      s.IsConstituent
          (ClassFunction.induce HC (r : ClassFunction HC ℂ)) →
      (¬ H.subgroupOf HC ≤
        ClassFunction.translationKernel (r : ClassFunction HC ℂ)) →
      ¬ H ≤ s.representation.ρ.ker := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r s hconst hHnon hsH
  have hrHrho : H.subgroupOf HC ≤ r.representation.ρ.ker :=
    pTypeGalois_sub_ker_constituent_induce_mpr
      HC H le_sup_left s r hconst hsH
  apply hHnon
  rw [internal.pTypeGaloisTranslationKernel_irreducibleCharacter r]
  exact hrHrho

set_option maxHeartbeats 3000000

set_option maxHeartbeats 8000000
/-- Inducing a character with the preceding prime-kernel data gives the
required irreducible witness in the `H₀C'` layer. -/
private theorem pTypeGalois_prime_layer_witness_of_kernel_data
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    ∀ r : IrreducibleCharacter HC ℂ,
      ClassFunction.inertia HC (r : ClassFunction HC ℂ) ≤ HC →
      (¬ H.subgroupOf HC ≤
        ClassFunction.translationKernel (r : ClassFunction HC ℂ)) →
      H₀CPrime ≤ HC →
      H₀CPrime.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) →
      ∃ s : IrreducibleCharacter HU ℂ,
        s.IsConstituent
            (ClassFunction.induce HC (r : ClassFunction HC ℂ)) ∧
        s ∈ Iirr_kerD (k := ℂ) H H₀CPrime := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀CPrime.Normal :=
    internal.pTypeH0CPrimeInDerived_normal ctx facts
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r hrInertia hHnon hPrimeHC hPrimeKer
  obtain ⟨s, hsInduce, hconst⟩ :=
    pTypeGalois_exists_induced_irreducible_constituent
      ctx facts r hrInertia
  have hsPrimeRho : H₀CPrime ≤ s.representation.ρ.ker :=
    pTypeGalois_constituent_prime_kernel
      ctx facts r s hsInduce hPrimeHC hPrimeKer
  have hsHnon : ¬ H ≤ s.representation.ρ.ker :=
    pTypeGalois_constituent_not_H_kernel
      ctx facts r s hconst hHnon
  exact ⟨s, hconst,
    pTypeGalois_mem_Iirr_kerD_of_representation_kernel
      H H₀CPrime s hsPrimeRho hsHnon⟩

set_option maxHeartbeats 3000000

/-- A direct-product character whose kernel contains `H₀` induces an
irreducible witness in the `H₀C'` layer. -/
private theorem pTypeGalois_prime_layer_witness_of_direct_character
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    ∀ r : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter r →
      ClassFunction.inertia HC (r : ClassFunction HC ℂ) ≤ HC →
      H₀.subgroupOf HC ≤
        ClassFunction.translationKernel (r : ClassFunction HC ℂ) →
      (¬ H.subgroupOf HC ≤
        ClassFunction.translationKernel (r : ClassFunction HC ℂ)) →
      ∃ s : IrreducibleCharacter HU ℂ,
        s.IsConstituent
            (ClassFunction.induce HC (r : ClassFunction HC ℂ)) ∧
        s ∈ Iirr_kerD (k := ℂ) H H₀CPrime := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r hrlinear hrInertia hH₀ker hHnon
  have hPrime := pTypeGalois_prime_kernel_of_direct_linear_character
    ctx facts r hrlinear hH₀ker
  exact pTypeGalois_prime_layer_witness_of_kernel_data
    ctx facts r hrInertia hHnon hPrime.1 hPrime.2

/-- A nontrivial complement kernel produces an induced irreducible witness
in the `H₀C'` layer, before using the reducibility hypothesis. -/
private theorem pTypeGalois_exists_prime_layer_witness_of_C_ne_bot
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : TypePGaloisConclusion (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    C ≠ ⊥ →
    ∃ (r : IrreducibleCharacter HC ℂ)
        (s : IrreducibleCharacter HU ℂ),
      s.IsConstituent
          (ClassFunction.induce HC (r : ClassFunction HC ℂ)) ∧
      ¬ C.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) ∧
      s ∈ Iirr_kerD (k := ℂ) H H₀CPrime := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro hCne
  obtain ⟨r, hrlinear, hrInertia, hH₀ker, hHnon, hCnon⟩ :=
    pTypeGalois_exists_direct_product_character
      ctx facts hGal hCne
  obtain ⟨s, hconst, hsLayer⟩ :=
    pTypeGalois_prime_layer_witness_of_direct_character
      ctx facts r hrlinear hrInertia hH₀ker hHnon
  exact ⟨r, s, hconst, hCnon, hsLayer⟩


/-- A nontrivial `C`, together with reducibility of the `H₀C'` layer,
produces a constituent witness in the ordinary reducible `H₀` layer. -/
private theorem pTypeGalois_exists_reducible_witness_of_C_ne_bot
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : TypePGaloisConclusion (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    C ≠ ⊥ →
    (∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
      ¬ IsIrreducibleCharacter M ℂ zeta) →
    ∃ (r : IrreducibleCharacter HC ℂ)
        (s : IrreducibleCharacter HU ℂ),
      s.IsConstituent
          (ClassFunction.induce HC (r : ClassFunction HC ℂ)) ∧
      ¬ C.subgroupOf HC ≤
          ClassFunction.translationKernel (r : ClassFunction HC ℂ) ∧
      ClassFunction.induce HU (s : ClassFunction HU ℂ) ∈
        pTypeReducibleLayer HU H H₀ := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀CPrime.Normal :=
    internal.pTypeH0CPrimeInDerived_normal ctx facts
  change C ≠ ⊥ →
    (∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
      ¬ IsIrreducibleCharacter M ℂ zeta) → _
  intro hCne hAllReducible
  obtain ⟨r, s, hconst, hCnon, hsLayer⟩ :=
    pTypeGalois_exists_prime_layer_witness_of_C_ne_bot
      ctx facts hGal hCne
  let zeta : ClassFunction M ℂ :=
    ClassFunction.induce HU (s : ClassFunction HU ℂ)
  have hzetaPrime : zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime :=
    seqIndP.mpr ⟨s, hsLayer, rfl⟩
  have hzetaReducible : ¬ IsIrreducibleCharacter M ℂ zeta :=
    hAllReducible zeta hzetaPrime
  have hsLayerH₀ : s ∈ Iirr_kerD (k := ℂ) H H₀ := by
    have hsData := mem_Iirr_kerD.mp hsLayer
    exact mem_Iirr_kerD.mpr
      ⟨(show H₀ ≤ H₀CPrime from le_sup_left).trans hsData.1,
        hsData.2⟩
  have hzetaH₀ : zeta ∈ seqIndD (k := ℂ) HU H H₀ :=
    seqIndP.mpr ⟨s, hsLayerH₀, rfl⟩
  have hzetaMu : zeta ∈ pTypeReducibleLayer HU H H₀ := by
    rw [pTypeReducibleLayer, Finset.mem_filter]
    exact ⟨hzetaH₀, hzetaReducible⟩
  refine ⟨r, s, hconst, hCnon, ?_⟩
  simpa only [zeta] using hzetaMu

/-- The canonical Fitting subgroup of `HU` maps back to a normal subgroup
of `M`.  Keeping this normality proof opaque avoids repeatedly unfolding the
nested `subgroupOf` presentation during `mem_seqInd`. -/
private theorem pTypeGalois_H_map_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    (H.map HU.subtype).Normal := by
  dsimp only
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hHHU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro x hx
    exact hHder hx
  have hHmap : H.map HU.subtype =
      (Fitting_core M).subgroupOf M := by
    simpa only [H, HU, pTypeHInDerived, pTypeHUInMaximal] using
      Subgroup.map_subgroupOf_eq_of_le hHHU
  rw [hHmap]
  infer_instance

/-- The literal `H₀C` kernel bound of `HU` maps back to the normal
F-core/complement extension in `M`. -/
private theorem pTypeGalois_H0C_map_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    (H₀C.map HU.subtype).Normal := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let H₀a := Ptype_Fcore_kernel ctx
  let Cₐ := Ptype_Fcompl_kernel ctx
  let Kₐ : Subgroup Gamma := H₀a ⊔ Cₐ
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hH₀der : H₀a ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hCder : Cₐ ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hH₀M : H₀a ≤ M := hH₀der.trans hDerM
  have hCM : Cₐ ≤ M := hCder.trans hDerM
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hCHU : Cₐ.subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  have hKHU : Kₐ.subgroupOf M ≤ HU := by
    change (H₀a ⊔ Cₐ).subgroupOf M ≤ HU
    rw [Subgroup.subgroupOf_sup hH₀M hCM]
    exact sup_le hH₀HU hCHU
  have hH₀Ceq : H₀C = (Kₐ.subgroupOf M).subgroupOf HU := by
    change (H₀a.subgroupOf M).subgroupOf HU ⊔
        (((D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      (Kₐ.subgroupOf M).subgroupOf HU
    have hDC : D.C.map U.subtype = Cₐ := rfl
    rw [hDC, ← Subgroup.subgroupOf_sup hH₀HU hCHU,
      ← Subgroup.subgroupOf_sup hH₀M hCM]
  change (H₀C.map HU.subtype).Normal
  rw [hH₀Ceq, Subgroup.map_subgroupOf_eq_of_le hKHU]
  exact (Ptype_Fcore_extensions_normal ctx).H₀C_normal.2

/-- The reducible-layer transfer places the induced character in the
literal `H₀C` induction family. -/
private theorem pTypeGalois_reducible_induce_mem_seqInd_H0C
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    ∀ s : IrreducibleCharacter HU ℂ,
      ClassFunction.induce HU (s : ClassFunction HU ℂ) ∈
          pTypeReducibleLayer HU H H₀ →
      ClassFunction.induce HU (s : ClassFunction HU ℂ) ∈
          seqIndD (k := ℂ) HU H H₀C := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
  intro s hsReducible
  exact (pType_nb_redM_H0 ctx facts).2
    (ClassFunction.induce HU (s : ClassFunction HU ℂ)) hsReducible

/-- Membership of an induced character in the literal `H₀C` family
reflects back to its specified irreducible source. -/
private theorem pTypeGalois_seqInd_H0C_reflects_source
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    ∀ s : IrreducibleCharacter HU ℂ,
      ClassFunction.induce HU (s : ClassFunction HU ℂ) ∈
          seqIndD (k := ℂ) HU H H₀C →
      s ∈ Iirr_kerD (k := ℂ) H H₀C := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
  letI : HU.Normal :=
    Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 M
  letI : (H.map HU.subtype).Normal :=
    pTypeGalois_H_map_normal ctx
  letI : (H₀C.map HU.subtype).Normal :=
    pTypeGalois_H0C_map_normal ctx facts
  intro s hsInduced
  exact (mem_seqInd HU H H₀C s).mp hsInduced


/-- The reducible-layer transfer theorem puts the witness back in the
literal `H₀C` kernel layer of `HU`. -/
private theorem pTypeGalois_reducible_witness_mem_H0C
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    ∀ s : IrreducibleCharacter HU ℂ,
      ClassFunction.induce HU (s : ClassFunction HU ℂ) ∈
          pTypeReducibleLayer HU H H₀ →
        s ∈ Iirr_kerD (k := ℂ) H H₀C := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  intro s hsReducible
  exact pTypeGalois_seqInd_H0C_reflects_source ctx facts s
    (pTypeGalois_reducible_induce_mem_seqInd_H0C
      ctx facts s hsReducible)

/-- The literal `H₀C` kernel bound lies in `HC`. -/
private theorem pTypeGalois_H0C_le_HC
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    H₀C ≤ HC := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  have hH₀H : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Ptype_Fcore_kernel_lt ctx).le)
  change H₀ ⊔ C ≤ H ⊔ C
  exact sup_le_sup hH₀H le_rfl

set_option maxHeartbeats 8000000
/-- The `H₀C` representation-kernel bound transports from a constituent
to its inducing character. -/
private theorem pTypeGalois_constituent_H0C_kernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : HC.Normal :=
      PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
    ∀ (r : IrreducibleCharacter HC ℂ)
        (s : IrreducibleCharacter HU ℂ),
      s.IsConstituent
          (ClassFunction.induce HC (r : ClassFunction HC ℂ)) →
      s ∈ Iirr_kerD (k := ℂ) H H₀C →
      H₀C.subgroupOf HC ≤ r.representation.ρ.ker := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := internal.pTypeHInDerived_normal ctx
  letI : H₀C.Normal := internal.pTypeH0CInDerived_normal ctx facts
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r s hconst hsLayerH₀C
  have hsH₀CRho : H₀C ≤ s.representation.ρ.ker := by
    rw [← internal.pTypeGaloisTranslationKernel_irreducibleCharacter s]
    exact (mem_Iirr_kerD.mp hsLayerH₀C).1
  exact pTypeGalois_sub_ker_constituent_induce_mpr
    HC H₀C (pTypeGalois_H0C_le_HC ctx facts)
      s r hconst hsH₀CRho

set_option maxHeartbeats 3000000

/-- The canonical `C` copy inside `HC` is contained in the restricted
`H₀C` copy. -/
private theorem pTypeGalois_C_subgroupOf_le_H0C_subgroupOf
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    C.subgroupOf HC ≤ H₀C.subgroupOf HC := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  intro x hx
  change ((x : HC) : HU) ∈ H₀C
  have hC : C ≤ H₀C := by
    exact le_sup_right
  exact hC hx

set_option maxHeartbeats 8000000
/-- A constituent in the `H₀C` kernel layer forces the canonical copy of
`C` into the translation kernel of the inducing character. -/
private theorem pTypeGalois_C_le_translationKernel_of_H0C_witness
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    ∀ (r : IrreducibleCharacter HC ℂ)
        (s : IrreducibleCharacter HU ℂ),
      s.IsConstituent
          (ClassFunction.induce HC (r : ClassFunction HC ℂ)) →
      s ∈ Iirr_kerD (k := ℂ) H H₀C →
      C.subgroupOf HC ≤
        ClassFunction.translationKernel (r : ClassFunction HC ℂ) := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : HC.Normal :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeHCInDerived_normal ctx facts
  intro r s hconst hsLayerH₀C
  rw [internal.pTypeGaloisTranslationKernel_irreducibleCharacter r]
  exact (pTypeGalois_C_subgroupOf_le_H0C_subgroupOf ctx facts).trans
    (pTypeGalois_constituent_H0C_kernel
      ctx facts r s hconst hsLayerH₀C)

set_option maxHeartbeats 3000000

/-- If every character induced from the `H₀C'` kernel layer is reducible,
then the complement action kernel `C` is trivial. -/
theorem pTypeGalois_all_reducible_forces_C_bot
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : TypePGaloisConclusion (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    (∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
      ¬ IsIrreducibleCharacter M ℂ zeta) →
    C = ⊥ := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  change (∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
    ¬ IsIrreducibleCharacter M ℂ zeta) → C = ⊥
  intro hAllReducible
  apply eq_bot_iff.mpr
  by_contra hCne
  have hCne' : C ≠ ⊥ := by
    intro hC
    apply hCne
    exact hC.le
  obtain ⟨r, s, hconst, hCnon, hsReducible⟩ :=
    pTypeGalois_exists_reducible_witness_of_C_ne_bot
      ctx facts hGal hCne' hAllReducible
  have hsH₀C :=
    pTypeGalois_reducible_witness_mem_H0C ctx facts s hsReducible
  apply hCnon
  exact pTypeGalois_C_le_translationKernel_of_H0C_witness
    ctx facts r s hconst hsH₀C


end PTypeGaloisLocalFrobeniusInternal

end

end Submission.OddOrder.PF
