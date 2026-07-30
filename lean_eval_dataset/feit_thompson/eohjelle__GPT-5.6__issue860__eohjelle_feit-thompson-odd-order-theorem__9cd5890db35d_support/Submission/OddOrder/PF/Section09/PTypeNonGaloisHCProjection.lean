import Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore

/-!
# Peterfalvi Section 9: the non-Galois `HC` projection

This phase identifies the quotient of `HC = H C` by `H₀ C` with the
non-Galois chief factor `H / H₀`.  It then pulls the coordinate characters of
the chief factor back to `HC` and records the conjugation formulas needed by
the later `HU`-family construction.

The reusable interface lives in a module-specific internal namespace.  Proof
scaffolding for the quotient identification is kept private.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF.internal
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open PTypeNonGaloisCoordinateCoreInternal

universe u v w

local instance (priority := 10) pTypeHCProjectionFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisHCProjectionInternal

/-! ## The normal subgroups `H₀C` and `HC` -/

/-- Source `H₀C`, formed in the maximal-subgroup type. -/
def pTypeH0CInMaximal
    {Gamma : Type u} [Group Gamma]
    (M H₀ U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) : Subgroup M :=
  H₀.subgroupOf M ⊔
    (D.C.map U.subtype).subgroupOf M

/-- The canonical copy of `H₀C` inside `HC`. -/
def pTypeH0CInHC
    {Gamma : Type u} [Group Gamma]
    (M H H₀ U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    Subgroup (pTypeHCInMaximal M H U W₁ D) :=
  (pTypeH0CInMaximal M H₀ U W₁ D).subgroupOf
    (pTypeHCInMaximal M H U W₁ D)

/-- The lower extension `H₀C` lies in `HC`. -/
theorem pTypeH0CInMaximal_le_HC
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    pTypeH0CInMaximal M (Ptype_Fcore_kernel ctx) U W₁
        (Ptype_factor_action ctx facts) ≤
      pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts) := by
  apply sup_le
  · exact (Subgroup.subgroupOf_mono M
      (Ptype_Fcore_kernel_lt ctx).le).trans le_sup_left
  · exact le_sup_right

/-- Forming `H₀C` in `HU` agrees with restricting its copy in `M`. -/
theorem pTypeH0CInDerived_eq_subgroupOf
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    pTypeH0CInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U W₁ D =
      (pTypeH0CInMaximal M (Ptype_Fcore_kernel ctx) U W₁ D).subgroupOf HU := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hH₀der : Ptype_Fcore_kernel ctx ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hCder : D.C.map U.subtype ≤ derivedWithin M := by
    change Ptype_Fcompl_kernel ctx ≤ derivedWithin M
    exact (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hH₀HU : (Ptype_Fcore_kernel ctx).subgroupOf M ≤ HU :=
    fun _x hx ↦ hH₀der hx
  have hCHU : (D.C.map U.subtype).subgroupOf M ≤ HU :=
    fun _x hx ↦ hCder hx
  change
    ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU ⊔
        ((D.C.map U.subtype).subgroupOf M).subgroupOf HU =
      (((Ptype_Fcore_kernel ctx).subgroupOf M ⊔
        (D.C.map U.subtype).subgroupOf M).subgroupOf HU)
  rw [Subgroup.subgroupOf_sup hH₀HU hCHU]

/-- The literal `H₀U'` agrees with the normal F-core extension. -/
theorem pTypeH0DerivedComplementInDerived_eq_subgroupOf
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    pTypeH0DerivedComplementInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U =
      ((Ptype_Fcore_kernel ctx ⊔ derivedWithin U).subgroupOf M).subgroupOf HU := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀ := Ptype_Fcore_kernel ctx
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hH₀der : H₀ ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hUPrimeM : derivedWithin U ≤ M :=
    (Subgroup.map_subtype_le (_root_.commutator U)).trans hUM
  have hH₀M : H₀ ≤ M := hH₀der.trans hDerM
  have hH₀HU : H₀.subgroupOf M ≤ HU :=
    fun _x hx ↦ hH₀der hx
  have hUPrimeHU : (derivedWithin U).subgroupOf M ≤ HU := by
    exact Subgroup.subgroupOf_mono M
      ((Subgroup.map_subtype_le (_root_.commutator U)).trans hUder)
  change (H₀.subgroupOf M).subgroupOf HU ⊔
        (pTypeDerivedComplementInMaximal
          (U.subgroupOf M).subtype).subgroupOf HU =
      ((H₀ ⊔ derivedWithin U).subgroupOf M).subgroupOf HU
  rw [← pTypeDerivedComplementInMaximal_eq_subgroupOf hUM,
    pTypeDerivedComplementInMaximal_eq_derivedWithin_subgroupOf hUM,
    ← Subgroup.subgroupOf_sup hH₀HU hUPrimeHU,
    ← Subgroup.subgroupOf_sup hH₀M hUPrimeM]

/-- Normality of source `H₀U'` in `HU`. -/
instance pTypeH0DerivedComplementInDerived_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeH0DerivedComplementInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U).Normal := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  rw [pTypeH0DerivedComplementInDerived_eq_subgroupOf ctx]
  exact Subgroup.Normal.subgroupOf
    (Ptype_Fcore_extensions_normal ctx).H₀U'_normal.2 HU

/-- The canonical `H₀C` is normal in the maximal subgroup. -/
instance pTypeH0CInMaximal_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeH0CInMaximal M (Ptype_Fcore_kernel ctx) U W₁
      (Ptype_factor_action ctx facts)).Normal := by
  let D := Ptype_factor_action ctx facts
  let H₀ := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let K := pTypeH0CInMaximal M H₀ U W₁ D
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hCM : C ≤ M := (Ptype_Fcompl_kernel_le ctx).trans hUM
  have hDC : D.C.map U.subtype = C := rfl
  have hK : K = (H₀ ⊔ C).subgroupOf M := by
    change H₀.subgroupOf M ⊔
        (D.C.map U.subtype).subgroupOf M =
      (H₀ ⊔ C).subgroupOf M
    rw [hDC, ← Subgroup.subgroupOf_sup hH₀M hCM]
  change K.Normal
  rw [hK]
  exact (Ptype_Fcore_extensions_normal ctx).H₀C_normal.2

/-- Normality of `H₀C` persists after restricting it to `HC`. -/
instance pTypeH0CInHC_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
      U W₁ (Ptype_factor_action ctx facts)).Normal := by
  let D := Ptype_factor_action ctx facts
  let H₀ := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let K := pTypeH0CInMaximal M H₀ U W₁ D
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hCM : C ≤ M := (Ptype_Fcompl_kernel_le ctx).trans hUM
  have hDC : D.C.map U.subtype = C := rfl
  have hK : K = (H₀ ⊔ C).subgroupOf M := by
    change H₀.subgroupOf M ⊔
        (D.C.map U.subtype).subgroupOf M =
      (H₀ ⊔ C).subgroupOf M
    rw [hDC, ← Subgroup.subgroupOf_sup hH₀M hCM]
  have hKnormal : K.Normal := by
    rw [hK]
    exact (Ptype_Fcore_extensions_normal ctx).H₀C_normal.2
  exact Subgroup.Normal.subgroupOf hKnormal HC

/-- The canonical `HC = H C` is normal in the maximal subgroup. -/
instance pTypeNonGaloisHCInMaximal_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)).Normal := by
  let D := Ptype_factor_action ctx facts
  let C := Ptype_Fcompl_kernel ctx
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  have hCM : C ≤ M := (Ptype_Fcompl_kernel_le ctx).trans hUM
  have hDC : D.C.map U.subtype = C := rfl
  have hHC : HC = (Fitting_core M ⊔ C).subgroupOf M := by
    change (Fitting_core M).subgroupOf M ⊔
        (D.C.map U.subtype).subgroupOf M =
      (Fitting_core M ⊔ C).subgroupOf M
    rw [hDC, ← Subgroup.subgroupOf_sup (Fcore_sub M) hCM]
  change HC.Normal
  rw [hHC]
  exact (Ptype_Fcore_extensions_normal ctx).HC_normal.2

/-- The canonical subgroup `HC` lies in `HU = M'`. -/
theorem pTypeNonGaloisHCInMaximal_le_HU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts) ≤
      pTypeHUInMaximal M (derivedWithin M) := by
  have hinner : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M) :=
    ctx.typeP.2.1.2.2.2
  apply sup_le
  · exact Subgroup.subgroupOf_mono M hinner.1
  · exact Subgroup.subgroupOf_mono M
      ((Subgroup.map_subtype_le
        (Ptype_factor_action ctx facts).C).trans hinner.2.1)

/-- Normality persists after restricting `HC` to `HU = M'`. -/
instance pTypeNonGaloisHCInHU_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    ((pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))).Normal :=
  Subgroup.Normal.subgroupOf
    (pTypeNonGaloisHCInMaximal_normal ctx facts)
    (pTypeHUInMaximal M (derivedWithin M))

/-! ## The quotient `HC / H₀C` -/

/-- Include the F-core into `HC`. -/
noncomputable def pTypeFCoreToHC
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    Fitting_core M →*
      pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts) :=
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let FM : Subgroup M := (Fitting_core M).subgroupOf M
  let eFM : FM ≃* Fitting_core M :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
  (Subgroup.inclusion (show FM ≤ HC from le_sup_left)).comp
    eFM.symm.toMonoidHom

@[simp]
theorem pTypeFCoreToHC_coe
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) (h : Fitting_core M) :
    (((pTypeFCoreToHC ctx facts h :
        pTypeHCInMaximal M (Fitting_core M) U W₁
          (Ptype_factor_action ctx facts)) : M) : Gamma) = h :=
  rfl

/-- The F-core map followed by quotienting `HC` by `H₀C`. -/
private noncomputable def pTypeFCoreToHCQuotient
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let H₀C := pTypeH0CInHC M (Fitting_core M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    Fitting_core M →* HC ⧸ H₀C := by
  let D := Ptype_factor_action ctx facts
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let H₀C := pTypeH0CInHC M (Fitting_core M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  exact (QuotientGroup.mk' H₀C).comp (pTypeFCoreToHC ctx facts)

/-- The kernel of the F-core-to-`HC/H₀C` map is exactly `H₀`. -/
private theorem pTypeFCoreToHCQuotient_ker
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeFCoreToHCQuotient ctx facts).ker =
      (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M) := by
  let D := Ptype_factor_action ctx facts
  let H₀ := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let H₀C := pTypeH0CInHC M (Fitting_core M) H₀ U W₁ D
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hCM : C ≤ M := (Ptype_Fcompl_kernel_le ctx).trans hUM
  have hDC : D.C.map U.subtype = C := rfl
  ext h
  change QuotientGroup.mk' H₀C (pTypeFCoreToHC ctx facts h) = 1 ↔ _
  constructor
  · intro hh
    have hhmem : pTypeFCoreToHC ctx facts h ∈ H₀C :=
      (QuotientGroup.eq_one_iff
        (N := H₀C) (pTypeFCoreToHC ctx facts h)).mp hh
    have hh' : (h : Gamma) ∈ H₀ ⊔ C := by
      change ((pTypeFCoreToHC ctx facts h : HC) : M) ∈
        pTypeH0CInMaximal M H₀ U W₁ D at hhmem
      rw [pTypeH0CInMaximal, hDC,
        ← Subgroup.subgroupOf_sup hH₀M hCM] at hhmem
      exact hhmem
    have hhInf : (h : Gamma) ∈ (H₀ ⊔ C) ⊓ Fitting_core M :=
      ⟨hh', h.property⟩
    rw [pTypeFcoreKernel_sup_complKernel_inf_Fcore ctx] at hhInf
    exact hhInf
  · intro hh
    apply (QuotientGroup.eq_one_iff
      (N := H₀C) (pTypeFCoreToHC ctx facts h)).mpr
    change ((pTypeFCoreToHC ctx facts h : HC) : M) ∈
      pTypeH0CInMaximal M H₀ U W₁ D
    rw [pTypeH0CInMaximal, hDC]
    have hhM : ((pTypeFCoreToHC ctx facts h : HC) : M) ∈
        H₀.subgroupOf M := hh
    exact (le_sup_left :
      (H₀.subgroupOf M) ≤ (H₀.subgroupOf M) ⊔ C.subgroupOf M) hhM

/-- Every coset of `HC/H₀C` has a representative in the F-core. -/
private theorem pTypeFCoreToHCQuotient_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    Function.Surjective (pTypeFCoreToHCQuotient ctx facts) := by
  let D := Ptype_factor_action ctx facts
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let H₀C := pTypeH0CInHC M (Fitting_core M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H₀C z
  let FM : Subgroup M := (Fitting_core M).subgroupOf M
  let CM : Subgroup M := (D.C.map U.subtype).subgroupOf M
  letI : FM.Normal := Fcore_normal M
  have hx : (x : M) ∈ FM ⊔ CM := x.property
  obtain ⟨f, hf, c, hc, hfc⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hx
  let h : Fitting_core M := ⟨((f : M) : Gamma), hf⟩
  let fHC : HC := ⟨f, by
    change f ∈ FM ⊔ CM
    exact (le_sup_left : FM ≤ FM ⊔ CM) hf⟩
  let cHC : HC := ⟨c, by
    change c ∈ FM ⊔ CM
    exact (le_sup_right : CM ≤ FM ⊔ CM) hc⟩
  have hxfc : fHC * cHC = x := by
    apply Subtype.ext
    exact hfc
  have hcK : cHC ∈ H₀C := by
    change c ∈ (Ptype_Fcore_kernel ctx).subgroupOf M ⊔ CM
    exact (le_sup_right : CM ≤
      (Ptype_Fcore_kernel ctx).subgroupOf M ⊔ CM) hc
  have hcOne : QuotientGroup.mk' H₀C cHC = 1 :=
    (QuotientGroup.eq_one_iff cHC).mpr hcK
  refine ⟨h, ?_⟩
  change QuotientGroup.mk' H₀C (pTypeFCoreToHC ctx facts h) =
    QuotientGroup.mk' H₀C x
  have hfEq : pTypeFCoreToHC ctx facts h = fHC := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hfEq, ← hxfc, map_mul, hcOne, mul_one]

/-- The canonical quotient equivalence `H/H₀ ≃ HC/H₀C`. -/
noncomputable def pTypeFCoreFactorEquivHCQuotient
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let H₀C := pTypeH0CInHC M (Fitting_core M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    ptypeFCoreFactor ctx ≃* HC ⧸ H₀C := by
  let f := pTypeFCoreToHCQuotient ctx facts
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (pTypeFCoreToHCQuotient_ker ctx facts).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f
        (pTypeFCoreToHCQuotient_surjective ctx facts))

/-- The quotient equivalence agrees with the literal quotient maps. -/
@[simp]
theorem pTypeFCoreFactorEquivHCQuotient_mk
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) (h : Fitting_core M) :
    pTypeFCoreFactorEquivHCQuotient ctx facts
        (QuotientGroup.mk'
          ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) h) =
      QuotientGroup.mk'
        (pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
          U W₁ (Ptype_factor_action ctx facts))
        (pTypeFCoreToHC ctx facts h) := by
  rfl

/-! ## Projection and character extension -/

/-- Kill `H₀C` in `HC`, then identify the quotient with `H/H₀`. -/
noncomputable def pTypeHCProjection
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts) →*
      ptypeFCoreFactor ctx :=
  (pTypeFCoreFactorEquivHCQuotient ctx facts).symm.toMonoidHom.comp
    (QuotientGroup.mk'
      (pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
        U W₁ (Ptype_factor_action ctx facts)))

/-- The canonical `HC → H/H₀` projection is onto. -/
theorem pTypeHCProjection_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    Function.Surjective (pTypeHCProjection ctx facts) :=
  (pTypeFCoreFactorEquivHCQuotient ctx facts).symm.surjective.comp
    (QuotientGroup.mk'_surjective
      (pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
        U W₁ (Ptype_factor_action ctx facts)))

/-- The projection kernel is the literal subgroup `H₀C` of `HC`. -/
theorem pTypeHCProjection_ker
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeHCProjection ctx facts).ker =
      pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
        U W₁ (Ptype_factor_action ctx facts) := by
  rw [pTypeHCProjection,
    MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk'
        (pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
          U W₁ (Ptype_factor_action ctx facts)))
      (pTypeFCoreFactorEquivHCQuotient ctx facts).symm.toMonoidHom
      (pTypeFCoreFactorEquivHCQuotient ctx facts).symm.injective,
    QuotientGroup.ker_mk']

/-- On the F-core, the `HC` projection is the original quotient map. -/
@[simp]
theorem pTypeHCProjection_apply_Fcore
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) (h : Fitting_core M) :
    pTypeHCProjection ctx facts (pTypeFCoreToHC ctx facts h) =
      QuotientGroup.mk'
        ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) h := by
  rw [pTypeHCProjection, MonoidHom.comp_apply,
    ← pTypeFCoreFactorEquivHCQuotient_mk ctx facts h]
  change (pTypeFCoreFactorEquivHCQuotient ctx facts).symm
      ((pTypeFCoreFactorEquivHCQuotient ctx facts)
        (QuotientGroup.mk'
          ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) h)) = _
  exact (pTypeFCoreFactorEquivHCQuotient ctx facts).symm_apply_apply _

/-- Irreducibility is preserved by pullback along a surjective homomorphism. -/
private theorem pTypeRepresentationIrreducibleCompSurjective
    {A B : Type u} {k : Type v} {V : Type w}
    [Group A] [Group B] [Field k]
    [AddCommGroup V] [Module k V]
    (rho : Representation k B V) [Representation.IsIrreducible rho]
    (f : A →* B) (hf : Function.Surjective f) :
    Representation.IsIrreducible (rho.comp f) := by
  let sigma : Representation k A V := rho.comp f
  have hbot_ne_top : (⊥ : Subrepresentation sigma) ≠ ⊤ := by
    intro h
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation rho)
    apply SetLike.ext
    intro v
    have hv := congrArg (fun U : Subrepresentation sigma ↦ v ∈ U) h
    change (v ∈ (⊥ : Submodule k V)) =
      (v ∈ (⊤ : Submodule k V)) at hv
    exact iff_of_eq hv
  letI : Nontrivial (Subrepresentation sigma) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let U' : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule b v hv := by
        obtain ⟨a, rfl⟩ := hf b
        exact U.apply_mem_toSubmodule a hv }
  have hU' : U' ≠ ⊥ := by
    intro hbot
    apply hU
    apply SetLike.ext
    intro v
    have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) hbot
    change (v ∈ U.toSubmodule) =
      (v ∈ (⊥ : Submodule k V)) at hv
    exact iff_of_eq hv
  have htop : U' = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  apply SetLike.ext
  intro v
  have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) htop
  change (v ∈ U.toSubmodule) =
    (v ∈ (⊤ : Submodule k V)) at hv
  exact iff_of_eq hv

/-- Inflate an irreducible character along a surjective homomorphism. -/
private noncomputable def pTypeIrreducibleComapSurjective
    {A B : Type u} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ.comp f
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible rho :=
    pTypeRepresentationIrreducibleCompSurjective
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem pTypeIrreducibleComapSurjective_apply
    {A B : Type u} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeIrreducibleComapSurjective f hf chi a = chi (f a) := by
  simp only [pTypeIrreducibleComapSurjective,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

/-- Pull a chief-factor irreducible character back to `HC`. -/
noncomputable def pTypeExtendFCoreFactorCharacterToHC
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ) :
    IrreducibleCharacter
      (pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)) ℂ :=
  pTypeIrreducibleComapSurjective
    (pTypeHCProjection ctx facts)
    (pTypeHCProjection_surjective ctx facts) theta

@[simp]
theorem pTypeExtendFCoreFactorCharacterToHC_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ)
    (x : pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)) :
    pTypeExtendFCoreFactorCharacterToHC ctx facts theta x =
      theta (pTypeHCProjection ctx facts x) :=
  pTypeIrreducibleComapSurjective_apply
    (pTypeHCProjection ctx facts)
    (pTypeHCProjection_surjective ctx facts) theta x

/-- Every extended factor character kills `H₀C`. -/
theorem pTypeH0CInHC_le_extension_translationKernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ) :
    pTypeH0CInHC M (Fitting_core M) (Ptype_Fcore_kernel ctx)
        U W₁ (Ptype_factor_action ctx facts) ≤
      ClassFunction.translationKernel
        (pTypeExtendFCoreFactorCharacterToHC ctx facts theta :
          ClassFunction
            (pTypeHCInMaximal M (Fitting_core M) U W₁
              (Ptype_factor_action ctx facts)) ℂ) := by
  rw [← pTypeHCProjection_ker ctx facts]
  intro x hx
  rw [ClassFunction.mem_translationKernel_iff]
  intro y
  rw [pTypeExtendFCoreFactorCharacterToHC_apply,
    pTypeExtendFCoreFactorCharacterToHC_apply, map_mul,
    MonoidHom.mem_ker.mp hx, one_mul]

/-- Pullback to `HC` preserves the irreducible degree. -/
theorem pTypeExtendFCoreFactorCharacterToHC_degree
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ) :
    pTypeIrreducibleDegree
        (pTypeExtendFCoreFactorCharacterToHC ctx facts theta) =
      pTypeIrreducibleDegree theta := by
  apply Nat.cast_injective (R := ℂ)
  unfold pTypeIrreducibleDegree
  rw [← IrreducibleCharacter.apply_one_eq_finrank,
    ← IrreducibleCharacter.apply_one_eq_finrank,
    pTypeExtendFCoreFactorCharacterToHC_apply, map_one]

/-- Restriction back to the F-core is the original quotient inflation. -/
@[simp]
theorem pTypeExtendFCoreFactorCharacterToHC_apply_Fcore
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ)
    (h : Fitting_core M) :
    pTypeExtendFCoreFactorCharacterToHC ctx facts theta
        (pTypeFCoreToHC ctx facts h) =
      theta
        (QuotientGroup.mk'
          ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) h) := by
  rw [pTypeExtendFCoreFactorCharacterToHC_apply,
    pTypeHCProjection_apply_Fcore]

/-! ## Coordinate characters on `HC` and its copy in `HU` -/

/-- The linear `HC` character attached to a coordinate family on the
non-Galois direct-product decomposition. -/
noncomputable def pTypeNonGaloisHCCoordinateCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    (W₁ → MulChar data.H₁ ℂ) →
      IrreducibleCharacter
        (pTypeHCInMaximal M (Fitting_core M) U W₁ D) ℂ := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda ↦ ?_
  exact pTypeExtendFCoreFactorCharacterToHC ctx facts
    (pTypeNonGaloisCoordinateCharacter D data lambda)

/-- Evaluation of an `HC` coordinate character factors through the canonical
projection. -/
@[simp]
theorem pTypeNonGaloisHCCoordinateCharacter_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ) (x : HC),
      pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois lambda x =
        pTypeNonGaloisCoordinateCharacter D data lambda
          (pTypeHCProjection ctx facts x) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda x ↦ ?_
  exact pTypeExtendFCoreFactorCharacterToHC_apply ctx facts _ x

/-- Every coordinate-family extension to `HC` is linear. -/
theorem pTypeNonGaloisHCCoordinateCharacter_linear
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ lambda : W₁ → MulChar data.H₁ ℂ,
      pTypeIsLinearCharacter
        (pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois lambda) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda ↦ ?_
  rw [pTypeIsLinearCharacter,
    pTypeNonGaloisHCCoordinateCharacter,
    pTypeExtendFCoreFactorCharacterToHC_degree]
  exact pTypeNonGaloisCoordinateCharacter_degree D data lambda

/-- On the F-core, the extended coordinate character is the inflated
chief-factor coordinate character. -/
@[simp]
theorem pTypeNonGaloisHCCoordinateCharacter_apply_Fcore
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ) (h : Fitting_core M),
      pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois lambda
          (pTypeFCoreToHC ctx facts h) =
        pTypeNonGaloisCoordinateCharacter D data lambda
          (QuotientGroup.mk'
            ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) h) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda h ↦ ?_
  exact pTypeExtendFCoreFactorCharacterToHC_apply_Fcore
    ctx facts _ h

/-- Transport an `HC` coordinate character to the nested copy `HC ≤ HU`. -/
noncomputable def pTypeNonGaloisHCCoordinateCharacterInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    (W₁ → MulChar data.H₁ ℂ) →
      IrreducibleCharacter
        ((pTypeHCInMaximal M (Fitting_core M) U W₁ D).subgroupOf
          (pTypeHUInMaximal M (derivedWithin M))) ℂ := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda ↦ ?_
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let e : HC.subgroupOf HU ≃* HC :=
    Subgroup.subgroupOfEquivOfLe
      (pTypeNonGaloisHCInMaximal_le_HU ctx facts)
  exact pTypeIrreducibleComapSurjective e.toMonoidHom e.surjective
    (pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois lambda)

@[simp]
theorem pTypeNonGaloisHCCoordinateCharacterInHU_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ) (x : HC.subgroupOf HU),
      pTypeNonGaloisHCCoordinateCharacterInHU
          ctx facts not_Galois lambda x =
        pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois lambda
            (Subgroup.subgroupOfEquivOfLe
              (pTypeNonGaloisHCInMaximal_le_HU ctx facts) x) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda x ↦ ?_
  simp only [pTypeNonGaloisHCCoordinateCharacterInHU,
    pTypeIrreducibleComapSurjective_apply]
  rfl

/-! ## Equivariance of the projection -/

/-- Conjugating an F-core representative by `u : U` and then projecting
is the canonical `U`-action on `H/H₀`. -/
theorem pTypeHCProjection_conj_Fcore
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (u : U) (h : Fitting_core M) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let uM : M := ⟨(u : Gamma),
      (ctx.typeP.2.1.2.2.2.2.1.trans
        (Subgroup.map_subtype_le (_root_.commutator M))) u.property⟩
    pTypeHCProjection ctx facts
        (MulAut.conjNormal uM (pTypeFCoreToHC ctx facts h)) =
      D.U_action u (pTypeHCProjection ctx facts
        (pTypeFCoreToHC ctx facts h)) := by
  let D := Ptype_factor_action ctx facts
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  let uM : M := ⟨(u : Gamma), hUM u.property⟩
  have hUnormF : U ≤
      Subgroup.normalizer (Fitting_core M : Set Gamma) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Fcore_sub M)).mp (Fcore_normal M))
  let hconj : Fitting_core M :=
    ⟨(u : Gamma) * (h : Gamma) * (u : Gamma)⁻¹,
      (hUnormF u.property h).mp h.property⟩
  have hconjHC :
      MulAut.conjNormal uM (pTypeFCoreToHC ctx facts h) =
        pTypeFCoreToHC ctx facts hconj := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  change pTypeHCProjection ctx facts
      (MulAut.conjNormal uM (pTypeFCoreToHC ctx facts h)) =
    D.U_action u
      (pTypeHCProjection ctx facts (pTypeFCoreToHC ctx facts h))
  rw [hconjHC, pTypeHCProjection_apply_Fcore,
    pTypeHCProjection_apply_Fcore,
    Ptype_factor_action_U_action, ptypeFCoreAction,
    subgroupConjugationFactorHom_apply_mk]

/-- Conjugating an F-core representative by `w : W₁` and then projecting
is the canonical `W₁`-action on `H/H₀`. -/
theorem pTypeHCProjection_conj_W₁_Fcore
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (w : W₁) (h : Fitting_core M) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let wM : M := ⟨(w : Gamma), ctx.typeP.1.2.1.1 w.property⟩
    pTypeHCProjection ctx facts
        (MulAut.conjNormal wM (pTypeFCoreToHC ctx facts h)) =
      D.W₁_action w (pTypeHCProjection ctx facts
        (pTypeFCoreToHC ctx facts h)) := by
  let D := Ptype_factor_action ctx facts
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : Gamma), hW₁M w.property⟩
  have hW₁normF : W₁ ≤
      Subgroup.normalizer (Fitting_core M : Set Gamma) :=
    hW₁M.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Fcore_sub M)).mp (Fcore_normal M))
  let hconj : Fitting_core M :=
    ⟨(w : Gamma) * (h : Gamma) * (w : Gamma)⁻¹,
      (hW₁normF w.property h).mp h.property⟩
  have hconjHC :
      MulAut.conjNormal wM (pTypeFCoreToHC ctx facts h) =
        pTypeFCoreToHC ctx facts hconj := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  change pTypeHCProjection ctx facts
      (MulAut.conjNormal wM (pTypeFCoreToHC ctx facts h)) =
    D.W₁_action w
      (pTypeHCProjection ctx facts (pTypeFCoreToHC ctx facts h))
  rw [hconjHC, pTypeHCProjection_apply_Fcore,
    pTypeHCProjection_apply_Fcore,
    Ptype_factor_action_W₁_action, ptypeW₁FactorAction,
    subgroupConjugationFactorHom_apply_mk]

/-- The canonical projection is equivariant for conjugation by `W₁` on all
of `HC`. -/
theorem pTypeHCProjection_conj_W₁
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (w : W₁)
    (x : pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let wM : M := ⟨(w : Gamma), ctx.typeP.1.2.1.1 w.property⟩
    pTypeHCProjection ctx facts (MulAut.conjNormal wM x) =
      D.W₁_action w (pTypeHCProjection ctx facts x) := by
  classical
  let D := Ptype_factor_action ctx facts
  let H₀ := Ptype_Fcore_kernel ctx
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let FM : Subgroup M := (Fitting_core M).subgroupOf M
  let CM : Subgroup M := (D.C.map U.subtype).subgroupOf M
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : Gamma), hW₁M w.property⟩
  letI : FM.Normal := Fcore_normal M
  have hx : (x : M) ∈ FM ⊔ CM := x.property
  obtain ⟨f, hf, c, hc, hfc⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hx
  let h : Fitting_core M := ⟨((f : M) : Gamma), hf⟩
  let fHC : HC := ⟨f, by
    change f ∈ FM ⊔ CM
    exact (le_sup_left : FM ≤ FM ⊔ CM) hf⟩
  let cHC : HC := ⟨c, by
    change c ∈ FM ⊔ CM
    exact (le_sup_right : CM ≤ FM ⊔ CM) hc⟩
  have hxFC : fHC * cHC = x := by
    apply Subtype.ext
    exact hfc
  have hfEq : pTypeFCoreToHC ctx facts h = fHC := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hcH₀CM : (cHC : M) ∈
      pTypeH0CInMaximal M H₀ U W₁ D := by
    change c ∈ H₀.subgroupOf M ⊔ CM
    exact (le_sup_right : CM ≤ H₀.subgroupOf M ⊔ CM) hc
  have hcKer : cHC ∈ (pTypeHCProjection ctx facts).ker := by
    rw [pTypeHCProjection_ker]
    exact hcH₀CM
  have hconjCKer : MulAut.conjNormal wM cHC ∈
      (pTypeHCProjection ctx facts).ker := by
    rw [pTypeHCProjection_ker]
    change wM * (cHC : M) * wM⁻¹ ∈
      pTypeH0CInMaximal M H₀ U W₁ D
    exact (pTypeH0CInMaximal_normal ctx facts).conj_mem
      (cHC : M) hcH₀CM wM
  have hcProj : pTypeHCProjection ctx facts cHC = 1 :=
    MonoidHom.mem_ker.mp hcKer
  have hconjCProj : pTypeHCProjection ctx facts
      (MulAut.conjNormal wM cHC) = 1 :=
    MonoidHom.mem_ker.mp hconjCKer
  calc
    pTypeHCProjection ctx facts (MulAut.conjNormal wM x) =
        pTypeHCProjection ctx facts
          (MulAut.conjNormal wM (fHC * cHC)) := by rw [hxFC]
    _ = pTypeHCProjection ctx facts (MulAut.conjNormal wM fHC) *
          pTypeHCProjection ctx facts (MulAut.conjNormal wM cHC) := by
      rw [map_mul, map_mul]
    _ = pTypeHCProjection ctx facts (MulAut.conjNormal wM fHC) := by
      rw [hconjCProj, mul_one]
    _ = D.W₁_action w (pTypeHCProjection ctx facts fHC) := by
      rw [← hfEq]
      exact pTypeHCProjection_conj_W₁_Fcore ctx facts w h
    _ = D.W₁_action w
          (pTypeHCProjection ctx facts fHC *
            pTypeHCProjection ctx facts cHC) := by
      rw [hcProj, mul_one]
    _ = D.W₁_action w
          (pTypeHCProjection ctx facts (fHC * cHC)) := by
      exact congrArg (D.W₁_action w)
        ((pTypeHCProjection ctx facts).map_mul fHC cHC).symm
    _ = D.W₁_action w (pTypeHCProjection ctx facts x) := by
      rw [hxFC]

/-- The canonical projection is equivariant for conjugation by `U` on all
of `HC`. -/
theorem pTypeHCProjection_conj_U
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (u : U)
    (x : pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let uM : M := ⟨(u : Gamma),
      (ctx.typeP.2.1.2.2.2.2.1.trans
        (Subgroup.map_subtype_le (_root_.commutator M))) u.property⟩
    pTypeHCProjection ctx facts (MulAut.conjNormal uM x) =
      D.U_action u (pTypeHCProjection ctx facts x) := by
  classical
  let D := Ptype_factor_action ctx facts
  let H₀ := Ptype_Fcore_kernel ctx
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let FM : Subgroup M := (Fitting_core M).subgroupOf M
  let CM : Subgroup M := (D.C.map U.subtype).subgroupOf M
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  let uM : M := ⟨(u : Gamma), hUM u.property⟩
  letI : FM.Normal := Fcore_normal M
  have hx : (x : M) ∈ FM ⊔ CM := x.property
  obtain ⟨f, hf, c, hc, hfc⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hx
  let h : Fitting_core M := ⟨((f : M) : Gamma), hf⟩
  let fHC : HC := ⟨f, by
    change f ∈ FM ⊔ CM
    exact (le_sup_left : FM ≤ FM ⊔ CM) hf⟩
  let cHC : HC := ⟨c, by
    change c ∈ FM ⊔ CM
    exact (le_sup_right : CM ≤ FM ⊔ CM) hc⟩
  have hxFC : fHC * cHC = x := by
    apply Subtype.ext
    exact hfc
  have hfEq : pTypeFCoreToHC ctx facts h = fHC := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hcH₀CM : (cHC : M) ∈
      pTypeH0CInMaximal M H₀ U W₁ D := by
    change c ∈ H₀.subgroupOf M ⊔ CM
    exact (le_sup_right : CM ≤ H₀.subgroupOf M ⊔ CM) hc
  have hcKer : cHC ∈ (pTypeHCProjection ctx facts).ker := by
    rw [pTypeHCProjection_ker]
    exact hcH₀CM
  have hconjCKer : MulAut.conjNormal uM cHC ∈
      (pTypeHCProjection ctx facts).ker := by
    rw [pTypeHCProjection_ker]
    change uM * (cHC : M) * uM⁻¹ ∈
      pTypeH0CInMaximal M H₀ U W₁ D
    exact (pTypeH0CInMaximal_normal ctx facts).conj_mem
      (cHC : M) hcH₀CM uM
  have hcProj : pTypeHCProjection ctx facts cHC = 1 :=
    MonoidHom.mem_ker.mp hcKer
  have hconjCProj : pTypeHCProjection ctx facts
      (MulAut.conjNormal uM cHC) = 1 :=
    MonoidHom.mem_ker.mp hconjCKer
  calc
    pTypeHCProjection ctx facts (MulAut.conjNormal uM x) =
        pTypeHCProjection ctx facts
          (MulAut.conjNormal uM (fHC * cHC)) := by rw [hxFC]
    _ = pTypeHCProjection ctx facts (MulAut.conjNormal uM fHC) *
          pTypeHCProjection ctx facts (MulAut.conjNormal uM cHC) := by
      rw [map_mul, map_mul]
    _ = pTypeHCProjection ctx facts (MulAut.conjNormal uM fHC) := by
      rw [hconjCProj, mul_one]
    _ = D.U_action u (pTypeHCProjection ctx facts fHC) := by
      rw [← hfEq]
      exact pTypeHCProjection_conj_Fcore ctx facts u h
    _ = D.U_action u
          (pTypeHCProjection ctx facts fHC *
            pTypeHCProjection ctx facts cHC) := by
      rw [hcProj, mul_one]
    _ = D.U_action u
          (pTypeHCProjection ctx facts (fHC * cHC)) := by
      exact congrArg (D.U_action u)
        ((pTypeHCProjection ctx facts).map_mul fHC cHC).symm
    _ = D.U_action u (pTypeHCProjection ctx facts x) := by
      rw [hxFC]

/-! ## Conjugation of coordinate characters -/

/-- Normal conjugation of an `HC` coordinate character by `u : U` is the
coordinatewise translate of its family. -/
theorem pTypeNonGaloisHCCoordinateCharacter_normalConjugate_U
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ) (u : U),
      let uM : M := ⟨(u : Gamma),
        (ctx.typeP.2.1.2.2.2.2.1.trans
          (Subgroup.map_subtype_le (_root_.commutator M))) u.property⟩
      ClassFunction.normalConjugate HC uM
          (pTypeNonGaloisHCCoordinateCharacter
            ctx facts not_Galois lambda : ClassFunction HC ℂ) =
        (pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois
          (pTypeNonGaloisUTranslateCoordinateFamily
            D data u⁻¹ lambda) : ClassFunction HC ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda u ↦ ?_
  dsimp only
  have hUM : U ≤ M := ctx.typeP.2.1.2.2.2.2.1.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  let uM : M := ⟨(u : Gamma), hUM u.property⟩
  let uInvM : M := ⟨(u⁻¹ : Gamma), hUM u⁻¹.property⟩
  ext x
  rw [ClassFunction.normalConjugate_apply]
  have harg : (MulAut.conjNormal uM).symm x =
      MulAut.conjNormal uInvM x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [pTypeNonGaloisHCCoordinateCharacter_apply,
    pTypeNonGaloisHCCoordinateCharacter_apply, harg]
  have hproj : pTypeHCProjection ctx facts
      (MulAut.conjNormal uInvM x) =
      D.U_action u⁻¹ (pTypeHCProjection ctx facts x) := by
    dsimp only [uInvM]
    exact pTypeHCProjection_conj_U ctx facts u⁻¹ x
  rw [hproj]
  exact (pTypeNonGaloisCoordinateCharacter_U_translate
    D data u⁻¹ lambda (pTypeHCProjection ctx facts x)).symm

/-- The same conjugation formula on the nested copy `HC ≤ HU`. -/
theorem pTypeNonGaloisHCCoordinateCharacterInHU_normalConjugate_U
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let HCN := HC.subgroupOf HU
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (v : (U.subgroupOf M).subgroupOf HU),
      let u : U := ⟨((v : HU) : M), v.property⟩
      ClassFunction.normalConjugate HCN (v : HU)
          (pTypeNonGaloisHCCoordinateCharacterInHU
            ctx facts not_Galois lambda : ClassFunction HCN ℂ) =
        (pTypeNonGaloisHCCoordinateCharacterInHU ctx facts not_Galois
          (pTypeNonGaloisUTranslateCoordinateFamily
            D data u⁻¹ lambda) : ClassFunction HCN ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  refine fun lambda v ↦ ?_
  dsimp only
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe
    (pTypeNonGaloisHCInMaximal_le_HU ctx facts)
  let u : U := ⟨((v : HU) : M), v.property⟩
  have hUM : U ≤ M := ctx.typeP.2.1.2.2.2.2.1.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  let uM : M := ⟨(u : Gamma), hUM u.property⟩
  ext x
  rw [ClassFunction.normalConjugate_apply]
  have harg : eHC ((MulAut.conjNormal (v : HU)).symm x) =
      (MulAut.conjNormal uM).symm (eHC x) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
    pTypeNonGaloisHCCoordinateCharacterInHU_apply, harg]
  have hvalue := congrArg
    (fun f : ClassFunction HC ℂ ↦ f (eHC x))
    (pTypeNonGaloisHCCoordinateCharacter_normalConjugate_U
      ctx facts not_Galois lambda u)
  rw [ClassFunction.normalConjugate_apply] at hvalue
  exact hvalue

end PTypeNonGaloisHCProjectionInternal

end

end Submission.OddOrder.PF
