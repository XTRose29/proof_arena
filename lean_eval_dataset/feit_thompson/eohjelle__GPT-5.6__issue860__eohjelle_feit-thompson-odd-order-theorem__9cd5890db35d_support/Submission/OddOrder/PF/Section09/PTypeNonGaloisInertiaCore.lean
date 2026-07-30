import Submission.OddOrder.PF.Section09.PTypeNonGaloisSelectedCoordinate

/-!
# Peterfalvi Section 9: the selected non-Galois inertia core

This module inflates the selected coordinate to the nested F-core, compares
the nested and ambient character models, and computes their exact inertia
subgroups.  The extension and quotient-twist constructions live in the
downstream `PTypeNonGaloisInertiaExtensions` phase.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical IsMulCommutative

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15

universe u

local instance (priority := 10) pTypeInertiaFactorFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisInertiaCoreInternal

open PTypeNonGaloisSelectedCoordinateInternal

local instance pTypeNonGaloisFCoreFactor_commutative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsMulCommutative (ptypeFCoreFactor ctx) :=
  (ptypeFCoreFactor_elementary ctx).commutative

/-! ## The nested F-core quotient -/

instance pTypeNonGaloisHInHU_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M : Subgroup Gamma} :
    (((Fitting_core M).subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))).Normal :=
  Subgroup.Normal.subgroupOf (Fcore_normal M)
    (pTypeHUInMaximal M (derivedWithin M))

/-- Forget the two nested subgroup layers without changing the underlying
ambient element. -/
noncomputable def pTypeNonGaloisHToFCoreEquiv
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    H ≃* Fitting_core M := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  exact
    { toFun := fun h ↦ ⟨(((h : H) : HU) : M), h.property⟩
      invFun := fun h ↦
        ⟨⟨⟨(h : Gamma), Fcore_sub M h.property⟩,
            hHder h.property⟩, h.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The quotient map from the nested F-core to the factor `H/H₀`. -/
noncomputable def pTypeNonGaloisHToFactorProjection
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    H →* ptypeFCoreFactor ctx := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let eH : H ≃* Fitting_core M := pTypeNonGaloisHToFCoreEquiv ctx
  exact (QuotientGroup.mk'
    ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))).comp
      eH.toMonoidHom

theorem pTypeNonGaloisHToFactorProjection_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Function.Surjective (pTypeNonGaloisHToFactorProjection ctx) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let eH : H ≃* Fitting_core M := pTypeNonGaloisHToFCoreEquiv ctx
  exact (QuotientGroup.mk'_surjective
    ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))).comp
      eH.surjective

theorem pTypeNonGaloisHToFactorProjection_ker
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    (pTypeNonGaloisHToFactorProjection ctx).ker = H₀.subgroupOf H := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  let eH : H ≃* Fitting_core M := pTypeNonGaloisHToFCoreEquiv ctx
  ext h
  rw [MonoidHom.mem_ker]
  change QuotientGroup.mk'
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))
        (eH h) = 1 ↔ h ∈ H₀.subgroupOf H
  constructor
  · intro hz
    have hz' : eH h ∈
        (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M) :=
      (QuotientGroup.eq_one_iff (eH h)).mp hz
    exact hz'
  · intro hh
    apply (QuotientGroup.eq_one_iff (eH h)).mpr
    exact hh

theorem pTypeNonGaloisHToFactorProjection_conj_U
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (v : (U.subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M)))
    (h : ((Fitting_core M).subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let u : U := ⟨((v : HU) : M), by
      change (((v : HU) : M) : Gamma) ∈ U
      exact v.property⟩
    pTypeNonGaloisHToFactorProjection ctx
        (MulAut.conjNormal (v : HU) h) =
      D.U_action u (pTypeNonGaloisHToFactorProjection ctx h) := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  have hUnormF : U ≤ Subgroup.normalizer (Fitting_core M : Set Gamma) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  let eH : H ≃* Fitting_core M := pTypeNonGaloisHToFCoreEquiv ctx
  let u : U := ⟨((v : HU) : M), by
    change (((v : HU) : M) : Gamma) ∈ U
    exact v.property⟩
  let hconj : Fitting_core M :=
    ⟨(u : Gamma) * (eH h : Gamma) * (u : Gamma)⁻¹,
      (hUnormF u.property (eH h)).mp (eH h).property⟩
  have heConj : eH (MulAut.conjNormal (v : HU) h) = hconj := by
    apply Subtype.ext
    rfl
  change QuotientGroup.mk'
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))
        (eH (MulAut.conjNormal (v : HU) h)) =
    D.U_action u
      (QuotientGroup.mk'
        ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) (eH h))
  rw [heConj,
    Ptype_factor_action_U_action, ptypeFCoreAction,
    subgroupConjugationFactorHom_apply_mk]

/-- The canonical `HU → U` projection restricts to the evident identification
on the literal nested complement. -/
theorem pTypeNonGaloisHUToUProjection_apply_complement
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (v : (U.subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let u : U := ⟨((v : HU) : M), by
      change (((v : HU) : M) : Gamma) ∈ U
      exact v.property⟩
    pTypeNonGaloisHUToUProjection ctx (v : HU) = u := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let hcomp : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  let eU : UHU ≃* U := pTypeNonGaloisUInHUEquiv ctx
  let eQ : HU ⧸ H ≃* UHU := hcomp.symm.QuotientMulEquiv
  let u : U := ⟨((v : HU) : M), by
    change (((v : HU) : M) : Gamma) ∈ U
    exact v.property⟩
  change eU (eQ (QuotientGroup.mk' H (v : HU))) = eU v
  apply congrArg eU
  apply hcomp.quotientMap_injective_on_right le_rfl
  exact hcomp.symm.quotientGroupMk_leftQuotientEquiv
    (QuotientGroup.mk' H (v : HU))

/-! ## Ambient and nested selected-coordinate characters -/

noncomputable def pTypeNonGaloisFCoreInMaximalToFactorProjection
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (Fitting_core M).subgroupOf M →* ptypeFCoreFactor ctx := by
  let eHM : (Fitting_core M).subgroupOf M ≃* Fitting_core M :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
  exact (QuotientGroup.mk'
    ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))).comp
      eHM.toMonoidHom

theorem pTypeNonGaloisFCoreInMaximalToFactorProjection_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Function.Surjective
      (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx) :=
  (QuotientGroup.mk'_surjective
    ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))).comp
      (Subgroup.subgroupOfEquivOfLe (Fcore_sub M)).surjective

theorem pTypeNonGaloisFCoreInMaximalToFactorProjection_conj_U
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (u : U) (h : (Fitting_core M).subgroupOf M) :
    let D := Ptype_factor_action ctx facts
    let uM : M := ⟨(u : Gamma),
      (ctx.typeP.2.1.2.2.2.2.1.trans
        (Subgroup.map_subtype_le (_root_.commutator M))) u.property⟩
    pTypeNonGaloisFCoreInMaximalToFactorProjection ctx
        (MulAut.conjNormal uM h) =
      D.U_action u
        (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx h) := by
  let D := Ptype_factor_action ctx facts
  have hUder : U ≤ derivedWithin M := ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  let uM : M := ⟨(u : Gamma), hUM u.property⟩
  let eHM : (Fitting_core M).subgroupOf M ≃* Fitting_core M :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
  have hUnormF : U ≤ Subgroup.normalizer (Fitting_core M : Set Gamma) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  let hconj : Fitting_core M :=
    ⟨(u : Gamma) * (eHM h : Gamma) * (u : Gamma)⁻¹,
      (hUnormF u.property (eHM h)).mp (eHM h).property⟩
  have heConj : eHM (MulAut.conjNormal uM h) = hconj := by
    apply Subtype.ext
    rfl
  change QuotientGroup.mk'
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))
        (eHM (MulAut.conjNormal uM h)) =
    D.U_action u
      (QuotientGroup.mk'
        ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) (eHM h))
  rw [heConj,
    Ptype_factor_action_U_action, ptypeFCoreAction,
    subgroupConjugationFactorHom_apply_mk]

theorem pTypeNonGaloisFCoreInMaximalToFactorProjection_conj_W₁
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (w : W₁) (h : (Fitting_core M).subgroupOf M) :
    let D := Ptype_factor_action ctx facts
    let wM : M := ⟨(w : Gamma), ctx.typeP.1.2.1.1 w.property⟩
    pTypeNonGaloisFCoreInMaximalToFactorProjection ctx
        (MulAut.conjNormal wM h) =
      D.W₁_action w
        (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx h) := by
  let D := Ptype_factor_action ctx facts
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : Gamma), hW₁M w.property⟩
  let eHM : (Fitting_core M).subgroupOf M ≃* Fitting_core M :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
  have hW₁normF : W₁ ≤ Subgroup.normalizer (Fitting_core M : Set Gamma) :=
    hW₁M.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  let hconj : Fitting_core M :=
    ⟨(w : Gamma) * (eHM h : Gamma) * (w : Gamma)⁻¹,
      (hW₁normF w.property (eHM h)).mp (eHM h).property⟩
  have heConj : eHM (MulAut.conjNormal wM h) = hconj := by
    apply Subtype.ext
    rfl
  change QuotientGroup.mk'
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))
        (eHM (MulAut.conjNormal wM h)) =
    D.W₁_action w
      (QuotientGroup.mk'
        ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) (eHM h))
  rw [heConj,
    Ptype_factor_action_W₁_action, ptypeW₁FactorAction,
    subgroupConjugationFactorHom_apply_mk]

noncomputable def pTypeNonGaloisSingleHCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    IrreducibleCharacter H ℂ :=
  PTypeNonGaloisCoordinateCoreInternal.pTypeIrreducibleCharacterOfMulChar
    (pTypeNonGaloisHToFactorProjection ctx)
    (pTypeNonGaloisSingleCoordinateMulChar
      (Ptype_factor_action ctx facts)
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois)
      lambda)

@[simp]
theorem pTypeNonGaloisSingleHCharacter_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (h : ((Fitting_core M).subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda h =
      pTypeNonGaloisSingleCoordinateMulChar
        (Ptype_factor_action ctx facts)
        (typeP_Galois_Pn
          (Ptype_factor_action_hypotheses ctx facts) not_Galois)
        lambda (pTypeNonGaloisHToFactorProjection ctx h) := by
  simp only [pTypeNonGaloisSingleHCharacter,
    PTypeNonGaloisCoordinateCoreInternal.pTypeIrreducibleCharacterOfMulChar_apply]

noncomputable def pTypeNonGaloisSingleFCoreCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ) :
    IrreducibleCharacter ((Fitting_core M).subgroupOf M) ℂ :=
  PTypeNonGaloisCoordinateCoreInternal.pTypeIrreducibleCharacterOfMulChar
    (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx)
    (pTypeNonGaloisSingleCoordinateMulChar
      (Ptype_factor_action ctx facts)
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois)
      lambda)

@[simp]
theorem pTypeNonGaloisSingleFCoreCharacter_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (h : (Fitting_core M).subgroupOf M) :
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois lambda h =
      pTypeNonGaloisSingleCoordinateMulChar
        (Ptype_factor_action ctx facts)
        (typeP_Galois_Pn
          (Ptype_factor_action_hypotheses ctx facts) not_Galois)
        lambda
          (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx h) := by
  simp only [pTypeNonGaloisSingleFCoreCharacter,
    PTypeNonGaloisCoordinateCoreInternal.pTypeIrreducibleCharacterOfMulChar_apply]

theorem pTypeNonGaloisSingleFCoreCharacter_eq_nested
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (h : (Fitting_core M).subgroupOf M) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let hHder : Fitting_core M ≤ derivedWithin M :=
      ctx.typeP.2.1.2.2.2.1
    let hHU : HU := ⟨h, hHder h.property⟩
    let hH : ((Fitting_core M).subgroupOf M).subgroupOf HU :=
      ⟨hHU, h.property⟩
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois lambda h =
      pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda hH := by
  simp only [pTypeNonGaloisSingleFCoreCharacter,
    pTypeNonGaloisSingleHCharacter,
    PTypeNonGaloisCoordinateCoreInternal.pTypeIrreducibleCharacterOfMulChar_apply]
  rfl

/-- The selected inertia subgroup, flattened from `HU` into the maximal
subgroup. -/
def pTypeNonGaloisH1InertiaInMaximal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Subgroup M :=
  (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois).map
    (pTypeHUInMaximal M (derivedWithin M)).subtype

/-- Normal conjugation is unchanged when the ambient F-core character is
transported to its nested copy in `HU`. -/
theorem pTypeNonGaloisSingleFCoreCharacter_conjugate_nested
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda mu : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (d : pTypeHUInMaximal M (derivedWithin M))
    (horbit :
      let HM := (Fitting_core M).subgroupOf M
      ClassFunction.normalConjugate HM (d : M)
          (pTypeNonGaloisSingleFCoreCharacter
            ctx facts not_Galois lambda : ClassFunction HM ℂ) =
        (pTypeNonGaloisSingleFCoreCharacter
          ctx facts not_Galois mu : ClassFunction HM ℂ)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    ClassFunction.normalConjugate H d
        (pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois lambda : ClassFunction H ℂ) =
      (pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois mu : ClassFunction H ℂ) := by
  classical
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let H := HM.subgroupOf HU
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  ext h
  rw [ClassFunction.normalConjugate_apply]
  let hM : HM := ⟨((h : HU) : M), h.property⟩
  let hConjM : HM := (MulAut.conjNormal (d : M)).symm hM
  let hConjH : H := (MulAut.conjNormal d).symm h
  have hConjUnderlying : (hConjM : M) = ((hConjH : HU) : M) := by
    rfl
  have hvalue := congrArg (fun f : ClassFunction HM ℂ ↦ f hM) horbit
  rw [ClassFunction.normalConjugate_apply] at hvalue
  have hleft := pTypeNonGaloisSingleFCoreCharacter_eq_nested
    ctx facts not_Galois lambda hConjM
  have hright := pTypeNonGaloisSingleFCoreCharacter_eq_nested
    ctx facts not_Galois mu hM
  have hcanonicalConj :
      (⟨⟨hConjM, hHder hConjM.property⟩, hConjM.property⟩ : H) =
        hConjH := by
    apply Subtype.ext
    apply Subtype.ext
    exact hConjUnderlying.symm
  have hcanonical :
      (⟨⟨hM, hHder hM.property⟩, hM.property⟩ : H) = h :=
    rfl
  calc
    pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois lambda hConjH =
      pTypeNonGaloisSingleFCoreCharacter
        ctx facts not_Galois lambda hConjM := by
          rw [← hcanonicalConj]
          exact hleft.symm
    _ = pTypeNonGaloisSingleFCoreCharacter
        ctx facts not_Galois mu hM := hvalue
    _ = pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois mu h := by
          rw [← hcanonical]
          exact hright

/-- Conversely, conjugacy of the nested characters determines conjugacy of
their ambient F-core models. -/
theorem pTypeNonGaloisSingleHCharacter_conjugate_ambient
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda mu : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (d : pTypeHUInMaximal M (derivedWithin M))
    (horbit :
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      ClassFunction.normalConjugate H d
          (pTypeNonGaloisSingleHCharacter
            ctx facts not_Galois lambda : ClassFunction H ℂ) =
        (pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois mu : ClassFunction H ℂ)) :
    let HM := (Fitting_core M).subgroupOf M
    ClassFunction.normalConjugate HM (d : M)
        (pTypeNonGaloisSingleFCoreCharacter
          ctx facts not_Galois lambda : ClassFunction HM ℂ) =
      (pTypeNonGaloisSingleFCoreCharacter
        ctx facts not_Galois mu : ClassFunction HM ℂ) := by
  classical
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let H := HM.subgroupOf HU
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  ext hM
  rw [ClassFunction.normalConjugate_apply]
  let hConjM : HM := (MulAut.conjNormal (d : M)).symm hM
  let hH : H :=
    ⟨⟨hM, hHder hM.property⟩, hM.property⟩
  let hConjH : H := (MulAut.conjNormal d).symm hH
  have hConjUnderlying : (hConjM : M) = ((hConjH : HU) : M) := by
    rfl
  have hvalue := congrArg (fun f : ClassFunction H ℂ ↦ f hH) horbit
  rw [ClassFunction.normalConjugate_apply] at hvalue
  have hleft := pTypeNonGaloisSingleFCoreCharacter_eq_nested
    ctx facts not_Galois lambda hConjM
  have hright := pTypeNonGaloisSingleFCoreCharacter_eq_nested
    ctx facts not_Galois mu hM
  have hcanonicalConj :
      (⟨⟨hConjM, hHder hConjM.property⟩, hConjM.property⟩ : H) =
        hConjH := by
    apply Subtype.ext
    apply Subtype.ext
    exact hConjUnderlying.symm
  calc
    pTypeNonGaloisSingleFCoreCharacter
        ctx facts not_Galois lambda hConjM =
      pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois lambda hConjH := by
          rw [← hcanonicalConj]
          exact hleft
    _ = pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois mu hH := hvalue
    _ = pTypeNonGaloisSingleFCoreCharacter
        ctx facts not_Galois mu hM := hright.symm

/-- A maximal-subgroup conjugator between two selected F-core characters has
trivial outer component, hence already belongs to `HU`. -/
theorem pTypeNonGaloisSingleFCoreCharacter_conjugator_mem_HU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda mu : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1)
    (x : M)
    (horbit :
      let HM := (Fitting_core M).subgroupOf M
      ClassFunction.normalConjugate HM x
          (pTypeNonGaloisSingleFCoreCharacter
            ctx facts not_Galois lambda : ClassFunction HM ℂ) =
        (pTypeNonGaloisSingleFCoreCharacter
          ctx facts not_Galois mu : ClassFunction HM ℂ)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    ∃ d : HU, (d : M) = x := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let H := HM.subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let W₁M := W₁.subgroupOf M
  let thetaLambda : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois lambda
  let thetaMu : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois mu
  have houter : HU.IsComplement' W₁M :=
    ctx.typeP.1.2.2.2.2.2.2
  have hinner : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  obtain ⟨⟨d, wM⟩, hdw⟩ := houter.2 x
  obtain ⟨⟨n, v⟩, hnv⟩ := hinner.2 d
  change (d : M) * (wM : M) = x at hdw
  change (n : HU) * (v : HU) = d at hnv
  let w : W₁ := ⟨((wM : M) : Gamma), wM.property⟩
  let u : U := ⟨(((v : HU) : M) : Gamma), by
    change (((v : HU) : M) : Gamma) ∈ U
    exact v.property⟩
  let nHM : HM := ⟨((n : HU) : M), n.property⟩
  let vM : M := ((v : HU) : M)
  have hnvM : (nHM : M) * vM = (d : M) := by
    exact congrArg Subtype.val hnv
  have hxProduct : (nHM : M) * (vM * (wM : M)) = x := by
    calc
      (nHM : M) * (vM * (wM : M)) =
          ((nHM : M) * vM) * (wM : M) :=
        (mul_assoc _ _ _).symm
      _ = (d : M) * (wM : M) := by rw [hnvM]
      _ = x := hdw
  have hvwOrbit : ClassFunction.normalConjugate HM
      (vM * (wM : M)) (thetaLambda : ClassFunction HM ℂ) =
        (thetaMu : ClassFunction HM ℂ) := by
    calc
      ClassFunction.normalConjugate HM (vM * (wM : M))
          (thetaLambda : ClassFunction HM ℂ) =
        ClassFunction.normalConjugate HM (nHM : M)
          (ClassFunction.normalConjugate HM (vM * (wM : M))
            (thetaLambda : ClassFunction HM ℂ)) :=
        (ClassFunction.normalConjugate_coe HM _ nHM).symm
      _ = ClassFunction.normalConjugate HM
          ((nHM : M) * (vM * (wM : M)))
            (thetaLambda : ClassFunction HM ℂ) :=
        (ClassFunction.normalConjugate_mul HM
          (nHM : M) (vM * (wM : M))
            (thetaLambda : ClassFunction HM ℂ)).symm
      _ = ClassFunction.normalConjugate HM x
          (thetaLambda : ClassFunction HM ℂ) := by rw [hxProduct]
      _ = (thetaMu : ClassFunction HM ℂ) := horbit
  have hfactorOrbit : ∀ z : ptypeFCoreFactor ctx,
      pTypeNonGaloisSingleCoordinateCharacter D data lambda
          (D.W₁_action w⁻¹ (D.U_action u⁻¹ z)) =
        pTypeNonGaloisSingleCoordinateCharacter D data mu z := by
    intro z
    obtain ⟨h, hh⟩ :=
      pTypeNonGaloisFCoreInMaximalToFactorProjection_surjective ctx z
    let hv : HM := MulAut.conjNormal vM⁻¹ h
    let hw : HM := MulAut.conjNormal (wM : M)⁻¹ hv
    have harg : (MulAut.conjNormal (vM * (wM : M))).symm h = hw := by
      have hhw : (hw : M) =
          (wM : M)⁻¹ * (vM⁻¹ * (h : M) * vM) * (wM : M) := by
        have hhv : (hv : M) = vM⁻¹ * (h : M) * vM := by
          dsimp only [hv]
          change vM⁻¹ * (h : M) * (vM⁻¹)⁻¹ = _
          rw [inv_inv]
        dsimp only [hw]
        change (wM : M)⁻¹ * (hv : M) * ((wM : M)⁻¹)⁻¹ = _
        rw [inv_inv, hhv]
      apply Subtype.ext
      rw [hhw]
      simp only [MulAut.conjNormal_symm_apply]
      change (vM * (wM : M))⁻¹ * (h : M) *
          (vM * (wM : M)) =
        (wM : M)⁻¹ * (vM⁻¹ * (h : M) * vM) * (wM : M)
      group
    have hvalue := congrArg (fun f : ClassFunction HM ℂ ↦ f h) hvwOrbit
    rw [ClassFunction.normalConjugate_apply, harg,
      pTypeNonGaloisSingleFCoreCharacter_apply,
      pTypeNonGaloisSingleFCoreCharacter_apply] at hvalue
    have hvProj : pTypeNonGaloisFCoreInMaximalToFactorProjection ctx hv =
        D.U_action u⁻¹ z := by
      let uInvM : M := ⟨(u⁻¹ : Gamma),
        (ctx.typeP.2.1.2.2.2.2.1.trans
          (Subgroup.map_subtype_le (_root_.commutator M)))
            (u⁻¹).property⟩
      have huInvM : uInvM = vM⁻¹ := by
        apply Subtype.ext
        rfl
      have hp :=
        pTypeNonGaloisFCoreInMaximalToFactorProjection_conj_U
          ctx facts u⁻¹ h
      change pTypeNonGaloisFCoreInMaximalToFactorProjection ctx
          (MulAut.conjNormal uInvM h) =
        D.U_action u⁻¹
          (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx h) at hp
      rw [huInvM, hh] at hp
      exact hp
    have hwProj : pTypeNonGaloisFCoreInMaximalToFactorProjection ctx hw =
        D.W₁_action w⁻¹ (D.U_action u⁻¹ z) := by
      let wInvM : M := ⟨(w⁻¹ : Gamma),
        ctx.typeP.1.2.1.1 (w⁻¹).property⟩
      have hwInvM : wInvM = (wM : M)⁻¹ := by
        apply Subtype.ext
        rfl
      have hp :=
        pTypeNonGaloisFCoreInMaximalToFactorProjection_conj_W₁
          ctx facts w⁻¹ hv
      change pTypeNonGaloisFCoreInMaximalToFactorProjection ctx
          (MulAut.conjNormal wInvM hv) =
        D.W₁_action w⁻¹
          (pTypeNonGaloisFCoreInMaximalToFactorProjection ctx hv) at hp
      rw [hwInvM, hvProj] at hp
      exact hp
    rw [hwProj, hh] at hvalue
    simpa only [pTypeNonGaloisSingleCoordinateCharacter_apply] using hvalue
  have hfactorOrbit' : ∀ z : ptypeFCoreFactor ctx,
      pTypeNonGaloisSingleCoordinateCharacter D data lambda
          (D.U_action (D.W₁_action_U w⁻¹ u⁻¹)
            (D.W₁_action w⁻¹ z)) =
        pTypeNonGaloisSingleCoordinateCharacter D data mu z := by
    intro z
    rw [D.action_compatibility]
    exact hfactorOrbit z
  have hwinv : w⁻¹ = 1 :=
    pTypeNonGaloisSingleCoordinate_outer_support_rigidity
      D data lambda mu hlambda
        (D.W₁_action_U w⁻¹ u⁻¹) w⁻¹ hfactorOrbit'
  have hw : w = 1 := inv_eq_one.mp hwinv
  have hwM : wM = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (w : Gamma) = 1
    exact congrArg Subtype.val hw
  refine ⟨d, ?_⟩
  simpa only [hwM, Subgroup.coe_one, mul_one] using hdw

/-! ## Exact inertia in the nested derived subgroup -/

theorem pTypeNonGaloisSingleHCharacter_normalConjugate_U_fixed_iff
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1)
    (v : (U.subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    let D := Ptype_factor_action ctx facts
    let data := typeP_Galois_Pn
      (Ptype_factor_action_hypotheses ctx facts) not_Galois
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let u : U := ⟨((v : HU) : M), by
      change (((v : HU) : M) : Gamma) ∈ U
      exact v.property⟩
    ClassFunction.normalConjugate H (v : HU)
        (pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois lambda : ClassFunction H ℂ) =
      (pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois lambda : ClassFunction H ℂ) ↔
      u ∈ pointwiseActionKernel D.U_action data.H₁ := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let theta : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda
  let u : U := ⟨((v : HU) : M), by
    change (((v : HU) : M) : Gamma) ∈ U
    exact v.property⟩
  let K := pointwiseActionKernel D.U_action data.H₁
  have hprojInv : ∀ h : H,
      pTypeNonGaloisHToFactorProjection ctx
          (MulAut.conjNormal ((v : HU)⁻¹) h) =
        D.U_action u⁻¹ (pTypeNonGaloisHToFactorProjection ctx h) := by
    intro h
    let vinv : UHU := v⁻¹
    let uinv : U := ⟨((vinv : HU) : M), by
      change (((vinv : HU) : M) : Gamma) ∈ U
      exact vinv.property⟩
    have hvInv : (vinv : HU) = (v : HU)⁻¹ := by
      apply Subtype.ext
      rfl
    have huInv : uinv = u⁻¹ := by
      apply Subtype.ext
      rfl
    have hp := pTypeNonGaloisHToFactorProjection_conj_U
      ctx facts vinv h
    change pTypeNonGaloisHToFactorProjection ctx
        (MulAut.conjNormal (vinv : HU) h) =
      D.U_action uinv (pTypeNonGaloisHToFactorProjection ctx h) at hp
    rw [hvInv, huInv] at hp
    exact hp
  constructor
  · intro hfixed
    have hfactorFixed : ∀ z : ptypeFCoreFactor ctx,
        pTypeNonGaloisSingleCoordinateCharacter D data lambda
            (D.U_action u⁻¹ z) =
          pTypeNonGaloisSingleCoordinateCharacter D data lambda z := by
      intro z
      obtain ⟨h, rfl⟩ := pTypeNonGaloisHToFactorProjection_surjective ctx z
      have hvalue := congrArg (fun f : ClassFunction H ℂ ↦ f h) hfixed
      rw [ClassFunction.normalConjugate_apply] at hvalue
      have harg : (MulAut.conjNormal (v : HU)).symm h =
          MulAut.conjNormal ((v : HU)⁻¹) h := by
        apply Subtype.ext
        rfl
      rw [harg, pTypeNonGaloisSingleHCharacter_apply,
        pTypeNonGaloisSingleHCharacter_apply,
        hprojInv] at hvalue
      simpa only [pTypeNonGaloisSingleCoordinateCharacter_apply]
        using hvalue
    have huInv : u⁻¹ ∈ K :=
      (pTypeNonGaloisSingleCoordinateCharacter_fixed_iff
        D data lambda hlambda u⁻¹).mp hfactorFixed
    simpa only [K, inv_inv] using K.inv_mem huInv
  · intro hu
    have huInv : u⁻¹ ∈ K := K.inv_mem hu
    have hfactorFixed :=
      (pTypeNonGaloisSingleCoordinateCharacter_fixed_iff
        D data lambda hlambda u⁻¹).mpr huInv
    ext h
    rw [ClassFunction.normalConjugate_apply]
    have harg : (MulAut.conjNormal (v : HU)).symm h =
        MulAut.conjNormal ((v : HU)⁻¹) h := by
      apply Subtype.ext
      rfl
    rw [harg, pTypeNonGaloisSingleHCharacter_apply,
      pTypeNonGaloisSingleHCharacter_apply,
      hprojInv]
    simpa only [pTypeNonGaloisSingleCoordinateCharacter_apply] using
      hfactorFixed (pTypeNonGaloisHToFactorProjection ctx h)

theorem pTypeNonGaloisSingleHCharacter_inertia
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    ClassFunction.inertia H
        (pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois lambda : ClassFunction H ℂ) =
      pTypeNonGaloisH1InertiaInHU ctx facts not_Galois := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let theta : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let K := pointwiseActionKernel D.U_action data.H₁
  have hcomp : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  ext x
  obtain ⟨⟨n, v⟩, hnv⟩ := hcomp.2 x
  change (n : HU) * (v : HU) = x at hnv
  let u : U := ⟨((v : HU) : M), by
    change (((v : HU) : M) : Gamma) ∈ U
    exact v.property⟩
  have hnKer : (n : HU) ∈
      (pTypeNonGaloisHUToUProjection ctx).ker := by
    rw [pTypeNonGaloisHUToUProjection_ker ctx]
    exact n.property
  have hnOne : pi (n : HU) = 1 := by
    change pTypeNonGaloisHUToUProjection ctx (n : HU) = 1
    exact MonoidHom.mem_ker.mp hnKer
  have hvProj : pi (v : HU) = u :=
    pTypeNonGaloisHUToUProjection_apply_complement ctx v
  have hxProj : pi x = u := by
    calc
      pi x = pi ((n : HU) * (v : HU)) := by rw [hnv]
      _ = pi (n : HU) * pi (v : HU) := map_mul pi _ _
      _ = u := by rw [hnOne, hvProj, one_mul]
  constructor
  · intro hx
    have hxFixed : ClassFunction.normalConjugate H x
        (theta : ClassFunction H ℂ) = (theta : ClassFunction H ℂ) :=
      (ClassFunction.mem_inertia_iff H
        (theta : ClassFunction H ℂ) x).mp hx
    have hvFixed : ClassFunction.normalConjugate H (v : HU)
        (theta : ClassFunction H ℂ) = (theta : ClassFunction H ℂ) := by
      calc
        ClassFunction.normalConjugate H (v : HU)
            (theta : ClassFunction H ℂ) =
          ClassFunction.normalConjugate H (n : HU)
            (ClassFunction.normalConjugate H (v : HU)
              (theta : ClassFunction H ℂ)) :=
          (ClassFunction.normalConjugate_coe H _ n).symm
        _ = ClassFunction.normalConjugate H
            ((n : HU) * (v : HU)) (theta : ClassFunction H ℂ) :=
          (ClassFunction.normalConjugate_mul H
            (n : HU) (v : HU) (theta : ClassFunction H ℂ)).symm
        _ = ClassFunction.normalConjugate H x
            (theta : ClassFunction H ℂ) := by rw [hnv]
        _ = (theta : ClassFunction H ℂ) := hxFixed
    have huK : u ∈ K :=
      (pTypeNonGaloisSingleHCharacter_normalConjugate_U_fixed_iff
        ctx facts not_Galois lambda hlambda v).mp hvFixed
    change pi x ∈ K
    simpa only [hxProj] using huK
  · intro hx
    have huK : u ∈ K := by
      change pi x ∈ K at hx
      simpa only [hxProj] using hx
    have hvFixed : ClassFunction.normalConjugate H (v : HU)
        (theta : ClassFunction H ℂ) = (theta : ClassFunction H ℂ) :=
      (pTypeNonGaloisSingleHCharacter_normalConjugate_U_fixed_iff
        ctx facts not_Galois lambda hlambda v).mpr huK
    rw [ClassFunction.mem_inertia_iff]
    calc
      ClassFunction.normalConjugate H x (theta : ClassFunction H ℂ) =
        ClassFunction.normalConjugate H
          ((n : HU) * (v : HU)) (theta : ClassFunction H ℂ) := by
        rw [hnv]
      _ = ClassFunction.normalConjugate H (n : HU)
          (ClassFunction.normalConjugate H (v : HU)
            (theta : ClassFunction H ℂ)) :=
        ClassFunction.normalConjugate_mul H
          (n : HU) (v : HU) (theta : ClassFunction H ℂ)
      _ = ClassFunction.normalConjugate H (n : HU)
          (theta : ClassFunction H ℂ) := by rw [hvFixed]
      _ = (theta : ClassFunction H ℂ) :=
        ClassFunction.normalConjugate_coe H _ n

/-- The ambient selected F-core character has no additional outer
stabilizer: its inertia in `M` is exactly the flattened inertia from `HU`. -/
theorem pTypeNonGaloisSingleFCoreCharacter_inertia
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts) not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    let HM := (Fitting_core M).subgroupOf M
    ClassFunction.inertia HM
        (pTypeNonGaloisSingleFCoreCharacter
          ctx facts not_Galois lambda : ClassFunction HM ℂ) =
      pTypeNonGaloisH1InertiaInMaximal ctx facts not_Galois := by
  classical
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let H := HM.subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let thetaM : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois lambda
  let thetaH : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda
  letI : HM.Normal := Fcore_normal M
  ext x
  constructor
  · intro hx
    have hxFixed : ClassFunction.normalConjugate HM x
        (thetaM : ClassFunction HM ℂ) = (thetaM : ClassFunction HM ℂ) :=
      (ClassFunction.mem_inertia_iff HM
        (thetaM : ClassFunction HM ℂ) x).mp hx
    obtain ⟨d, hdx⟩ :=
      pTypeNonGaloisSingleFCoreCharacter_conjugator_mem_HU
        ctx facts not_Galois lambda lambda hlambda x hxFixed
    have hdFixed : ClassFunction.normalConjugate HM (d : M)
        (thetaM : ClassFunction HM ℂ) = (thetaM : ClassFunction HM ℂ) := by
      rw [hdx]
      exact hxFixed
    have hdNested : ClassFunction.normalConjugate H d
        (thetaH : ClassFunction H ℂ) = (thetaH : ClassFunction H ℂ) :=
      pTypeNonGaloisSingleFCoreCharacter_conjugate_nested
        ctx facts not_Galois lambda lambda d hdFixed
    have hdInertia : d ∈ ClassFunction.inertia H
        (thetaH : ClassFunction H ℂ) :=
      (ClassFunction.mem_inertia_iff H
        (thetaH : ClassFunction H ℂ) d).mpr hdNested
    have hdT : d ∈ T := by
      change d ∈ pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
      rw [← pTypeNonGaloisSingleHCharacter_inertia
        ctx facts not_Galois lambda hlambda]
      exact hdInertia
    exact ⟨d, hdT, hdx⟩
  · rintro ⟨d, hdT, rfl⟩
    have hdInertia : d ∈ ClassFunction.inertia H
        (thetaH : ClassFunction H ℂ) := by
      rw [pTypeNonGaloisSingleHCharacter_inertia
        ctx facts not_Galois lambda hlambda]
      exact hdT
    have hdNested : ClassFunction.normalConjugate H d
        (thetaH : ClassFunction H ℂ) = (thetaH : ClassFunction H ℂ) :=
      (ClassFunction.mem_inertia_iff H
        (thetaH : ClassFunction H ℂ) d).mp hdInertia
    have hdAmbient : ClassFunction.normalConjugate HM (d : M)
        (thetaM : ClassFunction HM ℂ) = (thetaM : ClassFunction HM ℂ) :=
      pTypeNonGaloisSingleHCharacter_conjugate_ambient
        ctx facts not_Galois lambda lambda d hdNested
    exact (ClassFunction.mem_inertia_iff HM
      (thetaM : ClassFunction HM ℂ) (d : M)).mpr hdAmbient

theorem pTypeNonGaloisH_le_H1InertiaInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    H ≤ pTypeNonGaloisH1InertiaInHU ctx facts not_Galois := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  change H ≤ pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  intro h hh
  change pTypeNonGaloisHUToUProjection ctx h ∈
    pointwiseActionKernel D.U_action data.H₁
  have hhKer : h ∈ (pTypeNonGaloisHUToUProjection ctx).ker := by
    rw [pTypeNonGaloisHUToUProjection_ker ctx]
    exact hh
  rw [MonoidHom.mem_ker.mp hhKer]
  exact Subgroup.one_mem _

end PTypeNonGaloisInertiaCoreInternal

end

end Submission.OddOrder.PF
