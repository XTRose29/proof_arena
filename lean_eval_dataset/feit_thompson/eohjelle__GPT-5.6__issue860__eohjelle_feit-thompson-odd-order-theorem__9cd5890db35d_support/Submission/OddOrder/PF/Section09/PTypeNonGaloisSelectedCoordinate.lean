import Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore

/-!
# Peterfalvi Section 9: the selected non-Galois coordinate

This module specializes the non-Galois coordinate construction to the factor
`H₁` selected by `typeP_Galois_Pn`.  It also constructs the canonical
projection `HU → U` and pulls the pointwise stabilizer of `H₁` back to the
corresponding inertia subgroup of `HU`.

The character-level adapters are kept in a module-specific internal namespace;
the source-facing declarations of this phase are the projection and inertia
subgroup at the end of the file.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical IsMulCommutative

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15

universe u

local instance (priority := 10) pTypeSelectedFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisSelectedCoordinateInternal

open PTypeNonGaloisCoordinateCoreInternal

/-! ## The selected coordinate -/

/-- A scalar character supported on `H₁` and trivial on every other
direct-product coordinate. -/
noncomputable def pTypeNonGaloisSingleCoordinateFamily
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) : W₁ → MulChar data.H₁ ℂ :=
  fun w ↦ if w = 1 then lambda else 1

@[simp]
theorem pTypeNonGaloisSingleCoordinateFamily_one
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) :
    pTypeNonGaloisSingleCoordinateFamily data lambda 1 = lambda := by
  simp [pTypeNonGaloisSingleCoordinateFamily]

@[simp]
theorem pTypeNonGaloisSingleCoordinateFamily_of_ne
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) {w : W₁} (hw : w ≠ 1) :
    pTypeNonGaloisSingleCoordinateFamily data lambda w = 1 := by
  simp [pTypeNonGaloisSingleCoordinateFamily, hw]

/-- Evaluation of the coordinate family translated by `u`.  The core keeps
the underlying character-composition helper private, so this is the
selected-coordinate-facing evaluation adapter. -/
@[simp]
theorem pTypeNonGaloisUTranslateCoordinateFamily_apply
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (u : U) (lambda : W₁ → MulChar data.H₁ ℂ)
    (w : W₁) (x : data.H₁) :
    pTypeNonGaloisUTranslateCoordinateFamily D data u lambda w x =
      lambda w
        (restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
          (D.W₁_action_U w⁻¹ u) x) :=
  rfl

/-- The linear irreducible character associated to the selected coordinate. -/
noncomputable def pTypeNonGaloisSingleCoordinateCharacter
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) :
    IrreducibleCharacter Hbar ℂ :=
  pTypeNonGaloisCoordinateCharacter D data
    (pTypeNonGaloisSingleCoordinateFamily data lambda)

@[simp]
theorem pTypeNonGaloisSingleCoordinateCharacter_degree
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) :
    pTypeIrreducibleDegree
      (pTypeNonGaloisSingleCoordinateCharacter D data lambda) = 1 :=
  pTypeNonGaloisCoordinateCharacter_degree D data _

/-- A nonprincipal multiplicative character of a group of prime order is
faithful. -/
private theorem pTypeNontrivialMulChar_injective_of_prime_card
    {Q : Type u} [Group Q] [Finite Q] [IsMulCommutative Q]
    (hQ : (Nat.card Q).Prime) (lambda : MulChar Q ℂ)
    (hlambda : lambda ≠ 1) : Function.Injective lambda := by
  letI : Fact (Nat.card Q).Prime := ⟨hQ⟩
  have hker : lambda.toMonoidHom.ker = ⊥ := by
    apply lambda.toMonoidHom.ker.eq_bot_or_eq_top_of_prime_card.resolve_right
    intro htop
    apply hlambda
    apply MulChar.ext'
    intro x
    have hx : x ∈ lambda.toMonoidHom.ker := by
      rw [htop]
      trivial
    change lambda x = 1 at hx
    rw [MulChar.one_apply (Group.isUnit x)]
    exact hx
  exact lambda.toMonoidHom.ker_eq_bot_iff.mp hker

/-- The stabilizer in `U` of a nonprincipal selected-coordinate character is
exactly the pointwise action kernel of `H₁`. -/
theorem pTypeNonGaloisSingleCoordinateCharacter_fixed_iff
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1)
    (u : U) :
    (∀ h : Hbar,
        pTypeNonGaloisSingleCoordinateCharacter D data lambda
            (D.U_action u h) =
          pTypeNonGaloisSingleCoordinateCharacter D data lambda h) ↔
      u ∈ pointwiseActionKernel D.U_action data.H₁ := by
  classical
  let family := pTypeNonGaloisSingleCoordinateFamily data lambda
  constructor
  · intro hfixed
    have hcharacters :
        pTypeNonGaloisCoordinateCharacter D data
            (pTypeNonGaloisUTranslateCoordinateFamily D data u family) =
          pTypeNonGaloisCoordinateCharacter D data family := by
      ext h
      exact (pTypeNonGaloisCoordinateCharacter_U_translate
        D data u family h).trans (hfixed h)
    have hfamilies :=
      pTypeNonGaloisCoordinateCharacter_injective D data hcharacters
    have hcoordinate := congrFun hfamilies (1 : W₁)
    have hlambda_injective : Function.Injective lambda :=
      pTypeNontrivialMulChar_injective_of_prime_card
        (by rw [data.card_H₁]; exact D.p_prime) lambda hlambda
    rw [mem_pointwiseActionKernel_iff]
    intro h hh
    let x : data.H₁ := ⟨h, hh⟩
    have hvalue := congrArg
      (fun chi : MulChar data.H₁ ℂ ↦ chi x) hcoordinate
    have hvalue' : lambda
        (restrictMulAutHom data.H₁ D.U_action data.H₁_normalized u x) =
      lambda x := by
      simpa only [pTypeNonGaloisUTranslateCoordinateFamily_apply,
        family, pTypeNonGaloisSingleCoordinateFamily_one,
        inv_one, map_one, MulAut.one_apply] using hvalue
    have hx := hlambda_injective hvalue'
    exact congrArg Subtype.val hx
  · intro hu h
    have hfamilies :
        pTypeNonGaloisUTranslateCoordinateFamily D data u family =
          family := by
      funext w
      by_cases hw : w = 1
      · subst w
        apply MulChar.ext'
        intro x
        have hfix :=
          (mem_pointwiseActionKernel_iff D.U_action data.H₁ u).mp
            hu (x : Hbar) x.property
        have hrestricted :
            restrictMulAutHom data.H₁ D.U_action
                data.H₁_normalized u x = x := by
          apply Subtype.ext
          exact hfix
        simpa only [pTypeNonGaloisUTranslateCoordinateFamily_apply,
          family, pTypeNonGaloisSingleCoordinateFamily_one,
          inv_one, map_one, MulAut.one_apply] using
            congrArg lambda hrestricted
      · apply MulChar.ext
        intro x
        rw [pTypeNonGaloisUTranslateCoordinateFamily_apply]
        have hfamilyw : family w = 1 := by
          simpa only [family] using
            pTypeNonGaloisSingleCoordinateFamily_of_ne data lambda hw
        rw [hfamilyw]
        let alpha : MulEquiv data.H₁ data.H₁ :=
          restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
            (D.W₁_action_U w⁻¹ u)
        let y : data.H₁ˣ := Units.map alpha.toMonoidHom x
        change (1 : MulChar data.H₁ ℂ) (y : data.H₁) =
          (1 : MulChar data.H₁ ℂ) (x : data.H₁)
        rw [MulChar.one_apply_coe, MulChar.one_apply_coe]
    calc
      pTypeNonGaloisSingleCoordinateCharacter D data lambda
          (D.U_action u h) =
        pTypeNonGaloisCoordinateCharacter D data
          (pTypeNonGaloisUTranslateCoordinateFamily D data u family) h :=
        (pTypeNonGaloisCoordinateCharacter_U_translate
          D data u family h).symm
      _ = pTypeNonGaloisSingleCoordinateCharacter D data lambda h := by
        rw [hfamilies]
        simp only [family, pTypeNonGaloisSingleCoordinateCharacter]

/-- Inserting a scalar character into the selected coordinate is injective. -/
theorem pTypeNonGaloisSingleCoordinateCharacter_injective
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D) :
    Function.Injective
      (pTypeNonGaloisSingleCoordinateCharacter D data) := by
  intro lambda mu hlm
  have hfamilies :=
    pTypeNonGaloisCoordinateCharacter_injective D data hlm
  simpa [pTypeNonGaloisSingleCoordinateFamily] using
    congrFun hfamilies (1 : W₁)

/-- The multiplicative character underlying the selected-coordinate
irreducible character. -/
noncomputable def pTypeNonGaloisSingleCoordinateMulChar
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) : MulChar Hbar ℂ :=
  let A := fun w : W₁ ↦
    actionConjugate D.W₁_action data.H₁ w
  pTypeInternalDirectProductMulChar A data.conjugates_direct
    (fun w ↦ pTypeActionConjugateMulChar D data.H₁ w
      (pTypeNonGaloisSingleCoordinateFamily data lambda w))

@[simp]
theorem pTypeNonGaloisSingleCoordinateCharacter_apply
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) (h : Hbar) :
    pTypeNonGaloisSingleCoordinateCharacter D data lambda h =
      pTypeNonGaloisSingleCoordinateMulChar D data lambda h := by
  simp only [pTypeNonGaloisSingleCoordinateCharacter,
    pTypeNonGaloisCoordinateCharacter,
    pTypeIrreducibleCharacterOfMulChar_apply, MonoidHom.id_apply,
    pTypeNonGaloisSingleCoordinateMulChar]

/-- A selected coordinate cannot be carried to another selected coordinate by
a nonidentity outer action. -/
theorem pTypeNonGaloisSingleCoordinate_outer_support_rigidity
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda mu : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1)
    (u : U) (w : W₁)
    (hfixed : ∀ z : Hbar,
      pTypeNonGaloisSingleCoordinateCharacter D data lambda
          (D.U_action u (D.W₁_action w z)) =
        pTypeNonGaloisSingleCoordinateCharacter D data mu z) :
    w = 1 :=
  Submission.OddOrder.PF.PTypeNonGaloisCoordinateCoreInternal.pTypeNonGaloisSingleCoordinate_outer_support_rigidity
      D data lambda mu hlambda u w hfixed

/-- Equal-character specialization of selected-coordinate support rigidity. -/
theorem pTypeNonGaloisSingleCoordinate_outer_rigidity
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1)
    (u : U) (w : W₁)
    (hfixed : ∀ z : Hbar,
      pTypeNonGaloisSingleCoordinateCharacter D data lambda
          (D.U_action u (D.W₁_action w z)) =
        pTypeNonGaloisSingleCoordinateCharacter D data lambda z) :
    w = 1 :=
  pTypeNonGaloisSingleCoordinate_outer_support_rigidity
    D data lambda lambda hlambda u w hfixed

/-! ## Canonical complement data in `HU` -/

/-- The canonical identification of the nested `HU` subgroup with the derived
subgroup of the maximal subgroup. -/
noncomputable def pTypeNonGaloisHUToDerivedEquiv
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (_ctx : PTypeFCoreContext M U W W₁ W₂) :
    pTypeHUInMaximal M (derivedWithin M) ≃* derivedWithin M :=
  Subgroup.subgroupOfEquivOfLe
    (Subgroup.map_subtype_le (_root_.commutator M))

/-- The complement inside `HU` is canonically identified with `U`. -/
noncomputable def pTypeNonGaloisUInHUEquiv
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ((U.subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) ≃* U := by
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hUHU : U.subgroupOf M ≤
      pTypeHUInMaximal M (derivedWithin M) := by
    intro x hx
    exact hUder hx
  exact (Subgroup.subgroupOfEquivOfLe hUHU).trans
    (Subgroup.subgroupOfEquivOfLe hUM)

/-- The nested F-core and nested complement form the canonical complement
decomposition of `HU`. -/
theorem pTypeNonGaloisHInHU_isComplement'
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (((Fitting_core M).subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))).IsComplement'
      ((U.subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let eHU : HU ≃* derivedWithin M :=
    pTypeNonGaloisHUToDerivedEquiv ctx
  have hmapped := internal.pTypeIsComplement_map_mulEquiv
    ctx.typeP.2.1.2.2.2.2.2.2 eHU.symm
  have hmapH :
      ((Fitting_core M).subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eHU x, hx, ?_⟩
      exact eHU.symm_apply_apply x
  have hmapU :
      (U.subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom = UHU := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eHU x, hx, ?_⟩
      exact eHU.symm_apply_apply x
  rw [hmapH, hmapU] at hmapped
  exact hmapped

end PTypeNonGaloisSelectedCoordinateInternal

open PTypeNonGaloisSelectedCoordinateInternal

/-! ## The projection `HU → U` -/

/-- Projection `HU = H ⋊ U → U` supplied by the canonical complement
decomposition. -/
noncomputable def pTypeNonGaloisHUToUProjection
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    pTypeHUInMaximal M (derivedWithin M) →* U := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let hcomp : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  let eU : UHU ≃* U := pTypeNonGaloisUInHUEquiv ctx
  exact eU.toMonoidHom.comp
    ((hcomp.symm.QuotientMulEquiv).toMonoidHom.comp
      (QuotientGroup.mk' H))

/-- The complement projection is onto. -/
theorem pTypeNonGaloisHUToUProjection_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Function.Surjective (pTypeNonGaloisHUToUProjection ctx) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let hcomp : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  let eU : UHU ≃* U := pTypeNonGaloisUInHUEquiv ctx
  exact eU.surjective.comp
    ((hcomp.symm.QuotientMulEquiv).surjective.comp
      (QuotientGroup.mk'_surjective H))

/-- The kernel of `HU → U` is the F-core factor `H`. -/
theorem pTypeNonGaloisHUToUProjection_ker
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeNonGaloisHUToUProjection ctx).ker =
      ((Fitting_core M).subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M)) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let hcomp : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  let eU : UHU ≃* U := pTypeNonGaloisUInHUEquiv ctx
  rw [pTypeNonGaloisHUToUProjection,
    MonoidHom.ker_comp_of_injective _ eU.toMonoidHom eU.injective,
    MonoidHom.ker_comp_of_injective _
      (hcomp.symm.QuotientMulEquiv).toMonoidHom
      (hcomp.symm.QuotientMulEquiv).injective,
    QuotientGroup.ker_mk']

/-! ## The selected-coordinate inertia subgroup -/

/-- Clause (d)'s inertia subgroup `H ⋊ K`, expressed as the pullback of the
pointwise kernel `K ≤ U`. -/
def pTypeNonGaloisH1InertiaInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Subgroup (pTypeHUInMaximal M (derivedWithin M)) :=
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  (pointwiseActionKernel D.U_action data.H₁).comap
    (pTypeNonGaloisHUToUProjection ctx)

instance pTypeNonGaloisH1InertiaInHU_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois).Normal := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  exact Subgroup.Normal.comap data.actionKernel_normal _

/-- The index of the selected-coordinate inertia subgroup in `HU` is the
non-Galois index `a`. -/
theorem pTypeNonGaloisH1InertiaInHU_index
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois).index =
      pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  exact (pointwiseActionKernel D.U_action data.H₁).index_comap_of_surjective
    (pTypeNonGaloisHUToUProjection_surjective ctx)

end

end Submission.OddOrder.PF
