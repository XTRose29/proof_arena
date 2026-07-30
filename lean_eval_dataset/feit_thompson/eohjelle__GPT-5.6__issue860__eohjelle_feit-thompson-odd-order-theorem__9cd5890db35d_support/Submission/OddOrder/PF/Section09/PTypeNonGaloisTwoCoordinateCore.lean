import Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaExtensions

/-!
# Peterfalvi Section 9: the two-coordinate non-Galois core

This phase puts one nonprincipal scalar character in two chief-factor
coordinates, computes its stabilizer in the complement, and inflates it to
the nested Fitting subgroup.  The resulting character has exact inertia the
pullback of the intersection of the two coordinate kernels.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical IsMulCommutative

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15

universe u

local instance (priority := 10) pTypeTwoCoordinateFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisTwoCoordinateCoreInternal

open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisSelectedCoordinateInternal
open PTypeNonGaloisInertiaCoreInternal
open PTypeNonGaloisInertiaExtensionsInternal

local instance pTypeNonGaloisFCoreFactor_commutative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsMulCommutative (ptypeFCoreFactor ctx) :=
  (ptypeFCoreFactor_elementary ctx).commutative

/-! ## The two-coordinate factor character -/

/-- Use the same scalar character in the coordinates `1` and `w`, and the
principal character in all remaining coordinates. -/
noncomputable def pTypeNonGaloisTwoCoordinateFamily
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : MulChar data.H₁ ℂ) :
    W₁ → MulChar data.H₁ ℂ :=
  fun v ↦ if v = 1 then lambda else if v = w then lambda else 1

@[simp]
theorem pTypeNonGaloisTwoCoordinateFamily_one
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : MulChar data.H₁ ℂ) :
    pTypeNonGaloisTwoCoordinateFamily data w lambda 1 = lambda := by
  simp [pTypeNonGaloisTwoCoordinateFamily]

@[simp]
theorem pTypeNonGaloisTwoCoordinateFamily_at_second
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    {w : W₁} (hw : w ≠ 1) (lambda : MulChar data.H₁ ℂ) :
    pTypeNonGaloisTwoCoordinateFamily data w lambda w = lambda := by
  simp [pTypeNonGaloisTwoCoordinateFamily, hw]

@[simp]
theorem pTypeNonGaloisTwoCoordinateFamily_of_ne
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    {w v : W₁} (hvOne : v ≠ 1) (hvw : v ≠ w)
    (lambda : MulChar data.H₁ ℂ) :
    pTypeNonGaloisTwoCoordinateFamily data w lambda v = 1 := by
  simp [pTypeNonGaloisTwoCoordinateFamily, hvOne, hvw]

/-- The irreducible linear character associated with the two-coordinate
family. -/
noncomputable def pTypeNonGaloisTwoCoordinateCharacter
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : MulChar data.H₁ ℂ) :
    IrreducibleCharacter Hbar ℂ :=
  pTypeNonGaloisCoordinateCharacter D data
    (pTypeNonGaloisTwoCoordinateFamily data w lambda)

/-- The scalar character underlying the two-coordinate irreducible
character. -/
noncomputable def pTypeNonGaloisTwoCoordinateMulChar
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : MulChar data.H₁ ℂ) : MulChar Hbar ℂ :=
  let A := fun v : W₁ ↦
    actionConjugate D.W₁_action data.H₁ v
  pTypeInternalDirectProductMulChar A data.conjugates_direct
    (fun v ↦ pTypeActionConjugateMulChar D data.H₁ v
      (pTypeNonGaloisTwoCoordinateFamily data w lambda v))

@[simp]
theorem pTypeNonGaloisTwoCoordinateCharacter_apply
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : MulChar data.H₁ ℂ) (h : Hbar) :
    pTypeNonGaloisTwoCoordinateCharacter D data w lambda h =
      pTypeNonGaloisTwoCoordinateMulChar D data w lambda h := by
  simp only [pTypeNonGaloisTwoCoordinateCharacter,
    pTypeNonGaloisCoordinateCharacter,
    pTypeIrreducibleCharacterOfMulChar_apply, MonoidHom.id_apply,
    pTypeNonGaloisTwoCoordinateMulChar]

private theorem pTypeTwoCoordinate_nontrivialMulChar_injective
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

/-- The stabilizer in `U` of the two-coordinate factor character is the
intersection of the pointwise kernels for the selected coordinate and its
`w`-conjugate. -/
theorem pTypeNonGaloisTwoCoordinateCharacter_fixed_iff
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (hw : w ≠ 1)
    (lambda : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1)
    (u : U) :
    (∀ h : Hbar,
        pTypeNonGaloisTwoCoordinateCharacter D data w lambda
            (D.U_action u h) =
          pTypeNonGaloisTwoCoordinateCharacter D data w lambda h) ↔
      u ∈ pointwiseActionKernel D.U_action data.H₁ ⊓
        actionConjugate D.W₁_action_U
          (pointwiseActionKernel D.U_action data.H₁) w := by
  classical
  let family := pTypeNonGaloisTwoCoordinateFamily data w lambda
  let K := pointwiseActionKernel D.U_action data.H₁
  let Kw := actionConjugate D.W₁_action_U K w
  have hWActionInv :
      D.W₁_action_U w⁻¹ = (D.W₁_action_U w).symm := by
    rw [map_inv]
    rfl
  have hlambdaInjective : Function.Injective lambda :=
    pTypeTwoCoordinate_nontrivialMulChar_injective
      (by rw [data.card_H₁]; exact D.p_prime) lambda hlambda
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
    have huK : u ∈ K := by
      rw [mem_pointwiseActionKernel_iff]
      intro h hh
      let x : data.H₁ := ⟨h, hh⟩
      have hcoordinate := congrFun hfamilies (1 : W₁)
      have hvalue := congrArg
        (fun chi : MulChar data.H₁ ℂ ↦ chi x) hcoordinate
      have hvalue' : lambda
          (restrictMulAutHom data.H₁ D.U_action
            data.H₁_normalized u x) = lambda x := by
        simpa only [pTypeNonGaloisUTranslateCoordinateFamily_apply,
          family, pTypeNonGaloisTwoCoordinateFamily_one,
          inv_one, map_one, MulAut.one_apply] using hvalue
      exact congrArg Subtype.val (hlambdaInjective hvalue')
    have huKw : u ∈ Kw := by
      change u ∈ actionConjugate D.W₁_action_U K w
      rw [mem_actionConjugate_iff]
      rw [← hWActionInv]
      rw [mem_pointwiseActionKernel_iff]
      intro h hh
      let x : data.H₁ := ⟨h, hh⟩
      have hcoordinate := congrFun hfamilies w
      have hvalue := congrArg
        (fun chi : MulChar data.H₁ ℂ ↦ chi x) hcoordinate
      have hvalue' : lambda
          (restrictMulAutHom data.H₁ D.U_action
            data.H₁_normalized (D.W₁_action_U w⁻¹ u) x) =
          lambda x := by
        simpa only [pTypeNonGaloisUTranslateCoordinateFamily_apply,
          family, pTypeNonGaloisTwoCoordinateFamily_at_second data hw]
          using hvalue
      exact congrArg Subtype.val (hlambdaInjective hvalue')
    exact ⟨huK, huKw⟩
  · rintro ⟨huK, huKw⟩ h
    have huKw' : D.W₁_action_U w⁻¹ u ∈ K := by
      rw [hWActionInv]
      exact (mem_actionConjugate_iff D.W₁_action_U K w u).mp huKw
    have hfamilies :
        pTypeNonGaloisUTranslateCoordinateFamily D data u family =
          family := by
      funext v
      by_cases hvOne : v = 1
      · subst v
        apply MulChar.ext'
        intro x
        have hfix :=
          (mem_pointwiseActionKernel_iff D.U_action data.H₁ u).mp
            huK (x : Hbar) x.property
        have hrestricted :
            restrictMulAutHom data.H₁ D.U_action
                data.H₁_normalized u x = x := by
          apply Subtype.ext
          exact hfix
        simpa only [pTypeNonGaloisUTranslateCoordinateFamily_apply,
          family, pTypeNonGaloisTwoCoordinateFamily_one,
          inv_one, map_one, MulAut.one_apply] using
            congrArg lambda hrestricted
      · by_cases hvW : v = w
        · subst v
          apply MulChar.ext'
          intro x
          have hfix :=
            (mem_pointwiseActionKernel_iff D.U_action data.H₁
              (D.W₁_action_U w⁻¹ u)).mp
                huKw' (x : Hbar) x.property
          have hrestricted :
              restrictMulAutHom data.H₁ D.U_action
                  data.H₁_normalized (D.W₁_action_U w⁻¹ u) x = x := by
            apply Subtype.ext
            exact hfix
          simpa only [pTypeNonGaloisUTranslateCoordinateFamily_apply,
            family, pTypeNonGaloisTwoCoordinateFamily_at_second data hw]
              using congrArg lambda hrestricted
        · apply MulChar.ext
          intro x
          rw [pTypeNonGaloisUTranslateCoordinateFamily_apply]
          have hfamily : family v = 1 := by
            simpa only [family] using
              pTypeNonGaloisTwoCoordinateFamily_of_ne
                data hvOne hvW lambda
          rw [hfamily]
          let alpha : MulEquiv data.H₁ data.H₁ :=
            restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
              (D.W₁_action_U v⁻¹ u)
          let y : data.H₁ˣ := Units.map alpha.toMonoidHom x
          change (1 : MulChar data.H₁ ℂ) (y : data.H₁) =
            (1 : MulChar data.H₁ ℂ) (x : data.H₁)
          rw [MulChar.one_apply_coe, MulChar.one_apply_coe]
    calc
      pTypeNonGaloisTwoCoordinateCharacter D data w lambda
          (D.U_action u h) =
        pTypeNonGaloisCoordinateCharacter D data
          (pTypeNonGaloisUTranslateCoordinateFamily D data u family) h :=
        (pTypeNonGaloisCoordinateCharacter_U_translate
          D data u family h).symm
      _ = pTypeNonGaloisTwoCoordinateCharacter D data w lambda h := by
        rw [hfamilies]
        rfl

/-! ## The corresponding inertia subgroup in `HU` -/

/-- Pull back the intersection of the two coordinate kernels along the
canonical projection `HU → U`. -/
def pTypeNonGaloisTwoCoordinateInertiaInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) : Subgroup (pTypeHUInMaximal M (derivedWithin M)) :=
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  (K ⊓ actionConjugate D.W₁_action_U K w).comap
    (pTypeNonGaloisHUToUProjection ctx)

instance pTypeNonGaloisTwoCoordinateInertiaInHU_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    (pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w).Normal := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let Kw := actionConjugate D.W₁_action_U K w
  let J := K ⊓ Kw
  have hKw : Kw.Normal := by
    change (K.map (D.W₁_action_U w).toMonoidHom).Normal
    exact Subgroup.Normal.map data.actionKernel_normal
      (D.W₁_action_U w).toMonoidHom
      (D.W₁_action_U w).surjective
  letI : K.Normal := data.actionKernel_normal
  letI : Kw.Normal := hKw
  letI : J.Normal := inferInstance
  exact Subgroup.Normal.comap (inferInstance : J.Normal)
    (pTypeNonGaloisHUToUProjection ctx)

/-- The nested Fitting subgroup is contained in every two-coordinate
inertia pullback. -/
theorem pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    H ≤ pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let K := pointwiseActionKernel D.U_action data.H₁
  change H ≤ pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  intro h hh
  change pi (h : HU) ∈ K ⊓ actionConjugate D.W₁_action_U K w
  have hhKer : (h : HU) ∈
      (pTypeNonGaloisHUToUProjection ctx).ker := by
    rw [pTypeNonGaloisHUToUProjection_ker ctx]
    exact hh
  have hhOne : pi (h : HU) = 1 := by
    change pTypeNonGaloisHUToUProjection ctx (h : HU) = 1
    exact MonoidHom.mem_ker.mp hhKer
  rw [hhOne]
  exact Subgroup.one_mem _

/-- The index of the inertia pullback is the index of the kernel
intersection in `U`. -/
theorem pTypeNonGaloisTwoCoordinateInertiaInHU_index
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let D := Ptype_factor_action ctx facts
    let data := typeP_Galois_Pn
      (Ptype_factor_action_hypotheses ctx facts) not_Galois
    let K := pointwiseActionKernel D.U_action data.H₁
    (pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w).index =
      (K ⊓ actionConjugate D.W₁_action_U K w).index := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  exact (K ⊓ actionConjugate D.W₁_action_U K w).index_comap_of_surjective
    (pTypeNonGaloisHUToUProjection_surjective ctx)

/-! ## Inflation to the nested Fitting subgroup -/

/-- Inflate the two-coordinate scalar character through the Fitting-factor
projection. -/
noncomputable def pTypeNonGaloisTwoCoordinateHMonoidHom
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁)
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    H →* ℂ := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  exact (pTypeNonGaloisTwoCoordinateMulChar
    D data w lambda).toMonoidHom.comp
      (pTypeNonGaloisHToFactorProjection ctx)

/-- The inflated two-coordinate irreducible character of the nested Fitting
subgroup. -/
noncomputable def pTypeNonGaloisTwoCoordinateHCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁)
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    IrreducibleCharacter H ℂ :=
  pTypeIrreducibleCharacterOfMonoidHom
    (pTypeNonGaloisTwoCoordinateHMonoidHom
      ctx facts not_Galois w lambda)

@[simp]
theorem pTypeNonGaloisTwoCoordinateHCharacter_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁)
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (h : ((Fitting_core M).subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    pTypeNonGaloisTwoCoordinateHCharacter
        ctx facts not_Galois w lambda h =
      pTypeNonGaloisTwoCoordinateHMonoidHom
        ctx facts not_Galois w lambda h := by
  exact pTypeIrreducibleCharacterOfMonoidHom_apply _ h

/-- On the literal complement `U`, the inflated character is fixed exactly
at the intersection of the two pointwise kernels. -/
theorem pTypeNonGaloisTwoCoordinateHCharacter_normalConjugate_U_fixed_iff
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) (hw : w ≠ 1)
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1)
    (v : (U.subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    let D := Ptype_factor_action ctx facts
    let data := typeP_Galois_Pn
      (Ptype_factor_action_hypotheses ctx facts) not_Galois
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let K := pointwiseActionKernel D.U_action data.H₁
    let u : U := ⟨((v : HU) : M), by
      exact v.property⟩
    ClassFunction.normalConjugate H (v : HU)
        (pTypeNonGaloisTwoCoordinateHCharacter
          ctx facts not_Galois w lambda : ClassFunction H ℂ) =
      (pTypeNonGaloisTwoCoordinateHCharacter
        ctx facts not_Galois w lambda : ClassFunction H ℂ) ↔
      u ∈ K ⊓ actionConjugate D.W₁_action_U K w := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let theta : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisTwoCoordinateHCharacter
      ctx facts not_Galois w lambda
  let u : U := ⟨((v : HU) : M), by
    exact v.property⟩
  let K := pointwiseActionKernel D.U_action data.H₁
  let J := K ⊓ actionConjugate D.W₁_action_U K w
  have hprojInv : ∀ h : H,
      pTypeNonGaloisHToFactorProjection ctx
          (MulAut.conjNormal ((v : HU)⁻¹) h) =
        D.U_action u⁻¹ (pTypeNonGaloisHToFactorProjection ctx h) := by
    intro h
    let vinv : UHU := v⁻¹
    let uinv : U := ⟨((vinv : HU) : M), by
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
        pTypeNonGaloisTwoCoordinateCharacter D data w lambda
            (D.U_action u⁻¹ z) =
          pTypeNonGaloisTwoCoordinateCharacter D data w lambda z := by
      intro z
      obtain ⟨h, rfl⟩ := pTypeNonGaloisHToFactorProjection_surjective ctx z
      have hvalue := congrArg (fun f : ClassFunction H ℂ ↦ f h) hfixed
      rw [ClassFunction.normalConjugate_apply] at hvalue
      have harg : (MulAut.conjNormal (v : HU)).symm h =
          MulAut.conjNormal ((v : HU)⁻¹) h := by
        apply Subtype.ext
        rfl
      rw [harg, pTypeNonGaloisTwoCoordinateHCharacter_apply,
        pTypeNonGaloisTwoCoordinateHCharacter_apply] at hvalue
      change pTypeNonGaloisTwoCoordinateMulChar D data w lambda
          (pTypeNonGaloisHToFactorProjection ctx
            (MulAut.conjNormal ((v : HU)⁻¹) h)) =
        pTypeNonGaloisTwoCoordinateMulChar D data w lambda
          (pTypeNonGaloisHToFactorProjection ctx h) at hvalue
      rw [hprojInv] at hvalue
      simpa only [pTypeNonGaloisTwoCoordinateCharacter_apply]
        using hvalue
    have huInv : u⁻¹ ∈ J :=
      (pTypeNonGaloisTwoCoordinateCharacter_fixed_iff
        D data w hw lambda hlambda u⁻¹).mp hfactorFixed
    simpa only [J, inv_inv] using J.inv_mem huInv
  · intro hu
    have huInv : u⁻¹ ∈ J := J.inv_mem hu
    have hfactorFixed :=
      (pTypeNonGaloisTwoCoordinateCharacter_fixed_iff
        D data w hw lambda hlambda u⁻¹).mpr huInv
    ext h
    rw [ClassFunction.normalConjugate_apply]
    have harg : (MulAut.conjNormal (v : HU)).symm h =
        MulAut.conjNormal ((v : HU)⁻¹) h := by
      apply Subtype.ext
      rfl
    rw [harg, pTypeNonGaloisTwoCoordinateHCharacter_apply,
      pTypeNonGaloisTwoCoordinateHCharacter_apply]
    change pTypeNonGaloisTwoCoordinateMulChar D data w lambda
        (pTypeNonGaloisHToFactorProjection ctx
          (MulAut.conjNormal ((v : HU)⁻¹) h)) =
      pTypeNonGaloisTwoCoordinateMulChar D data w lambda
        (pTypeNonGaloisHToFactorProjection ctx h)
    rw [hprojInv]
    simpa only [pTypeNonGaloisTwoCoordinateCharacter_apply] using
      hfactorFixed (pTypeNonGaloisHToFactorProjection ctx h)

/-- The inertia of the inflated two-coordinate character in `HU` is exactly
the canonical pullback of the two coordinate kernels. -/
theorem pTypeNonGaloisTwoCoordinateHCharacter_inertia
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) (hw : w ≠ 1)
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    ClassFunction.inertia H
        (pTypeNonGaloisTwoCoordinateHCharacter
          ctx facts not_Galois w lambda : ClassFunction H ℂ) =
      pTypeNonGaloisTwoCoordinateInertiaInHU
        ctx facts not_Galois w := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let theta : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisTwoCoordinateHCharacter
      ctx facts not_Galois w lambda
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let K := pointwiseActionKernel D.U_action data.H₁
  let J := K ⊓ actionConjugate D.W₁_action_U K w
  have hcomp : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  ext x
  obtain ⟨⟨n, v⟩, hnv⟩ := hcomp.2 x
  change (n : HU) * (v : HU) = x at hnv
  let u : U := ⟨((v : HU) : M), by
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
    have huJ : u ∈ J :=
      (pTypeNonGaloisTwoCoordinateHCharacter_normalConjugate_U_fixed_iff
        ctx facts not_Galois w hw lambda hlambda v).mp hvFixed
    change pi x ∈ J
    simpa only [hxProj] using huJ
  · intro hx
    have huJ : u ∈ J := by
      change pi x ∈ J at hx
      simpa only [hxProj] using hx
    have hvFixed : ClassFunction.normalConjugate H (v : HU)
        (theta : ClassFunction H ℂ) = (theta : ClassFunction H ℂ) :=
      (pTypeNonGaloisTwoCoordinateHCharacter_normalConjugate_U_fixed_iff
        ctx facts not_Galois w hw lambda hlambda v).mpr huJ
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

end PTypeNonGaloisTwoCoordinateCoreInternal

end

end Submission.OddOrder.PF
