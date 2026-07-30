import Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaCore

/-!
# Peterfalvi Section 9: inertia extensions in the non-Galois case

Building on the exact-inertia calculation, this phase chooses a normalized
linear extension of the selected coordinate and constructs the quotient-twist
family used in clause (d).  Declarations needed by the induction phases are
collected in a module-specific internal namespace.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15

universe u

local instance (priority := 10) pTypeInertiaExtensionsFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisInertiaExtensionsInternal

open PTypeNonGaloisSelectedCoordinateInternal
open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisInertiaCoreInternal
open internal

local instance pTypeNonGaloisFCoreFactor_commutative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsMulCommutative (ptypeFCoreFactor ctx) :=
  (ptypeFCoreFactor_elementary ctx).commutative

theorem pTypeNontrivialMulCharSubtype_ne_one
    {Q : Type u} [Group Q] [Finite Q] [IsMulCommutative Q]
    (lambda : ↑(pTypeNontrivialMulChars Q)) :
    (lambda : MulChar Q ℂ) ≠ 1 :=
  (mem_pTypeNontrivialMulChars (lambda : MulChar Q ℂ)).mp
    lambda.property

/-- The subgroup `H₀U'` is contained in the selected inertia group. -/
theorem pTypeNonGaloisH0DerivedComplement_le_H1InertiaInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeH0DerivedComplementInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U ≤
      pTypeNonGaloisH1InertiaInHU ctx facts not_Galois := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let K := pointwiseActionKernel D.U_action data.H₁
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  apply sup_le
  · exact (Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Ptype_Fcore_kernel_lt ctx).le)).trans
          (pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois)
  · intro x hx
    change ((x : HU) : M) ∈
      pTypeDerivedComplementInMaximal (U.subgroupOf M).subtype at hx
    rw [← pTypeDerivedComplementInMaximal_eq_subgroupOf hUM] at hx
    rcases hx with ⟨u, hu, hux⟩
    let v : (U.subgroupOf M).subgroupOf HU := ⟨x, by
      change ((x : HU) : M) ∈ U.subgroupOf M
      change ((x : HU) : Gamma) ∈ U
      rw [← congrArg Subtype.val hux]
      exact u.property⟩
    let ux : U := ⟨((v : HU) : M), by
      change (((v : HU) : M) : Gamma) ∈ U
      exact v.property⟩
    have huxEq : ux = u := by
      apply Subtype.ext
      exact (congrArg Subtype.val hux).symm
    have hpi : pi x = ux := by
      exact pTypeNonGaloisHUToUProjection_apply_complement ctx v
    change pi x ∈ K
    rw [hpi, huxEq]
    exact pTypeDerived_le_nonGaloisActionKernel hD not_Galois hu

/-! ## Quotient projection used by the twist family -/

/-- Projection from `H ⋊ K` onto `K`. -/
def pTypeNonGaloisH1InertiaToKernelProjection
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let data := typeP_Galois_Pn
      (Ptype_factor_action_hypotheses ctx facts) not_Galois
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    T →* pointwiseActionKernel D.U_action data.H₁ := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  exact
    { toFun := fun t ↦ ⟨pi (t : HU), t.property⟩
      map_one' := by
        apply Subtype.ext
        exact map_one pi
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul pi (x : HU) (y : HU) }

theorem pTypeNonGaloisH1InertiaToKernelProjection_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Function.Surjective
      (pTypeNonGaloisH1InertiaToKernelProjection ctx facts not_Galois) := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  intro k
  obtain ⟨x, hx⟩ := pTypeNonGaloisHUToUProjection_surjective ctx k
  let t : T := ⟨x, by
    change pi x ∈ K
    rw [hx]
    exact k.property⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  exact hx

theorem pTypeNonGaloisH1InertiaToKernelProjection_ker
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    (pTypeNonGaloisH1InertiaToKernelProjection
      ctx facts not_Galois).ker = H.subgroupOf T := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  ext t
  constructor
  · intro ht
    have hpi : pi (t : HU) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
    change (t : HU) ∈
      ((Fitting_core M).subgroupOf M).subgroupOf HU
    rw [← pTypeNonGaloisHUToUProjection_ker ctx]
    exact MonoidHom.mem_ker.mpr hpi
  · intro ht
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    have htKer : (t : HU) ∈
        (pTypeNonGaloisHUToUProjection ctx).ker := by
      rw [pTypeNonGaloisHUToUProjection_ker ctx]
      exact ht
    exact MonoidHom.mem_ker.mp htKer

/-- The abelian quotient `K/U'` parametrizing the twists. -/
abbrev PTypeNonGaloisInertiaTwistQuotient
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :=
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  K ⧸ (_root_.commutator U).subgroupOf K

/-- Quotient the inertia projection further by `U'`. -/
noncomputable def pTypeNonGaloisH1InertiaTwistProjection
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeNonGaloisH1InertiaInHU ctx facts not_Galois →*
      PTypeNonGaloisInertiaTwistQuotient ctx facts not_Galois := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  exact (QuotientGroup.mk' ((_root_.commutator U).subgroupOf K)).comp
    (pTypeNonGaloisH1InertiaToKernelProjection ctx facts not_Galois)

theorem pTypeNonGaloisH1InertiaTwistProjection_surjective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Function.Surjective
      (pTypeNonGaloisH1InertiaTwistProjection ctx facts not_Galois) := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  exact (QuotientGroup.mk'_surjective
    ((_root_.commutator U).subgroupOf K)).comp
      (pTypeNonGaloisH1InertiaToKernelProjection_surjective
        ctx facts not_Galois)

instance pTypeNonGaloisInertiaTwistQuotient_commutative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    IsMulCommutative
      (PTypeNonGaloisInertiaTwistQuotient ctx facts not_Galois) := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let U' := _root_.commutator U
  let U'K := U'.subgroupOf K
  letI : U'K.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : U'.Normal) K
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  have hmap : (_root_.commutator K).map K.subtype ≤ U' := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  intro x hx
  change ((x : K) : U) ∈ U'
  exact hmap ⟨x, hx, rfl⟩

/-! ## Linear characters from scalar homomorphisms -/

/-- The one-dimensional representation attached to a scalar homomorphism. -/
def pTypeScalarMonoidHomRepresentation
    {T : Type u} [Group T] (omega : T →* ℂ) :
    Representation ℂ T ℂ where
  toFun t := omega t • LinearMap.id
  map_one' := by
    ext z
    simp
  map_mul' x y := by
    ext z
    simp only [map_mul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      Module.End.mul_apply]
    ring

@[simp]
theorem pTypeScalarMonoidHomRepresentation_character
    {T : Type u} [Group T] [Fintype T]
    (omega : T →* ℂ) (t : T) :
    (FDRep.of (pTypeScalarMonoidHomRepresentation omega)).character t =
      omega t := by
  change LinearMap.trace ℂ ℂ (omega t • LinearMap.id) = omega t
  rw [map_smul, LinearMap.trace_id]
  simp

/-- A scalar homomorphism regarded as an irreducible linear character. -/
noncomputable def pTypeIrreducibleCharacterOfMonoidHom
    {T : Type u} [Group T] [Fintype T]
    (omega : T →* ℂ) : IrreducibleCharacter T ℂ := by
  let rho : Representation ℂ T ℂ :=
    pTypeScalarMonoidHomRepresentation omega
  letI : Representation.IsIrreducible rho :=
    { toNontrivial := by
        refine ⟨⊥, ⊤, ?_⟩
        intro h
        have hone : (1 : ℂ) ∈ (⊥ : Subrepresentation rho) := by
          rw [h]
          trivial
        change (1 : ℂ) = 0 at hone
        exact one_ne_zero hone
      eq_bot_or_eq_top := by
        intro V
        rcases eq_bot_or_eq_top V.toSubmodule with hV | hV
        · left
          apply Subrepresentation.toSubmodule_injective
          exact hV
        · right
          apply Subrepresentation.toSubmodule_injective
          exact hV }
  let V : FDRep ℂ T := FDRep.of rho
  letI : CategoryTheory.Simple V := simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep V

@[simp]
theorem pTypeIrreducibleCharacterOfMonoidHom_apply
    {T : Type u} [Group T] [Fintype T]
    (omega : T →* ℂ) (t : T) :
    pTypeIrreducibleCharacterOfMonoidHom omega t = omega t := by
  change (FDRep.of
    (pTypeScalarMonoidHomRepresentation omega)).character t = omega t
  exact pTypeScalarMonoidHomRepresentation_character omega t

@[simp]
theorem pTypeIrreducibleCharacterOfMonoidHom_degree
    {T : Type u} [Group T] [Fintype T]
    (omega : T →* ℂ) :
    Module.finrank ℂ
      (pTypeIrreducibleCharacterOfMonoidHom omega).representation = 1 := by
  apply Nat.cast_injective (R := ℂ)
  rw [← IrreducibleCharacter.apply_one_eq_finrank]
  simp

theorem pTypeIrreducibleCharacterOfMonoidHom_apply_ne_zero
    {T : Type u} [Group T] [Fintype T]
    (omega : T →* ℂ) (t : T) :
    pTypeIrreducibleCharacterOfMonoidHom omega t ≠ 0 := by
  rw [pTypeIrreducibleCharacterOfMonoidHom_apply]
  exact (IsUnit.map omega (Group.isUnit t)).ne_zero

/-- Extend an invariant scalar character across an internal semidirect
product, taking value one on the complement. -/
noncomputable def pTypeSemidirectScalarExtension
    {G : Type u} [Group G]
    {HN HC : Subgroup G} [HN.Normal]
    (hcomp : HN.IsComplement' HC)
    (theta : HN →* ℂ)
    (htheta : ∀ c : HC,
      theta.comp
          ((HN.normalizerMonoidHom.comp
            (Subgroup.inclusion
              (HN.normalizer_eq_top ▸ le_top))) c).toMonoidHom = theta) :
    G →* ℂ := by
  let phi : HC →* MulAut HN := HN.normalizerMonoidHom.comp
    (Subgroup.inclusion (HN.normalizer_eq_top ▸ le_top))
  let thetaU : HN →* ℂˣ := theta.toHomUnits
  have hthetaU : ∀ c : HC,
      thetaU.comp (phi c).toMonoidHom =
        (MulAut.conj ((1 : HC →* ℂˣ) c)).toMonoidHom.comp thetaU := by
    intro c
    ext n
    have hvalue := congrArg (fun f : HN →* ℂ ↦ f n) (htheta c)
    simpa only [MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
      MonoidHom.one_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      one_mul, inv_one, mul_one, thetaU, phi] using hvalue
  let liftU : G →* ℂˣ :=
    (SemidirectProduct.lift thetaU (1 : HC →* ℂˣ) hthetaU).comp
      (SemidirectProduct.mulEquivSubgroup hcomp).symm.toMonoidHom
  exact (Units.coeHom ℂ).comp liftU

@[simp]
theorem pTypeSemidirectScalarExtension_apply_left
    {G : Type u} [Group G]
    {HN HC : Subgroup G} [HN.Normal]
    (hcomp : HN.IsComplement' HC)
    (theta : HN →* ℂ)
    (htheta : ∀ c : HC,
      theta.comp
          ((HN.normalizerMonoidHom.comp
            (Subgroup.inclusion
              (HN.normalizer_eq_top ▸ le_top))) c).toMonoidHom = theta)
    (n : HN) :
    pTypeSemidirectScalarExtension hcomp theta htheta (n : G) =
      theta n := by
  let e := SemidirectProduct.mulEquivSubgroup hcomp
  have heInl : e (SemidirectProduct.inl n) = (n : G) := by
    simp [e, SemidirectProduct.mulEquivSubgroup,
      SemidirectProduct.monoidHomSubgroup]
  have heSymm : e.symm (n : G) = SemidirectProduct.inl n := by
    apply e.injective
    rw [e.apply_symm_apply, heInl]
  simp [pTypeSemidirectScalarExtension, e, heSymm]

@[simp]
theorem pTypeSemidirectScalarExtension_apply_right
    {G : Type u} [Group G]
    {HN HC : Subgroup G} [HN.Normal]
    (hcomp : HN.IsComplement' HC)
    (theta : HN →* ℂ)
    (htheta : ∀ c : HC,
      theta.comp
          ((HN.normalizerMonoidHom.comp
            (Subgroup.inclusion
              (HN.normalizer_eq_top ▸ le_top))) c).toMonoidHom = theta)
    (c : HC) :
    pTypeSemidirectScalarExtension hcomp theta htheta (c : G) = 1 := by
  let e := SemidirectProduct.mulEquivSubgroup hcomp
  have heInr : e (SemidirectProduct.inr c) = (c : G) := by
    simp [e, SemidirectProduct.mulEquivSubgroup,
      SemidirectProduct.monoidHomSubgroup]
  have heSymm : e.symm (c : G) = SemidirectProduct.inr c := by
    apply e.injective
    rw [e.apply_symm_apply, heInr]
  simp [pTypeSemidirectScalarExtension, e, heSymm]

/-! ## A normalized extension to the selected inertia group -/

/-- The scalar homomorphism underlying the inflated selected character. -/
noncomputable def pTypeNonGaloisSingleHMonoidHom
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
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
  exact (pTypeNonGaloisSingleCoordinateMulChar
    D data lambda).toMonoidHom.comp
      (pTypeNonGaloisHToFactorProjection ctx)

@[simp]
theorem pTypeNonGaloisSingleHMonoidHom_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (h : ((Fitting_core M).subgroupOf M).subgroupOf
      (pTypeHUInMaximal M (derivedWithin M))) :
    pTypeNonGaloisSingleHMonoidHom ctx facts not_Galois lambda h =
      pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda h :=
  (pTypeNonGaloisSingleHCharacter_apply
    ctx facts not_Galois lambda h).symm

/-- The selected character extends to `H ⋊ K` and can be normalized to
take value one on the canonical complement. -/
theorem pTypeNonGaloisSingleHExtensionMonoidHom_exists
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let UHU := (U.subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    let hHT : H ≤ T :=
      pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois
    let HT := H.subgroupOf T
    let KT := (UHU ⊓ T).subgroupOf T
    ∃ omega : T →* ℂ,
      (∀ h : HT,
        omega (h : T) =
          pTypeNonGaloisSingleHMonoidHom
            ctx facts not_Galois lambda
              (Subgroup.subgroupOfEquivOfLe hHT h)) ∧
      (∀ k : KT, omega (k : T) = 1) := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois
  let HT := H.subgroupOf T
  let KT := (UHU ⊓ T).subgroupOf T
  letI : HT.Normal :=
    Subgroup.Normal.subgroupOf (pTypeNonGaloisHInHU_normal (M := M)) T
  have hcompHU : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  have hcompT : HT.IsComplement' KT :=
    internal.pTypeIsComplement_subgroupOf_of_left_le hcompHU hHT
  let phi : KT →* MulAut HT :=
    HT.normalizerMonoidHom.comp
      (Subgroup.inclusion (HT.normalizer_eq_top ▸ le_top))
  let thetaH : H →* ℂ :=
    pTypeNonGaloisSingleHMonoidHom ctx facts not_Galois lambda
  let thetaT : HT →* ℂ :=
    thetaH.comp (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
  have hthetaInv : ∀ k : KT,
      thetaT.comp (phi k).toMonoidHom = thetaT := by
    intro k
    ext h
    let v : UHU := ⟨((k : T) : HU), k.property.1⟩
    let u : U := ⟨((v : HU) : M), by
      change (((v : HU) : M) : Gamma) ∈ U
      exact v.property⟩
    have huK : u ∈ K := by
      have hk := (k : T).property
      change pTypeNonGaloisHUToUProjection ctx (v : HU) ∈ K at hk
      rw [pTypeNonGaloisHUToUProjection_apply_complement ctx v] at hk
      exact hk
    have hfactorFixed :=
      (pTypeNonGaloisSingleCoordinateCharacter_fixed_iff
        D data lambda hlambda u).mpr huK
    have hproj := pTypeNonGaloisHToFactorProjection_conj_U
      ctx facts v (Subgroup.subgroupOfEquivOfLe hHT h)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      thetaT, thetaH]
    change pTypeNonGaloisSingleCoordinateMulChar D data lambda
        (pTypeNonGaloisHToFactorProjection ctx
          (Subgroup.subgroupOfEquivOfLe hHT (phi k h))) =
      pTypeNonGaloisSingleCoordinateMulChar D data lambda
        (pTypeNonGaloisHToFactorProjection ctx
          (Subgroup.subgroupOfEquivOfLe hHT h))
    rw [show Subgroup.subgroupOfEquivOfLe hHT (phi k h) =
        MulAut.conjNormal (v : HU)
          (Subgroup.subgroupOfEquivOfLe hHT h) by
      apply Subtype.ext
      rfl,
      hproj]
    simpa only [pTypeNonGaloisSingleCoordinateCharacter_apply] using
      hfactorFixed
        (pTypeNonGaloisHToFactorProjection ctx
          (Subgroup.subgroupOfEquivOfLe hHT h))
  refine ⟨pTypeSemidirectScalarExtension hcompT thetaT hthetaInv, ?_, ?_⟩
  · intro h
    exact pTypeSemidirectScalarExtension_apply_left
      hcompT thetaT hthetaInv h
  · intro k
    exact pTypeSemidirectScalarExtension_apply_right
      hcompT thetaT hthetaInv k

/-- The chosen normalized extension homomorphism. -/
noncomputable def pTypeNonGaloisSingleHExtensionMonoidHom
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    pTypeNonGaloisH1InertiaInHU ctx facts not_Galois →* ℂ :=
  Classical.choose
    (pTypeNonGaloisSingleHExtensionMonoidHom_exists
      ctx facts not_Galois lambda hlambda)

@[simp]
theorem pTypeNonGaloisSingleHExtensionMonoidHom_apply_H
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1)
    (h : let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
      H.subgroupOf T) :
    pTypeNonGaloisSingleHExtensionMonoidHom
        ctx facts not_Galois lambda hlambda h =
      pTypeNonGaloisSingleHMonoidHom
        ctx facts not_Galois lambda
          (Subgroup.subgroupOfEquivOfLe
            (pTypeNonGaloisH_le_H1InertiaInHU
              ctx facts not_Galois) h) :=
  (Classical.choose_spec
    (pTypeNonGaloisSingleHExtensionMonoidHom_exists
      ctx facts not_Galois lambda hlambda)).1 h

@[simp]
theorem pTypeNonGaloisSingleHExtensionMonoidHom_apply_K
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1)
    (k : let HU := pTypeHUInMaximal M (derivedWithin M)
      let UHU := (U.subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
      (UHU ⊓ T).subgroupOf T) :
    pTypeNonGaloisSingleHExtensionMonoidHom
        ctx facts not_Galois lambda hlambda k = 1 :=
  (Classical.choose_spec
    (pTypeNonGaloisSingleHExtensionMonoidHom_exists
      ctx facts not_Galois lambda hlambda)).2 k

/-- The normalized extension as an irreducible linear character. -/
noncomputable def pTypeNonGaloisSingleHCharacterExtension
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    IrreducibleCharacter
      (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois) ℂ :=
  pTypeIrreducibleCharacterOfMonoidHom
    (pTypeNonGaloisSingleHExtensionMonoidHom
      ctx facts not_Galois lambda hlambda)

theorem pTypeNonGaloisSingleHCharacterExtension_degree
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    Module.finrank ℂ
      (pTypeNonGaloisSingleHCharacterExtension
        ctx facts not_Galois lambda hlambda).representation = 1 :=
  pTypeIrreducibleCharacterOfMonoidHom_degree
    (pTypeNonGaloisSingleHExtensionMonoidHom
      ctx facts not_Galois lambda hlambda)

/-! ## Restriction and quotient twists -/

/-- Transport the selected F-core character to its copy inside `T`. -/
noncomputable def pTypeNonGaloisSingleHCharacterInInertia
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    IrreducibleCharacter (H.subgroupOf T) ℂ := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois
  exact pTypeIrreducibleCharacterOfMonoidHom
    ((pTypeNonGaloisSingleHMonoidHom
      ctx facts not_Galois lambda).comp
        (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom)

@[simp]
theorem pTypeNonGaloisSingleHCharacterInInertia_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (h : let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
      H.subgroupOf T) :
    pTypeNonGaloisSingleHCharacterInInertia
        ctx facts not_Galois lambda h =
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois lambda
        (Subgroup.subgroupOfEquivOfLe
          (pTypeNonGaloisH_le_H1InertiaInHU
            ctx facts not_Galois) h) := by
  rw [pTypeNonGaloisSingleHCharacterInInertia,
    pTypeIrreducibleCharacterOfMonoidHom_apply,
    MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    pTypeNonGaloisSingleHMonoidHom_apply]

/-- The normalized extension restricts to the selected F-core character. -/
theorem pTypeNonGaloisSingleHCharacterExtension_restrict
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (lambda : MulChar
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁ ℂ)
    (hlambda : lambda ≠ 1) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    let HT := H.subgroupOf T
    ClassFunction.restrict HT
        (pTypeNonGaloisSingleHCharacterExtension
          ctx facts not_Galois lambda hlambda : ClassFunction T ℂ) =
      (pTypeNonGaloisSingleHCharacterInInertia
        ctx facts not_Galois lambda : ClassFunction HT ℂ) := by
  ext h
  rw [ClassFunction.restrict_apply,
    pTypeNonGaloisSingleHCharacterExtension,
    pTypeIrreducibleCharacterOfMonoidHom_apply,
    pTypeNonGaloisSingleHExtensionMonoidHom_apply_H,
    pTypeNonGaloisSingleHMonoidHom_apply,
    pTypeNonGaloisSingleHCharacterInInertia_apply]

/-- Inflation from the chief factor is injective. -/
theorem pTypeNonGaloisSingleHCharacter_injective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Function.Injective
      (pTypeNonGaloisSingleHCharacter ctx facts not_Galois) := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  intro lambda mu hlm
  apply pTypeNonGaloisSingleCoordinateCharacter_injective D data
  ext z
  obtain ⟨h, hh⟩ := pTypeNonGaloisHToFactorProjection_surjective ctx z
  have hvalue := congrArg
    (fun chi : IrreducibleCharacter H ℂ ↦ chi h) hlm
  simpa only [pTypeNonGaloisSingleHCharacter_apply,
    pTypeNonGaloisSingleCoordinateCharacter_apply, hh] using hvalue

/-- A nonprincipal selected factor character and a scalar character of
`K/U'` form an index for the twist family. -/
abbrev PTypeNonGaloisInertiaTwistIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :=
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  ↑(pTypeNontrivialMulChars data.H₁) ×
    MulChar
      (PTypeNonGaloisInertiaTwistQuotient ctx facts not_Galois) ℂ

/-- The scalar homomorphism associated to a twist index. -/
noncomputable def pTypeNonGaloisInertiaTwistMonoidHomFromIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois →
      pTypeNonGaloisH1InertiaInHU ctx facts not_Galois →* ℂ := by
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  intro i
  let hlambda : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  exact (i.2.toMonoidHom.comp
      (pTypeNonGaloisH1InertiaTwistProjection ctx facts not_Galois)) *
    pTypeNonGaloisSingleHExtensionMonoidHom
      ctx facts not_Galois i.1 hlambda

/-- The irreducible linear character associated to a twist index. -/
noncomputable def pTypeNonGaloisInertiaTwistCharacterFromIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois →
      IrreducibleCharacter
        (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois) ℂ :=
  fun i ↦ pTypeIrreducibleCharacterOfMonoidHom
    (pTypeNonGaloisInertiaTwistMonoidHomFromIndex
      ctx facts not_Galois i)

@[simp]
theorem pTypeNonGaloisInertiaTwistCharacterFromIndex_apply
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois)
    (t : pTypeNonGaloisH1InertiaInHU ctx facts not_Galois) :
    pTypeNonGaloisInertiaTwistCharacterFromIndex
        ctx facts not_Galois i t =
      i.2 (pTypeNonGaloisH1InertiaTwistProjection
        ctx facts not_Galois t) *
      pTypeNonGaloisSingleHCharacterExtension
        ctx facts not_Galois i.1
        (pTypeNontrivialMulCharSubtype_ne_one i.1) t := by
  rw [pTypeNonGaloisInertiaTwistCharacterFromIndex,
    pTypeIrreducibleCharacterOfMonoidHom_apply,
    pTypeNonGaloisSingleHCharacterExtension,
    pTypeIrreducibleCharacterOfMonoidHom_apply]
  rfl

/-- Distinct twist indices give distinct inertia characters. -/
theorem pTypeNonGaloisInertiaTwistCharacterFromIndex_injective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Function.Injective
      (pTypeNonGaloisInertiaTwistCharacterFromIndex
        ctx facts not_Galois) := by
  classical
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let HT := H.subgroupOf T
  intro i j hij
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  let hj : (j.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one j.1
  have hqH : ∀ h : HT,
      pTypeNonGaloisH1InertiaTwistProjection
        ctx facts not_Galois (h : T) = 1 := by
    intro h
    rw [pTypeNonGaloisH1InertiaTwistProjection,
      MonoidHom.comp_apply]
    have hker : (h : T) ∈
        (pTypeNonGaloisH1InertiaToKernelProjection
          ctx facts not_Galois).ker := by
      rw [pTypeNonGaloisH1InertiaToKernelProjection_ker
        ctx facts not_Galois]
      exact h.property
    rw [MonoidHom.mem_ker.mp hker, map_one]
  have hbaseOnH : ∀ h : HT,
      pTypeNonGaloisSingleHCharacterExtension
          ctx facts not_Galois i.1 hi (h : T) =
        pTypeNonGaloisSingleHCharacterExtension
          ctx facts not_Galois j.1 hj (h : T) := by
    intro h
    have hvalue := congrArg
      (fun chi : IrreducibleCharacter T ℂ ↦ chi (h : T)) hij
    simpa only [pTypeNonGaloisInertiaTwistCharacterFromIndex_apply,
      hqH h, map_one, one_mul] using hvalue
  have hthetaT :
      pTypeNonGaloisSingleHCharacterInInertia
          ctx facts not_Galois i.1 =
        pTypeNonGaloisSingleHCharacterInInertia
          ctx facts not_Galois j.1 := by
    ext h
    have hri := congrArg (fun f : ClassFunction HT ℂ ↦ f h)
      (pTypeNonGaloisSingleHCharacterExtension_restrict
        ctx facts not_Galois i.1 hi)
    have hrj := congrArg (fun f : ClassFunction HT ℂ ↦ f h)
      (pTypeNonGaloisSingleHCharacterExtension_restrict
        ctx facts not_Galois j.1 hj)
    simpa only [ClassFunction.restrict_apply] using
      hri.symm.trans ((hbaseOnH h).trans hrj)
  have htheta :
      pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois i.1 =
        pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois j.1 := by
    ext h
    let hHT := pTypeNonGaloisH_le_H1InertiaInHU
      ctx facts not_Galois
    let e : HT ≃* H := Subgroup.subgroupOfEquivOfLe hHT
    let hT : HT := e.symm h
    have hvalue := congrArg
      (fun chi : IrreducibleCharacter HT ℂ ↦ chi hT) hthetaT
    simpa only [pTypeNonGaloisSingleHCharacterInInertia_apply,
      e, hT, MulEquiv.apply_symm_apply] using hvalue
  have hi1 : i.1 = j.1 := by
    apply Subtype.ext
    exact pTypeNonGaloisSingleHCharacter_injective
      ctx facts not_Galois htheta
  have hi2 : i.2 = j.2 := by
    ext z
    obtain ⟨t, ht⟩ :=
      pTypeNonGaloisH1InertiaTwistProjection_surjective
        ctx facts not_Galois z
    have hvalue := congrArg
      (fun chi : IrreducibleCharacter T ℂ ↦ chi t) hij
    rw [pTypeNonGaloisInertiaTwistCharacterFromIndex_apply,
      pTypeNonGaloisInertiaTwistCharacterFromIndex_apply, ht] at hvalue
    rw [hi1] at hvalue
    have hne : pTypeNonGaloisSingleHCharacterExtension
        ctx facts not_Galois j.1 hj t ≠ 0 := by
      exact pTypeIrreducibleCharacterOfMonoidHom_apply_ne_zero
        (pTypeNonGaloisSingleHExtensionMonoidHom
          ctx facts not_Galois j.1 hj) t
    exact mul_right_cancel₀ hne hvalue
  exact Prod.ext hi1 hi2

/-- The twist-index source has size `(p - 1) * |K/U'|`. -/
theorem pTypeNonGaloisInertiaTwistIndex_card
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Nat.card (PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) =
      ((Ptype_factor_action ctx facts).p - 1) *
        Nat.card (PTypeNonGaloisInertiaTwistQuotient
          ctx facts not_Galois) := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let Q := PTypeNonGaloisInertiaTwistQuotient ctx facts not_Galois
  have hQcard : Nat.card (MulChar Q ℂ) = Nat.card Q := by
    calc
      Nat.card (MulChar Q ℂ) = Nat.card Qˣ :=
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity Q ℂ
      _ = Nat.card Q := Nat.card_congr toUnits.toEquiv.symm
  rw [Nat.card_prod, natCard_pTypeNontrivialMulChars,
    data.card_H₁, hQcard]

/-- The quotient twist is trivial on the nested F-core. -/
theorem pTypeNonGaloisH1InertiaTwistProjection_apply_H
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (h : let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
      H.subgroupOf T) :
    pTypeNonGaloisH1InertiaTwistProjection
        ctx facts not_Galois h = 1 := by
  rw [pTypeNonGaloisH1InertiaTwistProjection, MonoidHom.comp_apply]
  have hker : (h : pTypeNonGaloisH1InertiaInHU
      ctx facts not_Galois) ∈
      (pTypeNonGaloisH1InertiaToKernelProjection
        ctx facts not_Galois).ker := by
    rw [pTypeNonGaloisH1InertiaToKernelProjection_ker
      ctx facts not_Galois]
    exact h.property
  rw [MonoidHom.mem_ker.mp hker, map_one]

/-- Twisting does not change the restriction to the nested F-core. -/
theorem pTypeNonGaloisInertiaTwistCharacterFromIndex_restrict
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    let HT := H.subgroupOf T
    ClassFunction.restrict HT
        (pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois i : ClassFunction T ℂ) =
      (pTypeNonGaloisSingleHCharacterInInertia
        ctx facts not_Galois i.1 : ClassFunction HT ℂ) := by
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let HT := H.subgroupOf T
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  ext h
  rw [ClassFunction.restrict_apply,
    pTypeNonGaloisInertiaTwistCharacterFromIndex_apply,
    pTypeNonGaloisH1InertiaTwistProjection_apply_H,
    map_one, one_mul]
  have hres := congrArg (fun f : ClassFunction HT ℂ ↦ f h)
    (pTypeNonGaloisSingleHCharacterExtension_restrict
      ctx facts not_Galois i.1 hi)
  simpa only [ClassFunction.restrict_apply] using hres

/-- Every quotient twist is linear. -/
theorem pTypeNonGaloisInertiaTwistCharacterFromIndex_degree
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    Module.finrank ℂ
      (pTypeNonGaloisInertiaTwistCharacterFromIndex
        ctx facts not_Galois i).representation = 1 :=
  pTypeIrreducibleCharacterOfMonoidHom_degree
    (pTypeNonGaloisInertiaTwistMonoidHomFromIndex
      ctx facts not_Galois i)

/-! ## Selected orbits -/

/-- The finite family of `HU`-orbits represented by nonprincipal selected
coordinate characters. -/
abbrev PTypeNonGaloisSelectedHOrbitIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :=
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let S : ↑(pTypeNontrivialMulChars data.H₁) →
      IrreducibleCharacter H ℂ := fun lambda ↦
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois
      (lambda : MulChar data.H₁ ℂ)
  {O : Set (IrreducibleCharacter H ℂ) //
    O ∈ (Finset.univ.image fun lambda ↦
      MulAction.orbit HU (S lambda))}

/-- A chosen source character representing a selected orbit. -/
noncomputable def pTypeNonGaloisSelectedHOrbitRepresentative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (O : PTypeNonGaloisSelectedHOrbitIndex ctx facts not_Galois) :
    ↑(pTypeNontrivialMulChars
      (typeP_Galois_Pn
        (Ptype_factor_action_hypotheses ctx facts)
        not_Galois).H₁) :=
  Classical.choose (Finset.mem_image.mp O.property)

theorem pTypeNonGaloisSelectedHOrbitRepresentative_orbit
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (O : PTypeNonGaloisSelectedHOrbitIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    MulAction.orbit HU
        (pTypeNonGaloisSingleHCharacter ctx facts not_Galois
          (pTypeNonGaloisSelectedHOrbitRepresentative
            ctx facts not_Galois O)) = O.1 :=
  (Classical.choose_spec (Finset.mem_image.mp O.property)).2

/-- Each selected orbit has at most the non-Galois index many source
characters. -/
theorem pTypeNonGaloisSelectedHOrbit_card_bound
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    D.p - 1 ≤ pTypeNonGaloisIndex hD not_Galois *
      Nat.card (PTypeNonGaloisSelectedHOrbitIndex
        ctx facts not_Galois) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let L := ↑(pTypeNontrivialMulChars data.H₁)
  let S : L → IrreducibleCharacter H ℂ := fun lambda ↦
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois
      (lambda : MulChar data.H₁ ℂ)
  let O : L → Set (IrreducibleCharacter H ℂ) :=
    fun lambda ↦ MulAction.orbit HU (S lambda)
  let B := PTypeNonGaloisSelectedHOrbitIndex
    ctx facts not_Galois
  have hfiber (lambda₀ : L) :
      {lambda ∈ (Finset.univ : Finset L) |
        O lambda = O lambda₀}.card ≤
        pTypeNonGaloisIndex hD not_Galois := by
    let fiber := {lambda ∈ (Finset.univ : Finset L) |
      O lambda = O lambda₀}
    let toOrbit : {lambda : L // lambda ∈ fiber} →
        MulAction.orbit HU (S lambda₀) := fun lambda ↦
      ⟨S lambda.1, by
        have horbit := (Finset.mem_filter.mp lambda.property).2
        change S lambda.1 ∈ O lambda₀
        rw [← horbit]
        exact MulAction.mem_orbit_self (S lambda.1)⟩
    have hToOrbitInjective : Function.Injective toOrbit := by
      intro lambda mu hlm
      apply Subtype.ext
      apply Subtype.ext
      exact pTypeNonGaloisSingleHCharacter_injective
        ctx facts not_Galois (congrArg Subtype.val hlm)
    have hlambda₀ : (lambda₀ : MulChar data.H₁ ℂ) ≠ 1 :=
      pTypeNontrivialMulCharSubtype_ne_one lambda₀
    have hStabilizer : MulAction.stabilizer HU (S lambda₀) = T :=
      (IrreducibleCharacter.stabilizer_eq_inertia H (S lambda₀)).trans
        (pTypeNonGaloisSingleHCharacter_inertia
          ctx facts not_Galois lambda₀ hlambda₀)
    have hIndexOrbit := MulAction.index_stabilizer HU (S lambda₀)
    rw [hStabilizer] at hIndexOrbit
    have hOrbitCard : Nat.card (MulAction.orbit HU (S lambda₀)) =
        pTypeNonGaloisIndex hD not_Galois := by
      calc
        Nat.card (MulAction.orbit HU (S lambda₀)) = T.index := by
          rw [Nat.card_coe_set_eq]
          exact hIndexOrbit.symm
        _ = pTypeNonGaloisIndex hD not_Galois :=
          pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois
    have hOrbitFinite :
        (MulAction.orbit HU (S lambda₀)).Finite := by
      change (Set.range fun g : HU ↦ g • S lambda₀).Finite
      exact Set.finite_range _
    letI : Finite (MulAction.orbit HU (S lambda₀)) :=
      hOrbitFinite.to_subtype
    calc
      fiber.card = Nat.card {lambda : L // lambda ∈ fiber} := by
        exact (Nat.card_eq_finsetCard fiber).symm
      _ ≤ Nat.card (MulAction.orbit HU (S lambda₀)) :=
        Nat.card_le_card_of_injective toOrbit hToOrbitInjective
      _ = pTypeNonGaloisIndex hD not_Galois := hOrbitCard
  have hcard := Finset.card_le_mul_card_image
    (Finset.univ : Finset L)
    (pTypeNonGaloisIndex hD not_Galois)
      (fun (orbit : Set (IrreducibleCharacter H ℂ)) horbit ↦ by
      obtain ⟨lambda₀, _hlambda₀, rfl⟩ := Finset.mem_image.mp horbit
      exact hfiber lambda₀)
  have hLcard : Nat.card L =
      (Ptype_factor_action ctx facts).p - 1 := by
    simpa only [L, natCard_pTypeNontrivialMulChars,
      data.card_H₁]
  have hBcard : Nat.card B = (Finset.univ.image O).card := by
    change Nat.card {x // x ∈ Finset.univ.image O} =
      (Finset.univ.image O).card
    exact Nat.subtype_card _ (fun _ ↦ Iff.rfl)
  calc
    D.p - 1 = Nat.card L := hLcard.symm
    _ ≤ pTypeNonGaloisIndex hD not_Galois *
        (Finset.univ.image O).card := by
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hcard
    _ = pTypeNonGaloisIndex hD not_Galois * Nat.card B := by
      rw [hBcard]

end PTypeNonGaloisInertiaExtensionsInternal

end

end Submission.OddOrder.PF
