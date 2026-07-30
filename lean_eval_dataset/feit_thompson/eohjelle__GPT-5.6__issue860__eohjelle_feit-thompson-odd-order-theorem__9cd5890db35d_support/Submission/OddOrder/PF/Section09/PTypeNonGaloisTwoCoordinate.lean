import Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinateCore

/-!
# Peterfalvi Section 9: the final two-coordinate character

This module extends the scalar character constructed in
`PTypeNonGaloisTwoCoordinateCore` to its exact inertia subgroup, induces the
extension to `HU`, and places the resulting irreducible character in the core
layer required by Peterfalvi (9.11.2).
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open CategoryTheory

universe u v

local instance (priority := 10) pTypeTwoCoordinateFinalFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisTwoCoordinateInternal

open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisSelectedCoordinateInternal
open PTypeNonGaloisInertiaCoreInternal
open PTypeNonGaloisInertiaExtensionsInternal
open PTypeNonGaloisTwoCoordinateCoreInternal
open internal

local instance pTypeNonGaloisFCoreFactor_commutative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsMulCommutative (ptypeFCoreFactor ctx) :=
  (ptypeFCoreFactor_elementary ctx).commutative

/-! ## Split-universe character-kernel transport -/

/-- The translation kernel of an irreducible character is its realizing
representation kernel, without coupling the group and coefficient universes. -/
private theorem pTypeTwoCoordinate_translationKernel_irreducibleCharacter
    {G : Type u} {k : Type v} [Group G]
    [Field k] [IsAlgClosed k]
    (chi : IrreducibleCharacter G k) :
    ClassFunction.translationKernel (chi : ClassFunction G k) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation k G chi.representation :=
      chi.representation.ρ
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep chi.representation
    have htraceGroup (g : G) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : k[G]) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End k chi.representation) :
        LinearMap.trace k chi.representation ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        Representation.IsIrreducible.asAlgebraHom_surjective rho X
      exact htraceAlgebra z
    have hzero : rho a - 1 = 0 := by
      let b := Module.finBasis k chi.representation
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_zero]
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      have hX := htraceEnd ((LinearMap.toMatrixAlgEquiv b).symm X)
      rw [LinearMap.trace_eq_matrix_trace k b] at hX
      change
        ((LinearMap.toMatrixAlgEquiv b)
            ((rho a - 1) * (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0
        at hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply, Matrix.zero_mul,
        Matrix.trace_zero] using hX
    exact sub_eq_zero.mp hzero
  · intro a ha g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace k chi.representation
        (chi.representation.ρ (a * g)) =
      LinearMap.trace k chi.representation (chi.representation.ρ g)
    rw [chi.representation.ρ.map_mul, MonoidHom.mem_ker.mp ha, one_mul]

private theorem pTypeTwoCoordinate_exists_hom_ne_zero_of_isConstituent
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V, f ≠ 0 := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction G k) =
        (Module.finrank k (chi.representation ⟶ V) : k) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant
        chi.representation V
    have hcharV (g : G) :
        V.character g = _root_.Representation.character V.ρ g := rfl
    simpa only [characterPairing,
      ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character, invOf_eq_inv,
      smul_eq_mul, Fintype.card_eq_nat_card, hcharV] using hhom
  have hcast : (Module.finrank k (chi.representation ⟶ V) : k) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank k (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact Module.finrank_pos_iff_exists_ne_zero.mp
    (Nat.pos_of_ne_zero hfin)

private theorem pTypeTwoCoordinate_fdRep_kernel_le_constituent_kernel
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ :=
    pTypeTwoCoordinate_exists_hom_ne_zero_of_isConstituent V chi hchi
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Mono f := CategoryTheory.mono_of_nonzero_from_simple hf
  let fR := (forget₂ (FDRep k G) (Rep k G)).map f
  have hfR : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp inferInstance
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro x
  apply hfR
  change fR.hom (chi.representation.ρ g x) = fR.hom x
  have hinter :=
    _root_.Representation.IntertwiningMap.isIntertwining
      (ρ := ((forget₂ (FDRep k G) (Rep k G)).obj
        chi.representation).ρ)
      (σ := ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ)
      (f := fR.hom) g x
  change fR.hom (chi.representation.ρ g x) =
    V.ρ g (fR.hom x) at hinter
  have hfix : V.ρ g (fR.hom x) = fR.hom x := by
    rw [MonoidHom.mem_ker.mp hg]
    rfl
  exact hinter.trans hfix

/-- A subgroup acting trivially on an induced irreducible constituent acts
trivially on the inducing constituent after restriction. -/
private theorem pTypeTwoCoordinate_subgroupOf_le_constituent_kernel
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (H A : Subgroup G) (hAH : A ≤ H)
    (chi : IrreducibleCharacter G k)
    (psi : IrreducibleCharacter H k)
    (hchi : chi.IsConstituent
      (ClassFunction.induce H (psi : ClassFunction H k)))
    (hAchi : A ≤ chi.representation.ρ.ker) :
    A.subgroupOf H ≤ psi.representation.ρ.ker := by
  have hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G k)) :=
    (psi.isConstituent_restrict_iff_induce H chi).2 hchi
  let R : FDRep k H :=
    FDRep.of (chi.representation.ρ.comp H.subtype)
  have hcharR : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict H (chi : ClassFunction G k) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  have hpsiR : psi.IsConstituent
      (ClassFunction.ofRepresentation R.ρ) := by
    rwa [hcharR]
  have hkerRpsi : R.ρ.ker ≤ psi.representation.ρ.ker :=
    pTypeTwoCoordinate_fdRep_kernel_le_constituent_kernel R psi hpsiR
  intro h hh
  apply hkerRpsi
  rw [MonoidHom.mem_ker]
  change chi.representation.ρ (h : G) = 1
  exact MonoidHom.mem_ker.mp (hAchi hh)

/-! ## Normality of the explicit source kernel -/

private theorem pTypeTwoCoordinate_derivedComplement_eq_derivedWithin_map
    {Gamma : Type u} [Group Gamma]
    {U : Subgroup Gamma} (C : Subgroup U) :
    pTypeDerivedComplementInMaximal
        (U.subtype.comp C.subtype) =
      derivedWithin (C.map U.subtype) := by
  change (_root_.commutator C).map
      (U.subtype.comp C.subtype) =
    (_root_.commutator (C.map U.subtype)).map
      (C.map U.subtype).subtype
  calc
    (_root_.commutator C).map (U.subtype.comp C.subtype) =
        ((_root_.commutator C).map C.subtype).map U.subtype :=
      (Subgroup.map_map _ _ _).symm
    _ = ⁅C, C⁆.map U.subtype := by
      rw [C.map_subtype_commutator]
    _ = ⁅C.map U.subtype, C.map U.subtype⁆ :=
      Subgroup.map_commutator C C U.subtype
    _ = (_root_.commutator (C.map U.subtype)).map
        (C.map U.subtype).subtype :=
      (C.map U.subtype).map_subtype_commutator.symm

private theorem pTypeTwoCoordinateH0CPrime_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀CPrime := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) ⊔
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    H₀CPrime.Normal := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀a := Ptype_Fcore_kernel ctx
  let Cₐ := Ptype_Fcompl_kernel ctx
  let CₐPrime := derivedWithin Cₐ
  let Kₐ : Subgroup Gamma := H₀a ⊔ CₐPrime
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hH₀der : H₀a ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hCder : Cₐ ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hCₐPrimeDer : CₐPrime ≤ derivedWithin M :=
    (Subgroup.map_subtype_le (_root_.commutator Cₐ)).trans hCder
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hH₀M : H₀a ≤ M := hH₀der.trans hDerM
  have hCₐPrimeM : CₐPrime ≤ M := hCₐPrimeDer.trans hDerM
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hCₐPrimeHU : CₐPrime.subgroupOf M ≤ HU := by
    intro x hx
    exact hCₐPrimeDer hx
  letI : (Kₐ.subgroupOf M).Normal :=
    (Ptype_Fcore_extensions_normal ctx).H₀C'_normal.2
  have hkernelEq :
      pTypeH0InDerived M (derivedWithin M) H₀a ⊔
          ((pTypeDerivedComplementInMaximal
            (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU =
        (Kₐ.subgroupOf M).subgroupOf HU := by
    change (H₀a.subgroupOf M).subgroupOf HU ⊔
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU =
      (Kₐ.subgroupOf M).subgroupOf HU
    have hDC : D.C.map U.subtype = Cₐ := rfl
    rw [pTypeTwoCoordinate_derivedComplement_eq_derivedWithin_map D.C,
      hDC, ← Subgroup.subgroupOf_sup hH₀HU hCₐPrimeHU,
      ← Subgroup.subgroupOf_sup hH₀M hCₐPrimeM]
  change (pTypeH0InDerived M (derivedWithin M) H₀a ⊔
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU).Normal
  rw [hkernelEq]
  exact Subgroup.Normal.subgroupOf
    (inferInstance : (Kₐ.subgroupOf M).Normal) HU

/-! ## A normalized scalar extension to the exact inertia subgroup -/

/-- The two-coordinate scalar character extends to its exact inertia
subgroup, with value one on the canonical complement. -/
theorem pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_exists
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
    let UHU := (U.subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w
    let hHT : H ≤ T :=
      pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
        ctx facts not_Galois w
    let HT := H.subgroupOf T
    let JT := (UHU ⊓ T).subgroupOf T
    ∃ omega : T →* ℂ,
      (∀ h : HT,
        omega (h : T) =
          pTypeNonGaloisTwoCoordinateHMonoidHom
            ctx facts not_Galois w lambda
              (Subgroup.subgroupOfEquivOfLe hHT h)) ∧
      (∀ k : JT, omega (k : T) = 1) := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let J := K ⊓ actionConjugate D.W₁_action_U K w
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  let HT := H.subgroupOf T
  let JT := (UHU ⊓ T).subgroupOf T
  letI : HT.Normal :=
    Subgroup.Normal.subgroupOf (pTypeNonGaloisHInHU_normal (M := M)) T
  have hcompHU : H.IsComplement' UHU :=
    pTypeNonGaloisHInHU_isComplement' ctx
  have hcompT : HT.IsComplement' JT :=
    pTypeIsComplement_subgroupOf_of_left_le hcompHU hHT
  let phi : JT →* MulAut HT :=
    HT.normalizerMonoidHom.comp
      (Subgroup.inclusion (HT.normalizer_eq_top ▸ le_top))
  let thetaH : H →* ℂ :=
    pTypeNonGaloisTwoCoordinateHMonoidHom
      ctx facts not_Galois w lambda
  let thetaT : HT →* ℂ :=
    thetaH.comp (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
  have hthetaInv : ∀ k : JT,
      thetaT.comp (phi k).toMonoidHom = thetaT := by
    intro k
    ext h
    let v : UHU := ⟨((k : T) : HU), k.property.1⟩
    let u : U := ⟨((v : HU) : M), by
      change (((v : HU) : M) : Gamma) ∈ U
      exact v.property⟩
    have huJ : u ∈ J := by
      have hk := (k : T).property
      change pTypeNonGaloisHUToUProjection ctx (v : HU) ∈ J at hk
      rw [pTypeNonGaloisHUToUProjection_apply_complement ctx v] at hk
      exact hk
    have hfactorFixed :=
      (pTypeNonGaloisTwoCoordinateCharacter_fixed_iff
        D data w hw lambda hlambda u).mpr huJ
    have hproj := pTypeNonGaloisHToFactorProjection_conj_U
      ctx facts v (Subgroup.subgroupOfEquivOfLe hHT h)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      thetaT, thetaH]
    change pTypeNonGaloisTwoCoordinateMulChar D data w lambda
        (pTypeNonGaloisHToFactorProjection ctx
          (Subgroup.subgroupOfEquivOfLe hHT (phi k h))) =
      pTypeNonGaloisTwoCoordinateMulChar D data w lambda
        (pTypeNonGaloisHToFactorProjection ctx
          (Subgroup.subgroupOfEquivOfLe hHT h))
    rw [show Subgroup.subgroupOfEquivOfLe hHT (phi k h) =
        MulAut.conjNormal (v : HU)
          (Subgroup.subgroupOfEquivOfLe hHT h) by
      apply Subtype.ext
      rfl,
      hproj]
    simpa only [pTypeNonGaloisTwoCoordinateCharacter_apply] using
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

/-- The chosen normalized scalar extension. -/
noncomputable def pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
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
    pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w →* ℂ :=
  Classical.choose
    (pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_exists
      ctx facts not_Galois w hw lambda hlambda)

@[simp]
theorem pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_apply_H
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
    (h : let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisTwoCoordinateInertiaInHU
        ctx facts not_Galois w
      H.subgroupOf T) :
    pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
        ctx facts not_Galois w hw lambda hlambda h =
      pTypeNonGaloisTwoCoordinateHMonoidHom
        ctx facts not_Galois w lambda
          (Subgroup.subgroupOfEquivOfLe
            (pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
              ctx facts not_Galois w) h) :=
  (Classical.choose_spec
    (pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_exists
      ctx facts not_Galois w hw lambda hlambda)).1 h

@[simp]
theorem pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_apply_J
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
    (k : let HU := pTypeHUInMaximal M (derivedWithin M)
      let UHU := (U.subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisTwoCoordinateInertiaInHU
        ctx facts not_Galois w
      (UHU ⊓ T).subgroupOf T) :
    pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
        ctx facts not_Galois w hw lambda hlambda k = 1 :=
  (Classical.choose_spec
    (pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_exists
      ctx facts not_Galois w hw lambda hlambda)).2 k

/-! ## The induced irreducible character -/

/-- The normalized extension as an irreducible linear character. -/
noncomputable def pTypeNonGaloisTwoCoordinateHExtensionCharacter
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
    IrreducibleCharacter
      (pTypeNonGaloisTwoCoordinateInertiaInHU
        ctx facts not_Galois w) ℂ :=
  pTypeIrreducibleCharacterOfMonoidHom
    (pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
      ctx facts not_Galois w hw lambda hlambda)

@[simp]
theorem pTypeNonGaloisTwoCoordinateHExtensionCharacter_apply
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
    (t : pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w) :
    pTypeNonGaloisTwoCoordinateHExtensionCharacter
        ctx facts not_Galois w hw lambda hlambda t =
      pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
        ctx facts not_Galois w hw lambda hlambda t :=
  pTypeIrreducibleCharacterOfMonoidHom_apply _ t

/-- The two-coordinate `H` character transported to its copy inside the
exact inertia subgroup. -/
noncomputable def pTypeNonGaloisTwoCoordinateHCharacterInInertia
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
    let T := pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w
    IrreducibleCharacter (H.subgroupOf T) ℂ := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  exact pTypeIrreducibleCharacterOfMonoidHom
    ((pTypeNonGaloisTwoCoordinateHMonoidHom
      ctx facts not_Galois w lambda).comp
        (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom)

@[simp]
theorem pTypeNonGaloisTwoCoordinateHCharacterInInertia_apply
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
    (h : let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let T := pTypeNonGaloisTwoCoordinateInertiaInHU
        ctx facts not_Galois w
      H.subgroupOf T) :
    pTypeNonGaloisTwoCoordinateHCharacterInInertia
        ctx facts not_Galois w lambda h =
      pTypeNonGaloisTwoCoordinateHCharacter
        ctx facts not_Galois w lambda
          (Subgroup.subgroupOfEquivOfLe
            (pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
              ctx facts not_Galois w) h) := by
  rw [pTypeNonGaloisTwoCoordinateHCharacterInInertia,
    pTypeIrreducibleCharacterOfMonoidHom_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    pTypeNonGaloisTwoCoordinateHCharacter_apply]

theorem pTypeNonGaloisTwoCoordinateHExtensionCharacter_restrict
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
    let T := pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w
    let HT := H.subgroupOf T
    ClassFunction.restrict HT
        (pTypeNonGaloisTwoCoordinateHExtensionCharacter
          ctx facts not_Galois w hw lambda hlambda : ClassFunction T ℂ) =
      (pTypeNonGaloisTwoCoordinateHCharacterInInertia
        ctx facts not_Galois w lambda : ClassFunction HT ℂ) := by
  ext h
  rw [ClassFunction.restrict_apply,
    pTypeNonGaloisTwoCoordinateHExtensionCharacter_apply,
    pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_apply_H,
    pTypeNonGaloisTwoCoordinateHCharacterInInertia_apply,
    pTypeNonGaloisTwoCoordinateHCharacter_apply]

/-- Any ambient stabilizer of the normalized extension stabilizes its
restriction to `H`, and hence lies in the exact two-coordinate inertia. -/
theorem pTypeNonGaloisTwoCoordinateHExtensionCharacter_inertia_le
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
    let T := pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w
    ClassFunction.inertia T
        (pTypeNonGaloisTwoCoordinateHExtensionCharacter
          ctx facts not_Galois w hw lambda hlambda :
            ClassFunction T ℂ) ≤ T := by
  classical
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  let HT := H.subgroupOf T
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter
      ctx facts not_Galois w hw lambda hlambda
  let theta : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisTwoCoordinateHCharacter
      ctx facts not_Galois w lambda
  let thetaT : IrreducibleCharacter HT ℂ :=
    pTypeNonGaloisTwoCoordinateHCharacterInInertia
      ctx facts not_Galois w lambda
  have hrestrict : ClassFunction.restrict HT
      (psi : ClassFunction T ℂ) = (thetaT : ClassFunction HT ℂ) :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter_restrict
      ctx facts not_Galois w hw lambda hlambda
  change ClassFunction.inertia T (psi : ClassFunction T ℂ) ≤ T
  intro x hx
  have hxFixed : ClassFunction.normalConjugate T x
      (psi : ClassFunction T ℂ) = (psi : ClassFunction T ℂ) :=
    (ClassFunction.mem_inertia_iff T
      (psi : ClassFunction T ℂ) x).mp hx
  have hthetaFixed : ClassFunction.normalConjugate H x
      (theta : ClassFunction H ℂ) = (theta : ClassFunction H ℂ) := by
    ext h
    rw [ClassFunction.normalConjugate_apply]
    let hT : HT :=
      ⟨⟨(h : HU), hHT h.property⟩, h.property⟩
    let hconj : H := (MulAut.conjNormal x).symm h
    let hconjT : HT :=
      ⟨⟨(hconj : HU), hHT hconj.property⟩, hconj.property⟩
    have harg : (MulAut.conjNormal x).symm (hT : T) =
        (hconjT : T) := by
      apply Subtype.ext
      rfl
    have hvalue := congrArg
      (fun f : ClassFunction T ℂ ↦ f (hT : T)) hxFixed
    rw [ClassFunction.normalConjugate_apply, harg] at hvalue
    have hresConj := congrArg
      (fun f : ClassFunction HT ℂ ↦ f hconjT) hrestrict
    have hres := congrArg
      (fun f : ClassFunction HT ℂ ↦ f hT) hrestrict
    have hthetaValue : thetaT hconjT = thetaT hT := by
      simpa only [ClassFunction.restrict_apply] using
        hresConj.symm.trans (hvalue.trans hres)
    have hthetaConj : thetaT hconjT = theta hconj := by
      change pTypeNonGaloisTwoCoordinateHCharacterInInertia
          ctx facts not_Galois w lambda hconjT = theta hconj
      rw [pTypeNonGaloisTwoCoordinateHCharacterInInertia_apply]
      congr 1
    have hthetaBase : thetaT hT = theta h := by
      change pTypeNonGaloisTwoCoordinateHCharacterInInertia
          ctx facts not_Galois w lambda hT = theta h
      rw [pTypeNonGaloisTwoCoordinateHCharacterInInertia_apply]
      congr 1
    calc
      theta hconj = thetaT hconjT := hthetaConj.symm
      _ = thetaT hT := hthetaValue
      _ = theta h := hthetaBase
  have hxTheta : x ∈ ClassFunction.inertia H
      (theta : ClassFunction H ℂ) :=
    (ClassFunction.mem_inertia_iff H
      (theta : ClassFunction H ℂ) x).mpr hthetaFixed
  rw [pTypeNonGaloisTwoCoordinateHCharacter_inertia
    ctx facts not_Galois w hw lambda hlambda] at hxTheta
  exact hxTheta

/-- Induction from the exact inertia subgroup produces an irreducible
character of `HU`. -/
theorem pTypeNonGaloisTwoCoordinateHExtensionCharacter_induce_irreducible
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
    let T := pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w
    IsIrreducibleCharacter HU ℂ
      (ClassFunction.induce T
        (pTypeNonGaloisTwoCoordinateHExtensionCharacter
          ctx facts not_Galois w hw lambda hlambda :
            ClassFunction T ℂ)) := by
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter
      ctx facts not_Galois w hw lambda hlambda
  change IsIrreducibleCharacter
    (pTypeHUInMaximal M (derivedWithin M)) ℂ
      (ClassFunction.induce T (psi : ClassFunction T ℂ))
  have hpsi : ClassFunction.inertia T
      (psi : ClassFunction T ℂ) ≤ T := by
    exact pTypeNonGaloisTwoCoordinateHExtensionCharacter_inertia_le
      ctx facts not_Galois w hw lambda hlambda
  exact FrobeniusKernelInductionAux.irreducible_induce_of_inertia psi hpsi

set_option maxHeartbeats 800000 in
/-- The irreducible `HU` character obtained from the normalized extension. -/
noncomputable def pTypeNonGaloisTwoCoordinateHUCharacter
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
    IrreducibleCharacter
      (pTypeHUInMaximal M (derivedWithin M)) ℂ := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter
      ctx facts not_Galois w hw lambda hlambda
  let chi : ClassFunction HU ℂ :=
    ClassFunction.induce T (psi : ClassFunction T ℂ)
  have hchi : IsIrreducibleCharacter HU ℂ chi :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter_induce_irreducible
      ctx facts not_Galois w hw lambda hlambda
  exact ⟨chi, hchi⟩

@[simp]
theorem pTypeNonGaloisTwoCoordinateHUCharacter_coe
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
    (pTypeNonGaloisTwoCoordinateHUCharacter
      ctx facts not_Galois w hw lambda hlambda : ClassFunction
        (pTypeHUInMaximal M (derivedWithin M)) ℂ) =
      ClassFunction.induce
        (pTypeNonGaloisTwoCoordinateInertiaInHU
          ctx facts not_Galois w)
        (pTypeNonGaloisTwoCoordinateHExtensionCharacter
          ctx facts not_Galois w hw lambda hlambda : ClassFunction _ ℂ) := by
  rfl

/-- The induced character has degree equal to the exact inertia index. -/
theorem pTypeNonGaloisTwoCoordinateHUCharacter_degree
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
    let D := Ptype_factor_action ctx facts
    let data := typeP_Galois_Pn
      (Ptype_factor_action_hypotheses ctx facts) not_Galois
    let K := pointwiseActionKernel D.U_action data.H₁
    pTypeIrreducibleDegree
        (pTypeNonGaloisTwoCoordinateHUCharacter
          ctx facts not_Galois w hw lambda hlambda) =
      (K ⊓ actionConjugate D.W₁_action_U K w).index := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let psi := pTypeNonGaloisTwoCoordinateHExtensionCharacter
    ctx facts not_Galois w hw lambda hlambda
  let s := pTypeNonGaloisTwoCoordinateHUCharacter
    ctx facts not_Galois w hw lambda hlambda
  rw [pTypeIrreducibleDegree_eq_index_mul_of_induced T psi s rfl,
    show pTypeIrreducibleDegree psi = 1 from
      pTypeIrreducibleCharacterOfMonoidHom_degree
        (pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
          ctx facts not_Galois w hw lambda hlambda),
    mul_one]
  exact pTypeNonGaloisTwoCoordinateInertiaInHU_index
    ctx facts not_Galois w

/-! ## Containment in the exact inertia subgroup -/

/-- The kernel of the full `U`-action fixes the selected factor and every
`W₁`-conjugate of that factor. -/
theorem pTypeNonGalois_C_le_twoCoordinateKernelInf
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D) (w : W₁) :
    D.C ≤ pointwiseActionKernel D.U_action data.H₁ ⊓
      actionConjugate D.W₁_action_U
        (pointwiseActionKernel D.U_action data.H₁) w := by
  intro c hc
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_pointwiseActionKernel_iff]
    intro h _
    exact (D.mem_C_iff c).mp hc h
  · rw [mem_actionConjugate_iff, mem_pointwiseActionKernel_iff]
    intro h _
    simpa using
      (D.mem_C_iff (D.W₁_action_U w⁻¹ c)).mp
        (D.W₁_action_U_mem_C w⁻¹ hc) h

/-- The subgroup `H₀ C'` used as the induction kernel lies in the pullback
of the two-coordinate stabilizer. -/
theorem pTypeNonGaloisH0CPrime_le_TwoCoordinateInertiaInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀CPrime := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) ⊔
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    H₀CPrime ≤ pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w := by
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let K := pointwiseActionKernel D.U_action data.H₁
  let J := K ⊓ actionConjugate D.W₁_action_U K w
  have hH₀H : H₀ ≤ H :=
    Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Ptype_Fcore_kernel_lt ctx).le)
  apply sup_le
  · exact hH₀H.trans
      (pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
        ctx facts not_Galois w)
  · intro x hx
    change pi x ∈ J
    change (((x : HU) : M) : Gamma) ∈
      pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype) at hx
    obtain ⟨c, hc, hcx⟩ := hx
    let UHU := (U.subgroupOf M).subgroupOf HU
    let v : UHU := ⟨x, by
      change ((x : HU) : Gamma) ∈ U
      rw [← hcx]
      exact (c : U).property⟩
    let ux : U := ⟨((v : HU) : M), v.property⟩
    have huxEq : ux = (c : U) := by
      apply Subtype.ext
      exact hcx.symm
    have hpi : pi x = ux := by
      change pi (v : HU) = ux
      exact pTypeNonGaloisHUToUProjection_apply_complement ctx v
    rw [hpi, huxEq]
    exact pTypeNonGalois_C_le_twoCoordinateKernelInf
      D data w c.property

/-- The derived subgroup of the full action kernel, embedded in `HU`, lies in
the literal `U` complement. -/
theorem pTypeNonGaloisCPrimeInDerived_le_UInDerived
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU ≤
      (U.subgroupOf M).subgroupOf HU := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  change
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU ≤
      (U.subgroupOf M).subgroupOf HU
  intro x hx
  change (((x : HU) : M) : Gamma) ∈
    pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype) at hx
  obtain ⟨c, _, hcx⟩ := hx
  change ((x : HU) : Gamma) ∈ U
  rw [← hcx]
  exact (c : U).property

/-! ## The core-layer kernel argument -/

/-- The normalized inertia extension kills the explicit source subgroup
`H₀C'`: its `H₀` part is killed by the Fitting-factor projection, while
its `C'` part lies in the complement on which the extension was normalized to
be trivial. -/
theorem pTypeNonGaloisTwoCoordinateHExtensionCharacter_H0CPrime_le_kernel
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
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀CPrime := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) ⊔
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    let T := pTypeNonGaloisTwoCoordinateInertiaInHU
      ctx facts not_Galois w
    H₀CPrime.subgroupOf T ≤
      ClassFunction.translationKernel
        (pTypeNonGaloisTwoCoordinateHExtensionCharacter
          ctx facts not_Galois w hw lambda hlambda :
            ClassFunction T ℂ) := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let CPrime :=
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let H₀CPrime := H₀ ⊔ CPrime
  let UHU := (U.subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  let HT := H.subgroupOf T
  let JT := (UHU ⊓ T).subgroupOf T
  let omega : T →* ℂ := pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
    ctx facts not_Galois w hw lambda hlambda
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter
    ctx facts not_Galois w hw lambda hlambda
  change H₀CPrime.subgroupOf T ≤
    ClassFunction.translationKernel (psi : ClassFunction T ℂ)
  have hpsi_apply (t : T) : psi t = omega t :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter_apply
      ctx facts not_Galois w hw lambda hlambda t
  have hPrimeT : H₀CPrime ≤ T :=
    pTypeNonGaloisH0CPrime_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  have hH₀T : H₀ ≤ T := le_sup_left.trans hPrimeT
  have hCPrimeT : CPrime ≤ T := le_sup_right.trans hPrimeT
  have hCPrimeU : CPrime ≤ UHU :=
    pTypeNonGaloisCPrimeInDerived_le_UInDerived ctx facts
  have hH₀Kernel : H₀.subgroupOf T ≤
      ClassFunction.translationKernel (psi : ClassFunction T ℂ) := by
    intro x hx
    rw [ClassFunction.mem_translationKernel_iff]
    intro y
    rw [hpsi_apply (x * y), hpsi_apply y, map_mul]
    have hxH : ((x : T) : HU) ∈ H :=
      (Subgroup.subgroupOf_mono HU
        (Subgroup.subgroupOf_mono M
          (Ptype_Fcore_kernel_lt ctx).le)) hx
    let hT : HT := ⟨x, hxH⟩
    let h : H := Subgroup.subgroupOfEquivOfLe hHT hT
    have hhKer : h ∈ (pTypeNonGaloisHToFactorProjection ctx).ker := by
      rw [pTypeNonGaloisHToFactorProjection_ker ctx]
      exact hx
    have homega : omega (x : T) = 1 := by
      change omega (hT : T) = 1
      rw [pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_apply_H]
      change pTypeNonGaloisTwoCoordinateMulChar
          (Ptype_factor_action ctx facts)
          (typeP_Galois_Pn
            (Ptype_factor_action_hypotheses ctx facts) not_Galois)
          w lambda (pTypeNonGaloisHToFactorProjection ctx h) = 1
      rw [MonoidHom.mem_ker.mp hhKer]
      exact map_one _
    rw [homega, one_mul]
  have hCPrimeKernel : CPrime.subgroupOf T ≤
      ClassFunction.translationKernel (psi : ClassFunction T ℂ) := by
    intro x hx
    rw [ClassFunction.mem_translationKernel_iff]
    intro y
    rw [hpsi_apply (x * y), hpsi_apply y, map_mul]
    let jT : JT := ⟨x, ⟨hCPrimeU hx, (x : T).property⟩⟩
    have homega : omega (x : T) = 1 := by
      change omega (jT : T) = 1
      exact pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_apply_J
        ctx facts not_Galois w hw lambda hlambda jT
    rw [homega, one_mul]
  rw [show H₀CPrime.subgroupOf T =
      H₀.subgroupOf T ⊔ CPrime.subgroupOf T from
    Subgroup.subgroupOf_sup hH₀T hCPrimeT]
  exact sup_le hH₀Kernel hCPrimeKernel

/-- The induced two-coordinate character belongs to the precise core layer
`Irr(HU, H/H₀C')`. -/
theorem pTypeNonGaloisTwoCoordinateHUCharacter_mem_Iirr_kerD
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
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀CPrime := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) ⊔
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    pTypeNonGaloisTwoCoordinateHUCharacter
        ctx facts not_Galois w hw lambda hlambda ∈
      Iirr_kerD (k := ℂ) H H₀CPrime := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀CPrime := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) ⊔
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisTwoCoordinateInertiaInHU
    ctx facts not_Galois w
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  let HT := H.subgroupOf T
  let omega : T →* ℂ := pTypeNonGaloisTwoCoordinateHExtensionMonoidHom
    ctx facts not_Galois w hw lambda hlambda
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisTwoCoordinateHExtensionCharacter
    ctx facts not_Galois w hw lambda hlambda
  let s : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisTwoCoordinateHUCharacter
    ctx facts not_Galois w hw lambda hlambda
  letI : H₀CPrime.Normal :=
    pTypeTwoCoordinateH0CPrime_normal ctx facts
  have hPrimeT : H₀CPrime ≤ T :=
    pTypeNonGaloisH0CPrime_le_TwoCoordinateInertiaInHU
      ctx facts not_Galois w
  have hLower : H₀CPrime ≤
      ClassFunction.translationKernel (s : ClassFunction HU ℂ) := by
    change H₀CPrime ≤ ClassFunction.translationKernel
      (ClassFunction.induce T (psi : ClassFunction T ℂ))
    exact ClassFunction.le_translationKernel_induce
      H₀CPrime T hPrimeT (psi : ClassFunction T ℂ)
        (pTypeNonGaloisTwoCoordinateHExtensionCharacter_H0CPrime_le_kernel
          ctx facts not_Galois w hw lambda hlambda)
  have hConstituent : s.IsConstituent
      (ClassFunction.induce T (psi : ClassFunction T ℂ)) := by
    letI : Invertible (Nat.card HU : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    unfold IrreducibleCharacter.IsConstituent
    rw [← pTypeNonGaloisTwoCoordinateHUCharacter_coe
      ctx facts not_Galois w hw lambda hlambda,
      IrreducibleCharacter.characterPairing_self]
    exact one_ne_zero
  have hUpper : ¬ H ≤
      ClassFunction.translationKernel (s : ClassFunction HU ℂ) := by
    intro hHKernel
    have hHRep : H ≤ s.representation.ρ.ker := by
      simpa only [pTypeTwoCoordinate_translationKernel_irreducibleCharacter s]
        using hHKernel
    have hHTRep : H.subgroupOf T ≤ psi.representation.ρ.ker :=
      pTypeTwoCoordinate_subgroupOf_le_constituent_kernel
        T H hHT s psi hConstituent hHRep
    apply hlambda
    apply MulChar.ext'
    intro a
    let z : actionConjugate D.W₁_action data.H₁ (1 : W₁) :=
      ⟨(a : ptypeFCoreFactor ctx), by
        rw [actionConjugate_one]
        exact a.property⟩
    have hz :
        ((D.W₁_action (1 : W₁)).subgroupMap data.H₁).symm z = a := by
      apply Subtype.ext
      change (D.W₁_action (1 : W₁)).symm
          (a : ptypeFCoreFactor ctx) = a
      rw [map_one]
      rfl
    obtain ⟨h, hh⟩ :=
      pTypeNonGaloisHToFactorProjection_surjective ctx
        (z : ptypeFCoreFactor ctx)
    let hT : HT := ⟨⟨h, hHT h.property⟩, h.property⟩
    have hhPsiRep : (hT : T) ∈ psi.representation.ρ.ker :=
      hHTRep hT.property
    have hhPsiKernel : (hT : T) ∈
        ClassFunction.translationKernel (psi : ClassFunction T ℂ) := by
      rw [pTypeTwoCoordinate_translationKernel_irreducibleCharacter psi]
      exact hhPsiRep
    rw [ClassFunction.mem_translationKernel_iff] at hhPsiKernel
    have hhPsiValue := hhPsiKernel (1 : T)
    rw [mul_one] at hhPsiValue
    have hpsiOne : psi 1 = 1 := by
      rw [pTypeNonGaloisTwoCoordinateHExtensionCharacter_apply]
      exact map_one omega
    have hhPsiOne : psi (hT : T) = 1 :=
      hhPsiValue.trans hpsiOne
    calc
      lambda a =
          pTypeActionConjugateMulChar D data.H₁ (1 : W₁)
            (pTypeNonGaloisTwoCoordinateFamily data w lambda 1) z := by
        rw [pTypeNonGaloisTwoCoordinateFamily_one]
        change lambda a =
          lambda (((D.W₁_action (1 : W₁)).subgroupMap data.H₁).symm z)
        rw [hz]
      _ = pTypeNonGaloisTwoCoordinateCharacter D data w lambda
          (z : ptypeFCoreFactor ctx) :=
        (pTypeNonGaloisCoordinateCharacter_apply_coordinate
          D data (pTypeNonGaloisTwoCoordinateFamily data w lambda)
            (1 : W₁) z).symm
      _ = pTypeNonGaloisTwoCoordinateHMonoidHom
          ctx facts not_Galois w lambda h := by
        rw [pTypeNonGaloisTwoCoordinateCharacter_apply]
        change pTypeNonGaloisTwoCoordinateMulChar D data w lambda
            (z : ptypeFCoreFactor ctx) =
          pTypeNonGaloisTwoCoordinateMulChar D data w lambda
            (pTypeNonGaloisHToFactorProjection ctx h)
        rw [hh]
      _ = omega (hT : T) := by
        rw [pTypeNonGaloisTwoCoordinateHExtensionMonoidHom_apply_H]
        rfl
      _ = psi (hT : T) := by
        rw [pTypeNonGaloisTwoCoordinateHExtensionCharacter_apply]
      _ = 1 := hhPsiOne
      _ = (1 : MulChar data.H₁ ℂ) a := by
        rw [MulChar.one_apply (Group.isUnit a)]
  rw [mem_Iirr_kerD]
  exact ⟨hLower, hUpper⟩

end PTypeNonGaloisTwoCoordinateInternal

open PTypeNonGaloisTwoCoordinateInternal
open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisInertiaExtensionsInternal

/-- Peterfalvi (9.11.2), source `s_1`: for every nonidentity translated
coordinate there is an irreducible core character whose degree is the index
of the intersection of the two constituent action kernels. -/
theorem pTypeNonGalois_twoCoordinate_coreCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) (hw : w ≠ 1) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀C' := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) ⊔
      ((pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
    let K := pointwiseActionKernel D.U_action data.H₁
    ∃ s : IrreducibleCharacter HU ℂ,
      s ∈ Iirr_kerD (k := ℂ) H H₀C' ∧
      pTypeIrreducibleDegree s =
        (K ⊓ actionConjugate D.W₁_action_U K w).index := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  let L := ↑(pTypeNontrivialMulChars data.H₁)
  have hLcard : Nat.card L = D.p - 1 := by
    simpa only [L, natCard_pTypeNontrivialMulChars, data.card_H₁, D]
  have hLpos : 0 < Nat.card L := by
    rw [hLcard]
    exact Nat.sub_pos_of_lt D.p_prime.one_lt
  obtain ⟨lambda⟩ : Nonempty L := (Nat.card_pos_iff.mp hLpos).1
  have hlambda : (lambda : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one lambda
  let s := pTypeNonGaloisTwoCoordinateHUCharacter
    ctx facts not_Galois w hw (lambda : MulChar data.H₁ ℂ) hlambda
  exact ⟨s,
    pTypeNonGaloisTwoCoordinateHUCharacter_mem_Iirr_kerD
      ctx facts not_Galois w hw (lambda : MulChar data.H₁ ℂ) hlambda,
    pTypeNonGaloisTwoCoordinateHUCharacter_degree
      ctx facts not_Galois w hw (lambda : MulChar data.H₁ ℂ) hlambda⟩

end

end Submission.OddOrder.PF
