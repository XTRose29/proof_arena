import Submission.OddOrder.PF.Section09.PTypeNonGaloisCliffordSupport

/-!
# Peterfalvi Section 9: twist induction in the non-Galois case

This phase induces the quotient-twist family first through `HU` and then to
the maximal subgroup.  It records the cardinality estimates and degree filter
needed for clause (d) of the non-Galois conclusion.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open CategoryTheory

universe u v

local instance (priority := 10) pTypeTwistInductionFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisTwistInductionInternal

open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisSelectedCoordinateInternal
open PTypeNonGaloisInertiaCoreInternal
open PTypeNonGaloisInertiaExtensionsInternal
open PTypeNonGaloisCliffordSupportInternal
open internal

local instance pTypeTwistInductionFCoreFactor_commutative
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsMulCommutative (ptypeFCoreFactor ctx) :=
  (ptypeFCoreFactor_elementary ctx).commutative

/-! ## Local subgroup and split-universe character adapters -/

private theorem pTypeTwistH0DerivedComplementInDerived_eq_subgroupOf
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

private instance pTypeTwistH0DerivedComplementInDerived_normal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeH0DerivedComplementInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U).Normal := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  rw [pTypeTwistH0DerivedComplementInDerived_eq_subgroupOf ctx]
  exact Subgroup.Normal.subgroupOf
    (Ptype_Fcore_extensions_normal ctx).H₀U'_normal.2 HU

private theorem pTypeTwistRepresentationIrreducibleCompSurjective
    {A B : Type u} {V : Type v}
    [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ B V) [Representation.IsIrreducible rho]
    (f : A →* B) (hf : Function.Surjective f) :
    Representation.IsIrreducible (rho.comp f) := by
  let sigma : Representation ℂ A V := rho.comp f
  have hbot_ne_top : (⊥ : Subrepresentation sigma) ≠ ⊤ := by
    intro h
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation rho)
    apply SetLike.ext
    intro x
    have hx := congrArg (fun U : Subrepresentation sigma ↦ x ∈ U) h
    change (x ∈ (⊥ : Submodule ℂ V)) =
      (x ∈ (⊤ : Submodule ℂ V)) at hx
    exact iff_of_eq hx
  letI : Nontrivial (Subrepresentation sigma) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let U' : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule b x hx := by
        obtain ⟨a, rfl⟩ := hf b
        exact U.apply_mem_toSubmodule a hx }
  have hU' : U' ≠ ⊥ := by
    intro hbot
    apply hU
    apply SetLike.ext
    intro x
    have hx := congrArg (fun W : Subrepresentation rho ↦ x ∈ W) hbot
    change (x ∈ U.toSubmodule) =
      (x ∈ (⊥ : Submodule ℂ V)) at hx
    exact iff_of_eq hx
  have htop : U' = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  apply SetLike.ext
  intro x
  have hx := congrArg (fun W : Subrepresentation rho ↦ x ∈ W) htop
  change (x ∈ U.toSubmodule) =
    (x ∈ (⊤ : Submodule ℂ V)) at hx
  exact iff_of_eq hx

private noncomputable def pTypeTwistInflateIrreducible
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ.comp f
  letI : Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible rho :=
    pTypeTwistRepresentationIrreducibleCompSurjective
      chi.representation.ρ f hf
  letI : Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp] private theorem pTypeTwistInflateIrreducible_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeTwistInflateIrreducible f hf chi a = chi (f a) := by
  simp only [pTypeTwistInflateIrreducible,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

private noncomputable def pTypeTwistComapMulEquiv
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ :=
  pTypeTwistInflateIrreducible e.toMonoidHom e.surjective chi

@[simp] private theorem pTypeTwistComapMulEquiv_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeTwistComapMulEquiv e chi a = chi (e a) :=
  pTypeTwistInflateIrreducible_apply
    e.toMonoidHom e.surjective chi a

private theorem pTypeTwistComapMulEquiv_injective
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) :
    Function.Injective
      (pTypeTwistComapMulEquiv e :
        IrreducibleCharacter B ℂ → IrreducibleCharacter A ℂ) := by
  intro chi psi h
  apply IrreducibleCharacter.ext
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  simpa only [pTypeTwistComapMulEquiv_apply] using
    congrArg (fun z : IrreducibleCharacter A ℂ ↦ z a) h

/-- Split-universe form of the translation-kernel/representation-kernel
identity for irreducible characters. -/
private theorem pTypeTwistTranslationKernel_irreducibleCharacter
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
    letI : Simple chi.representation :=
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

private theorem pTypeTwistExists_hom_ne_zero_of_isConstituent
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

private theorem pTypeTwistFDRep_kernel_le_constituent_kernel
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ :=
    pTypeTwistExists_hom_ne_zero_of_isConstituent V chi hchi
  letI : Simple chi.representation :=
    chi.representation_simple
  letI : Mono f := mono_of_nonzero_from_simple hf
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

private theorem pTypeTwistSubgroupOf_le_constituent_kernel
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
    pTypeTwistFDRep_kernel_le_constituent_kernel R psi hpsiR
  intro h hh
  apply hkerRpsi
  rw [MonoidHom.mem_ker]
  change chi.representation.ρ (h : G) = 1
  exact MonoidHom.mem_ker.mp (hAchi hh)

/-! ## Induction from the exact inertia subgroup -/

/-- A twist cannot acquire new inertia outside the exact inertia subgroup of
its selected F-core constituent. -/
private theorem pTypeNonGaloisInertiaTwistCharacter_inertia_le
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    ClassFunction.inertia T
        (pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois i : ClassFunction T ℂ) ≤ T := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois
  let HT := H.subgroupOf T
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex
      ctx facts not_Galois i
  let theta : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisSingleHCharacter ctx facts not_Galois i.1
  let thetaT : IrreducibleCharacter HT ℂ :=
    pTypeNonGaloisSingleHCharacterInInertia
      ctx facts not_Galois i.1
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  have hrestrict : ClassFunction.restrict HT
      (psi : ClassFunction T ℂ) = (thetaT : ClassFunction HT ℂ) :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex_restrict
      ctx facts not_Galois i
  change ClassFunction.inertia T
      (pTypeNonGaloisInertiaTwistCharacterFromIndex
        ctx facts not_Galois i : ClassFunction T ℂ) ≤ T
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
      change pTypeNonGaloisSingleHCharacterInInertia
          ctx facts not_Galois i.1 hconjT = theta hconj
      rw [pTypeNonGaloisSingleHCharacterInInertia_apply]
      congr 1
    have hthetaBase : thetaT hT = theta h := by
      change pTypeNonGaloisSingleHCharacterInInertia
          ctx facts not_Galois i.1 hT = theta h
      rw [pTypeNonGaloisSingleHCharacterInInertia_apply]
      congr 1
    calc
      theta hconj = thetaT hconjT := hthetaConj.symm
      _ = thetaT hT := hthetaValue
      _ = theta h := hthetaBase
  have hxTheta : x ∈ ClassFunction.inertia H
      (theta : ClassFunction H ℂ) :=
    (ClassFunction.mem_inertia_iff H
      (theta : ClassFunction H ℂ) x).mpr hthetaFixed
  rw [pTypeNonGaloisSingleHCharacter_inertia
    ctx facts not_Galois i.1 hi] at hxTheta
  exact hxTheta

private theorem pTypeNonGaloisInertiaTwistCharacter_induce_irreducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    IsIrreducibleCharacter HU ℂ
      (ClassFunction.induce T
        (pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois i : ClassFunction T ℂ)) := by
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex
      ctx facts not_Galois i
  change IsIrreducibleCharacter
    (pTypeHUInMaximal M (derivedWithin M)) ℂ
      (ClassFunction.induce T (psi : ClassFunction T ℂ))
  have hI : ClassFunction.inertia T
      (psi : ClassFunction T ℂ) ≤ T := by
    exact pTypeNonGaloisInertiaTwistCharacter_inertia_le
      ctx facts not_Galois i
  exact FrobeniusKernelInductionAux.irreducible_induce_of_inertia psi hI

set_option maxHeartbeats 800000 in
/-- Induce a quotient twist to the canonical `HU` subgroup. -/
private noncomputable def pTypeNonGaloisHUCharacterFromTwistIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois →
      IrreducibleCharacter
        (pTypeHUInMaximal M (derivedWithin M)) ℂ :=
  fun i ↦ ⟨ClassFunction.induce
      (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois)
      (pTypeNonGaloisInertiaTwistCharacterFromIndex
        ctx facts not_Galois i : ClassFunction _ ℂ),
    pTypeNonGaloisInertiaTwistCharacter_induce_irreducible
      ctx facts not_Galois i⟩

@[simp]
private theorem pTypeNonGaloisHUCharacterFromTwistIndex_coe
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    (pTypeNonGaloisHUCharacterFromTwistIndex
      ctx facts not_Galois i : ClassFunction
        (pTypeHUInMaximal M (derivedWithin M)) ℂ) =
      ClassFunction.induce
        (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois)
        (pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois i : ClassFunction _ ℂ) :=
  rfl

/-- All intermediate induced twists have the non-Galois action index as
their degree. -/
private theorem pTypeNonGaloisHUCharacterFromTwistIndex_degree
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    pTypeIrreducibleDegree
      (pTypeNonGaloisHUCharacterFromTwistIndex
        ctx facts not_Galois i) =
      pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let psi := pTypeNonGaloisInertiaTwistCharacterFromIndex
    ctx facts not_Galois i
  let chi := pTypeNonGaloisHUCharacterFromTwistIndex
    ctx facts not_Galois i
  have hpsiDegree : pTypeIrreducibleDegree psi = 1 := by
    change Module.finrank ℂ psi.representation = 1
    simpa only [psi] using
      (pTypeNonGaloisInertiaTwistCharacterFromIndex_degree
        ctx facts not_Galois i)
  calc
    pTypeIrreducibleDegree chi =
        T.index * pTypeIrreducibleDegree psi :=
      pTypeIrreducibleDegree_eq_index_mul_of_induced T psi chi rfl
    _ = T.index := by
      rw [hpsiDegree, mul_one]
    _ = pTypeNonGaloisIndex hD not_Galois :=
      pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois

/-! ## The lower kernel of every twist -/

/-- Every source twist kills the nested copy of `H₀U'` in its inertia
group. -/
private theorem pTypeNonGaloisInertiaTwistMonoidHom_apply_H0UPrime
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois)
    (x : let HU := pTypeHUInMaximal M (derivedWithin M)
      let H₀UPrime := pTypeH0DerivedComplementInDerived
        M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
      let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
      H₀UPrime.subgroupOf T) :
    pTypeNonGaloisInertiaTwistMonoidHomFromIndex
        ctx facts not_Galois i x = 1 := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  let UHU := (U.subgroupOf M).subgroupOf HU
  let UPrime := (pTypeDerivedComplementInMaximal
    (U.subgroupOf M).subtype).subgroupOf HU
  let H₀UPrime := pTypeH0DerivedComplementInDerived
    M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois
  let HT := H.subgroupOf T
  let KT := (UHU ⊓ T).subgroupOf T
  let hH₀UPrimeT : H₀UPrime ≤ T :=
    pTypeNonGaloisH0DerivedComplement_le_H1InertiaInHU
      ctx facts not_Galois
  have hUPrimeT : UPrime ≤ T :=
    le_sup_right.trans hH₀UPrimeT
  let qT := pTypeNonGaloisH1InertiaTwistProjection
    ctx facts not_Galois
  let pi := pTypeNonGaloisHUToUProjection ctx
  let piK := pTypeNonGaloisH1InertiaToKernelProjection
    ctx facts not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let omega := pTypeNonGaloisSingleHExtensionMonoidHom
    ctx facts not_Galois i.1
      (pTypeNontrivialMulCharSubtype_ne_one i.1)
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  letI : H₀.Normal := by
    exact Subgroup.Normal.subgroupOf
      (Ptype_Fcore_kernel_normal_M ctx) HU
  obtain ⟨h₀, hh₀, uprime, huprime, hmul⟩ :=
    (Subgroup.mem_sup_of_normal_left
      (s := H₀) (t := UPrime)).mp x.property
  let h : H := ⟨h₀, (Ptype_Fcore_kernel_lt ctx).le hh₀⟩
  let hT : HT := ⟨⟨h₀, hHT h.property⟩, h.property⟩
  have huprimeMapped : ((uprime : HU) : M) ∈
      pTypeDerivedComplementInMaximal
        (U.subgroupOf M).subtype := huprime
  rw [← pTypeDerivedComplementInMaximal_eq_subgroupOf hUM]
      at huprimeMapped
  obtain ⟨u, hu, hueq⟩ := huprimeMapped
  let v : UHU := ⟨uprime, by
    change ((uprime : HU) : M) ∈ U.subgroupOf M
    change ((uprime : HU) : Gamma) ∈ U
    rw [← congrArg Subtype.val hueq]
    exact u.property⟩
  let uT : T := ⟨uprime, hUPrimeT huprime⟩
  let kT : KT := ⟨uT, ⟨v.property, uT.property⟩⟩
  let ux : U := ⟨((v : HU) : M), v.property⟩
  have hux : ux = u := by
    apply Subtype.ext
    exact (congrArg Subtype.val hueq).symm
  have hxMul : (x : T) = (hT : T) * (kT : T) := by
    apply Subtype.ext
    exact hmul.symm
  have hqH : qT (hT : T) = 1 :=
    pTypeNonGaloisH1InertiaTwistProjection_apply_H
      ctx facts not_Galois hT
  have hpiK : ((piK (kT : T) : K) : U) = u := by
    change pi uprime = u
    calc
      pi uprime = ux := by
        simpa only [pi, ux] using
          (pTypeNonGaloisHUToUProjection_apply_complement ctx v)
      _ = u := hux
  have hqK : qT (kT : T) = 1 := by
    change pTypeNonGaloisH1InertiaTwistProjection
      ctx facts not_Galois (kT : T) = 1
    rw [pTypeNonGaloisH1InertiaTwistProjection,
      MonoidHom.comp_apply]
    apply (QuotientGroup.eq_one_iff (piK (kT : T))).mpr
    change ((piK (kT : T) : K) : U) ∈ _root_.commutator U
    rw [hpiK]
    exact hu
  have hhKer : h ∈
      (pTypeNonGaloisHToFactorProjection ctx).ker := by
    rw [pTypeNonGaloisHToFactorProjection_ker ctx]
    exact hh₀
  have hhProj : pTypeNonGaloisHToFactorProjection ctx h = 1 :=
    MonoidHom.mem_ker.mp hhKer
  have homegaH : omega (hT : T) = 1 := by
    change pTypeNonGaloisSingleHExtensionMonoidHom
      ctx facts not_Galois i.1
        (pTypeNontrivialMulCharSubtype_ne_one i.1) (hT : T) = 1
    rw [pTypeNonGaloisSingleHExtensionMonoidHom_apply_H]
    change pTypeNonGaloisSingleCoordinateMulChar D data i.1
      (pTypeNonGaloisHToFactorProjection ctx h) = 1
    rw [hhProj, map_one]
  have homegaK : omega (kT : T) = 1 := by
    exact pTypeNonGaloisSingleHExtensionMonoidHom_apply_K
      ctx facts not_Galois i.1
        (pTypeNontrivialMulCharSubtype_ne_one i.1) kT
  change i.2 (qT (x : T)) * omega (x : T) = 1
  rw [hxMul, map_mul, map_mul, map_mul, hqH, hqK,
    homegaH, homegaK]
  simp

/-- Translation-kernel form of the preceding pointwise calculation. -/
private theorem pTypeNonGaloisInertiaTwistCharacter_H0UPrime_le_kernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H₀UPrime := pTypeH0DerivedComplementInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    H₀UPrime.subgroupOf T ≤
      ClassFunction.translationKernel
        (pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois i : ClassFunction T ℂ) := by
  dsimp only
  let H₀UPrime := pTypeH0DerivedComplementInDerived
    M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  intro x hx
  rw [ClassFunction.mem_translationKernel_iff]
  intro y
  rw [pTypeNonGaloisInertiaTwistCharacterFromIndex,
    pTypeIrreducibleCharacterOfMonoidHom_apply,
    pTypeIrreducibleCharacterOfMonoidHom_apply,
    map_mul,
    pTypeNonGaloisInertiaTwistMonoidHom_apply_H0UPrime
      ctx facts not_Galois i ⟨x, hx⟩,
    one_mul]

set_option maxHeartbeats 1000000 in
/-- The intermediate character belongs to the exact source layer
`Irr(HU,H/H₀U')`. -/
private theorem pTypeNonGaloisHUCharacterFromTwistIndex_mem_Iirr_kerD
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀UPrime := pTypeH0DerivedComplementInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
    pTypeNonGaloisHUCharacterFromTwistIndex
        ctx facts not_Galois i ∈
      Iirr_kerD (k := ℂ) H H₀UPrime := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀UPrime := pTypeH0DerivedComplementInDerived
    M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let hHT : H ≤ T :=
    pTypeNonGaloisH_le_H1InertiaInHU ctx facts not_Galois
  let HT := H.subgroupOf T
  let psi := pTypeNonGaloisInertiaTwistCharacterFromIndex
    ctx facts not_Galois i
  let chi := pTypeNonGaloisHUCharacterFromTwistIndex
    ctx facts not_Galois i
  letI : H.Normal := pTypeNonGaloisHInHU_normal
  letI : H₀UPrime.Normal :=
    pTypeTwistH0DerivedComplementInDerived_normal ctx
  have hH₀UPrimeT : H₀UPrime ≤ T :=
    pTypeNonGaloisH0DerivedComplement_le_H1InertiaInHU
      ctx facts not_Galois
  have hLowerKernel : H₀UPrime ≤
      ClassFunction.translationKernel (chi : ClassFunction HU ℂ) := by
    change H₀UPrime ≤ ClassFunction.translationKernel
      (ClassFunction.induce T (psi : ClassFunction T ℂ))
    exact ClassFunction.le_translationKernel_induce
      H₀UPrime T hH₀UPrimeT (psi : ClassFunction T ℂ)
        (pTypeNonGaloisInertiaTwistCharacter_H0UPrime_le_kernel
          ctx facts not_Galois i)
  have hConstituent : chi.IsConstituent
      (ClassFunction.induce T (psi : ClassFunction T ℂ)) := by
    letI : Invertible (Nat.card HU : ℂ) :=
      invertibleOfNonzero
        (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HU)).ne')
    unfold IrreducibleCharacter.IsConstituent
    rw [← pTypeNonGaloisHUCharacterFromTwistIndex_coe
      ctx facts not_Galois i,
      IrreducibleCharacter.characterPairing_self]
    exact one_ne_zero
  have hUpperNotKernel : ¬ H ≤
      ClassFunction.translationKernel (chi : ClassFunction HU ℂ) := by
    intro hHKernel
    have hHRep : H ≤ chi.representation.ρ.ker := by
      rw [← pTypeTwistTranslationKernel_irreducibleCharacter chi]
      exact hHKernel
    have hHTRep : H.subgroupOf T ≤ psi.representation.ρ.ker :=
      pTypeTwistSubgroupOf_le_constituent_kernel
        T H hHT chi psi hConstituent hHRep
    have hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
      pTypeNontrivialMulCharSubtype_ne_one i.1
    apply hi
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
      rw [pTypeTwistTranslationKernel_irreducibleCharacter psi]
      exact hhPsiRep
    rw [ClassFunction.mem_translationKernel_iff] at hhPsiKernel
    have hhPsiValue := hhPsiKernel (1 : T)
    rw [mul_one] at hhPsiValue
    have hpsiOne : psi 1 = 1 := by
      simpa only [psi,
        pTypeNonGaloisInertiaTwistCharacterFromIndex,
        pTypeIrreducibleCharacterOfMonoidHom_apply] using
        (map_one (pTypeNonGaloisInertiaTwistMonoidHomFromIndex
          ctx facts not_Galois i))
    have hhPsiOne : psi (hT : T) = 1 :=
      hhPsiValue.trans hpsiOne
    have hresValue := congrArg (fun f : ClassFunction HT ℂ ↦ f hT)
      (pTypeNonGaloisInertiaTwistCharacterFromIndex_restrict
        ctx facts not_Galois i)
    calc
      (i.1 : MulChar data.H₁ ℂ) a =
          pTypeActionConjugateMulChar D data.H₁ (1 : W₁)
            (pTypeNonGaloisSingleCoordinateFamily data i.1 1) z := by
        rw [pTypeNonGaloisSingleCoordinateFamily_one]
        change (i.1 : MulChar data.H₁ ℂ) a =
          (i.1 : MulChar data.H₁ ℂ)
            (((D.W₁_action (1 : W₁)).subgroupMap data.H₁).symm z)
        rw [hz]
      _ = pTypeNonGaloisSingleCoordinateCharacter D data i.1
          (z : ptypeFCoreFactor ctx) :=
        (pTypeNonGaloisCoordinateCharacter_apply_coordinate
          D data (pTypeNonGaloisSingleCoordinateFamily data i.1)
            (1 : W₁) z).symm
      _ = pTypeNonGaloisSingleHCharacter
          ctx facts not_Galois i.1 h := by
        rw [pTypeNonGaloisSingleCoordinateCharacter_apply,
          pTypeNonGaloisSingleHCharacter_apply, hh]
      _ = pTypeNonGaloisSingleHCharacterInInertia
          ctx facts not_Galois i.1 hT := by
        rw [pTypeNonGaloisSingleHCharacterInInertia_apply]
        rfl
      _ = psi (hT : T) := by
        simpa only [ClassFunction.restrict_apply, psi] using hresValue.symm
      _ = 1 := hhPsiOne
      _ = (1 : MulChar data.H₁ ℂ) a := by
        rw [MulChar.one_apply (Group.isUnit a)]
  rw [mem_Iirr_kerD]
  exact ⟨hLowerKernel, hUpperNotKernel⟩

/-- Inducing an intermediate twist to `M` lands in the literal clause-(d)
source family. -/
private theorem pTypeNonGaloisAmbientTwist_mem_seqIndD
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀UPrime := pTypeH0DerivedComplementInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
    ClassFunction.induce HU
        (pTypeNonGaloisHUCharacterFromTwistIndex
          ctx facts not_Galois i : ClassFunction HU ℂ) ∈
      seqIndD (k := ℂ) HU H H₀UPrime := by
  apply seqIndP.mpr
  exact ⟨pTypeNonGaloisHUCharacterFromTwistIndex
      ctx facts not_Galois i,
    pTypeNonGaloisHUCharacterFromTwistIndex_mem_Iirr_kerD
      ctx facts not_Galois i, rfl⟩

/-! ## Fibers and the intermediate image -/

private theorem pTypeNonGaloisHUCharacterFromTwistIndex_fiber_le
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i₀ : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
    let F := pTypeNonGaloisHUCharacterFromTwistIndex
      ctx facts not_Galois
    {i ∈ (Finset.univ : Finset I) | F i = F i₀}.card ≤
      pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
  classical
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
  let S : I → IrreducibleCharacter T ℂ :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex
      ctx facts not_Galois
  let F : I → IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCharacterFromTwistIndex
      ctx facts not_Galois
  let fiber := {i ∈ (Finset.univ : Finset I) | F i = F i₀}
  letI : Invertible (Nat.card T : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := T)).ne')
  have hOrbit (j : {i : I // i ∈ fiber}) :
      S j.1 ∈ MulAction.orbit HU (S i₀) := by
    have hj : F j.1 = F i₀ :=
      (Finset.mem_filter.mp j.property).2
    apply (ClassFunction.cfclass_Ind_irrP T (S j.1) (S i₀)).2
    simpa only [S, F,
      pTypeNonGaloisHUCharacterFromTwistIndex_coe] using
        congrArg Subtype.val hj
  let toOrbit : {i : I // i ∈ fiber} →
      MulAction.orbit HU (S i₀) :=
    fun j ↦ ⟨S j.1, hOrbit j⟩
  have hToOrbitInjective : Function.Injective toOrbit := by
    intro j k hjk
    apply Subtype.ext
    apply pTypeNonGaloisInertiaTwistCharacterFromIndex_injective
      ctx facts not_Galois
    exact congrArg Subtype.val hjk
  have hInertia : ClassFunction.inertia T
      (S i₀ : ClassFunction T ℂ) = T :=
    le_antisymm
      (pTypeNonGaloisInertiaTwistCharacter_inertia_le
        ctx facts not_Galois i₀)
      (ClassFunction.le_inertia T (S i₀ : ClassFunction T ℂ))
  have hStabilizer : MulAction.stabilizer HU (S i₀) = T :=
    (IrreducibleCharacter.stabilizer_eq_inertia T (S i₀)).trans
      hInertia
  have hIndexOrbit := MulAction.index_stabilizer HU (S i₀)
  rw [hStabilizer] at hIndexOrbit
  have hOrbitCard : Nat.card (MulAction.orbit HU (S i₀)) =
      T.index := by
    rw [Nat.card_coe_set_eq]
    exact hIndexOrbit.symm
  calc
    fiber.card = Nat.card {i : I // i ∈ fiber} := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card (MulAction.orbit HU (S i₀)) :=
      Nat.card_le_card_of_injective toOrbit hToOrbitInjective
    _ = T.index := hOrbitCard
    _ = pTypeNonGaloisIndex hD not_Galois :=
      pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois

private theorem pTypeNonGaloisInertiaTwistIndex_card_le_HU_image
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
    let F := pTypeNonGaloisHUCharacterFromTwistIndex
      ctx facts not_Galois
    Nat.card I ≤
      pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois *
        (Finset.univ.image F).card := by
  classical
  let hD := Ptype_factor_action_hypotheses ctx facts
  let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
  let F := pTypeNonGaloisHUCharacterFromTwistIndex
    ctx facts not_Galois
  have hcard := Finset.card_le_mul_card_image
    (f := F) (Finset.univ : Finset I)
    (pTypeNonGaloisIndex hD not_Galois) (fun chi hchi ↦ by
      obtain ⟨i₀, _hi₀, rfl⟩ := Finset.mem_image.mp hchi
      exact pTypeNonGaloisHUCharacterFromTwistIndex_fiber_le
        ctx facts not_Galois i₀)
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card, I, F] using hcard

/-- The twist source cardinality is the non-Galois index times clause (d)'s
internal lower quotient. -/
private theorem pTypeNonGaloisInertiaTwistIndex_card_eq_index_mul_lower
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
    Nat.card I = pTypeNonGaloisIndex hD not_Galois *
      (((D.p - 1) * Nat.card U) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 *
          Nat.card (_root_.commutator U))) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let UPrime := _root_.commutator U
  let hUPrimeK : UPrime ≤ K :=
    pTypeDerived_le_nonGaloisActionKernel hD not_Galois
  let UPrimeK := UPrime.subgroupOf K
  let Q := PTypeNonGaloisInertiaTwistQuotient
    ctx facts not_Galois
  let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
  let a := pTypeNonGaloisIndex hD not_Galois
  have hQcard : Nat.card K = Nat.card Q * Nat.card UPrime := by
    calc
      Nat.card K = Nat.card Q * Nat.card UPrimeK :=
        UPrimeK.card_eq_card_quotient_mul_card_subgroup
      _ = Nat.card Q * Nat.card UPrime := by
        rw [natCard_subgroupOf_eq hUPrimeK]
  have hUcard : Nat.card U = a * (Nat.card Q * Nat.card UPrime) := by
    calc
      Nat.card U = K.index * Nat.card K := K.index_mul_card.symm
      _ = a * Nat.card K := by rfl
      _ = a * (Nat.card Q * Nat.card UPrime) := by rw [hQcard]
  obtain ⟨c, hc⟩ := pTypeNonGaloisIndex_dvd_prime_pred
    hD not_Galois
  have hdenDvd : a ^ 2 * Nat.card UPrime ∣
      (D.p - 1) * Nat.card U :=
    pTypeNonGaloisLowerDenominator_dvd_internal hD not_Galois
  have hnumerator : (D.p - 1) * Nat.card U =
      (a ^ 2 * Nat.card UPrime) * (c * Nat.card Q) := by
    rw [hc, hUcard]
    ring
  have hdenPos : 0 < a ^ 2 * Nat.card UPrime :=
    Nat.mul_pos (pow_pos (Nat.zero_lt_of_lt
      (one_lt_pTypeNonGaloisIndex hD not_Galois)) _)
      (Nat.card_pos (α := UPrime))
  have hlower : ((D.p - 1) * Nat.card U) /
      (a ^ 2 * Nat.card UPrime) = c * Nat.card Q := by
    apply Nat.eq_of_mul_eq_mul_left hdenPos
    calc
      (a ^ 2 * Nat.card UPrime) *
          (((D.p - 1) * Nat.card U) /
            (a ^ 2 * Nat.card UPrime)) =
        (((D.p - 1) * Nat.card U) /
            (a ^ 2 * Nat.card UPrime)) *
          (a ^ 2 * Nat.card UPrime) := by ac_rfl
      _ = (D.p - 1) * Nat.card U :=
        Nat.div_mul_cancel hdenDvd
      _ = (a ^ 2 * Nat.card UPrime) * (c * Nat.card Q) :=
        hnumerator
  change Nat.card I = a *
    (((D.p - 1) * Nat.card U) / (a ^ 2 * Nat.card UPrime))
  rw [pTypeNonGaloisInertiaTwistIndex_card ctx facts not_Galois,
    hlower, hc]
  ring

/-- The distinct intermediate twists already meet clause (d)'s lower
quotient. -/
private theorem pTypeNonGaloisLowerQuotient_le_HU_image
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let F := pTypeNonGaloisHUCharacterFromTwistIndex
      ctx facts not_Galois
    ((D.p - 1) * Nat.card U) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 *
          Nat.card (_root_.commutator U)) ≤
      (Finset.univ.image F).card := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let I := PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois
  let F := pTypeNonGaloisHUCharacterFromTwistIndex
    ctx facts not_Galois
  let lower := ((D.p - 1) * Nat.card U) /
    (pTypeNonGaloisIndex hD not_Galois ^ 2 *
      Nat.card (_root_.commutator U))
  have hcard := pTypeNonGaloisInertiaTwistIndex_card_le_HU_image
    ctx facts not_Galois
  change Nat.card I ≤
    pTypeNonGaloisIndex hD not_Galois *
      (Finset.univ.image F).card at hcard
  have hsource : Nat.card I =
      pTypeNonGaloisIndex hD not_Galois * lower := by
    simpa only [I, D, hD, lower] using
      (pTypeNonGaloisInertiaTwistIndex_card_eq_index_mul_lower
        ctx facts not_Galois)
  rw [hsource] at hcard
  exact Nat.le_of_mul_le_mul_left hcard
    (Nat.zero_lt_of_lt (one_lt_pTypeNonGaloisIndex hD not_Galois))

/-! ## Transport to the ambient inertia subgroup -/

private theorem pTypeTwistInduceComapMulEquivSubgroupCongr
    {A : Type u} [Group A] [Fintype A]
    (H K : Subgroup A) (hHK : H = K)
    (chi : IrreducibleCharacter K ℂ) :
    ClassFunction.induce H
        (pTypeTwistComapMulEquiv
          (MulEquiv.subgroupCongr hHK) chi : ClassFunction H ℂ) =
      ClassFunction.induce K (chi : ClassFunction K ℂ) := by
  subst K
  apply congrArg (ClassFunction.induce H)
  ext x
  rw [pTypeTwistComapMulEquiv_apply]
  apply congrArg (fun y : H ↦ chi y)
  apply Subtype.ext
  rfl

private theorem pTypeTwistInduceNestedImage_trans
    {A : Type u} [Group A] [Fintype A]
    (L : Subgroup A) (T : Subgroup L)
    (psi : IrreducibleCharacter T ℂ) :
    let TM := T.map L.subtype
    let eT : T ≃* TM :=
      T.equivMapOfInjective L.subtype L.subtype_injective
    let psiM : IrreducibleCharacter TM ℂ :=
      pTypeTwistComapMulEquiv eT.symm psi
    ClassFunction.induce L
        (ClassFunction.induce T (psi : ClassFunction T ℂ)) =
      ClassFunction.induce TM (psiM : ClassFunction TM ℂ) := by
  classical
  let TM := T.map L.subtype
  let eT : T ≃* TM :=
    T.equivMapOfInjective L.subtype L.subtype_injective
  let psiM : IrreducibleCharacter TM ℂ :=
    pTypeTwistComapMulEquiv eT.symm psi
  have hTML : TM ≤ L := by
    rintro x ⟨t, _ht, htx⟩
    exact htx ▸ t.property
  have hNested : TM.subgroupOf L = T := by
    ext t
    constructor
    · rintro ⟨s, hs, hst⟩
      exact L.subtype_injective hst ▸ hs
    · intro ht
      exact ⟨t, ht, rfl⟩
  have htransport : ClassFunction.toSubgroupOf TM L hTML
        (psiM : ClassFunction TM ℂ) =
      (pTypeTwistComapMulEquiv
        (MulEquiv.subgroupCongr hNested) psi :
          ClassFunction (TM.subgroupOf L) ℂ) := by
    ext t
    rw [ClassFunction.toSubgroupOf_apply,
      pTypeTwistComapMulEquiv_apply,
      pTypeTwistComapMulEquiv_apply]
    apply congrArg psi
    apply eT.injective
    rw [eT.apply_symm_apply]
    apply Subtype.ext
    rfl
  calc
    ClassFunction.induce L
        (ClassFunction.induce T (psi : ClassFunction T ℂ)) =
      ClassFunction.induce L
        (ClassFunction.induce (TM.subgroupOf L)
          (ClassFunction.toSubgroupOf TM L hTML
            (psiM : ClassFunction TM ℂ))) := by
      rw [htransport,
        pTypeTwistInduceComapMulEquivSubgroupCongr
          (TM.subgroupOf L) T hNested psi]
    _ = ClassFunction.induce TM (psiM : ClassFunction TM ℂ) :=
      ClassFunction.induce_trans TM L hTML (psiM : ClassFunction TM ℂ)

/-- Transport a flattened twist to the literal inertia subgroup of the
selected F-core character in `M`. -/
private noncomputable def pTypeNonGaloisAmbientInertiaTwistCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HM := (Fitting_core M).subgroupOf M
    let thetaM := pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois i.1
    IrreducibleCharacter
      (ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ)) ℂ := by
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let TM := T.map HU.subtype
  let thetaM : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois i.1
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex
      ctx facts not_Galois i
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  have hInertia : ClassFunction.inertia HM
      (thetaM : ClassFunction HM ℂ) = TM :=
    pTypeNonGaloisSingleFCoreCharacter_inertia
      ctx facts not_Galois i.1 hi
  let eT : T ≃* TM :=
    T.equivMapOfInjective HU.subtype HU.subtype_injective
  let eI : ClassFunction.inertia HM
        (thetaM : ClassFunction HM ℂ) ≃* TM :=
    MulEquiv.subgroupCongr hInertia
  exact pTypeTwistComapMulEquiv eI
    (pTypeTwistComapMulEquiv eT.symm psi)

/-- The transported twist restricts to the selected F-core character inside
its literal ambient inertia subgroup. -/
private theorem pTypeNonGaloisAmbientInertiaTwistCharacter_restrict
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HM := (Fitting_core M).subgroupOf M
    let thetaM := pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois i.1
    let I := ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ)
    let HI := HM.subgroupOf I
    ClassFunction.restrict HI
        (pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois i : ClassFunction I ℂ) =
      ClassFunction.comap
        (Subgroup.subgroupOfEquivOfLe
          (ClassFunction.le_inertia HM _)).toMonoidHom
        (thetaM : ClassFunction HM ℂ) := by
  classical
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let H := HM.subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let TM := T.map HU.subtype
  let HT := H.subgroupOf T
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex
      ctx facts not_Galois i
  let thetaM : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois i.1
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  letI : HM.Normal := Fcore_normal M
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hInertia : ClassFunction.inertia HM
      (thetaM : ClassFunction HM ℂ) = TM :=
    pTypeNonGaloisSingleFCoreCharacter_inertia
      ctx facts not_Galois i.1 hi
  let eT : T ≃* TM :=
    T.equivMapOfInjective HU.subtype HU.subtype_injective
  let psiM : IrreducibleCharacter TM ℂ :=
    pTypeTwistComapMulEquiv eT.symm psi
  let eI : ClassFunction.inertia HM
        (thetaM : ClassFunction HM ℂ) ≃* TM :=
    MulEquiv.subgroupCongr hInertia
  let I := ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ)
  let HI := HM.subgroupOf I
  have hres : ClassFunction.restrict HT (psi : ClassFunction T ℂ) =
      (pTypeNonGaloisSingleHCharacterInInertia
        ctx facts not_Galois i.1 : ClassFunction HT ℂ) :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex_restrict
      ctx facts not_Galois i
  ext h
  let hM : HM := Subgroup.subgroupOfEquivOfLe
    (ClassFunction.le_inertia HM (thetaM : ClassFunction HM ℂ)) h
  let tM : TM := eI (h : I)
  let t : T := eT.symm tM
  have htMap : eT t = tM := eT.apply_symm_apply tM
  have htUnderlying : (((t : T) : HU) : M) = (hM : M) := by
    calc
      (((t : T) : HU) : M) = ((eT t : TM) : M) := rfl
      _ = (tM : M) := congrArg (fun x : TM ↦ (x : M)) htMap
      _ = ((eI (h : I) : TM) : M) := rfl
      _ = (((h : HI) : I) : M) := rfl
      _ = (hM : M) := rfl
  let hH : H := ⟨(t : HU), by
    change ((((t : T) : HU) : M) : Gamma) ∈ Fitting_core M
    rw [htUnderlying]
    exact hM.property⟩
  let ht : HT := ⟨t, hH.property⟩
  have hresValue := congrArg (fun f : ClassFunction HT ℂ ↦ f ht) hres
  have hNestedEq : hH =
      (⟨⟨hM, hHder hM.property⟩, hM.property⟩ : H) := by
    apply Subtype.ext
    apply Subtype.ext
    exact htUnderlying
  calc
    ClassFunction.restrict HI
        (pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois i : ClassFunction I ℂ) h =
        psi (t : T) := by
      rw [ClassFunction.restrict_apply,
        pTypeNonGaloisAmbientInertiaTwistCharacter,
        pTypeTwistComapMulEquiv_apply,
        pTypeTwistComapMulEquiv_apply]
    _ = pTypeNonGaloisSingleHCharacterInInertia
        ctx facts not_Galois i.1 ht := by
      simpa only [ClassFunction.restrict_apply] using hresValue
    _ = pTypeNonGaloisSingleHCharacter
        ctx facts not_Galois i.1 hH := by
      rw [pTypeNonGaloisSingleHCharacterInInertia_apply]
      rfl
    _ = thetaM hM := by
      rw [hNestedEq]
      simpa only [thetaM] using
        (pTypeNonGaloisSingleFCoreCharacter_eq_nested
          ctx facts not_Galois i.1 hM).symm
    _ = ClassFunction.comap
        (Subgroup.subgroupOfEquivOfLe
          (ClassFunction.le_inertia HM _)).toMonoidHom
        (thetaM : ClassFunction HM ℂ) h := by
      rw [ClassFunction.comap_apply]
      rfl

/-- For a fixed selected F-core character, transport to the literal ambient
inertia subgroup does not identify two quotient twists. -/
private theorem pTypeNonGaloisAmbientInertiaTwistCharacter_fixed_injective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let Q := PTypeNonGaloisInertiaTwistQuotient
      ctx facts not_Galois
    ∀ {tau sigma : MulChar Q ℂ},
      pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois (i.1, tau) =
        pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois (i.1, sigma) →
      tau = sigma := by
  classical
  dsimp only
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let TM := T.map HU.subtype
  let thetaM : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois i.1
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  have hInertia : ClassFunction.inertia HM
      (thetaM : ClassFunction HM ℂ) = TM :=
    pTypeNonGaloisSingleFCoreCharacter_inertia
      ctx facts not_Galois i.1 hi
  let eT : T ≃* TM :=
    T.equivMapOfInjective HU.subtype HU.subtype_injective
  let eI : ClassFunction.inertia HM
        (thetaM : ClassFunction HM ℂ) ≃* TM :=
    MulEquiv.subgroupCongr hInertia
  intro tau sigma hpsi
  have hsource :
      pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois (i.1, tau) =
        pTypeNonGaloisInertiaTwistCharacterFromIndex
          ctx facts not_Galois (i.1, sigma) := by
    apply pTypeTwistComapMulEquiv_injective eT.symm
    apply pTypeTwistComapMulEquiv_injective eI
    simpa only [pTypeNonGaloisAmbientInertiaTwistCharacter,
      thetaM, eT, eI, TM] using hpsi
  have hindex :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex_injective
      ctx facts not_Galois hsource
  exact congrArg Prod.snd hindex

/-- Induction from the transported inertia subgroup agrees with the original
two-stage induction through `HU`. -/
private theorem pTypeNonGaloisAmbientTwist_induce_transport
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HM := (Fitting_core M).subgroupOf M
    let thetaM := pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois i.1
    let I := ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ)
    ClassFunction.induce I
        (pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois i : ClassFunction I ℂ) =
      ClassFunction.induce HU
        (pTypeNonGaloisHUCharacterFromTwistIndex
          ctx facts not_Galois i : ClassFunction HU ℂ) := by
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let TM := T.map HU.subtype
  let thetaM : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois i.1
  let psi : IrreducibleCharacter T ℂ :=
    pTypeNonGaloisInertiaTwistCharacterFromIndex
      ctx facts not_Galois i
  let hi : (i.1 : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one i.1
  have hInertia : ClassFunction.inertia HM
      (thetaM : ClassFunction HM ℂ) = TM :=
    pTypeNonGaloisSingleFCoreCharacter_inertia
      ctx facts not_Galois i.1 hi
  let eT : T ≃* TM :=
    T.equivMapOfInjective HU.subtype HU.subtype_injective
  let psiM : IrreducibleCharacter TM ℂ :=
    pTypeTwistComapMulEquiv eT.symm psi
  let eI : ClassFunction.inertia HM
        (thetaM : ClassFunction HM ℂ) ≃* TM :=
    MulEquiv.subgroupCongr hInertia
  have hNested : ClassFunction.induce HU
        (ClassFunction.induce T (psi : ClassFunction T ℂ)) =
      ClassFunction.induce TM (psiM : ClassFunction TM ℂ) := by
    simpa only [TM, eT, psiM] using
        (pTypeTwistInduceNestedImage_trans HU T psi)
  have hTransport : ClassFunction.induce
        (ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ))
        (pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois i : ClassFunction _ ℂ) =
      ClassFunction.induce TM (psiM : ClassFunction TM ℂ) := by
    exact pTypeTwistInduceComapMulEquivSubgroupCongr
      (ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ))
      TM hInertia psiM
  rw [pTypeNonGaloisHUCharacterFromTwistIndex_coe]
  exact hTransport.trans hNested.symm

private theorem pTypeNonGaloisAmbientTwist_induce_irreducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (i : PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    IsIrreducibleCharacter M ℂ
      (ClassFunction.induce HU
        (pTypeNonGaloisHUCharacterFromTwistIndex
          ctx facts not_Galois i : ClassFunction HU ℂ)) := by
  classical
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let thetaM : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter ctx facts not_Galois i.1
  let I := ClassFunction.inertia HM (thetaM : ClassFunction HM ℂ)
  let psiI : IrreducibleCharacter I ℂ :=
    pTypeNonGaloisAmbientInertiaTwistCharacter
      ctx facts not_Galois i
  letI : HM.Normal := Fcore_normal M
  have hrestrict :=
    pTypeNonGaloisAmbientInertiaTwistCharacter_restrict
      ctx facts not_Galois i
  have hirr : IsIrreducibleCharacter M ℂ
      (ClassFunction.induce I (psiI : ClassFunction I ℂ)) :=
    pTypeTwistExtension_induce_isIrreducible
      HM thetaM psiI hrestrict
  rw [pTypeNonGaloisAmbientTwist_induce_transport
    ctx facts not_Galois i] at hirr
  exact hirr

/-! ## A reduced ambient source family -/

/-- Choose one selected `HU`-orbit representative and one quotient twist. -/
private abbrev PTypeNonGaloisAmbientSelectedIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :=
  PTypeNonGaloisSelectedHOrbitIndex ctx facts not_Galois ×
    MulChar (PTypeNonGaloisInertiaTwistQuotient
      ctx facts not_Galois) ℂ

private noncomputable def pTypeNonGaloisAmbientSelectedToTwistIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    PTypeNonGaloisAmbientSelectedIndex ctx facts not_Galois →
      PTypeNonGaloisInertiaTwistIndex ctx facts not_Galois :=
  fun j ↦
    (pTypeNonGaloisSelectedHOrbitRepresentative
      ctx facts not_Galois j.1, j.2)

private noncomputable def pTypeNonGaloisAmbientSelectedCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    PTypeNonGaloisAmbientSelectedIndex ctx facts not_Galois →
      IrreducibleCharacter M ℂ := fun j ↦ by
  let i := pTypeNonGaloisAmbientSelectedToTwistIndex
    ctx facts not_Galois j
  exact ⟨ClassFunction.induce
      (pTypeHUInMaximal M (derivedWithin M))
      (pTypeNonGaloisHUCharacterFromTwistIndex
        ctx facts not_Galois i : ClassFunction _ ℂ),
    pTypeNonGaloisAmbientTwist_induce_irreducible
      ctx facts not_Galois i⟩

@[simp]
private theorem pTypeNonGaloisAmbientSelectedCharacter_coe
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (j : PTypeNonGaloisAmbientSelectedIndex ctx facts not_Galois) :
    (pTypeNonGaloisAmbientSelectedCharacter
      ctx facts not_Galois j : ClassFunction M ℂ) =
      ClassFunction.induce
        (pTypeHUInMaximal M (derivedWithin M))
        (pTypeNonGaloisHUCharacterFromTwistIndex
          ctx facts not_Galois
            (pTypeNonGaloisAmbientSelectedToTwistIndex
              ctx facts not_Galois j) : ClassFunction _ ℂ) :=
  rfl

/-- The reduced ambient character is also the one-step induction of its
transported extension from the literal ambient inertia subgroup. -/
private theorem pTypeNonGaloisAmbientSelectedCharacter_eq_induce_inertia
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (j : PTypeNonGaloisAmbientSelectedIndex
      ctx facts not_Galois) :
    let i := pTypeNonGaloisAmbientSelectedToTwistIndex
      ctx facts not_Galois j
    let HM := (Fitting_core M).subgroupOf M
    let thetaM := pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois i.1
    let I := ClassFunction.inertia HM
      (thetaM : ClassFunction HM ℂ)
    (pTypeNonGaloisAmbientSelectedCharacter
        ctx facts not_Galois j : ClassFunction M ℂ) =
      ClassFunction.induce I
        (pTypeNonGaloisAmbientInertiaTwistCharacter
          ctx facts not_Galois i : ClassFunction I ℂ) := by
  rw [pTypeNonGaloisAmbientSelectedCharacter_coe]
  exact (pTypeNonGaloisAmbientTwist_induce_transport
    ctx facts not_Galois
      (pTypeNonGaloisAmbientSelectedToTwistIndex
        ctx facts not_Galois j)).symm

/-- Selecting one representative from each `HU`-orbit removes precisely the
remaining collisions in outer induction. -/
private theorem pTypeNonGaloisAmbientSelectedCharacter_injective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Function.Injective
      (pTypeNonGaloisAmbientSelectedCharacter
        ctx facts not_Galois) := by
  classical
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HM := (Fitting_core M).subgroupOf M
  let H := HM.subgroupOf HU
  let Z := pTypeNonGaloisAmbientSelectedCharacter
    ctx facts not_Galois
  let toI := pTypeNonGaloisAmbientSelectedToTwistIndex
    ctx facts not_Galois
  letI : HM.Normal := Fcore_normal M
  rintro ⟨OJ, tauJ⟩ ⟨OK, tauK⟩ hZ
  let j : PTypeNonGaloisAmbientSelectedIndex
      ctx facts not_Galois := (OJ, tauJ)
  let k : PTypeNonGaloisAmbientSelectedIndex
      ctx facts not_Galois := (OK, tauK)
  let iJ := toI j
  let iK := toI k
  have hZjk : Z j = Z k := by
    simpa only [Z, j, k] using hZ
  let lambdaJ := pTypeNonGaloisSelectedHOrbitRepresentative
    ctx facts not_Galois OJ
  let lambdaK := pTypeNonGaloisSelectedHOrbitRepresentative
    ctx facts not_Galois OK
  let thetaHJ : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisSingleHCharacter
      ctx facts not_Galois lambdaJ
  let thetaHK : IrreducibleCharacter H ℂ :=
    pTypeNonGaloisSingleHCharacter
      ctx facts not_Galois lambdaK
  let thetaMJ : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois lambdaJ
  let thetaMK : IrreducibleCharacter HM ℂ :=
    pTypeNonGaloisSingleFCoreCharacter
      ctx facts not_Galois lambdaK
  let psiJ := pTypeNonGaloisAmbientInertiaTwistCharacter
    ctx facts not_Galois (lambdaJ, tauJ)
  let psiK := pTypeNonGaloisAmbientInertiaTwistCharacter
    ctx facts not_Galois (lambdaK, tauK)
  have hrestrictJ :=
    pTypeNonGaloisAmbientInertiaTwistCharacter_restrict
      ctx facts not_Galois (lambdaJ, tauJ)
  have hrestrictK :=
    pTypeNonGaloisAmbientInertiaTwistCharacter_restrict
      ctx facts not_Galois (lambdaK, tauK)
  have hIndJ :=
    pTypeNonGaloisAmbientSelectedCharacter_eq_induce_inertia
      ctx facts not_Galois j
  have hIndK :=
    pTypeNonGaloisAmbientSelectedCharacter_eq_induce_inertia
      ctx facts not_Galois k
  have hconstJ : (Z j).IsConstituent
      (ClassFunction.induce HM
        (thetaMJ : ClassFunction HM ℂ)) := by
    exact pTypeTwistExtension_induced_isConstituent
      HM thetaMJ psiJ hrestrictJ (Z j) hIndJ
  have hconstK' : (Z k).IsConstituent
      (ClassFunction.induce HM
        (thetaMK : ClassFunction HM ℂ)) := by
    exact pTypeTwistExtension_induced_isConstituent
      HM thetaMK psiK hrestrictK (Z k) hIndK
  have hconstK : (Z j).IsConstituent
      (ClassFunction.induce HM
        (thetaMK : ClassFunction HM ℂ)) := by
    rw [hZjk]
    exact hconstK'
  obtain ⟨x, hx⟩ :=
    pTypeTwistCommonInducedConstituent_conjugate
      HM thetaMJ thetaMK (Z j) hconstJ hconstK
  have hlambdaJ : (lambdaJ : MulChar data.H₁ ℂ) ≠ 1 :=
    pTypeNontrivialMulCharSubtype_ne_one lambdaJ
  obtain ⟨d, hd⟩ :=
    pTypeNonGaloisSingleFCoreCharacter_conjugator_mem_HU
      ctx facts not_Galois lambdaJ lambdaK hlambdaJ x hx
  have hNested : ClassFunction.normalConjugate H d
      (thetaHJ : ClassFunction H ℂ) =
        (thetaHK : ClassFunction H ℂ) :=
    pTypeNonGaloisSingleFCoreCharacter_conjugate_nested
      ctx facts not_Galois lambdaJ lambdaK d (by
        simpa only [hd] using hx)
  have hBundle : d • thetaHJ = thetaHK := by
    apply Subtype.ext
    exact hNested
  have hThetaOrbit : MulAction.orbit HU thetaHJ =
      MulAction.orbit HU thetaHK := by
    rw [← hBundle, MulAction.orbit_smul]
  have hOJ := pTypeNonGaloisSelectedHOrbitRepresentative_orbit
    ctx facts not_Galois OJ
  have hOK := pTypeNonGaloisSelectedHOrbitRepresentative_orbit
    ctx facts not_Galois OK
  have hOrbitKey : OJ = OK := by
    apply Subtype.ext
    exact hOJ.symm.trans (hThetaOrbit.trans hOK)
  subst OK
  let kFresh : PTypeNonGaloisAmbientSelectedIndex
      ctx facts not_Galois := (OJ, tauK)
  let psiKFresh := pTypeNonGaloisAmbientInertiaTwistCharacter
    ctx facts not_Galois (lambdaJ, tauK)
  have hrestrictKFresh :=
    pTypeNonGaloisAmbientInertiaTwistCharacter_restrict
      ctx facts not_Galois (lambdaJ, tauK)
  have hIndKFresh :=
    pTypeNonGaloisAmbientSelectedCharacter_eq_induce_inertia
      ctx facts not_Galois kFresh
  have hZjkFresh : Z j = Z kFresh := by
    simpa only [kFresh, k] using hZjk
  have hInduceEq := hIndJ.symm.trans
    ((congrArg Subtype.val hZjkFresh).trans hIndKFresh)
  have hpsi : psiJ = psiKFresh := by
    exact pTypeTwistExtension_induce_injective
      HM thetaMJ psiJ psiKFresh hrestrictJ hrestrictKFresh
        hInduceEq
  have htau : tauJ = tauK := by
    apply pTypeNonGaloisAmbientInertiaTwistCharacter_fixed_injective
      ctx facts not_Galois iJ
    simpa only [psiJ, psiKFresh, iJ, toI, j,
      pTypeNonGaloisAmbientSelectedToTwistIndex] using hpsi
  exact Prod.ext rfl htau

/-! ## Cardinality and degree of the reduced ambient family -/

/-- Choosing one representative from every selected `HU`-orbit preserves
enough quotient twists to attain the internal lower bound in clause (d). -/
private theorem pTypeNonGaloisLowerQuotient_le_ambientSelectedIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    ((D.p - 1) * Nat.card U) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 *
          Nat.card (_root_.commutator U)) ≤
      Nat.card (PTypeNonGaloisAmbientSelectedIndex
        ctx facts not_Galois) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let Q := PTypeNonGaloisInertiaTwistQuotient
    ctx facts not_Galois
  let I := PTypeNonGaloisInertiaTwistIndex
    ctx facts not_Galois
  let B := PTypeNonGaloisSelectedHOrbitIndex
    ctx facts not_Galois
  let J := PTypeNonGaloisAmbientSelectedIndex
    ctx facts not_Galois
  let lower := ((D.p - 1) * Nat.card U) /
    (a ^ 2 * Nat.card (_root_.commutator U))
  have hIcardLower : Nat.card I = a * lower := by
    simpa only [I, a, lower, D, hD] using
      (pTypeNonGaloisInertiaTwistIndex_card_eq_index_mul_lower
        ctx facts not_Galois)
  have hIcardQ : Nat.card I = (D.p - 1) * Nat.card Q := by
    simpa only [I, Q, D] using
      (pTypeNonGaloisInertiaTwistIndex_card
        ctx facts not_Galois)
  have hsource : a * lower = (D.p - 1) * Nat.card Q := by
    exact hIcardLower.symm.trans hIcardQ
  have horbit : D.p - 1 ≤ a * Nat.card B :=
    pTypeNonGaloisSelectedHOrbit_card_bound
      ctx facts not_Galois
  have hQcard : Nat.card (MulChar Q ℂ) = Nat.card Q := by
    calc
      Nat.card (MulChar Q ℂ) = Nat.card Qˣ :=
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity Q ℂ
      _ = Nat.card Q := Nat.card_congr toUnits.toEquiv.symm
  have hJcard : Nat.card J = Nat.card B * Nat.card Q := by
    rw [Nat.card_prod, hQcard]
  have hscaled : (D.p - 1) * Nat.card Q ≤
      (a * Nat.card B) * Nat.card Q :=
    Nat.mul_le_mul_right (Nat.card Q) horbit
  apply Nat.le_of_mul_le_mul_left _
    (Nat.zero_lt_of_lt (one_lt_pTypeNonGaloisIndex hD not_Galois))
  calc
    a * lower = (D.p - 1) * Nat.card Q := hsource
    _ ≤ (a * Nat.card B) * Nat.card Q := hscaled
    _ = a * Nat.card J := by rw [hJcard]; ring

/-- Outer induction multiplies the intermediate degree by the action
parameter `q`. -/
private theorem pTypeNonGaloisAmbientSelectedCharacter_degree
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (j : PTypeNonGaloisAmbientSelectedIndex
      ctx facts not_Galois) :
    pTypeIrreducibleDegree
        (pTypeNonGaloisAmbientSelectedCharacter
          ctx facts not_Galois j) =
      (Ptype_factor_action ctx facts).q *
        pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let i := pTypeNonGaloisAmbientSelectedToTwistIndex
    ctx facts not_Galois j
  let chi := pTypeNonGaloisHUCharacterFromTwistIndex
    ctx facts not_Galois i
  let zeta := pTypeNonGaloisAmbientSelectedCharacter
    ctx facts not_Galois j
  have houter : IsInternalSemidirectProductIn
      (derivedWithin M) W₁ M := ctx.typeP.1.2.2.2
  have hHUIndex : HU.index = D.q := by
    calc
      HU.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ := natCard_subgroupOf_eq houter.2.1
      _ = D.q := by rw [Ptype_factor_action_q]
  calc
    pTypeIrreducibleDegree zeta =
        HU.index * pTypeIrreducibleDegree chi :=
      pTypeIrreducibleDegree_eq_index_mul_of_induced HU chi zeta rfl
    _ = D.q * pTypeNonGaloisIndex hD not_Galois := by
      rw [hHUIndex,
        pTypeNonGaloisHUCharacterFromTwistIndex_degree
          ctx facts not_Galois i]

/-- Each reduced ambient character lies in the exact degree-filtered family
appearing in clause (d). -/
private theorem pTypeNonGaloisAmbientSelectedCharacter_mem_degreeFilter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (j : PTypeNonGaloisAmbientSelectedIndex
      ctx facts not_Galois) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀UPrime := pTypeH0DerivedComplementInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
    (pTypeNonGaloisAmbientSelectedCharacter
      ctx facts not_Galois j : ClassFunction M ℂ) ∈
      (seqIndD (k := ℂ) HU H H₀UPrime).filter fun zeta ↦
        pTypeIsIrreducibleOfDegree
          (D.q * pTypeNonGaloisIndex hD not_Galois) zeta := by
  let i := pTypeNonGaloisAmbientSelectedToTwistIndex
    ctx facts not_Galois j
  apply Finset.mem_filter.mpr
  refine ⟨pTypeNonGaloisAmbientTwist_mem_seqIndD
      ctx facts not_Galois i, ?_⟩
  exact ⟨pTypeNonGaloisAmbientSelectedCharacter
      ctx facts not_Galois j, rfl,
    pTypeNonGaloisAmbientSelectedCharacter_degree
      ctx facts not_Galois j⟩

/-- Transporting the complement and its commutator into `M` leaves the
numerical lower quotient unchanged. -/
private theorem pTypeNonGaloisMappedLowerQuotient_eq_internal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let hUM : U ≤ M :=
      ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1
    pTypeNonGaloisLowerNumerator D.p (U.subgroupOf M) /
        pTypeNonGaloisLowerDenominator
          (pTypeNonGaloisIndex hD not_Galois)
          (pTypeDerivedComplementInMaximal
            (Subgroup.inclusion hUM)) =
      ((D.p - 1) * Nat.card U) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 *
          Nat.card (_root_.commutator U)) := by
  dsimp only
  let hUM : U ≤ M :=
    ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1
  have hUPrimeM : derivedWithin U ≤ M :=
    (Subgroup.map_subtype_le (_root_.commutator U)).trans hUM
  have hUPrimeCard : Nat.card (derivedWithin U) =
      Nat.card (_root_.commutator U) := by
    unfold derivedWithin
    exact Subgroup.card_map_of_injective U.subtype_injective
  unfold pTypeNonGaloisLowerNumerator
    pTypeNonGaloisLowerDenominator
  rw [natCard_subgroupOf_eq hUM,
    pTypeDerivedComplementInMaximal_eq_derivedWithin_subgroupOf hUM,
    natCard_subgroupOf_eq hUPrimeM, hUPrimeCard]

/-- Internal clause-(d) count before rewriting the complement subgroups in
the maximal-subgroup type. -/
private theorem pTypeNonGalois_lower_count_bound_internal
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀UPrime := pTypeH0DerivedComplementInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
    ((D.p - 1) * Nat.card U) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 *
          Nat.card (_root_.commutator U)) ≤
      pTypeNonGaloisDegreeCount HU H H₀UPrime D.q
        (pTypeNonGaloisIndex hD not_Galois) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀UPrime := pTypeH0DerivedComplementInDerived
    M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
  let J := PTypeNonGaloisAmbientSelectedIndex
    ctx facts not_Galois
  let Z := pTypeNonGaloisAmbientSelectedCharacter
    ctx facts not_Galois
  let target :=
    (seqIndD (k := ℂ) HU H H₀UPrime).filter fun zeta ↦
      pTypeIsIrreducibleOfDegree
        (D.q * pTypeNonGaloisIndex hD not_Galois) zeta
  let toTarget : J → {zeta : ClassFunction M ℂ // zeta ∈ target} :=
    fun j ↦ ⟨(Z j : ClassFunction M ℂ),
      pTypeNonGaloisAmbientSelectedCharacter_mem_degreeFilter
        ctx facts not_Galois j⟩
  have hToTarget : Function.Injective toTarget := by
    intro j k hjk
    apply pTypeNonGaloisAmbientSelectedCharacter_injective
      ctx facts not_Galois
    apply IrreducibleCharacter.ext
    intro m
    exact congrArg
      (fun zeta : {zeta : ClassFunction M ℂ // zeta ∈ target} ↦
        zeta.1 m) hjk
  calc
    ((D.p - 1) * Nat.card U) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 *
          Nat.card (_root_.commutator U)) ≤ Nat.card J :=
      pTypeNonGaloisLowerQuotient_le_ambientSelectedIndex
        ctx facts not_Galois
    _ ≤ Nat.card {zeta : ClassFunction M ℂ // zeta ∈ target} :=
      Nat.card_le_card_of_injective toTarget hToTarget
    _ = target.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = pTypeNonGaloisDegreeCount HU H H₀UPrime D.q
        (pTypeNonGaloisIndex hD not_Galois) := rfl

/-- Clause (d)'s lower count after transporting `U` and its commutator to
the maximal-subgroup type used by the final non-Galois conclusion. -/
theorem pTypeNonGalois_lower_count_bound_mapped
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let hUM : U ≤ M :=
      ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀UPrime := pTypeH0DerivedComplementInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U
    pTypeNonGaloisLowerNumerator D.p (U.subgroupOf M) /
        pTypeNonGaloisLowerDenominator
          (pTypeNonGaloisIndex hD not_Galois)
          (pTypeDerivedComplementInMaximal
            (Subgroup.inclusion hUM)) ≤
      pTypeNonGaloisDegreeCount HU H H₀UPrime D.q
        (pTypeNonGaloisIndex hD not_Galois) := by
  dsimp only
  rw [pTypeNonGaloisMappedLowerQuotient_eq_internal
    ctx facts not_Galois]
  exact pTypeNonGalois_lower_count_bound_internal
    ctx facts not_Galois

end PTypeNonGaloisTwistInductionInternal

end

end Submission.OddOrder.PF
