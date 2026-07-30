import Submission.OddOrder.PF.Section09.PTypeGaloisLocalFrobenius
import Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer
import Submission.OddOrder.PF.Section09.PTypeNonGaloisCliffordSupport
import Submission.OddOrder.PF.Section09.PTypeCoreContext

/-!
# Peterfalvi Section 9: the Galois-character conclusion

This module assembles Peterfalvi (9.9) from the canonical local Frobenius
quotient and the already-counted reducible layer.  The action, kernels, and
subgroups in the public statement are all the canonical ones attached to the
type-P F-core context.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical IsMulCommutative Pointwise

noncomputable section

universe u v

namespace PTypeGaloisConclusionInternal

set_option synthInstance.maxHeartbeats 100000

open PTypeGaloisCharacterArithmeticInternal
open PTypeGaloisLocalFrobeniusInternal
open PTypeNonGaloisCliffordSupportInternal
open PTypeGaloisSubgroupAdaptersInternal
open PTypeCoreContextInternal
open internal
open CategoryTheory

/-! ## Split-universe restriction constituents -/

/- The public constituent-kernel equivalence inherited from Section 1 ties
the group and coefficient universes together.  These small opaque adapters
keep the arbitrary-universe group while working over `ℂ`. -/

private theorem induced_from_localFrobenius_generic
    {A : Type u} [Group A] [Fintype A]
    (N H R T : Subgroup A) [N.Normal] [H.Normal]
    (hjoin : H ⊔ N = T)
    (hFrob : IsFrobeniusDecomposition
      (H.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)))
    (theta : IrreducibleCharacter H ℂ)
    (hker : ((QuotientGroup.mk' N).subgroupMap H).ker ≤
      ClassFunction.translationKernel
        (theta : ClassFunction H ℂ))
    (htheta : theta ≠ IrreducibleCharacter.trivial)
    (chi : IrreducibleCharacter A ℂ)
    (hconst : theta.IsConstituent
      (ClassFunction.restrict H
        (chi : ClassFunction A ℂ))) :
    ∃ xi : IrreducibleCharacter T ℂ,
      (chi : ClassFunction A ℂ) =
        ClassFunction.induce T
          (xi : ClassFunction T ℂ) := by
  let f : H →* H.map (QuotientGroup.mk' N) :=
    (QuotientGroup.mk' N).subgroupMap H
  have hf : Function.Surjective f :=
    (QuotientGroup.mk' N).subgroupMap_surjective H
  let thetaBar : IrreducibleCharacter
      (H.map (QuotientGroup.mk' N)) ℂ :=
    pTypeGaloisDescendIrreducibleSurjective
      f hf theta hker
  have hthetaInflate : ClassFunction.comap f
      (thetaBar : ClassFunction
        (H.map (QuotientGroup.mk' N)) ℂ) =
      (theta : ClassFunction H ℂ) :=
    pTypeGalois_comap_descendIrreducibleSurjective
      f hf theta hker
  have hthetaBar : thetaBar ≠ IrreducibleCharacter.trivial :=
    pTypeGalois_descendIrreducibleSurjective_ne_trivial
      f hf theta hker htheta
  have hinertia : ClassFunction.inertia H
      (theta : ClassFunction H ℂ) = T := by
    calc
      ClassFunction.inertia H (theta : ClassFunction H ℂ) =
          H ⊔ N := by
        rw [← hthetaInflate]
        exact pTypeInertia_inflated_FrobeniusKernel
          N H R hFrob thetaBar hthetaBar
      _ = T := hjoin
  exact pTypeCliffordInduced_of_inertia_eq
    H T theta hinertia chi hconst

private theorem exists_hom_ne_zero_of_isConstituent_general
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
  have hcast :
      (Module.finrank k (chi.representation ⟶ V) : k) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank k (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact Module.finrank_pos_iff_exists_ne_zero.mp
    (Nat.pos_of_ne_zero hfin)

private theorem fdRep_kernel_le_constituent_kernel_general
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ :=
    exists_hom_ne_zero_of_isConstituent_general V chi hchi
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

private theorem subgroupOf_le_constituent_kernel_restrict_general
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (H A : Subgroup G)
    (chi : IrreducibleCharacter G k)
    (psi : IrreducibleCharacter H k)
    (hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G k)))
    (hAchi : A ≤ chi.representation.ρ.ker) :
    A.subgroupOf H ≤ psi.representation.ρ.ker := by
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
    fdRep_kernel_le_constituent_kernel_general R psi hpsiR
  intro h hh
  apply hkerRpsi
  rw [MonoidHom.mem_ker]
  change chi.representation.ρ (h : G) = 1
  exact MonoidHom.mem_ker.mp (hAchi hh)

private theorem normal_le_kernel_of_constituent_top_kernel
    {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] [Fintype H]
    (chi : IrreducibleCharacter G ℂ)
    (psi : IrreducibleCharacter H ℂ)
    (hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G ℂ)))
    (hpsiTop : (⊤ : Subgroup H) ≤ psi.representation.ρ.ker) :
    H ≤ chi.representation.ρ.ker := by
  let R : FDRep ℂ H :=
    FDRep.of (chi.representation.ρ.comp H.subtype)
  have hcharR : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict H (chi : ClassFunction G ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  have hpsiR : psi.IsConstituent
      (ClassFunction.ofRepresentation R.ρ) := by
    rwa [hcharR]
  obtain ⟨f, hf⟩ :=
    exists_hom_ne_zero_of_isConstituent_general R psi hpsiR
  let rho : Representation ℂ G chi.representation :=
    chi.representation.ρ
  let fR := (CategoryTheory.forget₂
    (FDRep ℂ H) (Rep ℂ H)).map f
  let fLinear : psi.representation →ₗ[ℂ] chi.representation := by
    simpa only [R] using f.hom.hom.hom
  let U : Subrepresentation rho :=
    { toSubmodule := Representation.invariants (rho.comp H.subtype)
      apply_mem_toSubmodule g :=
        Representation.le_comap_invariants rho H g }
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    apply hf
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    have hxInv : fLinear x ∈
        Representation.invariants (rho.comp H.subtype) := by
      rw [Representation.mem_invariants]
      intro h
      have hinter :=
        _root_.Representation.IntertwiningMap.isIntertwining
          (ρ := ((CategoryTheory.forget₂
            (FDRep ℂ H) (Rep ℂ H)).obj
              psi.representation).ρ)
          (σ := ((CategoryTheory.forget₂
            (FDRep ℂ H) (Rep ℂ H)).obj R).ρ)
          (f := fR.hom) h x
      have htriv : psi.representation.ρ h x = x := by
        rw [MonoidHom.mem_ker.mp
          (hpsiTop (Subgroup.mem_top h))]
        rfl
      have hinter' : fLinear (psi.representation.ρ h x) =
          rho (h : G) (fLinear x) := by
        change fLinear (psi.representation.ρ h x) =
          rho (h : G) (fLinear x) at hinter
        exact hinter
      exact hinter'.symm.trans (congrArg fLinear htriv)
    have hxBot : fLinear x ∈
        (⊥ : Submodule ℂ chi.representation) := by
      change fLinear x ∈ U at hxInv
      rwa [hU] at hxInv
    change fLinear x = 0
    exact hxBot
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hUtop : U = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  intro h hh
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro x
  have hxU : x ∈ U := by
    rw [hUtop]
    trivial
  exact (Representation.mem_invariants _ _).mp hxU ⟨h, hh⟩

private theorem constituent_kernel_of_mem_Iirr
    {A : Type u} [Group A] [Fintype A]
    (H H₀ : Subgroup A) [H.Normal] [H₀.Normal]
    (hH₀H : H₀ ≤ H)
    (s : IrreducibleCharacter A ℂ)
    (hs : s ∈ Iirr_kerD (k := ℂ) H H₀)
    (theta : IrreducibleCharacter H ℂ)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict H (s : ClassFunction A ℂ))) :
    H₀.subgroupOf H ≤ ClassFunction.translationKernel
      (theta : ClassFunction H ℂ) := by
  have hsData := mem_Iirr_kerD.mp hs
  have hsH₀rho : H₀ ≤ s.representation.ρ.ker := by
    rw [← pTypeGaloisTranslationKernel_irreducibleCharacter s]
    exact hsData.1
  have hthetaH₀rho : H₀.subgroupOf H ≤
      theta.representation.ρ.ker :=
    subgroupOf_le_constituent_kernel_restrict_general
      H H₀ s theta htheta hsH₀rho
  rw [pTypeGaloisTranslationKernel_irreducibleCharacter]
  exact hthetaH₀rho

private theorem constituent_ne_trivial_of_mem_Iirr
    {A : Type u} [Group A] [Fintype A]
    (H H₀ : Subgroup A) [H.Normal] [H₀.Normal]
    (s : IrreducibleCharacter A ℂ)
    (hs : s ∈ Iirr_kerD (k := ℂ) H H₀)
    (theta : IrreducibleCharacter H ℂ)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict H (s : ClassFunction A ℂ))) :
    theta ≠ (IrreducibleCharacter.trivial :
      IrreducibleCharacter H ℂ) := by
  have hsData := mem_Iirr_kerD.mp hs
  have hsHrho : ¬ H ≤ s.representation.ρ.ker := by
    intro hker
    apply hsData.2
    rw [pTypeGaloisTranslationKernel_irreducibleCharacter]
    exact hker
  intro hthetaTrivial
  apply hsHrho
  apply normal_le_kernel_of_constituent_top_kernel
    H s theta htheta
  rw [← pTypeGaloisTranslationKernel_irreducibleCharacter theta]
  subst theta
  intro x _hx
  simp

private theorem quotient_subgroupMap_kernel_eq
    {A : Type u} [Group A]
    (H H₀ N : Subgroup A) [N.Normal]
    (hinter : H ⊓ N = H₀) :
    ((QuotientGroup.mk' N).subgroupMap H).ker =
      H₀.subgroupOf H := by
  rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  ext x
  change (x : A) ∈ N ↔ (x : A) ∈ H₀
  constructor
  · intro hx
    have hx' : (x : A) ∈ H ⊓ N := ⟨x.property, hx⟩
    rw [hinter] at hx'
    exact hx'
  · intro hx
    have hxInf : (x : A) ∈ H ⊓ N := by
      rw [hinter]
      exact hx
    exact hxInf.2

private theorem exists_constituent_for_quotient
    {A : Type u} [Group A] [Fintype A]
    (H H₀ N : Subgroup A) [H.Normal] [H₀.Normal] [N.Normal]
    (hH₀H : H₀ ≤ H)
    (hinter : H ⊓ N = H₀)
    (s : IrreducibleCharacter A ℂ)
    (hs : s ∈ Iirr_kerD (k := ℂ) H H₀) :
    ∃ theta : IrreducibleCharacter H ℂ,
      theta.IsConstituent
          (ClassFunction.restrict H (s : ClassFunction A ℂ)) ∧
        theta ≠ IrreducibleCharacter.trivial ∧
        ((QuotientGroup.mk' N).subgroupMap H).ker ≤
          ClassFunction.translationKernel
            (theta : ClassFunction H ℂ) := by
  obtain ⟨theta, htheta⟩ :=
    pTypeCore_exists_constituent_restrict H s
  have hthetaH₀ := constituent_kernel_of_mem_Iirr
    H H₀ hH₀H s hs theta htheta
  have hthetaNontrivial := constituent_ne_trivial_of_mem_Iirr
    H H₀ s hs theta htheta
  refine ⟨theta, htheta, hthetaNontrivial, ?_⟩
  rw [quotient_subgroupMap_kernel_eq H H₀ N hinter]
  exact hthetaH₀

/-! ## Induction from the canonical subgroup `HC` -/

/-- Every irreducible in the `H₀` kernel layer is induced from `HC`.

The proof first descends a nonprincipal constituent of the restriction to
`H / H₀`, whose inertia is identified by the local Frobenius quotient.  The
last step is the split-universe form of Clifford correspondence. -/
private theorem character_induced_from_HC
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
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : H.Normal := pTypeHInDerived_normal ctx
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    ∀ s ∈ Iirr_kerD (k := ℂ) H H₀,
      ∃ xi : IrreducibleCharacter HC ℂ,
        (s : ClassFunction HU ℂ) =
          ClassFunction.induce HC (xi : ClassFunction HC ℂ) := by
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
  letI : H.Normal := pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀C.Normal := pTypeH0CInDerived_normal ctx facts
  intro s hs
  have hH₀H : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Ptype_Fcore_kernel_lt ctx).le)
  have hCU : C ≤ UHU := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Subgroup.map_subtype_le D.C))
  have hcomp : H.IsComplement' UHU :=
    pTypeHInDerived_isComplement_UInDerived ctx
  have hinter : H ⊓ H₀C = H₀ := by
    change H ⊓ (H₀ ⊔ C) = H₀
    exact (pTypeInf_sup_eq_of_isComplement H UHU H₀ C
      hcomp hH₀H hCU).1
  obtain ⟨theta, htheta, hthetaNontrivial, hker⟩ :=
    exists_constituent_for_quotient H H₀ H₀C
      hH₀H hinter s hs
  have hFrob := pTypeGalois_localQuotient_frobenius ctx facts hGal
  have hjoin : H ⊔ H₀C = HC := by
    change H ⊔ (H₀ ⊔ C) = H ⊔ C
    rw [← sup_assoc, sup_eq_left.mpr hH₀H]
  exact induced_from_localFrobenius_generic
    H₀C H UHU HC hjoin hFrob theta hker hthetaNontrivial s htheta

/-- Part (a), first clause: the action-factor cardinal divides every degree
in the `H₀` kernel layer. -/
private theorem degree_divisibility
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
    letI : H.Normal := pTypeHInDerived_normal ctx
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    ∀ s ∈ Iirr_kerD (k := ℂ) H H₀,
      pTypeActionFactorCard D ∣ pTypeIrreducibleDegree s := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  intro s hs
  obtain ⟨xi, hind⟩ := character_induced_from_HC ctx facts hGal s hs
  exact actionFactor_dvd_degree_of_induced
    HC (pTypeActionFactorCard D)
      (pTypeHCInDerived_index_eq_actionFactorCard ctx facts)
      s xi hind

/-- Part (a), second clause: killing `H₀C'` forces the inducing character
on `HC` to be linear. -/
private theorem core_induced
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : TypePGaloisConclusion (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    letI : H.Normal := pTypeHInDerived_normal ctx
    letI : H₀CPrime.Normal := pTypeH0CPrimeInDerived_normal ctx facts
    ∀ s ∈ Iirr_kerD (k := ℂ) H H₀CPrime,
      PTypeCoreInduced HC (pTypeActionFactorCard D) s := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal := pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀CPrime.Normal := pTypeH0CPrimeInDerived_normal ctx facts
  have hH₀Prime : H₀ ≤ H₀CPrime := le_sup_left
  letI : Invertible (Nat.card HU : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HU)).ne')
  intro s hs
  have hsData := mem_Iirr_kerD.mp hs
  have hsH₀ : s ∈ Iirr_kerD (k := ℂ) H H₀ :=
    mem_Iirr_kerD.mpr ⟨hH₀Prime.trans hsData.1, hsData.2⟩
  obtain ⟨xi, hind⟩ := character_induced_from_HC ctx facts hGal s hsH₀
  have hsConstituent : s.IsConstituent
      (ClassFunction.induce HC (xi : ClassFunction HC ℂ)) := by
    unfold IrreducibleCharacter.IsConstituent
    rw [← hind, IrreducibleCharacter.characterPairing_self]
    exact one_ne_zero
  have hxiConstituent : xi.IsConstituent
      (ClassFunction.restrict HC (s : ClassFunction HU ℂ)) :=
    (xi.isConstituent_restrict_iff_induce HC s).mpr hsConstituent
  have hsPrimeRho : H₀CPrime ≤ s.representation.ρ.ker := by
    rw [← pTypeGaloisTranslationKernel_irreducibleCharacter s]
    exact hsData.1
  have hxiPrimeRho : H₀CPrime.subgroupOf HC ≤
      xi.representation.ρ.ker :=
    subgroupOf_le_constituent_kernel_restrict_general
      HC H₀CPrime s xi hxiConstituent hsPrimeRho
  have hxiPrime : H₀CPrime.subgroupOf HC ≤
      ClassFunction.translationKernel (xi : ClassFunction HC ℂ) := by
    rw [pTypeGaloisTranslationKernel_irreducibleCharacter]
    exact hxiPrimeRho
  have hcommutator : _root_.commutator HC ≤
      ClassFunction.translationKernel (xi : ClassFunction HC ℂ) :=
    (pTypeGalois_commutator_HC_le_H0CPrime ctx facts).trans hxiPrime
  exact coreInduced_of_commutator_le_kernel
    HC (pTypeActionFactorCard D)
      (pTypeHCInDerived_index_eq_actionFactorCard ctx facts)
      s xi hcommutator hind

/-! ## Reducible characters induced all the way to `M` -/

/-- Transport a core-induction package from `HC ≤ HU` to induction into
the ambient maximal subgroup. -/
private theorem induce_core_to_maximal
    {M : Type u} [Group M] [Fintype M]
    (HU HC : Subgroup M) (hHC : HC ≤ HU) (u : ℕ)
    (s : IrreducibleCharacter HU ℂ)
    (hs : PTypeCoreInduced (HC.subgroupOf HU) u s) :
    ∃ xi : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter xi ∧
        ClassFunction.induce HU (s : ClassFunction HU ℂ) =
          ClassFunction.induce HC (xi : ClassFunction HC ℂ) := by
  rcases hs with ⟨_degree, theta, hthetaLinear, hsInd⟩
  let e : HC.subgroupOf HU ≃* HC :=
    Subgroup.subgroupOfEquivOfLe hHC
  let xi : IrreducibleCharacter HC ℂ :=
    pTypeGaloisComapMulEquiv e.symm theta
  have hxiLinear : pTypeIsLinearCharacter xi :=
    pTypeIsLinearCharacter_comapMulEquiv e.symm theta hthetaLinear
  have htransport :
      ClassFunction.toSubgroupOf HC HU hHC (xi : ClassFunction HC ℂ) =
        (theta : ClassFunction (HC.subgroupOf HU) ℂ) := by
    ext x
    simp [ClassFunction.toSubgroupOf_apply, xi, e,
      pTypeGaloisComapMulEquiv_apply]
  refine ⟨xi, hxiLinear, ?_⟩
  calc
    ClassFunction.induce HU (s : ClassFunction HU ℂ) =
        ClassFunction.induce HU
          (ClassFunction.induce (HC.subgroupOf HU)
            (theta : ClassFunction (HC.subgroupOf HU) ℂ)) := by rw [hsInd]
    _ = ClassFunction.induce HU
        (ClassFunction.induce (HC.subgroupOf HU)
          (ClassFunction.toSubgroupOf HC HU hHC
            (xi : ClassFunction HC ℂ))) := by rw [htransport]
    _ = ClassFunction.induce HC (xi : ClassFunction HC ℂ) :=
      ClassFunction.induce_trans HC HU hHC _

/-- Part (b): every reducible member of the `H₀` layer has the prescribed
degree and is induced from a linear character of `HC`. -/
private theorem reducible_layer_induced
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
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    ∀ zeta ∈ pTypeReducibleLayer HU H H₀,
      pTypeIsIndHC HU H H₀C HCInM D.q
        (pTypeActionFactorCard D) zeta := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let actionCard := pTypeActionFactorCard D
  have hPrimeH₀C : H₀CPrime ≤ H₀C :=
    pTypeH0CPrimeInDerived_le_H0CInDerived
      M (derivedWithin M) (Ptype_Fcore_kernel ctx) U W₁ D
  have hHCle : HCInM ≤ HU := pTypeHCInMaximal_le_HU ctx D
  have hHCeq : HC = HCInM.subgroupOf HU :=
    pTypeHCInDerived_eq_subgroupOf ctx D
  intro zeta hzeta
  have hzetaSeq : zeta ∈ seqIndD (k := ℂ) HU H H₀C :=
    (pType_nb_redM_H0 ctx facts).2 zeta hzeta
  obtain ⟨s, hs, hzetaEq⟩ := seqIndP.mp hzetaSeq
  have hsData := mem_Iirr_kerD.mp hs
  have hsPrime : s ∈ Iirr_kerD (k := ℂ) H H₀CPrime :=
    mem_Iirr_kerD.mpr ⟨hPrimeH₀C.trans hsData.1, hsData.2⟩
  have hcore : PTypeCoreInduced HC actionCard s :=
    core_induced ctx facts hGal s hsPrime
  have hcoreInM : PTypeCoreInduced
      (HCInM.subgroupOf HU) actionCard s := by
    rw [← hHCeq]
    exact hcore
  obtain ⟨xi, hxiLinear, hind⟩ :=
    induce_core_to_maximal HU HCInM hHCle actionCard s hcoreInM
  refine ⟨?_, hzetaSeq, xi, hxiLinear, ?_⟩
  · calc
      zeta 1 = ClassFunction.induce HU (s : ClassFunction HU ℂ) 1 := by
        rw [hzetaEq]
      _ = (HU.index : ℂ) * s 1 := ClassFunction.induce_one HU _
      _ = (D.q : ℂ) * (actionCard : ℂ) := by
        rw [pTypeHUInMaximal_index_eq_action_q ctx facts, hcore.1]
      _ = ((D.q * actionCard : ℕ) : ℂ) := by norm_num
  · exact hzetaEq.trans hind

/-! ## Final assembly -/

/- Transport a Frobenius decomposition across equality of the quotient
kernel.  Keeping the equality abstract lets dependent elimination replace the
associated quotient-group instances in one step. -/
private theorem quotient_frobenius_transport
    {G : Type u} [Group G]
    (N N' K R : Subgroup G) [N.Normal] [N'.Normal]
    (hN : N = N')
    (hFrob : IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N))) :
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N'))
      (R.map (QuotientGroup.mk' N')) := by
  subst N'
  exact hFrob

/- The all-reducible counting clause is supplied below after its independent
scratch proof is integrated. -/
private theorem all_reducible_conclusion
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
    let UHU := pTypeUInDerived M (derivedWithin M) U
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let actionCard := pTypeActionFactorCard D
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    (∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
      ¬ IsIrreducibleCharacter M ℂ zeta) →
    C = ⊥ ∧ actionCard = (D.p ^ D.q - 1) / (D.p - 1) ∧
      IsFrobeniusDecomposition
        (ptypeQuotientImage H₀ H)
        (ptypeQuotientImage H₀ UHU) := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let actionCard := pTypeActionFactorCard D
  letI : H.Normal := pTypeHInDerived_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀C.Normal := pTypeH0CInDerived_normal ctx facts
  intro hAllReducible
  have hC : C = ⊥ :=
    pTypeGalois_all_reducible_forces_C_bot ctx facts hGal hAllReducible
  have hDC : D.C = ⊥ := (pTypeCInDerived_eq_bot_iff ctx D).mp hC
  have hH₀C : H₀C = H₀ := by
    change H₀ ⊔ C = H₀
    simp only [hC, sup_bot_eq]
  have hH₀H : H₀ ≤ H :=
    Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Ptype_Fcore_kernel_lt ctx).le)
  have hPrimeEq : H₀CPrime = H₀ := by
    apply le_antisymm
    · rw [← hH₀C]
      exact pTypeH0CPrimeInDerived_le_H0CInDerived
        M (derivedWithin M) (Ptype_Fcore_kernel ctx) U W₁ D
    · change H₀ ≤ H₀ ⊔
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU
      exact le_sup_left
  have hFrob : IsFrobeniusDecomposition
      (H.map (QuotientGroup.mk' H₀))
      (UHU.map (QuotientGroup.mk' H₀)) := by
    have hFrobC :=
      pTypeGalois_localQuotient_frobenius ctx facts hGal
    exact quotient_frobenius_transport
      H₀C H₀ H UHU hH₀C hFrobC
  let q : HU →* HU ⧸ H₀ := QuotientGroup.mk' H₀
  let K : Subgroup (HU ⧸ H₀) := H.map q
  let R : Subgroup (HU ⧸ H₀) := UHU.map q
  let sourceCharacters : Finset (IrreducibleCharacter HU ℂ) :=
    Iirr_kerD (k := ℂ) H H₀
  let reducibleCharacters : Finset (ClassFunction M ℂ) :=
    pTypeReducibleLayer HU H H₀
  let quotientCharacters : Finset
      (IrreducibleCharacter (HU ⧸ H₀) ℂ) :=
    Finset.univ.filter fun psi ↦
      ¬ K ≤ ClassFunction.translationKernel
        (psi : ClassFunction (HU ⧸ H₀) ℂ)

  /- Identify the Frobenius kernel with the canonical F-core factor by
  comparing two quotient maps out of `H`. -/
  let f : H →* K := q.subgroupMap H
  have hf : Function.Surjective f := q.subgroupMap_surjective H
  have hfker : f.ker = H₀.subgroupOf H := by
    ext h
    constructor
    · intro hh
      have hhval : q (h : HU) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hh)
      exact (QuotientGroup.eq_one_iff (N := H₀) (h : HU)).mp hhval
    · intro hh
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := H₀) (h : HU)).mpr hh
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hFcoreHU : (Fitting_core M).subgroupOf M ≤ HU :=
    Subgroup.subgroupOf_mono M hHder
  let eH : H ≃* Fitting_core M :=
    (Subgroup.subgroupOfEquivOfLe hFcoreHU).trans
      (Subgroup.subgroupOfEquivOfLe (Fcore_sub M))
  let N : Subgroup (Fitting_core M) :=
    (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
  letI : N.Normal := by
    simpa only [N] using Ptype_Fcore_kernel_normal_Fcore ctx
  let qF : Fitting_core M →* ptypeFCoreFactor ctx :=
    QuotientGroup.mk' N
  let g : H →* ptypeFCoreFactor ctx := qF.comp eH.toMonoidHom
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective N).comp eH.surjective
  have hgker : g.ker = H₀.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker]
    change qF (eH h) = 1 ↔ (h : HU) ∈ H₀
    rw [show qF (eH h) = 1 ↔ eH h ∈ N from
      QuotientGroup.eq_one_iff (N := N) (eH h)]
    change (((h : HU) : M) : Gamma) ∈ Ptype_Fcore_kernel ctx ↔
      (((h : HU) : M) : Gamma) ∈ Ptype_Fcore_kernel ctx
    rfl
  let eK : K ≃* ptypeFCoreFactor ctx :=
    pTypeGaloisImageEquivOfCommonKernel
      (H₀.subgroupOf H) f g hf hg hfker hgker
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    (ptypeFCoreFactor_elementary ctx).commutative
  letI : IsMulCommutative K :=
    isMulCommutative_iff.mpr fun x y ↦ by
      apply eK.injective
      rw [map_mul, map_mul]
      exact mul_comm (eK x) (eK y)
  have hKcard : Nat.card K = D.p ^ D.q := by
    calc
      Nat.card K = Nat.card (ptypeFCoreFactor ctx) :=
        Nat.card_congr eK.toEquiv
      _ = ptypeFactorPrime ctx ^ Nat.card W₁ := facts.factor_card
      _ = D.p ^ D.q := by
        rw [Ptype_factor_action_p, Ptype_factor_action_q]

  /- The quotient map is injective on the complementary factor. -/
  have hcomp : H.IsComplement' UHU :=
    pTypeHInDerived_isComplement_UInDerived ctx
  let fR : UHU → R := q.subgroupMap UHU
  have hfR : Function.Bijective fR :=
    ⟨Subgroup.IsComplement'.quotientRight_subgroupMap_injective
        hcomp hH₀H,
      q.subgroupMap_surjective UHU⟩
  have hRcardUHU : Nat.card R = Nat.card UHU :=
    (Nat.card_congr (Equiv.ofBijective fR hfR)).symm
  have hUder : U ≤ derivedWithin M := ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hUHU : U.subgroupOf M ≤ HU :=
    Subgroup.subgroupOf_mono M hUder
  have hUHUcard : Nat.card UHU = Nat.card U := by
    calc
      Nat.card UHU = Nat.card (U.subgroupOf M) :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUHU
      _ = Nat.card U :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUM
  have hactionCard : actionCard = Nat.card U :=
    pTypeActionFactorCard_eq_card_of_C_eq_bot D hDC
  have hRcard : Nat.card R = actionCard :=
    hRcardUHU.trans (hUHUcard.trans hactionCard.symm)

  /- Reducibility and the prime index force every inducing character to have
  full inertia.  Consequently induction is injective on this layer. -/
  have hsubset : reducibleCharacters ⊆ seqInd HU sourceCharacters := by
    intro zeta hzeta
    simp only [reducibleCharacters, pTypeReducibleLayer,
      Finset.mem_filter] at hzeta
    simpa only [sourceCharacters, seqIndD] using hzeta.1
  have hreducible : ∀ zeta ∈ reducibleCharacters,
      ¬ IsIrreducibleCharacter M ℂ zeta := by
    intro zeta hzeta
    simp only [reducibleCharacters, pTypeReducibleLayer,
      Finset.mem_filter] at hzeta
    exact hzeta.2
  letI : HU.Normal :=
    Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 M
  letI : Invertible (Nat.card HU : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HU)).ne')
  have hHUindex : HU.index = D.q :=
    pTypeHUInMaximal_index_eq_action_q ctx facts
  have hHUprime : HU.index.Prime := by
    rw [hHUindex]
    exact D.q_prime
  have hinertiaTop (chi : IrreducibleCharacter HU ℂ)
      (hred : ¬ IsIrreducibleCharacter M ℂ
        (ClassFunction.induce HU (chi : ClassFunction HU ℂ))) :
      ClassFunction.inertia HU (chi : ClassFunction HU ℂ) = ⊤ := by
    let I := ClassFunction.inertia HU (chi : ClassFunction HU ℂ)
    have hnorm := pTypeCore_reducible_induce_norm_eq_primeIndex
      HU hHUprime chi hred
    have hinertiaIndex :
        ClassFunction.inertiaIndex HU (chi : ClassFunction HU ℂ) =
          HU.index := by
      apply Nat.cast_injective (R := ℂ)
      calc
        (ClassFunction.inertiaIndex HU
            (chi : ClassFunction HU ℂ) : ℂ) =
            characterPairing
              (ClassFunction.induce HU (chi : ClassFunction HU ℂ))
              (ClassFunction.induce HU (chi : ClassFunction HU ℂ)) :=
          (ClassFunction.cfnorm_Ind_irr HU chi).symm
        _ = (HU.index : ℂ) := hnorm
    have hrel : HU.relIndex I = HU.index := by
      calc
        HU.relIndex I = ClassFunction.inertiaIndex HU
            (chi : ClassFunction HU ℂ) := by
          simpa only [I] using
            (pTypeCore_inertiaIndex_eq_relIndex
              HU (chi : ClassFunction HU ℂ)).symm
        _ = HU.index := hinertiaIndex
    have hmul : HU.relIndex I * I.index = HU.index :=
      HU.relIndex_mul_index
        (ClassFunction.le_inertia HU (chi : ClassFunction HU ℂ))
    have hmul' : HU.index * I.index = HU.index * 1 := by
      calc
        HU.index * I.index = HU.relIndex I * I.index := by rw [hrel]
        _ = HU.index := hmul
        _ = HU.index * 1 := by simp
    have hIindex : I.index = 1 :=
      Nat.mul_left_cancel hHUprime.pos hmul'
    simpa only [I] using (Subgroup.index_eq_one.mp hIindex)
  let induceIrr := fun chi : IrreducibleCharacter HU ℂ ↦
    ClassFunction.induce HU (chi : ClassFunction HU ℂ)
  let selected := Finset.univ.filter fun chi : IrreducibleCharacter HU ℂ ↦
    induceIrr chi ∈ reducibleCharacters
  have himage : selected.image induceIrr = reducibleCharacters := by
    ext phi
    constructor
    · intro hphi
      obtain ⟨chi, hchi, rfl⟩ := Finset.mem_image.mp hphi
      exact (Finset.mem_filter.mp hchi).2
    · intro hphi
      obtain ⟨chi, _, hchi⟩ := seqIndP.mp (hsubset hphi)
      apply Finset.mem_image.mpr
      refine ⟨chi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa only [induceIrr, hchi] using hphi
      · simpa only [induceIrr] using hchi.symm
  have hinjectiveSelected : Set.InjOn induceIrr
      (↑selected : Set (IrreducibleCharacter HU ℂ)) := by
    intro chi hchi psi _hpsi hind
    have hchiReducible : induceIrr chi ∈ reducibleCharacters :=
      (Finset.mem_filter.mp hchi).2
    have htop := hinertiaTop chi (hreducible _ hchiReducible)
    obtain ⟨x, hx⟩ :=
      (ClassFunction.cfclass_Ind_eq_iff HU chi psi).mp (by
        simpa only [induceIrr] using hind)
    have hfix : ClassFunction.normalConjugate HU x
        (chi : ClassFunction HU ℂ) = (chi : ClassFunction HU ℂ) := by
      apply (ClassFunction.mem_inertia_iff HU _ x).mp
      rw [htop]
      exact Subgroup.mem_top x
    apply Subtype.ext
    exact hfix.symm.trans hx
  have hsize : reducibleCharacters.card = selected.card := by
    calc
      reducibleCharacters.card = (selected.image induceIrr).card := by
        rw [himage]
      _ = selected.card := Finset.card_image_iff.mpr hinjectiveSelected
  have hAllH₀ : ∀ zeta ∈ seqIndD (k := ℂ) HU H H₀,
      ¬ IsIrreducibleCharacter M ℂ zeta := by
    intro zeta hzeta
    apply hAllReducible zeta
    change zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime
    rw [hPrimeEq]
    exact hzeta
  have hHmap : H.map HU.subtype = (Fitting_core M).subgroupOf M := by
    simpa only [H, HU, pTypeHInDerived, pTypeHUInMaximal] using
      Subgroup.map_subgroupOf_eq_of_le
        hFcoreHU
  letI : (H.map HU.subtype).Normal := by
    rw [hHmap]
    infer_instance
  have hH₀der : Ptype_Fcore_kernel ctx ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hH₀HU : (Ptype_Fcore_kernel ctx).subgroupOf M ≤ HU :=
    Subgroup.subgroupOf_mono M hH₀der
  have hH₀map : H₀.map HU.subtype =
      (Ptype_Fcore_kernel ctx).subgroupOf M := by
    simpa only [H₀, HU, pTypeH0InDerived, pTypeHUInMaximal] using
      Subgroup.map_subgroupOf_eq_of_le
        hH₀HU
  letI : (H₀.map HU.subtype).Normal := by
    rw [hH₀map]
    exact Ptype_Fcore_kernel_normal_M ctx
  have hselected : selected = sourceCharacters := by
    ext chi
    simp only [selected, Finset.mem_filter, induceIrr]
    constructor
    · rintro ⟨_, hindReducible⟩
      have hindSeq : ClassFunction.induce HU
          (chi : ClassFunction HU ℂ) ∈
          seqIndD (k := ℂ) HU H H₀ := by
        simp only [reducibleCharacters, pTypeReducibleLayer,
          Finset.mem_filter] at hindReducible
        exact hindReducible.1
      exact (mem_seqInd HU H H₀ chi).mp hindSeq
    · intro hchi
      have hindSeq : ClassFunction.induce HU
          (chi : ClassFunction HU ℂ) ∈
          seqIndD (k := ℂ) HU H H₀ :=
        (mem_seqInd HU H H₀ chi).mpr hchi
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [reducibleCharacters, pTypeReducibleLayer,
        Finset.mem_filter]
      exact ⟨hindSeq, hAllH₀ _ hindSeq⟩
  have hsourceCard : sourceCharacters.card = D.p - 1 := by
    calc
      sourceCharacters.card = selected.card := by rw [hselected]
      _ = reducibleCharacters.card := hsize.symm
      _ = D.p - 1 := (pType_nb_redM_H0 ctx facts).1

  have hquotientCard : quotientCharacters.card = sourceCharacters.card := by
    simpa only [quotientCharacters, K, q, sourceCharacters] using
      quotient_nontrivial_image_irreducibles_card H₀ H hH₀H
  have horbit : Nat.card K - 1 =
      Nat.card R * quotientCharacters.card := by
    simpa only [K, R, quotientCharacters, q] using
      frobenius_nontrivial_ambient_card K R hFrob
  have hcount : D.p ^ D.q - 1 = (D.p - 1) * actionCard := by
    calc
      D.p ^ D.q - 1 = Nat.card K - 1 := by rw [hKcard]
      _ = Nat.card R * quotientCharacters.card := horbit
      _ = actionCard * (D.p - 1) := by
        rw [hRcard, hquotientCard, hsourceCard]
      _ = (D.p - 1) * actionCard := by rw [mul_comm]
  have hquotient : actionCard = (D.p ^ D.q - 1) / (D.p - 1) :=
    actionFactor_eq_geometric_quotient D.p_prime hcount
  exact ⟨hC, hquotient, hFrob⟩

end PTypeGaloisConclusionInternal

open PTypeGaloisConclusionInternal

/-- `PFsection9.v: typeP_Galois_characters`, Peterfalvi (9.9). -/
theorem typeP_Galois_characters
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    (M U W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (maxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype5 : FTtype M ≠ 5)
    (is_Galois :
      typeP_Galois
        (Ptype_factor_action
          (Ptype_Fcore_context maxM defW MtypeP notMtype5)
          (Ptype_Fcore_factor_facts
            (Ptype_Fcore_context maxM defW MtypeP notMtype5)))) :
    let ctx := Ptype_Fcore_context maxM defW MtypeP notMtype5
    let facts := Ptype_Fcore_factor_facts ctx
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let UHU := pTypeUInDerived M (derivedWithin M) U
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let u := pTypeActionFactorCard D
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    ((∀ s ∈ Iirr_kerD (k := ℂ) H H₀,
        u ∣ pTypeIrreducibleDegree s) ∧
      (∀ s ∈ Iirr_kerD (k := ℂ) H H₀CPrime,
        PTypeCoreInduced HC u s)) ∧
    ((pTypeReducibleLayer HU H H₀).card = D.p - 1 ∧
      ∀ zeta ∈ pTypeReducibleLayer HU H H₀,
        pTypeIsIndHC HU H H₀C HCInM D.q u zeta) ∧
    ((∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
        ¬ IsIrreducibleCharacter M ℂ zeta) →
      C = ⊥ ∧ u = (D.p ^ D.q - 1) / (D.p - 1) ∧
        IsFrobeniusDecomposition
          (ptypeQuotientImage H₀ H)
          (ptypeQuotientImage H₀ UHU)) := by
  classical
  let ctx := Ptype_Fcore_context maxM defW MtypeP notMtype5
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let u := pTypeActionFactorCard D
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  let hD := Ptype_factor_action_hypotheses ctx facts
  have hGal : TypePGaloisConclusion D := typeP_Galois_P hD is_Galois
  change
    ((∀ s ∈ Iirr_kerD (k := ℂ) H H₀,
        u ∣ pTypeIrreducibleDegree s) ∧
      (∀ s ∈ Iirr_kerD (k := ℂ) H H₀CPrime,
        PTypeCoreInduced HC u s)) ∧
    ((pTypeReducibleLayer HU H H₀).card = D.p - 1 ∧
      ∀ zeta ∈ pTypeReducibleLayer HU H H₀,
        pTypeIsIndHC HU H H₀C HCInM D.q u zeta) ∧
    ((∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
        ¬ IsIrreducibleCharacter M ℂ zeta) →
      C = ⊥ ∧ u = (D.p ^ D.q - 1) / (D.p - 1) ∧
        IsFrobeniusDecomposition
          (ptypeQuotientImage H₀ H)
          (ptypeQuotientImage H₀ UHU))
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · exact degree_divisibility ctx facts hGal
  · exact core_induced ctx facts hGal
  · exact (pType_nb_redM_H0 ctx facts).1
  · exact reducible_layer_induced ctx facts hGal
  · exact all_reducible_conclusion ctx facts hGal

end

end Submission.OddOrder.PF
