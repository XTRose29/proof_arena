import Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure

/-!
# Peterfalvi Section 9: fixed degrees in the non-Galois branch

This module proves clause (a) of Peterfalvi (9.8).  The local character
adapters below keep the group and coefficient universes independent; the
available general-purpose wrappers currently do not all elaborate at the
universe-polymorphic statement needed here.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15

universe u v w

namespace internal

/-- Choose an irreducible constituent of a restricted irreducible character. -/
private theorem exists_constituent_restrict_complex
    {Q : Type u} [Group Q] [Fintype Q]
    (J : Subgroup Q) [Fintype J]
    (chi : IrreducibleCharacter Q ℂ) :
    ∃ theta : IrreducibleCharacter J ℂ,
      theta.IsConstituent
        (ClassFunction.restrict J (chi : ClassFunction Q ℂ)) := by
  let V : FDRep ℂ J :=
    FDRep.of (chi.representation.ρ.comp J.subtype)
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
      ClassFunction.restrict J (chi : ClassFunction Q ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  rwa [hV] at htheta

/-- Universe-polymorphic form of the translation-kernel/representation-kernel
identity for irreducible characters. -/
private theorem translationKernel_irreducibleCharacter_general
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

/-- A universe-polymorphic nonzero-intertwiner witness for a constituent. -/
private theorem exists_hom_ne_zero_of_isConstituent_general
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V, f ≠ 0 := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction G k) =
        (Module.finrank k (chi.representation ⟶ V) : k) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant chi.representation V
    have hcharV (g : G) :
        V.character g = _root_.Representation.character V.ρ g := rfl
    simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character, invOf_eq_inv,
      smul_eq_mul, Fintype.card_eq_nat_card, hcharV] using hhom
  have hcast : (Module.finrank k (chi.representation ⟶ V) : k) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank k (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hfin)

set_option maxHeartbeats 600000 in
/-- A subgroup in the representation kernel of an ambient irreducible is
also in the kernel of every constituent after restriction. -/
private theorem subgroup_le_constituent_kernel
    {G : Type u} [Group G] [Fintype G]
    (H A : Subgroup G) [Fintype H]
    (chi : IrreducibleCharacter G ℂ)
    (psi : IrreducibleCharacter H ℂ)
    (hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G ℂ)))
    (hAchi : A ≤ chi.representation.ρ.ker) :
    A.subgroupOf H ≤ psi.representation.ρ.ker := by
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
  letI : CategoryTheory.Simple psi.representation :=
    psi.representation_simple
  letI : CategoryTheory.Mono f :=
    CategoryTheory.mono_of_nonzero_from_simple hf
  let fR := (CategoryTheory.forget₂ (FDRep ℂ H) (Rep ℂ H)).map f
  let fLinear : psi.representation →ₗ[ℂ] chi.representation := by
    simpa only [R] using f.hom.hom.hom
  have hfR : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp (by infer_instance)
  have hfLinear : Function.Injective fLinear := by
    intro x y hxy
    apply hfR
    change fLinear x = fLinear y
    exact hxy
  intro h hh
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro x
  apply hfLinear
  have hinter :=
    _root_.Representation.IntertwiningMap.isIntertwining
      (ρ := ((CategoryTheory.forget₂ (FDRep ℂ H) (Rep ℂ H)).obj
        psi.representation).ρ)
      (σ := ((CategoryTheory.forget₂ (FDRep ℂ H) (Rep ℂ H)).obj R).ρ)
      (f := fR.hom) h x
  change fLinear (psi.representation.ρ h x) =
    chi.representation.ρ (h : G) (fLinear x) at hinter
  calc
    fLinear (psi.representation.ρ h x) =
        chi.representation.ρ (h : G) (fLinear x) := hinter
    _ = fLinear x := by
      have hhA : (h : G) ∈ A := hh
      have hmap : chi.representation.ρ (h : G) = 1 :=
        MonoidHom.mem_ker.mp (hAchi hhA)
      rw [hmap]
      rfl

/-- If a constituent of restriction to a normal subgroup is trivial on the
whole subgroup, then the ambient irreducible is trivial there too. -/
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
  let fR := (CategoryTheory.forget₂ (FDRep ℂ H) (Rep ℂ H)).map f
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
          (ρ := ((CategoryTheory.forget₂ (FDRep ℂ H) (Rep ℂ H)).obj
            psi.representation).ρ)
          (σ := ((CategoryTheory.forget₂ (FDRep ℂ H) (Rep ℂ H)).obj R).ρ)
          (f := fR.hom) h x
      have htriv : psi.representation.ρ h x = x := by
        rw [MonoidHom.mem_ker.mp (hpsiTop (Subgroup.mem_top h))]
        rfl
      have hinter' : fLinear (psi.representation.ρ h x) =
          rho (h : G) (fLinear x) := by
        change fLinear (psi.representation.ρ h x) =
          rho (h : G) (fLinear x) at hinter
        exact hinter
      exact hinter'.symm.trans (congrArg fLinear htriv)
    have hxBot : fLinear x ∈ (⊥ : Submodule ℂ chi.representation) := by
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

/-- Descend an irreducible complex character through a normal subgroup in
its translation kernel. -/
private noncomputable def quotientDescendIrreducibleComplex
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    IrreducibleCharacter (A ⧸ N) ℂ := by
  have hNrho : N ≤ chi.representation.ρ.ker := by
    rw [← translationKernel_irreducibleCharacter_general chi]
    exact hN
  let rhoQ : Representation ℂ (A ⧸ N) chi.representation :=
    QuotientGroup.lift N chi.representation.ρ hNrho
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hrhoQcomp : rhoQ.comp q = chi.representation.ρ := by
    ext a x
    rfl
  letI : Representation.IsIrreducible (rhoQ.comp q) := by
    rw [hrhoQcomp]
    infer_instance
  letI : Representation.IsIrreducible rhoQ :=
    representation_isIrreducible_of_comp rhoQ q
  letI : CategoryTheory.Simple (FDRep.of rhoQ) :=
    simple_fdRep_of_isIrreducible rhoQ
  exact IrreducibleCharacter.ofFDRep (FDRep.of rhoQ)

@[simp]
private theorem quotientDescendIrreducibleComplex_mk_apply
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    quotientDescendIrreducibleComplex N chi hN
        (QuotientGroup.mk' N a) = chi a := by
  simp only [quotientDescendIrreducibleComplex,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character a = chi a
  exact chi.representation_character a

/-- In dimension one, equality of character values determines the
representing endomorphisms. -/
private theorem representation_eq_of_character_eq_of_finrank_one
    {A : Type u} {V : Type v}
    [Group A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ A V)
    (hdim : Module.finrank ℂ V = 1)
    {a b : A} (hchar : rho.character a = rho.character b) :
    rho a = rho b := by
  obtain ⟨ca, hca, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (rho a)
  obtain ⟨cb, hcb, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (rho b)
  have hscalar : ca = cb := by
    change LinearMap.trace ℂ V (rho a) =
      LinearMap.trace ℂ V (rho b) at hchar
    rw [hca, hcb, map_smul, map_smul,
      LinearMap.trace_id, hdim] at hchar
    simpa using hchar
  rw [hca, hcb, hscalar]

/-- A nontrivial linear character on a prime-order invariant subgroup detects
every automorphism of that subgroup. -/
private theorem mem_pointwiseActionKernel_of_character_fixed
    {A : Type u} {B : Type v} [Group A] [Finite A]
    [Group B] [Finite B]
    (rho : A →* MulAut B) (L : Subgroup B)
    (hL : IsInvariantSubgroup rho L)
    (hLprime : (Nat.card L).Prime)
    (chi : IrreducibleCharacter B ℂ)
    (hdim : Module.finrank ℂ chi.representation = 1)
    (hnontrivial : ¬ L ≤ ClassFunction.translationKernel
      (chi : ClassFunction B ℂ))
    (a : A)
    (ha : ∀ b : B, chi (rho a b) = chi b) :
    a ∈ pointwiseActionKernel rho L := by
  let sigma : Representation ℂ L chi.representation :=
    chi.representation.ρ.comp L.subtype
  letI : Fact (Nat.card L).Prime := ⟨hLprime⟩
  have hker_ne_top : sigma.ker ≠ ⊤ := by
    intro htop
    apply hnontrivial
    intro x hx
    let xL : L := ⟨x, hx⟩
    have hxker : xL ∈ sigma.ker := by
      rw [htop]
      trivial
    rw [ClassFunction.mem_translationKernel_iff]
    intro g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace ℂ chi.representation
        (chi.representation.ρ (x * g)) =
      LinearMap.trace ℂ chi.representation
        (chi.representation.ρ g)
    rw [map_mul, show chi.representation.ρ x = 1 from hxker,
      one_mul]
  have hker_bot : sigma.ker = ⊥ :=
    sigma.ker.eq_bot_or_eq_top_of_prime_card.resolve_right hker_ne_top
  have hsigma_injective : Function.Injective sigma :=
    sigma.ker_eq_bot_iff.mp hker_bot
  rw [mem_pointwiseActionKernel_iff]
  intro b hb
  let bL : L := ⟨b, hb⟩
  let abL : L := ⟨rho a b, hL.mem a hb⟩
  have hrho : chi.representation.ρ (abL : B) =
      chi.representation.ρ (bL : B) := by
    apply representation_eq_of_character_eq_of_finrank_one
      chi.representation.ρ hdim
    calc
      chi.representation.character (abL : B) = chi (rho a b) :=
        chi.representation_character _
      _ = chi b := ha b
      _ = chi.representation.character (bL : B) :=
        (chi.representation_character _).symm
  have hab : abL = bL := hsigma_injective hrho
  exact congrArg Subtype.val hab

/-! The published inertia correspondence currently requires the group and
coefficient field to live in one universe.  These adapters resize the finite
group, apply that correspondence at universe zero, and transport its result
back to the original group. -/

private def classFunctionComapComplex
    {A : Type u} {B : Type v} [Group A] [Group B]
    (f : A →* B) : ClassFunction B ℂ →ₗ[ℂ] ClassFunction A ℂ where
  toFun phi :=
    ⟨fun a ↦ phi (f a), fun x a ↦ by
      simpa only [map_mul, map_inv] using
        ClassFunction.conj_apply phi (f x) (f a)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem classFunctionComapComplex_apply
    {A : Type u} {B : Type v} [Group A] [Group B]
    (f : A →* B) (phi : ClassFunction B ℂ) (a : A) :
    classFunctionComapComplex f phi a = phi (f a) :=
  rfl

private theorem classFunctionComapComplex_injective
    {A : Type u} {B : Type v} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    Function.Injective (classFunctionComapComplex f) := by
  intro phi psi h
  ext b
  obtain ⟨a, rfl⟩ := hf b
  exact congrArg (fun z : ClassFunction A ℂ ↦ z a) h

/-- Irreducibility is preserved by pullback along a surjective group
homomorphism, with independent universes for the two groups. -/
private theorem representationIrreducible_comp_surjective_complex
    {A : Type u} {B : Type v} {V : Type w}
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

private noncomputable def comapIrreducibleComplex
    {A : Type u} {B : Type v}
    [Group A] [Fintype A] [Group B] [Fintype B]
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
    representationIrreducible_comp_surjective_complex
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem comapIrreducibleComplex_apply
    {A : Type u} {B : Type v}
    [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    comapIrreducibleComplex f hf chi a = chi (f a) := by
  simp only [comapIrreducibleComplex,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

private theorem coe_comapIrreducibleComplex
    {A : Type u} {B : Type v}
    [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) :
    (comapIrreducibleComplex f hf chi : ClassFunction A ℂ) =
      classFunctionComapComplex f (chi : ClassFunction B ℂ) := by
  ext a
  exact comapIrreducibleComplex_apply f hf chi a

/-- Character pairing is unchanged by pullback along a group equivalence. -/
private theorem characterPairing_classFunctionComapComplex
    {A : Type u} {B : Type v}
    [Group A] [Fintype A] [Group B] [Fintype B]
    (e : A ≃* B) (phi psi : ClassFunction B ℂ) :
    characterPairing (classFunctionComapComplex e.toMonoidHom phi)
        (classFunctionComapComplex e.toMonoidHom psi) =
      characterPairing phi psi := by
  unfold characterPairing
  rw [Nat.card_congr e.toEquiv]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun a ↦ ?_
  simp only [classFunctionComapComplex_apply, map_inv]
  have hea : e.toMonoidHom a = e.toEquiv a := rfl
  rw [hea]

/-- Normal conjugation commutes with pullback along a group equivalence. -/
private theorem normalConjugate_classFunctionComapComplex
    {A : Type u} {B : Type v}
    [Group A] [Fintype A] [Group B] [Fintype B]
    (e : A ≃* B) (H : Subgroup A) [H.Normal]
    (theta : ClassFunction (H.map (e : A →* B)) ℂ) (x : A) :
    letI : (H.map (e : A →* B)).Normal :=
      Subgroup.Normal.map (inferInstance : H.Normal)
        e.toMonoidHom e.surjective
    ClassFunction.normalConjugate H x
        (classFunctionComapComplex
          (e.subgroupMap H).toMonoidHom theta) =
      classFunctionComapComplex (e.subgroupMap H).toMonoidHom
        (ClassFunction.normalConjugate
          (H.map (e : A →* B)) (e x) theta) := by
  letI : (H.map (e : A →* B)).Normal :=
    Subgroup.Normal.map (inferInstance : H.Normal)
      e.toMonoidHom e.surjective
  ext h
  simp only [ClassFunction.normalConjugate_apply,
    classFunctionComapComplex_apply]
  apply congrArg theta
  apply Subtype.ext
  change e (↑((MulAut.conjNormal x).symm h) : A) =
    ↑((MulAut.conjNormal (e x)).symm ((e.subgroupMap H) h))
  simp only [MulAut.conjNormal_symm_apply]
  have hmap : (↑((e.subgroupMap H) h) : B) = e (h : A) := rfl
  rw [hmap, map_mul, map_mul, map_inv]

/-- Induction commutes with pullback along a group equivalence. -/
private theorem induce_classFunctionComapComplex_map
    {A : Type u} {B : Type v}
    [Group A] [Fintype A] [Group B] [Fintype B]
    (e : A ≃* B) (H : Subgroup A)
    (theta : ClassFunction (H.map (e : A →* B)) ℂ) :
    classFunctionComapComplex e.toMonoidHom
        (ClassFunction.induce (H.map (e : A →* B)) theta) =
      ClassFunction.induce H
        (classFunctionComapComplex
          (e.subgroupMap H).toMonoidHom theta) := by
  ext g
  rw [classFunctionComapComplex_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula,
    Nat.card_congr (e.subgroupMap H).toEquiv]
  congr 1
  symm
  refine Fintype.sum_equiv e.toEquiv _ _ fun x ↦ ?_
  have hmem :
      (e.toEquiv x)⁻¹ * e.toMonoidHom g * e.toEquiv x ∈
          H.map (e : A →* B) ↔
        x⁻¹ * g * x ∈ H := by
    constructor
    · rintro ⟨z, hz, hzEq⟩
      have hze : z = x⁻¹ * g * x := by
        apply e.injective
        calc
          e z = (e.toEquiv x)⁻¹ * e.toMonoidHom g * e.toEquiv x := hzEq
          _ = e (x⁻¹ * g * x) := by
            simp only [map_mul, map_inv]
            rfl
      have hzH : z ∈ H := hz
      rw [hze] at hzH
      exact hzH
    · intro hx
      refine ⟨x⁻¹ * g * x, hx, ?_⟩
      simp only [map_mul, map_inv]
      rfl
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [dif_pos hx, dif_pos (hmem.2 hx),
      classFunctionComapComplex_apply]
    apply congrArg theta
    apply Subtype.ext
    calc
      ↑((e.subgroupMap H).toMonoidHom ⟨x⁻¹ * g * x, hx⟩) =
          e (x⁻¹ * g * x) := rfl
      _ = (e x)⁻¹ * e g * e x := by
        rw [map_mul, map_mul, map_inv]
      _ = (e.toEquiv x)⁻¹ * e.toMonoidHom g * e.toEquiv x := rfl
  · rw [dif_neg hx, dif_neg (hmem.not.mpr hx)]

/-- Induction is insensitive to transporting its subgroup across equality. -/
private theorem induce_comapIrreducibleComplex_subgroupCongr
    {A : Type u} [Group A] [Fintype A]
    (H K : Subgroup A) (hHK : H = K)
    (psi : IrreducibleCharacter K ℂ) :
    ClassFunction.induce H
        (comapIrreducibleComplex
          (MulEquiv.subgroupCongr hHK).toMonoidHom
          (MulEquiv.subgroupCongr hHK).surjective psi :
            ClassFunction H ℂ) =
      ClassFunction.induce K (psi : ClassFunction K ℂ) := by
  subst K
  apply congrArg (ClassFunction.induce H)
  ext h
  rw [comapIrreducibleComplex_apply]
  apply congrArg psi
  apply Subtype.ext
  rfl

/-- A constituent induced from a normal subgroup is induced irreducibly from
its inertia subgroup.  The finite resizing is solely an adapter around the
current equal-universe Clifford correspondence. -/
private theorem exists_inertia_inducing_character_complex
    {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (chi : IrreducibleCharacter G ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.induce H (theta : ClassFunction H ℂ))) :
    ∃ T : Subgroup G,
      T = ClassFunction.inertia H (theta : ClassFunction H ℂ) ∧
        ∃ psi : IrreducibleCharacter T ℂ,
          (chi : ClassFunction G ℂ) =
            ClassFunction.induce T (psi : ClassFunction T ℂ) := by
  classical
  obtain ⟨G₀, _, _, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let H₀ : Subgroup G₀ := H.map (e : G →* G₀)
  letI : H₀.Normal :=
    Subgroup.Normal.map (inferInstance : H.Normal)
      e.toMonoidHom e.surjective
  let theta₀ : IrreducibleCharacter H₀ ℂ :=
    comapIrreducibleComplex
      (e.subgroupMap H).symm.toMonoidHom
      (e.subgroupMap H).symm.surjective theta
  let chi₀ : IrreducibleCharacter G₀ ℂ :=
    comapIrreducibleComplex e.symm.toMonoidHom
      e.symm.surjective chi
  have hthetaPull :
      classFunctionComapComplex (e.subgroupMap H).toMonoidHom
          (theta₀ : ClassFunction H₀ ℂ) =
        (theta : ClassFunction H ℂ) := by
    ext h
    rw [classFunctionComapComplex_apply,
      comapIrreducibleComplex_apply]
    apply congrArg theta
    exact (e.subgroupMap H).symm_apply_apply h
  have hchiPull :
      classFunctionComapComplex e.toMonoidHom
          (chi₀ : ClassFunction G₀ ℂ) =
        (chi : ClassFunction G ℂ) := by
    ext g
    rw [classFunctionComapComplex_apply,
      comapIrreducibleComplex_apply]
    exact congrArg chi (e.symm_apply_apply g)
  have hinducePull :
      classFunctionComapComplex e.toMonoidHom
          (ClassFunction.induce H₀
            (theta₀ : ClassFunction H₀ ℂ)) =
        ClassFunction.induce H (theta : ClassFunction H ℂ) := by
    calc
      classFunctionComapComplex e.toMonoidHom
          (ClassFunction.induce H₀
            (theta₀ : ClassFunction H₀ ℂ)) =
        ClassFunction.induce H
          (classFunctionComapComplex
            (e.subgroupMap H).toMonoidHom
            (theta₀ : ClassFunction H₀ ℂ)) := by
          simpa only [H₀] using
            induce_classFunctionComapComplex_map e H
              (theta₀ : ClassFunction H₀ ℂ)
      _ = ClassFunction.induce H (theta : ClassFunction H ℂ) :=
        congrArg (ClassFunction.induce H) hthetaPull
  have hchi₀ : chi₀.IsConstituent
      (ClassFunction.induce H₀
        (theta₀ : ClassFunction H₀ ℂ)) := by
    unfold IrreducibleCharacter.IsConstituent at hchi ⊢
    intro hzero
    apply hchi
    rw [← hinducePull, ← hchiPull,
      characterPairing_classFunctionComapComplex, hzero]
  let T := ClassFunction.inertia H (theta : ClassFunction H ℂ)
  have hTmap :
      ClassFunction.inertia H₀ (theta₀ : ClassFunction H₀ ℂ) =
        T.map (e : G →* G₀) := by
    ext y
    have hmemMap : y ∈ T.map (e : G →* G₀) ↔ e.symm y ∈ T := by
      constructor
      · rintro ⟨x, hx, hxEq⟩
        have hxy : x = e.symm y := by
          apply e.injective
          rw [e.apply_symm_apply]
          exact hxEq
        have hxT : x ∈ T := hx
        rw [hxy] at hxT
        exact hxT
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    rw [hmemMap]
    dsimp only [T]
    rw [ClassFunction.mem_inertia_iff,
      ClassFunction.mem_inertia_iff]
    constructor
    · intro hy
      calc
        ClassFunction.normalConjugate H (e.symm y)
            (theta : ClassFunction H ℂ) =
          ClassFunction.normalConjugate H (e.symm y)
            (classFunctionComapComplex
              (e.subgroupMap H).toMonoidHom
              (theta₀ : ClassFunction H₀ ℂ)) := by rw [hthetaPull]
        _ = classFunctionComapComplex
              (e.subgroupMap H).toMonoidHom
              (ClassFunction.normalConjugate H₀ y
                (theta₀ : ClassFunction H₀ ℂ)) := by
          simpa only [H₀, e.apply_symm_apply] using
            normalConjugate_classFunctionComapComplex e H
              (theta₀ : ClassFunction H₀ ℂ) (e.symm y)
        _ = classFunctionComapComplex
              (e.subgroupMap H).toMonoidHom
              (theta₀ : ClassFunction H₀ ℂ) := by rw [hy]
        _ = theta := hthetaPull
    · intro hy
      apply classFunctionComapComplex_injective
        (e.subgroupMap H).toMonoidHom
        (e.subgroupMap H).surjective
      calc
        classFunctionComapComplex
            (e.subgroupMap H).toMonoidHom
            (ClassFunction.normalConjugate H₀ y
              (theta₀ : ClassFunction H₀ ℂ)) =
          ClassFunction.normalConjugate H (e.symm y)
            (classFunctionComapComplex
              (e.subgroupMap H).toMonoidHom
              (theta₀ : ClassFunction H₀ ℂ)) := by
          symm
          simpa only [H₀, e.apply_symm_apply] using
            normalConjugate_classFunctionComapComplex e H
              (theta₀ : ClassFunction H₀ ℂ) (e.symm y)
        _ = ClassFunction.normalConjugate H (e.symm y)
            (theta : ClassFunction H ℂ) := by rw [hthetaPull]
        _ = theta := hy
        _ = classFunctionComapComplex
            (e.subgroupMap H).toMonoidHom
            (theta₀ : ClassFunction H₀ ℂ) := hthetaPull.symm
  have hchiConst : chi₀ ∈ ClassFunction.constituents
      (ClassFunction.induce H₀ (theta₀ : ClassFunction H₀ ℂ)) :=
    (ClassFunction.mem_constituents_iff _ _).2 hchi₀
  rw [ClassFunction.inertiaConstituentMap_image H₀ theta₀] at hchiConst
  obtain ⟨index₀, _hindex₀, hindex₀⟩ := Finset.mem_image.mp hchiConst
  have hlow : (chi₀ : ClassFunction G₀ ℂ) =
      ClassFunction.induce
        (ClassFunction.inertia H₀ (theta₀ : ClassFunction H₀ ℂ))
        (index₀.1 : ClassFunction
          (ClassFunction.inertia H₀
            (theta₀ : ClassFunction H₀ ℂ)) ℂ) := by
    calc
      (chi₀ : ClassFunction G₀ ℂ) =
          (ClassFunction.inertiaConstituentMap H₀ theta₀ index₀ :
            ClassFunction G₀ ℂ) := by rw [hindex₀]
      _ = ClassFunction.induce
          (ClassFunction.inertia H₀
            (theta₀ : ClassFunction H₀ ℂ))
          (index₀.1 : ClassFunction
            (ClassFunction.inertia H₀
              (theta₀ : ClassFunction H₀ ℂ)) ℂ) :=
        ClassFunction.coe_inertiaConstituentMap H₀ theta₀ index₀
  let psiMap : IrreducibleCharacter (T.map (e : G →* G₀)) ℂ :=
    comapIrreducibleComplex
      (MulEquiv.subgroupCongr hTmap.symm).toMonoidHom
      (MulEquiv.subgroupCongr hTmap.symm).surjective index₀.1
  have hlowMap : (chi₀ : ClassFunction G₀ ℂ) =
      ClassFunction.induce (T.map (e : G →* G₀))
        (psiMap : ClassFunction (T.map (e : G →* G₀)) ℂ) := by
    calc
      (chi₀ : ClassFunction G₀ ℂ) =
          ClassFunction.induce
            (ClassFunction.inertia H₀
              (theta₀ : ClassFunction H₀ ℂ))
            (index₀.1 : ClassFunction
              (ClassFunction.inertia H₀
                (theta₀ : ClassFunction H₀ ℂ)) ℂ) := hlow
      _ = ClassFunction.induce (T.map (e : G →* G₀))
          (psiMap : ClassFunction (T.map (e : G →* G₀)) ℂ) := by
        symm
        simpa only [psiMap] using
          induce_comapIrreducibleComplex_subgroupCongr
            (T.map (e : G →* G₀))
            (ClassFunction.inertia H₀
              (theta₀ : ClassFunction H₀ ℂ))
            hTmap.symm index₀.1
  let psi : IrreducibleCharacter T ℂ :=
    comapIrreducibleComplex
      (e.subgroupMap T).toMonoidHom
      (e.subgroupMap T).surjective psiMap
  refine ⟨T, rfl, psi, ?_⟩
  calc
    (chi : ClassFunction G ℂ) =
        classFunctionComapComplex e.toMonoidHom
          (chi₀ : ClassFunction G₀ ℂ) := hchiPull.symm
    _ = classFunctionComapComplex e.toMonoidHom
        (ClassFunction.induce (T.map (e : G →* G₀))
          (psiMap : ClassFunction (T.map (e : G →* G₀)) ℂ)) :=
      congrArg (classFunctionComapComplex e.toMonoidHom) hlowMap
    _ = ClassFunction.induce T
        (classFunctionComapComplex
          (e.subgroupMap T).toMonoidHom
          (psiMap : ClassFunction (T.map (e : G →* G₀)) ℂ)) :=
      induce_classFunctionComapComplex_map e T
        (psiMap : ClassFunction (T.map (e : G →* G₀)) ℂ)
    _ = ClassFunction.induce T (psi : ClassFunction T ℂ) := by
      apply congrArg (ClassFunction.induce T)
      exact (coe_comapIrreducibleComplex
        (e.subgroupMap T).toMonoidHom
        (e.subgroupMap T).surjective psiMap).symm

end internal

set_option linter.unusedVariables false in
/-- Clause (a) of Peterfalvi (9.8), in the canonical factor-action model.
The selected non-Galois pointwise-kernel index divides the degree of every
irreducible character in `X_(H₀)`. -/
theorem pTypeNonGalois_fixed_degree_divisibility
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let HU := (derivedWithin M).subgroupOf M
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    ∀ chi ∈ Iirr_kerD (k := ℂ) H H₀,
      pTypeNonGaloisIndex hD not_Galois ∣
        pTypeIrreducibleDegree chi := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU : Subgroup M := (derivedWithin M).subgroupOf M
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ : Subgroup HU :=
    ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  let K := pointwiseActionKernel D.U_action data.H₁
  letI : H.Normal :=
    Subgroup.Normal.subgroupOf (Fcore_normal M) HU
  letI : H₀.Normal :=
    Subgroup.Normal.subgroupOf
      (Ptype_Fcore_kernel_normal_M ctx) HU
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  change ∀ chi ∈ Iirr_kerD (k := ℂ) H H₀,
    K.index ∣ pTypeIrreducibleDegree chi
  intro chi hchi
  obtain ⟨theta, htheta⟩ :=
    internal.exists_constituent_restrict_complex H chi
  have hchiData := mem_Iirr_kerD.mp hchi
  have hchiH₀rho : H₀ ≤ chi.representation.ρ.ker := by
    rw [← internal.translationKernel_irreducibleCharacter_general chi]
    exact hchiData.1
  have hchiHrho : ¬ H ≤ chi.representation.ρ.ker := by
    intro hker
    apply hchiData.2
    rw [internal.translationKernel_irreducibleCharacter_general chi]
    exact hker
  have hthetaH₀rho : H₀.subgroupOf H ≤
      theta.representation.ρ.ker :=
    internal.subgroup_le_constituent_kernel
      H H₀ chi theta htheta hchiH₀rho
  have hthetaNonrho :
      ¬ (⊤ : Subgroup H) ≤ theta.representation.ρ.ker := by
    intro hker
    apply hchiHrho
    exact internal.normal_le_kernel_of_constituent_top_kernel
      H chi theta htheta hker
  have hthetaH₀ : H₀.subgroupOf H ≤
      ClassFunction.translationKernel
        (theta : ClassFunction H ℂ) := by
    rw [internal.translationKernel_irreducibleCharacter_general theta]
    exact hthetaH₀rho
  have hthetaNon :
      ¬ (⊤ : Subgroup H) ≤
        ClassFunction.translationKernel
          (theta : ClassFunction H ℂ) := by
    rw [internal.translationKernel_irreducibleCharacter_general theta]
    exact hthetaNonrho
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hFMHU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro x hx
    exact hHder hx
  let eHM : H ≃* (Fitting_core M).subgroupOf M :=
    Subgroup.subgroupOfEquivOfLe hFMHU
  let eHF : (Fitting_core M).subgroupOf M ≃* Fitting_core M :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
  let eH : H ≃* Fitting_core M := eHM.trans eHF
  let N : Subgroup (Fitting_core M) :=
    (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
  letI : N.Normal := by
    simpa only [N] using Ptype_Fcore_kernel_normal_Fcore ctx
  let thetaF : IrreducibleCharacter (Fitting_core M) ℂ :=
    internal.comapIrreducibleComplex
      eH.symm.toMonoidHom eH.symm.surjective theta
  have hNthetaF : N ≤ ClassFunction.translationKernel
      (thetaF : ClassFunction (Fitting_core M) ℂ) := by
    intro n hn
    rw [ClassFunction.mem_translationKernel_iff]
    intro x
    let nH : H := eH.symm n
    let xH : H := eH.symm x
    have hnH : nH ∈ H₀.subgroupOf H := by
      change (n : Gamma) ∈ Ptype_Fcore_kernel ctx
      exact hn
    have hvalue :=
      (ClassFunction.mem_translationKernel_iff
        (theta : ClassFunction H ℂ) nH).mp
          (hthetaH₀ hnH) xH
    change (internal.comapIrreducibleComplex
      eH.symm.toMonoidHom eH.symm.surjective theta) (n * x) =
        (internal.comapIrreducibleComplex
          eH.symm.toMonoidHom eH.symm.surjective theta) x
    rw [internal.comapIrreducibleComplex_apply,
      internal.comapIrreducibleComplex_apply, map_mul]
    change theta (nH * xH) = theta xH
    exact hvalue
  have hthetaFNon :
      ¬ (⊤ : Subgroup (Fitting_core M)) ≤
        ClassFunction.translationKernel
          (thetaF : ClassFunction (Fitting_core M) ℂ) := by
    intro htop
    apply hthetaNon
    intro x _hx
    rw [ClassFunction.mem_translationKernel_iff]
    intro y
    have hxF := htop (Subgroup.mem_top (eH x))
    have hvalue :=
      (ClassFunction.mem_translationKernel_iff
        (thetaF : ClassFunction (Fitting_core M) ℂ) (eH x)).mp
          hxF (eH y)
    change (internal.comapIrreducibleComplex
      eH.symm.toMonoidHom eH.symm.surjective theta)
        (eH x * eH y) =
      (internal.comapIrreducibleComplex
        eH.symm.toMonoidHom eH.symm.surjective theta) (eH y) at hvalue
    rw [internal.comapIrreducibleComplex_apply,
      internal.comapIrreducibleComplex_apply, map_mul] at hvalue
    have hxBack : eH.symm.toMonoidHom (eH x) = x :=
      eH.symm_apply_apply x
    have hyBack : eH.symm.toMonoidHom (eH y) = y :=
      eH.symm_apply_apply y
    rw [hxBack, hyBack] at hvalue
    exact hvalue
  let thetaBar : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    internal.quotientDescendIrreducibleComplex N thetaF hNthetaF
  have hthetaBarNon :
      ¬ (⊤ : Subgroup (ptypeFCoreFactor ctx)) ≤
        ClassFunction.translationKernel
          (thetaBar : ClassFunction (ptypeFCoreFactor ctx) ℂ) := by
    intro htop
    apply hthetaFNon
    intro x _hx
    rw [ClassFunction.mem_translationKernel_iff]
    intro y
    let q : Fitting_core M →* ptypeFCoreFactor ctx :=
      QuotientGroup.mk' N
    have hvalue :=
      (ClassFunction.mem_translationKernel_iff
        (thetaBar : ClassFunction (ptypeFCoreFactor ctx) ℂ) (q x)).mp
          (htop (Subgroup.mem_top (q x))) (q y)
    calc
      thetaF (x * y) = thetaBar (q (x * y)) := by
        exact (internal.quotientDescendIrreducibleComplex_mk_apply
          N thetaF hNthetaF (x * y)).symm
      _ = thetaBar (q x * q y) := by rw [map_mul]
      _ = thetaBar (q y) := hvalue
      _ = thetaF y :=
        internal.quotientDescendIrreducibleComplex_mk_apply
          N thetaF hNthetaF y
  let A : W₁ → Subgroup (ptypeFCoreFactor ctx) :=
    fun w ↦ actionConjugate D.W₁_action data.H₁ w
  obtain ⟨w, hw⟩ : ∃ w : W₁,
      ¬ A w ≤ ClassFunction.translationKernel
        (thetaBar : ClassFunction (ptypeFCoreFactor ctx) ℂ) := by
    by_contra hall
    apply hthetaBarNon
    rw [← data.conjugates_direct.1]
    apply iSup_le
    intro w
    exact not_not.mp (not_exists.mp hall w)
  have hAcard : Nat.card (A w) = D.p := by
    change Nat.card
      (data.H₁.map (D.W₁_action w).toMonoidHom) = D.p
    exact (Nat.card_congr
      ((D.W₁_action w).subgroupMap data.H₁).toEquiv).symm.trans
        data.card_H₁
  have hAprime : (Nat.card (A w)).Prime := by
    rw [hAcard]
    exact D.p_prime
  have hAdim : Module.finrank ℂ thetaBar.representation = 1 := by
    letI : CategoryTheory.Simple thetaBar.representation :=
      thetaBar.representation_simple
    letI : Representation.IsIrreducible thetaBar.representation.ρ :=
      representation_isIrreducible_of_simple_fdRep thetaBar.representation
    exact
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        thetaBar.representation.ρ
  let T : Subgroup HU :=
    ClassFunction.inertia H (theta : ClassFunction H ℂ)
  have hHT : H ≤ T := ClassFunction.le_inertia H _
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let uToHU : U →* HU :=
    { toFun := fun x ↦
        ⟨⟨(x : Gamma), hUM x.property⟩, hUder x.property⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have huToHU_range : uToHU.range = UHU := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hy
      let x : U := ⟨((y : HU) : M), hy⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
  let UT : Subgroup U := T.comap uToHU
  let Kw := pointwiseActionKernel D.U_action (A w)
  have hUnormF : U ≤
      Subgroup.normalizer (Fitting_core M : Set Gamma) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Fcore_sub M)).mp (Fcore_normal M))
  have hUTKw : UT ≤ Kw := by
    intro x hx
    have hxT : uToHU x ∈ T := hx
    have hxInv : (uToHU x)⁻¹ ∈ T := T.inv_mem hxT
    have hinertia :=
      (ClassFunction.mem_inertia_iff H
        (theta : ClassFunction H ℂ) (uToHU x)⁻¹).mp hxInv
    apply internal.mem_pointwiseActionKernel_of_character_fixed
      D.U_action (A w)
      (D.actionConjugate_U_invariant data.H₁_normalized w)
      hAprime thetaBar hAdim hw x
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N z
    let hconj : Fitting_core M :=
      ⟨(x : Gamma) * (h : Gamma) * (x : Gamma)⁻¹,
        (hUnormF x.property h).mp h.property⟩
    let hH : H := eH.symm h
    have hvalue := congrArg
      (fun f : ClassFunction H ℂ ↦ f hH) hinertia
    rw [ClassFunction.normalConjugate_apply] at hvalue
    have heHcoe (z : H) : (eH z : Gamma) = (z : Gamma) := by
      rfl
    have hHval : (hH : Gamma) = (h : Gamma) := by
      calc
        (hH : Gamma) = (eH hH : Gamma) := (heHcoe hH).symm
        _ = (h : Gamma) := congrArg
          (fun z : Fitting_core M ↦ (z : Gamma))
          (eH.apply_symm_apply h)
    have hconjVal : ((eH.symm hconj : H) : Gamma) =
        (hconj : Gamma) := by
      calc
        ((eH.symm hconj : H) : Gamma) =
            (eH (eH.symm hconj) : Gamma) :=
          (heHcoe (eH.symm hconj)).symm
        _ = (hconj : Gamma) := congrArg
          (fun z : Fitting_core M ↦ (z : Gamma))
          (eH.apply_symm_apply hconj)
    have harg :
        (MulAut.conjNormal (uToHU x)⁻¹).symm hH =
          eH.symm hconj := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      simp only [MulAut.conjNormal_symm_apply, inv_inv]
      change (x : Gamma) * (hH : Gamma) * (x : Gamma)⁻¹ =
        ((eH.symm hconj : H) : Gamma)
      rw [hHval, hconjVal]
    have hthetaConj : thetaF hconj = thetaF h := by
      change (internal.comapIrreducibleComplex
        eH.symm.toMonoidHom eH.symm.surjective theta) hconj =
        (internal.comapIrreducibleComplex
          eH.symm.toMonoidHom eH.symm.surjective theta) h
      rw [internal.comapIrreducibleComplex_apply,
        internal.comapIrreducibleComplex_apply]
      change theta (eH.symm hconj) = theta hH
      rw [← harg]
      exact hvalue
    change thetaBar
        (ptypeFCoreAction ctx x (QuotientGroup.mk' N h)) =
      thetaBar (QuotientGroup.mk' N h)
    rw [ptypeFCoreAction,
      subgroupConjugationFactorHom_apply_mk,
      internal.quotientDescendIrreducibleComplex_mk_apply,
      internal.quotientDescendIrreducibleComplex_mk_apply]
    simpa only [hconj] using hthetaConj
  let eUw : U ≃* U := D.W₁_action_U w⁻¹
  have hKwComap : Kw = K.comap eUw.toMonoidHom := by
    ext x
    exact D.mem_pointwiseActionKernel_actionConjugate_iff
      data.H₁ w x
  have hKwIndex : Kw.index = K.index := by
    rw [hKwComap]
    exact K.index_comap_of_surjective eUw.surjective
  have hcomp : H.IsComplement' UHU := by
    let eHU : HU ≃* derivedWithin M :=
      Subgroup.subgroupOfEquivOfLe hDerM
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
  have hTindex : T.index = T.relIndex UHU :=
    internal.pTypeIndex_eq_relIndex_of_isComplement_of_left_le hcomp hHT
  have hUTindex : UT.index = T.relIndex UHU := by
    change (T.comap uToHU).index = T.relIndex UHU
    rw [Subgroup.index_comap, huToHU_range]
  have hKindex : K.index ∣ T.index := by
    calc
      K.index = Kw.index := hKwIndex.symm
      _ ∣ UT.index := Subgroup.index_dvd_of_le hUTKw
      _ = T.index := hUTindex.trans hTindex.symm
  have hchiConst : chi.IsConstituent
      (ClassFunction.induce H (theta : ClassFunction H ℂ)) :=
    (theta.isConstituent_restrict_iff_induce H chi).mp htheta
  obtain ⟨T', hT', psi, hchiInd⟩ :=
    internal.exists_inertia_inducing_character_complex
      H theta chi hchiConst
  subst T'
  exact internal.pTypeIrreducibleDegree_dvd_of_inertiaIndex_dvd
    T psi chi hchiInd hKindex

end

end Submission.OddOrder.PF
