import Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure
import Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer

/-!
# Peterfalvi Section 9: reusable Galois-character arithmetic

This module isolates the character-theoretic and numerical calculations used
in Peterfalvi (9.9).  The local subgroup constructions and the non-Galois
reducible layer are supplied by the two preceding Section 9 modules; the
results here deliberately stop before the subgroup adapters needed for (9.10).
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open CategoryTheory Limits
open scoped BigOperators Classical IsMulCommutative Pointwise MonoidAlgebra
  commutatorElement

noncomputable section

universe u

namespace PTypeGaloisCharacterArithmeticInternal

/-! The repository's global irreducible-character finiteness instance still
couples the group and coefficient universes.  Orthogonality gives the needed
split-universe instances directly. -/

private instance complexIrreducibleCharacterFinite
    {A : Type u} [Group A] [Fintype A] :
    Finite (IrreducibleCharacter A ℂ) := by
  letI : Invertible (Nat.card A : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact IrreducibleCharacter.linearIndependent.finite

private instance complexIrreducibleCharacterFintype
    {A : Type u} [Group A] [Fintype A] :
    Fintype (IrreducibleCharacter A ℂ) :=
  Fintype.ofFinite _

/-! ## Character counts for commutative groups -/

/-- A finite commutative group has one complex irreducible character for
each group element. -/
theorem card_irreducibleCharacter_of_commutative
    {A : Type u} [Group A] [Fintype A] [IsMulCommutative A] :
    Fintype.card (IrreducibleCharacter A ℂ) = Nat.card A := by
  letI : Invertible (Nat.card A : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype (ConjClasses A) := Fintype.ofFinite _
  let basis : Module.Basis (IrreducibleCharacter A ℂ) ℂ
      (ClassFunction A ℂ) :=
    Module.Basis.mk IrreducibleCharacter.linearIndependent (by
      rw [irreducibleCharacter_span_eq_top])
  calc
    Fintype.card (IrreducibleCharacter A ℂ) =
        Module.finrank ℂ (ClassFunction A ℂ) :=
      (Module.finrank_eq_card_basis basis).symm
    _ = Module.finrank ℂ (ConjClasses A → ℂ) :=
      (ClassFunction.conjClassesLinearEquiv
        (G := A) (k := ℂ)).finrank_eq
    _ = Fintype.card (ConjClasses A) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = Fintype.card A :=
      Fintype.card_congr (ConjClasses.mkEquiv (α := A)).symm
    _ = Nat.card A := Fintype.card_eq_nat_card

/-- Removing the principal character leaves `|A| - 1` irreducibles in a
finite commutative group. -/
theorem card_nontrivial_irreducibleCharacters_of_commutative
    (A : Type u) [Group A] [Fintype A] [IsMulCommutative A] :
    (Finset.univ.erase
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter A ℂ)).card = Nat.card A - 1 := by
  rw [Finset.card_erase_of_mem
      (Finset.mem_univ
        (IrreducibleCharacter.trivial : IrreducibleCharacter A ℂ)),
    Finset.card_univ, card_irreducibleCharacter_of_commutative]

/-! ## Local proof scaffolding -/

/-- Restricting a nonzero irreducible representation to a subgroup still has
an irreducible constituent. -/
private theorem exists_constituent_restrict
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [Fintype H]
    (chi : IrreducibleCharacter A ℂ) :
    ∃ theta : IrreducibleCharacter H ℂ,
      theta.IsConstituent
        (ClassFunction.restrict H (chi : ClassFunction A ℂ)) := by
  let V : FDRep ℂ H :=
    FDRep.of (chi.representation.ρ.comp H.subtype)
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
      ClassFunction.restrict H (chi : ClassFunction A ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  rwa [hV] at htheta

/-- A constituent admits an injective intertwiner into the representation
realizing the ambient class function.  This is the split-universe fragment
of the usual constituent-kernel argument. -/
private theorem exists_injective_constituent_hom
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
    simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
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

/-- The kernel of a realized character lies in the kernel of each
irreducible constituent, without identifying the group and coefficient
universes. -/
private theorem representationKernel_le_constituentKernel
    {G : Type u} [Group G] [Fintype G]
    (V : FDRep ℂ G) (chi : IrreducibleCharacter G ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ := exists_injective_constituent_hom V chi hchi
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

/-- If a constituent of the restriction to a normal subgroup is trivial on
that subgroup, then the ambient irreducible is trivial there as well. -/
private theorem normal_le_kernel_of_constituent_top_kernel
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (theta : IrreducibleCharacter N ℂ)
    (hconst : theta.IsConstituent
      (ClassFunction.restrict N (chi : ClassFunction A ℂ)))
    (htheta : (⊤ : Subgroup N) ≤ theta.representation.ρ.ker) :
    N ≤ chi.representation.ρ.ker := by
  let V : FDRep ℂ N :=
    FDRep.of (chi.representation.ρ.comp N.subtype)
  have hVchar : ClassFunction.ofRepresentation V.ρ =
      ClassFunction.restrict N (chi : ClassFunction A ℂ) := by
    calc
      ClassFunction.ofRepresentation V.ρ =
          ClassFunction.restrict N
            (ClassFunction.ofRepresentation chi.representation.ρ) := rfl
      _ = ClassFunction.restrict N (chi : ClassFunction A ℂ) := by
        rw [chi.ofRepresentation_representation]
  have hthetaV : theta.IsConstituent
      (ClassFunction.ofRepresentation V.ρ) := by
    rwa [hVchar]
  obtain ⟨f, hfinj⟩ :=
    exists_injective_constituent_hom V theta hthetaV
  let fR := (forget₂ (FDRep ℂ N) (Rep ℂ N)).map f
  let fLinear : theta.representation →ₗ[ℂ] chi.representation :=
    f.hom.hom.hom
  have hfinjLinear : Function.Injective fLinear := hfinj
  letI : CategoryTheory.Simple theta.representation :=
    theta.representation_simple
  letI : Nontrivial theta.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero theta.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := exists_ne (0 : theta.representation)
  let w : chi.representation := fLinear v
  have hw : w ≠ 0 := by
    intro hw0
    exact hv ((fLinear.map_eq_zero_iff hfinjLinear).mp hw0)
  let rho := chi.representation.ρ
  let tau : Representation ℂ N chi.representation :=
    rho.comp N.subtype
  have hwfix : w ∈ tau.invariants := by
    rw [Representation.mem_invariants]
    intro n
    have hinter := _root_.Representation.IntertwiningMap.isIntertwining
      (ρ := ((forget₂ (FDRep ℂ N) (Rep ℂ N)).obj
        theta.representation).ρ)
      (σ := ((forget₂ (FDRep ℂ N) (Rep ℂ N)).obj V).ρ)
      (f := fR.hom) n v
    change fLinear (theta.representation.ρ n v) =
      rho (n : A) (fLinear v) at hinter
    rw [MonoidHom.mem_ker.mp (htheta (Subgroup.mem_top n))] at hinter
    change rho (n : A) (fLinear v) = fLinear v
    calc
      rho (n : A) (fLinear v) =
          fLinear ((1 : Module.End ℂ theta.representation) v) := hinter.symm
      _ = fLinear v := by rfl
  let fixed : Subrepresentation rho :=
    normalInvariantsSubrepresentation rho N
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hfixed_ne : fixed ≠ ⊥ := by
    intro hbot
    have hwbot : w ∈ (⊥ : Submodule ℂ chi.representation) := by
      have hwfixed : w ∈ fixed := hwfix
      rw [hbot] at hwfixed
      exact hwfixed
    exact hw ((Submodule.mem_bot ℂ).mp hwbot)
  have hfixed : fixed = ⊤ :=
    (eq_bot_or_eq_top fixed).resolve_left hfixed_ne
  intro n hn
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro z
  have hz : z ∈ fixed := by rw [hfixed]; trivial
  exact (Representation.mem_invariants _ _).mp hz ⟨n, hn⟩

/-! ## Linearity and core induction -/

/-- A one-dimensional representation obtained from a multiplicative
character.  This local construction keeps the finite group and `ℂ` in
independent universes. -/
private def mulCharacterRepresentationComplex
    {A Q : Type u} [Group A] [CommGroup Q]
    (q : A →* Q) (lambda : MulChar Q ℂ) :
    Representation ℂ A ℂ where
  toFun a := lambda (q a) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro z
    simp only [map_mul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      Module.End.mul_apply]
    ring

@[simp]
private theorem mulCharacterRepresentationComplex_character
    {A Q : Type u} [Group A] [CommGroup Q]
    (q : A →* Q) (lambda : MulChar Q ℂ) (a : A) :
    (mulCharacterRepresentationComplex q lambda).character a =
      lambda (q a) := by
  change LinearMap.trace ℂ ℂ
    (lambda (q a) • LinearMap.id) = lambda (q a)
  rw [map_smul, LinearMap.trace_id]
  simp

/-- Bundle the character of the preceding one-dimensional representation as
an irreducible character. -/
private noncomputable def irreducibleOfMulCharComplex
    {A Q : Type u} [Group A] [Fintype A] [CommGroup Q]
    (q : A →* Q) (lambda : MulChar Q ℂ) :
    IrreducibleCharacter A ℂ := by
  let rho : Representation ℂ A ℂ :=
    mulCharacterRepresentationComplex q lambda
  letI : Representation.IsIrreducible rho := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    apply (isSimpleModule_iff ℂ[A] rho.asModule).mpr
    apply is_simple_module_of_finrank_eq_one (K := ℂ)
    change Module.finrank ℂ ℂ = 1
    simp
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem irreducibleOfMulCharComplex_apply
    {A Q : Type u} [Group A] [Fintype A] [CommGroup Q]
    (q : A →* Q) (lambda : MulChar Q ℂ) (a : A) :
    irreducibleOfMulCharComplex q lambda a = lambda (q a) := by
  change (mulCharacterRepresentationComplex q lambda).character a = _
  exact mulCharacterRepresentationComplex_character q lambda a

/-- An irreducible character whose translation kernel contains the
commutator subgroup is linear. -/
theorem isLinear_of_commutator_le_translationKernel
    {A : Type u} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hder : _root_.commutator A ≤
      ClassFunction.translationKernel
        (chi : ClassFunction A ℂ)) :
    pTypeIsLinearCharacter chi := by
  let rho := chi.representation.ρ
  have hder' : _root_.commutator A ≤ rho.ker := by
    rw [← internal.pTypeGaloisTranslationKernel_irreducibleCharacter chi]
    exact hder
  let Q := A ⧸ rho.ker
  let sigmaQ : Representation ℂ Q chi.representation :=
    quotientKerRepresentation rho
  let q : A →* Q := QuotientGroup.mk' rho.ker
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder'
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible (sigmaQ.comp q) := by
    change Representation.IsIrreducible rho
    infer_instance
  letI : Representation.IsIrreducible sigmaQ :=
    representation_isIrreducible_of_comp sigmaQ q
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    sigmaQ

/-- Conversely, every linear irreducible character kills the commutator
subgroup. -/
theorem commutator_le_translationKernel_of_isLinear
    {A : Type u} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hlinear : pTypeIsLinearCharacter chi) :
    _root_.commutator A ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ) := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ
  have hfinrank : Module.finrank ℂ chi.representation = 1 := hlinear
  let f : A →* chi.representation ≃ₗ[ℂ] chi.representation :=
    representationLinearEquivHom rho
  have hcomm : _root_.commutator A ≤ f.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro z ⟨x, y, rfl⟩
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement,
      commutatorElement_eq_one_iff_commute, commute_iff_eq]
    apply LinearEquiv.toLinearMap_injective
    exact (endomorphisms_commute_of_finrank_eq_one hfinrank
      (rho x) (rho y)).eq
  rw [internal.pTypeGaloisTranslationKernel_irreducibleCharacter]
  intro a ha
  rw [MonoidHom.mem_ker]
  have haOne := MonoidHom.mem_ker.mp (hcomm ha)
  apply LinearMap.ext
  intro v
  exact DFunLike.congr_fun haOne v

/-- Induction from a character killing the commutator subgroup, together
with the subgroup index, constructs the `PTypeCoreInduced` package. -/
theorem coreInduced_of_commutator_le_kernel
    {A : Type u} [Group A] [Fintype A]
    (HC : Subgroup A) (u : ℕ)
    (hindex : HC.index = u)
    (s : IrreducibleCharacter A ℂ)
    (xi : IrreducibleCharacter HC ℂ)
    (hder : _root_.commutator HC ≤
      ClassFunction.translationKernel
        (xi : ClassFunction HC ℂ))
    (hind : (s : ClassFunction A ℂ) =
      ClassFunction.induce HC (xi : ClassFunction HC ℂ)) :
    PTypeCoreInduced HC u s := by
  have hlinear : pTypeIsLinearCharacter xi :=
    isLinear_of_commutator_le_translationKernel xi hder
  have hxiOne : xi 1 = 1 := by
    rw [IrreducibleCharacter.apply_one_eq_finrank]
    change ((pTypeIrreducibleDegree xi : ℕ) : ℂ) = 1
    rw [hlinear]
    norm_num
  refine ⟨?_, xi, hlinear, hind⟩
  calc
    s 1 = ClassFunction.induce HC
        (xi : ClassFunction HC ℂ) 1 := by rw [hind]
    _ = (HC.index : ℂ) * xi 1 :=
      ClassFunction.induce_one HC _
    _ = (u : ℂ) := by rw [hindex, hxiOne, mul_one]

/-- The index of an inducing subgroup divides the degree of an induced
irreducible character. -/
theorem actionFactor_dvd_degree_of_induced
    {A : Type u} [Group A] [Fintype A]
    (HC : Subgroup A) (u : ℕ)
    (hindex : HC.index = u)
    (s : IrreducibleCharacter A ℂ)
    (xi : IrreducibleCharacter HC ℂ)
    (hind : (s : ClassFunction A ℂ) =
      ClassFunction.induce HC (xi : ClassFunction HC ℂ)) :
    u ∣ pTypeIrreducibleDegree s := by
  have hdegree : pTypeIrreducibleDegree s =
      HC.index * pTypeIrreducibleDegree xi := by
    apply Nat.cast_injective (R := ℂ)
    change (Module.finrank ℂ s.representation : ℂ) =
      ((HC.index * Module.finrank ℂ xi.representation : ℕ) : ℂ)
    rw [← IrreducibleCharacter.apply_one_eq_finrank, hind,
      ClassFunction.induce_one,
      IrreducibleCharacter.apply_one_eq_finrank, Nat.cast_mul]
  refine ⟨pTypeIrreducibleDegree xi, ?_⟩
  simpa only [hindex] using hdegree

/-- A nontrivial finite solvable group has a nonprincipal linear
irreducible character. -/
theorem exists_nontrivial_linear_character_of_solvable
    {A : Type u} [Group A] [Fintype A]
    [IsSolvable A] [Nontrivial A] :
    ∃ chi : IrreducibleCharacter A ℂ,
      pTypeIsLinearCharacter chi ∧
        chi ≠ IrreducibleCharacter.trivial := by
  have hcomm : _root_.commutator A < (⊤ : Subgroup A) :=
    IsSolvable.commutator_lt_top_of_nontrivial A
  let Aab := Abelianization A
  letI : Nontrivial Aab := by
    change Nontrivial (A ⧸ _root_.commutator A)
    exact QuotientGroup.nontrivial_iff.mpr hcomm.ne
  letI : Fintype Aab := Fintype.ofFinite Aab
  obtain ⟨a, ha⟩ := exists_ne (1 : Aab)
  obtain ⟨lambda : MulChar Aab ℂ, hlambda⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity Aab ℂ ha
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (_root_.commutator A) a
  let pi : A →* Aab := Abelianization.of
  have hpix : pi x = a := by
    change QuotientGroup.mk' (_root_.commutator A) x = a
    exact hx
  let chi : IrreducibleCharacter A ℂ :=
    irreducibleOfMulCharComplex pi lambda
  refine ⟨chi, ?_, ?_⟩
  · rw [pTypeIsLinearCharacter, pTypeIrreducibleDegree]
    apply Nat.cast_injective (R := ℂ)
    change (Module.finrank ℂ chi.representation : ℂ) =
      ((1 : ℕ) : ℂ)
    calc
      (Module.finrank ℂ chi.representation : ℂ) = chi 1 :=
        (IrreducibleCharacter.apply_one_eq_finrank chi).symm
      _ = lambda (pi 1) := by
        exact irreducibleOfMulCharComplex_apply pi lambda 1
      _ = ((1 : ℕ) : ℂ) := by simp
  · intro hchi
    have hxchi := congrArg
      (fun psi : IrreducibleCharacter A ℂ ↦ psi x) hchi
    have hlambdaPi : lambda (pi x) = 1 := by
      simpa only [chi, irreducibleOfMulCharComplex_apply,
        IrreducibleCharacter.trivial_apply] using hxchi
    apply hlambda
    rw [← hpix]
    exact hlambdaPi

/-! ## Frobenius character orbits -/

/-- Nonprincipal irreducibles of a Frobenius kernel occur in induction
orbits whose common size is the order of the complement. -/
theorem frobenius_nontrivial_induced_orbit_count
    {A : Type u} [Group A] [Fintype A]
    (K R : Subgroup A)
    (hFrob : IsFrobeniusDecomposition K R) :
    letI : K.Normal := hFrob.kernel_normal
    let X := Finset.univ.erase
      (IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ)
    ∃ hInd : ∀ theta ∈ X,
        IsIrreducibleCharacter A ℂ
          (ClassFunction.induce K (theta : ClassFunction K ℂ)),
      X.card = Nat.card R *
        (Finset.univ.image
          (ClassFunction.induceIrreducibleOn K X hInd)).card := by
  classical
  letI : K.Normal := hFrob.kernel_normal
  letI : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let X := Finset.univ.erase
    (IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ)
  let hInd : ∀ theta ∈ X,
      IsIrreducibleCharacter A ℂ
        (ClassFunction.induce K (theta : ClassFunction K ℂ)) := by
    intro theta htheta
    exact irr_induced_Frobenius_ker hFrob theta
      (Finset.ne_of_mem_erase htheta)
  have hstable : ∀ theta ∈ X, ∀ x : A,
      theta.normalConjugate K x ∈ X := by
    intro theta htheta x
    rw [Finset.mem_erase] at htheta ⊢
    refine ⟨?_, Finset.mem_univ _⟩
    intro hconj
    apply htheta.1
    apply Subtype.ext
    calc
      (theta : ClassFunction K ℂ) =
          ClassFunction.normalConjugate K x⁻¹
            (ClassFunction.normalConjugate K x
              (theta : ClassFunction K ℂ)) :=
        (ClassFunction.normalConjugate_inv_self K x
          (theta : ClassFunction K ℂ)).symm
      _ = ClassFunction.normalConjugate K x⁻¹
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ) :
            ClassFunction K ℂ) := by
        rw [← IrreducibleCharacter.coe_normalConjugate, hconj]
      _ = ((IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ) :
          ClassFunction K ℂ) := by
        ext y
        simp [ClassFunction.normalConjugate_apply]
  refine ⟨hInd, ?_⟩
  have hcount := ClassFunction.card_imset_Ind_irr K X hInd hstable
  rw [hFrob.isComplement.symm.index_eq_card] at hcount
  exact hcount

/-- In a Frobenius group with abelian kernel, the ambient irreducibles that
are nontrivial on the kernel are counted by kernel characters modulo the
complement action.  The reverse inclusion uses Frobenius reciprocity and the
split-universe irreducibility theorem directly, avoiding the universe-bound
Clifford-correspondence wrapper. -/
theorem frobenius_nontrivial_ambient_card
    {A : Type u} [Group A] [Fintype A]
    (K R : Subgroup A) (hFrob : IsFrobeniusDecomposition K R)
    [IsMulCommutative K] :
    letI : K.Normal := hFrob.kernel_normal
    let Y := Finset.univ.filter fun psi : IrreducibleCharacter A ℂ ↦
      ¬ K ≤ ClassFunction.translationKernel
        (psi : ClassFunction A ℂ)
    Nat.card K - 1 = Nat.card R * Y.card := by
  classical
  letI : K.Normal := hFrob.kernel_normal
  letI : Invertible (Nat.card A : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let X := Finset.univ.erase
    (IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ)
  let Y := Finset.univ.filter fun psi : IrreducibleCharacter A ℂ ↦
    ¬ K ≤ ClassFunction.translationKernel
      (psi : ClassFunction A ℂ)
  obtain ⟨hInd, hcount⟩ :=
    frobenius_nontrivial_induced_orbit_count K R hFrob
  let F : {theta // theta ∈ X} → IrreducibleCharacter A ℂ :=
    ClassFunction.induceIrreducibleOn K X hInd
  have himage : Finset.univ.image F = Y := by
    ext psi
    constructor
    · intro hpsi
      obtain ⟨theta, _hthetaUniv, rfl⟩ := Finset.mem_image.mp hpsi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hK
      have hconst : (F theta).IsConstituent
          (ClassFunction.induce K
            (theta.1 : ClassFunction K ℂ)) := by
        unfold IrreducibleCharacter.IsConstituent
        change characterPairing
            (F theta : ClassFunction A ℂ)
            (F theta : ClassFunction A ℂ) ≠ 0
        rw [IrreducibleCharacter.characterPairing_self]
        exact one_ne_zero
      have hKrho : K ≤ (F theta).representation.ρ.ker := by
        rw [← internal.pTypeGaloisTranslationKernel_irreducibleCharacter
          (F theta)]
        exact hK
      let V : FDRep ℂ K :=
        FDRep.of ((F theta).representation.ρ.comp K.subtype)
      have hVchar : ClassFunction.ofRepresentation V.ρ =
          ClassFunction.restrict K (F theta : ClassFunction A ℂ) := by
        calc
          ClassFunction.ofRepresentation V.ρ =
              ClassFunction.restrict K
                (ClassFunction.ofRepresentation
                  (F theta).representation.ρ) := rfl
          _ = ClassFunction.restrict K
              (F theta : ClassFunction A ℂ) := by
            rw [(F theta).ofRepresentation_representation]
      have hthetaRes : theta.1.IsConstituent
          (ClassFunction.restrict K
            (F theta : ClassFunction A ℂ)) :=
        (theta.1.isConstituent_restrict_iff_induce K (F theta)).mpr hconst
      have hthetaV : theta.1.IsConstituent
          (ClassFunction.ofRepresentation V.ρ) := by
        rwa [hVchar]
      have hkerVtheta : V.ρ.ker ≤
          theta.1.representation.ρ.ker :=
        representationKernel_le_constituentKernel V theta.1 hthetaV
      have htopV : (⊤ : Subgroup K) ≤ V.ρ.ker := by
        intro k _hk
        rw [MonoidHom.mem_ker]
        change (F theta).representation.ρ (k : A) = 1
        exact MonoidHom.mem_ker.mp (hKrho k.property)
      have hthetaRho : (⊤ : Subgroup K) ≤
          theta.1.representation.ρ.ker := htopV.trans hkerVtheta
      have hthetaKer : (⊤ : Subgroup K) ≤
          ClassFunction.translationKernel
            (theta.1 : ClassFunction K ℂ) := by
        rw [internal.pTypeGaloisTranslationKernel_irreducibleCharacter]
        exact hthetaRho
      have hmem := (mem_Iirr_ker1 theta.1).mpr
        (Finset.ne_of_mem_erase theta.2)
      rw [mem_Iirr_kerD] at hmem
      exact hmem.2 hthetaKer
    · intro hpsi
      have hpsiData := Finset.mem_filter.mp hpsi
      obtain ⟨theta, htheta⟩ := exists_constituent_restrict K psi
      have hthetaNe :
          theta ≠ (IrreducibleCharacter.trivial :
            IrreducibleCharacter K ℂ) := by
        intro hthetaTriv
        have hthetaRho : (⊤ : Subgroup K) ≤
            theta.representation.ρ.ker := by
          subst theta
          rw [← internal.pTypeGaloisTranslationKernel_irreducibleCharacter]
          intro x _hx
          rw [ClassFunction.mem_translationKernel_iff]
          intro y
          simp
        have hpsiRho : K ≤ psi.representation.ρ.ker :=
          normal_le_kernel_of_constituent_top_kernel
            K psi theta htheta hthetaRho
        apply hpsiData.2
        rw [internal.pTypeGaloisTranslationKernel_irreducibleCharacter]
        exact hpsiRho
      let thetaX : {eta // eta ∈ X} :=
        ⟨theta, Finset.mem_erase.mpr ⟨hthetaNe, Finset.mem_univ _⟩⟩
      have hpsiInd : psi.IsConstituent
          (ClassFunction.induce K (theta : ClassFunction K ℂ)) :=
        (theta.isConstituent_restrict_iff_induce K psi).mp htheta
      have hEq : F thetaX = psi := by
        by_contra hne
        apply hpsiInd
        change characterPairing
            (F thetaX : ClassFunction A ℂ)
            (psi : ClassFunction A ℂ) = 0
        exact IrreducibleCharacter.characterPairing_eq_zero hne
      apply Finset.mem_image.mpr
      exact ⟨thetaX, Finset.mem_univ _, hEq⟩
  calc
    Nat.card K - 1 = X.card :=
      (card_nontrivial_irreducibleCharacters_of_commutative K).symm
    _ = Nat.card R * (Finset.univ.image F).card := hcount
    _ = Nat.card R * Y.card := by rw [himage]

/-! ## Inflation and quotient counting -/

/-- Inflation bijects quotient irreducibles nontrivial on the image of `H`
with the literal kernel layer `Iirr_kerD H N` upstairs. -/
theorem quotient_nontrivial_image_irreducibles_card
    {A : Type u} [Group A] [Fintype A]
    (N H : Subgroup A) [N.Normal] (_hNH : N ≤ H) :
    let q : A →* A ⧸ N := QuotientGroup.mk' N
    let K := H.map q
    let Y := Finset.univ.filter fun psi :
        IrreducibleCharacter (A ⧸ N) ℂ ↦
      ¬ K ≤ ClassFunction.translationKernel
        (psi : ClassFunction (A ⧸ N) ℂ)
    Y.card = (Iirr_kerD (k := ℂ) H N).card := by
  classical
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let K := H.map q
  let Y := Finset.univ.filter fun psi :
      IrreducibleCharacter (A ⧸ N) ℂ ↦
    ¬ K ≤ ClassFunction.translationKernel
      (psi : ClassFunction (A ⧸ N) ℂ)
  let inflate : IrreducibleCharacter (A ⧸ N) ℂ →
      IrreducibleCharacter A ℂ :=
    internal.pTypeGaloisInflateIrreducible q hq
  have hinflateCF (psi : IrreducibleCharacter (A ⧸ N) ℂ) :
      (inflate psi : ClassFunction A ℂ) =
        ClassFunction.comap q
          (psi : ClassFunction (A ⧸ N) ℂ) := by
    ext a
    exact internal.pTypeGaloisInflateIrreducible_apply q hq psi a
  have hinjective : Function.Injective inflate := by
    intro psi eta hpsi
    apply IrreducibleCharacter.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    have hvalue := congrArg
      (fun chi : IrreducibleCharacter A ℂ ↦ chi x) hpsi
    simpa only [inflate,
      internal.pTypeGaloisInflateIrreducible_apply] using hvalue
  have himage : Finset.image inflate Y = Iirr_kerD (k := ℂ) H N := by
    ext chi
    constructor
    · intro hchi
      obtain ⟨psi, hpsiY, rfl⟩ := Finset.mem_image.mp hchi
      have hpsiData := Finset.mem_filter.mp hpsiY
      rw [mem_Iirr_kerD]
      constructor
      · rw [hinflateCF]
        have hNker : N ≤ q.ker := by
          rw [QuotientGroup.ker_mk']
        exact hNker.trans
          (ClassFunction.ker_le_translationKernel_comap q _)
      · intro hH
        apply hpsiData.2
        exact (internal.pTypeTranslationKernel_comap_surjective_iff
          q hq H (psi : ClassFunction (A ⧸ N) ℂ)).mp (by
            simpa only [hinflateCF] using hH)
    · intro hchi
      have hchiData := mem_Iirr_kerD.mp hchi
      have hker : q.ker ≤ ClassFunction.translationKernel
          (chi : ClassFunction A ℂ) := by
        rw [QuotientGroup.ker_mk']
        exact hchiData.1
      let psi : IrreducibleCharacter (A ⧸ N) ℂ :=
        internal.pTypeGaloisDescendIrreducibleSurjective q hq chi hker
      have hinflate : inflate psi = chi :=
        internal.pTypeGalois_inflate_descendIrreducibleSurjective
          q hq chi hker
      apply Finset.mem_image.mpr
      refine ⟨psi, ?_, hinflate⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hK
      apply hchiData.2
      have hcomap : ClassFunction.comap q
          (psi : ClassFunction (A ⧸ N) ℂ) =
          (chi : ClassFunction A ℂ) :=
        internal.pTypeGalois_comap_descendIrreducibleSurjective
          q hq chi hker
      rw [← hcomap]
      exact (internal.pTypeTranslationKernel_comap_surjective_iff
        q hq H (psi : ClassFunction (A ⧸ N) ℂ)).mpr hK
  calc
    Y.card = (Finset.image inflate Y).card :=
      (Finset.card_image_iff.mpr
        (Set.injOn_of_injective hinjective)).symm
    _ = (Iirr_kerD (k := ℂ) H N).card := by rw [himage]

/-! ## Numerical consequences -/

/-- Cancel the nonzero factor `p - 1` in the final Frobenius orbit identity. -/
theorem actionFactor_eq_geometric_quotient
    {p q u : ℕ} (hp : p.Prime)
    (hcount : p ^ q - 1 = (p - 1) * u) :
    u = (p ^ q - 1) / (p - 1) := by
  have hmul : (p - 1) * u =
      (p - 1) * Submission.OddOrder.BG.AppendixC.nU p q := by
    calc
      (p - 1) * u = p ^ q - 1 := hcount.symm
      _ = Submission.OddOrder.BG.AppendixC.nU p q * (p - 1) :=
        (Submission.OddOrder.BG.AppendixC.nU_mul_sub_one
          p q hp.one_lt.le).symm
      _ = (p - 1) * Submission.OddOrder.BG.AppendixC.nU p q := by
        rw [mul_comm]
  calc
    u = Submission.OddOrder.BG.AppendixC.nU p q :=
      Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.one_lt) hmul
    _ = (p ^ q - 1) / (p - 1) :=
      Submission.OddOrder.BG.AppendixC.nU_eq_div_of_prime hp

/-! ## Reducible-layer consequences -/

/-- A reducible layer of cardinality `p - 1` is nonempty for prime `p`. -/
theorem reducibleLayer_nonempty_of_card_eq_prime_pred
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H H₀ : Subgroup HU) {p : ℕ}
    (hp : p.Prime)
    (hcard : (pTypeReducibleLayer HU H H₀).card = p - 1) :
    (pTypeReducibleLayer HU H H₀).Nonempty := by
  apply Finset.card_pos.mp
  rw [hcard]
  exact Nat.sub_pos_of_lt hp.one_lt

/-- Every reducible member of the `H₀` layer is a nontrivial prime-TI
reduced column. -/
theorem reducibleLayer_subset_primeTIRed
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (H₀ : Subgroup (pTypeHUInMaximal M (derivedWithin M))) :
    let pti := FT_primeTI_hyp defW MtypeP
    let iso := pti.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
    pTypeReducibleLayer
        (pTypeHUInMaximal M (derivedWithin M))
        (pTypeHInDerived M (derivedWithin M) (Fitting_core M)) H₀ ⊆
      Finset.image (pti.primeTIRed iso)
        (Finset.univ.erase
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) := by
  classical
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let pti := FT_primeTI_hyp defW MtypeP
  let iso := pti.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
  change pTypeReducibleLayer HU H H₀ ⊆
    Finset.image (pti.primeTIRed iso)
      (Finset.univ.erase
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
  intro zeta hzeta
  rw [pTypeReducibleLayer, Finset.mem_filter] at hzeta
  obtain ⟨hzeta, hred⟩ := hzeta
  obtain ⟨theta, htheta, hzeta⟩ := seqIndP.mp hzeta
  subst zeta
  rcases pti.prTIres_irr_cases iso theta with ⟨j, hj⟩ | ⟨hirr, _⟩
  · have hj_ne :
        j ≠ (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₂ ℂ) := by
      intro hj0
      subst j
      apply (mem_Iirr_kerD.mp htheta).2
      intro x hx
      rw [hj, pti.prTIres0 iso,
        ClassFunction.mem_translationKernel_iff]
      intro y
      simp
    refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
    · exact Finset.mem_erase.mpr ⟨hj_ne, Finset.mem_univ j⟩
    · rw [← pti.cfInd_prTIres iso j, ← hj]
  · exact (hred hirr).elim

end PTypeGaloisCharacterArithmeticInternal

end

end Submission.OddOrder.PF
