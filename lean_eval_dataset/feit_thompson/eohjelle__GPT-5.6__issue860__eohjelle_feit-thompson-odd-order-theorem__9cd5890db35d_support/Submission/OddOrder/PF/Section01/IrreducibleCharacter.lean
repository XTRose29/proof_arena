import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RepresentationTheory.FinGroupCharZero
import Submission.OddOrder.PF.Section01.ClassFunction

/-!
Irreducible characters as character functions, rather than as equivalence
classes of representations.

The source development indexes virtual characters by `Iirr G`.  For the Lean
port it is more useful to make equality of indices mean equality of character
functions.  A witness that the function is the character of a simple
finite-dimensional representation is retained in the predicate below.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable (G : Type u) (k : Type v) [Group G] [Field k]

/-- A class function is irreducible when it is realized by a simple bundled
finite-dimensional representation. -/
def IsIrreducibleCharacter (chi : ClassFunction G k) : Prop :=
  ∃ V : FDRep k G,
    CategoryTheory.Simple V ∧ ClassFunction.ofRepresentation V.ρ = chi

/-- Irreducible characters, identified extensionally as class functions. -/
def IrreducibleCharacter :=
  {chi : ClassFunction G k // IsIrreducibleCharacter G k chi}

namespace IrreducibleCharacter

variable {G k}

/-- Forget that an irreducible character is irreducible. -/
instance : Coe (IrreducibleCharacter G k) (ClassFunction G k) :=
  ⟨Subtype.val⟩

/-- Evaluate an irreducible character. -/
instance : CoeFun (IrreducibleCharacter G k) fun _ ↦ G → k where
  coe chi := chi.1

@[ext]
theorem ext {chi psi : IrreducibleCharacter G k}
    (h : ∀ g, chi g = psi g) : chi = psi := by
  apply Subtype.ext
  exact ClassFunction.ext h

/-- The irreducible character attached to a simple bundled representation. -/
def ofFDRep (V : FDRep k G) [CategoryTheory.Simple V] :
    IrreducibleCharacter G k :=
  ⟨ClassFunction.ofRepresentation V.ρ, V, inferInstance, rfl⟩

@[simp]
theorem ofFDRep_apply (V : FDRep k G) [CategoryTheory.Simple V] (g : G) :
    ofFDRep V g = V.character g :=
  rfl

/-- A chosen representation realizing an irreducible character.  Statements
about characters are independent of this choice because the character itself
is the data of `IrreducibleCharacter`. -/
def representation (chi : IrreducibleCharacter G k) : FDRep k G :=
  chi.property.choose

/-- The chosen realization is simple. -/
theorem representation_simple (chi : IrreducibleCharacter G k) :
    CategoryTheory.Simple chi.representation :=
  chi.property.choose_spec.1

/-- The chosen realization has the specified character. -/
theorem ofRepresentation_representation (chi : IrreducibleCharacter G k) :
    ClassFunction.ofRepresentation chi.representation.ρ = (chi : ClassFunction G k) :=
  chi.property.choose_spec.2

@[simp]
theorem representation_character (chi : IrreducibleCharacter G k) (g : G) :
    chi.representation.character g = chi g := by
  have h := congrArg (fun f : ClassFunction G k ↦ f g)
    chi.ofRepresentation_representation
  change _root_.Representation.character chi.representation.ρ g = chi g
  exact h

section Orthogonality

variable [Fintype G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

open scoped Classical in
/-- Orthogonality for irreducible characters, with equality expressed as
equality of the character functions themselves. -/
theorem characterPairing_eq_ite (chi psi : IrreducibleCharacter G k) :
    characterPairing (chi : ClassFunction G k) (psi : ClassFunction G k) =
      if chi = psi then 1 else 0 := by
  let V := chi.representation
  let W := psi.representation
  letI : CategoryTheory.Simple V := chi.representation_simple
  letI : CategoryTheory.Simple W := psi.representation_simple
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have horth := FDRep.char_orthonormal V W
  have hcharV (g : G) :
      V.character g = _root_.Representation.character V.ρ g := rfl
  have hcharW (g : G) :
      W.character g = _root_.Representation.character W.ρ g := rfl
  have horth' :
      (Nat.card G : k)⁻¹ *
          ∑ g : G, _root_.Representation.character V.ρ g *
            _root_.Representation.character W.ρ g⁻¹ =
        if Nonempty (V ≅ W) then 1 else 0 := by
    simpa only [invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
      hcharV, hcharW] using horth
  have hrealV : ClassFunction.ofRepresentation V.ρ = (chi : ClassFunction G k) :=
    chi.ofRepresentation_representation
  have hrealW : ClassFunction.ofRepresentation W.ρ = (psi : ClassFunction G k) :=
    psi.ofRepresentation_representation
  rw [← hrealV, ← hrealW]
  simp only [characterPairing, ClassFunction.ofRepresentation_apply]
  rw [horth']
  by_cases hchi : chi = psi
  · rw [if_pos hchi]
    subst psi
    simp only [V, W]
    rw [if_pos]
    exact ⟨CategoryTheory.Iso.refl _⟩
  · rw [if_neg hchi, if_neg]
    rintro ⟨e⟩
    apply hchi
    ext g
    have heq := congrFun (FDRep.char_iso e) g
    simpa only [V, W, representation_character] using heq

@[simp]
theorem characterPairing_self (chi : IrreducibleCharacter G k) :
    characterPairing (chi : ClassFunction G k) (chi : ClassFunction G k) = 1 := by
  rw [characterPairing_eq_ite, if_pos rfl]

theorem characterPairing_eq_zero {chi psi : IrreducibleCharacter G k}
    (hne : chi ≠ psi) :
    characterPairing (chi : ClassFunction G k) (psi : ClassFunction G k) = 0 := by
  rw [characterPairing_eq_ite, if_neg hne]

/-- Pairing with a fixed class function is linear in the second argument. -/
def pairingLeft (f : ClassFunction G k) : ClassFunction G k →ₗ[k] k where
  toFun g := characterPairing f g
  map_add' g h := characterPairing_add_right f g h
  map_smul' a g := by
    simp [characterPairing_smul_right]

/-- Distinct irreducible characters are linearly independent in the space of
class functions. -/
theorem linearIndependent :
    LinearIndependent k
      (fun chi : IrreducibleCharacter G k ↦ (chi : ClassFunction G k)) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one
    (fun chi : IrreducibleCharacter G k ↦ (chi : ClassFunction G k))
    (fun chi ↦ pairingLeft (chi : ClassFunction G k))
  · intro chi psi hne
    exact characterPairing_eq_zero hne
  · exact characterPairing_self

/-- There are only finitely many irreducible characters of a finite group.
This is obtained directly from orthogonality and finite-dimensionality of the
ambient class-function space. -/
instance finite : Finite (IrreducibleCharacter G k) :=
  linearIndependent.finite

/-- A concrete finite indexing type for irreducible characters. -/
instance fintype : Fintype (IrreducibleCharacter G k) :=
  Fintype.ofFinite _

end Orthogonality

end IrreducibleCharacter

end

end Submission.OddOrder.PF
