import Mathlib.RepresentationTheory.Character

/-!
Class functions and their character pairing.

This is the first piece of the character-theory substrate used by the
Peterfalvi sections.  A class function is represented as the submodule of all
functions that are constant under conjugation.  This choice makes the usual
additive and scalar operations available without introducing a parallel
algebraic hierarchy.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v w w'

/-- The `R`-valued functions on `G` that are constant under conjugation. -/
def ClassFunction (G : Type u) (R : Type v) [Group G] [Ring R] :
    Submodule R (G → R) where
  carrier := {f | ∀ x g, f (x * g * x⁻¹) = f g}
  zero_mem' := by
    intro x g
    rfl
  add_mem' := by
    intro f g hf hg x y
    change f (x * y * x⁻¹) + g (x * y * x⁻¹) = f y + g y
    rw [hf x y, hg x y]
  smul_mem' := by
    intro a f hf x g
    change a • f (x * g * x⁻¹) = a • f g
    rw [hf x g]

namespace ClassFunction

variable {G : Type u} {R : Type v} [Group G] [Ring R]

/-- Coerce a bundled class function to its underlying function. -/
instance : CoeFun (ClassFunction G R) fun _ ↦ G → R where
  coe f := f.1

/-- A class function is unchanged by conjugation. -/
theorem conj_apply (f : ClassFunction G R) (x g : G) :
    f (x * g * x⁻¹) = f g :=
  f.property x g

/-- Two class functions are equal when they agree pointwise. -/
@[ext]
theorem ext {f g : ClassFunction G R} (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  exact funext h

@[simp]
theorem zero_apply (x : G) : (0 : ClassFunction G R) x = 0 :=
  rfl

@[simp]
theorem add_apply (f g : ClassFunction G R) (x : G) : (f + g) x = f x + g x :=
  rfl

@[simp]
theorem smul_apply (a : R) (f : ClassFunction G R) (x : G) : (a • f) x = a • f x :=
  rfl

@[simp]
theorem neg_apply (f : ClassFunction G R) (x : G) : (-f) x = -f x :=
  rfl

@[simp]
theorem sub_apply (f g : ClassFunction G R) (x : G) : (f - g) x = f x - g x :=
  rfl

section Representation

variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The character of a finite-dimensional representation, bundled as a class
function. -/
def ofRepresentation (rho : _root_.Representation k G V) : ClassFunction G k :=
  ⟨rho.character, fun x g ↦ rho.char_conj g x⟩

omit [FiniteDimensional k V] in
@[simp]
theorem ofRepresentation_apply (rho : _root_.Representation k G V) (g : G) :
    ofRepresentation rho g = rho.character g :=
  rfl

end Representation

section Restriction

/-- Restriction of class functions from a group to a subgroup. -/
def restrict (H : Subgroup G) : ClassFunction G R →ₗ[R] ClassFunction H R where
  toFun f :=
    ⟨fun h ↦ f h.1, fun x h ↦ by
      change f ((x : G) * (h : G) * (x : G)⁻¹) = f h
      exact conj_apply f (x : G) (h : G)⟩
  map_add' f g := by
    ext h
    rfl
  map_smul' a f := by
    ext h
    rfl

@[simp]
theorem restrict_apply (H : Subgroup G) (f : ClassFunction G R) (h : H) :
    restrict H f h = f h :=
  rfl

variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- Restricting a representation character is the character of the
representation obtained by composing with the subgroup inclusion. -/
@[simp]
theorem restrict_ofRepresentation (H : Subgroup G)
    (rho : _root_.Representation k G V) :
    restrict H (ofRepresentation rho) =
      ofRepresentation
        (rho.comp H.subtype : _root_.Representation k H V) := by
  ext h
  rfl

omit [FiniteDimensional k V] in
/-- Pointwise form of `restrict_ofRepresentation`. -/
@[simp]
theorem restrict_ofRepresentation_apply (H : Subgroup G)
    (rho : _root_.Representation k G V) (h : H) :
    restrict H (ofRepresentation rho) h =
      _root_.Representation.character
        (rho.comp H.subtype : _root_.Representation k H V) h :=
  rfl

end Restriction

end ClassFunction

section Pairing

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- The normalized character pairing.  The inverse in the second argument
matches Mathlib's convention for character orthogonality. -/
def characterPairing (f g : ClassFunction G k) : k :=
  (Nat.card G : k)⁻¹ * ∑ x : G, f x * g x⁻¹

@[simp]
theorem characterPairing_zero_left (g : ClassFunction G k) :
    characterPairing 0 g = 0 := by
  simp [characterPairing]

@[simp]
theorem characterPairing_zero_right (f : ClassFunction G k) :
    characterPairing f 0 = 0 := by
  simp [characterPairing]

@[simp]
theorem characterPairing_add_left (f₁ f₂ g : ClassFunction G k) :
    characterPairing (f₁ + f₂) g =
      characterPairing f₁ g + characterPairing f₂ g := by
  simp [characterPairing, add_mul, Finset.sum_add_distrib, mul_add]

@[simp]
theorem characterPairing_add_right (f g₁ g₂ : ClassFunction G k) :
    characterPairing f (g₁ + g₂) =
      characterPairing f g₁ + characterPairing f g₂ := by
  simp [characterPairing, mul_add, Finset.sum_add_distrib]

@[simp]
theorem characterPairing_smul_left (a : k) (f g : ClassFunction G k) :
    characterPairing (a • f) g = a * characterPairing f g := by
  simp [characterPairing, Finset.mul_sum, mul_assoc, mul_left_comm]

@[simp]
theorem characterPairing_smul_right (a : k) (f g : ClassFunction G k) :
    characterPairing f (a • g) = a * characterPairing f g := by
  simp [characterPairing, Finset.mul_sum, mul_left_comm]

variable [IsAlgClosed k] [Invertible (Nat.card G : k)]
variable {V : Type w} {W : Type w'}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

open scoped Classical in
/-- Character orthogonality, expressed using bundled class functions. -/
theorem characterPairing_ofRepresentation_of_isIrreducible
    (rho : _root_.Representation k G V) (sigma : _root_.Representation k G W)
    [rho.IsIrreducible] [sigma.IsIrreducible] :
    characterPairing (ClassFunction.ofRepresentation rho)
        (ClassFunction.ofRepresentation sigma) =
      if Nonempty (_root_.Representation.Equiv sigma rho) then 1 else 0 := by
  classical
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply] using
    rho.char_orthonormal sigma

end Pairing

end

end Submission.OddOrder.PF
