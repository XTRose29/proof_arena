import Submission.OddOrder.PF.Section01.GeneralInducedCharacterCompatibility
import Submission.OddOrder.PF.Section01.VirtualCharacterOfFDRep

/-!
# Induction of virtual characters

Induction from an arbitrary subgroup takes ordinary characters to ordinary
characters, hence extends additively to the free integral lattice of virtual
characters.  We construct that lattice map by inducing a representation
realizing each irreducible basis character.  The realization theorem below
identifies this construction with the existing explicit class-function
induction formula.

No compatibility with the character pairing (or its star variants) is used
or asserted here.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

namespace VirtualCharacter

variable {G k : Type u} [Group G] [Fintype G] [Field k]
  [IsAlgClosed k] [CharZero k]

/-- The virtual character of `G` obtained by inducing a representation
realizing the irreducible character `chi` of `H`. -/
def induceIrreducible (H : Subgroup G)
    (chi : IrreducibleCharacter H k) : VirtualCharacter G k :=
  ofFDRep (FDRep.induceFromSubgroup H chi.representation)

/-- Realization of the induced irreducible basis vector is ordinary
class-function induction. -/
theorem realize_induceIrreducible (H : Subgroup G)
    (chi : IrreducibleCharacter H k) :
    realize (induceIrreducible H chi) =
      ClassFunction.induce H (chi : ClassFunction H k) := by
  rw [induceIrreducible, realize_ofFDRep,
    ClassFunction.ofRepresentation_induceFromSubgroup_general,
    chi.ofRepresentation_representation]

/-- Integer multiples of one induced irreducible basis character. -/
private def induceIrreducibleHom (H : Subgroup G)
    (chi : IrreducibleCharacter H k) : ℤ →+ VirtualCharacter G k where
  toFun z := z • induceIrreducible H chi
  map_zero' := zero_zsmul _
  map_add' := fun m n ↦ add_zsmul (induceIrreducible H chi) m n

/-- Induction on the integral lattice of virtual characters, from an
arbitrary subgroup. -/
def induce (H : Subgroup G) :
    VirtualCharacter H k →+ VirtualCharacter G k :=
  (Finsupp.liftAddHom
    (α := IrreducibleCharacter H k)
    (M := ℤ) (N := VirtualCharacter G k))
      (fun chi ↦ induceIrreducibleHom H chi)

@[simp]
theorem induce_single (H : Subgroup G)
    (chi : IrreducibleCharacter H k) (z : ℤ) :
    induce H (Finsupp.single chi z) = z • induceIrreducible H chi := by
  simp [induce, induceIrreducibleHom]

@[simp]
theorem realize_induce_single (H : Subgroup G)
    (chi : IrreducibleCharacter H k) (z : ℤ) :
    realize (induce H (Finsupp.single chi z)) =
      ClassFunction.induce H
        (realize (Finsupp.single chi z : VirtualCharacter H k)) := by
  rw [induce_single, map_zsmul, realize_single,
    realize_induceIrreducible, ← Int.cast_smul_eq_zsmul k,
    map_smul]

/-- Induction of virtual characters commutes with realization as class
functions.  In particular, arbitrary-subgroup class-function induction
preserves virtual characters. -/
theorem realize_induce (H : Subgroup G) (f : VirtualCharacter H k) :
    realize (induce H f) = ClassFunction.induce H (realize f) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add chi z f hchi hz ih =>
      calc
        realize (induce H (Finsupp.single chi z + f)) =
            realize (induce H (Finsupp.single chi z)) +
              realize (induce H f) := by rw [map_add, realize_add]
        _ = ClassFunction.induce H
              (realize (Finsupp.single chi z : VirtualCharacter H k)) +
            ClassFunction.induce H (realize f) := by
              rw [realize_induce_single, ih]
        _ = ClassFunction.induce H
              (realize (Finsupp.single chi z : VirtualCharacter H k) +
                realize f) := by rw [map_add]
        _ = ClassFunction.induce H
              (realize (Finsupp.single chi z + f)) := by
                rw [realize_add]

/-- Existential form of `realize_induce`, convenient when only membership in
the virtual-character lattice matters. -/
theorem exists_realize_eq_induce (H : Subgroup G)
    (f : VirtualCharacter H k) :
    ∃ F : VirtualCharacter G k,
      realize F = ClassFunction.induce H (realize f) :=
  ⟨induce H f, realize_induce H f⟩

end VirtualCharacter

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G] [Field k]
  [IsAlgClosed k] [CharZero k]

/-- Class-function-oriented form of virtual-character induction. -/
theorem induce_realize (H : Subgroup G) (f : VirtualCharacter H k) :
    ClassFunction.induce H (VirtualCharacter.realize f) =
      VirtualCharacter.realize (VirtualCharacter.induce H f) :=
  (VirtualCharacter.realize_induce H f).symm

end ClassFunction

end

end Submission.OddOrder.PF
