import Submission.OddOrder.PF.Section01.CharacterCompleteness

/-!
The irreducible-character basis of the class functions.

This packages the completeness and first-orthogonality theorems from
Peterfalvi Section 1 into the basis API needed in Section 3.  Its coordinate
functionals are exactly the character pairings.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G] [Field k]
variable [IsAlgClosed k] [CharZero k]

local instance irreducibleCharacterBasisInvertibleCard :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- Ordinary irreducible characters, regarded as class functions, form a
basis of all class functions. -/
def irreducibleCharacterBasis :
    Module.Basis (IrreducibleCharacter G k) k (ClassFunction G k) :=
  Module.Basis.mk IrreducibleCharacter.linearIndependent (by
    rw [irreducibleCharacter_span_eq_top])

@[simp]
theorem irreducibleCharacterBasis_apply (chi : IrreducibleCharacter G k) :
    irreducibleCharacterBasis (G := G) (k := k) chi =
      (chi : ClassFunction G k) := by
  simp [irreducibleCharacterBasis]

/-- The coordinate of a class function at an irreducible character is its
pairing with that irreducible character. -/
@[simp]
theorem irreducibleCharacterBasis_repr_apply
    (f : ClassFunction G k) (chi : IrreducibleCharacter G k) :
    (irreducibleCharacterBasis (G := G) (k := k)).repr f chi =
      characterPairing (chi : ClassFunction G k) f := by
  classical
  let b := irreducibleCharacterBasis (G := G) (k := k)
  refine b.repr_apply_eq
    (fun g psi ↦ characterPairing (psi : ClassFunction G k) g) ?_ ?_ ?_ f chi
  · intro g h
    funext psi
    exact characterPairing_add_right (psi : ClassFunction G k) g h
  · intro c g
    funext psi
    simp [Pi.smul_apply]
  · intro psi
    funext chi'
    simp [b, IrreducibleCharacter.characterPairing_eq_ite,
      Finsupp.single_apply, eq_comm]

/-- Finite irreducible-character expansion of an arbitrary class function.
This is the basis form of Coq's `cfun_irr_sum`. -/
theorem sum_irreducibleCharacterBasis_eq (f : ClassFunction G k) :
    (∑ chi : IrreducibleCharacter G k,
        characterPairing (chi : ClassFunction G k) f •
          (chi : ClassFunction G k)) = f := by
  simpa only [irreducibleCharacterBasis_repr_apply,
    irreducibleCharacterBasis_apply] using
    (irreducibleCharacterBasis (G := G) (k := k)).sum_repr f

end ClassFunction

end

end Submission.OddOrder.PF
