import Submission.OddOrder.PF.Section01.CharacterCompleteness
import Submission.OddOrder.PF.Section01.CharacterMultiplicity
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence
import Submission.OddOrder.PF.Section01.VirtualCharacter

/-!
# Characters of finite-dimensional representations as virtual characters

The ordinary character of a finite-dimensional representation has
nonnegative integral coefficients in the irreducible-character basis.  This
file packages those natural multiplicities as a `VirtualCharacter` and
records that realization recovers the original character.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace VirtualCharacter

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- The virtual character whose coefficient at an irreducible character is
its multiplicity in `V`. -/
noncomputable def ofFDRep (V : FDRep k G) : VirtualCharacter G k := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact Finsupp.equivFunOnFinite.symm
    (fun chi : IrreducibleCharacter G k ↦ (chi.multiplicity V : ℤ))

/-- Realizing `ofFDRep V` gives the ordinary character of `V`. -/
theorem realize_ofFDRep (V : FDRep k G) :
    realize (ofFDRep V) = ClassFunction.ofRepresentation V.ρ := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [ofFDRep, Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
  simp only [realize_single, Int.cast_natCast]
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.ofRepresentation V.ρ)]
  rw [irreducibleCharacterExpansion]
  apply Finset.sum_congr rfl
  intro chi _
  rw [characterPairing_comm,
    IrreducibleCharacter.characterPairing_ofRepresentation_eq_multiplicity]

end VirtualCharacter

end

end Submission.OddOrder.PF
