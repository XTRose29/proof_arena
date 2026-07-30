import Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport

/-!
# Natural-number character multiplicities

The coefficients in Peterfalvi's constituent sums are nonnegative integer
multiplicities.  This file records them as dimensions of equivariant Hom
spaces and identifies their casts with the normalized character pairing.
The natural-number form is needed for the positivity argument in the
Clifford correspondence of 1.7(a).
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u

namespace FDRep

variable {G k : Type u} [Group G] [Field k] [Fintype G] [CharZero k]

/-- The pairing of two realized characters is the dimension of the
equivariant Hom space in the indicated direction. -/
theorem characterPairing_ofRepresentation_eq_finrank_hom
    (V W : FDRep k G) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank k (W ⟶ V) : k) := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hhom := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcharV (g : G) :
      V.character g = _root_.Representation.character V.ρ g := rfl
  have hcharW (g : G) :
      W.character g = _root_.Representation.character W.ρ g := rfl
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
    invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
    hcharV, hcharW] using hhom

end FDRep

namespace IrreducibleCharacter

variable {G k : Type u} [Group G] [Field k] [Fintype G] [CharZero k]

/-- Multiplicity of an irreducible character in a realized character. -/
def multiplicity (chi : IrreducibleCharacter G k) (V : FDRep k G) : ℕ :=
  Module.finrank k (chi.representation ⟶ V)

/-- The cast of `multiplicity` is the character pairing used by the source. -/
theorem characterPairing_ofRepresentation_eq_multiplicity
    (chi : IrreducibleCharacter G k) (V : FDRep k G) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (chi : ClassFunction G k) = (chi.multiplicity V : k) := by
  rw [← chi.ofRepresentation_representation]
  exact FDRep.characterPairing_ofRepresentation_eq_finrank_hom V chi.representation

/-- Being a constituent is equivalent to having positive natural-number
multiplicity. -/
theorem isConstituent_ofRepresentation_iff_multiplicity_pos
    (chi : IrreducibleCharacter G k) (V : FDRep k G) :
    chi.IsConstituent (ClassFunction.ofRepresentation V.ρ) ↔
      0 < chi.multiplicity V := by
  unfold IsConstituent
  rw [characterPairing_ofRepresentation_eq_multiplicity]
  exact ⟨fun h ↦ Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp h),
    fun h ↦ Nat.cast_ne_zero.mpr h.ne'⟩

end IrreducibleCharacter

end

end Submission.OddOrder.PF
