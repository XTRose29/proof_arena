import Submission.OddOrder.PF.Section01.HallCentralInertiaAssembly

/-!
# Constituents of nonzero realized characters

This file packages two elementary consequences of character completeness:
a nonzero finite-dimensional representation has an irreducible constituent,
and the degree of such a constituent is bounded by the dimension of the
realizing representation.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical
open CategoryTheory

universe u v

namespace IrreducibleCharacter

variable {G : Type u} {k : Type v} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- The degree of an irreducible character is the dimension of its chosen
realizing representation. -/
@[simp]
theorem apply_one_eq_finrank (chi : IrreducibleCharacter G k) :
    chi 1 = (Module.finrank k chi.representation : k) := by
  rw [← chi.representation_character, FDRep.char_one]

end IrreducibleCharacter

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Every nonzero finite-dimensional representation of a finite group has an
irreducible character constituent. -/
theorem exists_irreducible_constituent_of_nontrivial
    (V : FDRep k G) [Nontrivial V] :
    ∃ chi : IrreducibleCharacter G k,
      chi.IsConstituent (ofRepresentation V.ρ) := by
  let F : ClassFunction G k := ofRepresentation V.ρ
  have hFne : F ≠ 0 := by
    intro hzero
    have hone := congrArg (fun f : ClassFunction G k ↦ f 1) hzero
    change V.character 1 = 0 at hone
    rw [FDRep.char_one] at hone
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') hone
  by_contra hnone
  push Not at hnone
  apply hFne
  rw [← irreducibleCharacterExpansion_eq F]
  rw [irreducibleCharacterExpansion]
  apply Finset.sum_eq_zero
  intro chi _
  have hpairRight :
      characterPairing F (chi : ClassFunction G k) = 0 := by
    exact not_ne_iff.mp (hnone chi)
  have hpairLeft :
      characterPairing (chi : ClassFunction G k) F = 0 :=
    (characterPairing_comm (chi : ClassFunction G k) F).trans hpairRight
  simp only [hpairLeft, zero_smul]

end ClassFunction

namespace FDRep

variable {G : Type u} {k : Type v} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Universe-polymorphic form of the nonzero-intertwiner construction used
below.  The upstream compatibility lemma currently identifies the universes
of the group and coefficient field. -/
private theorem exists_hom_ne_zero_of_isConstituent_general
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

/-- An irreducible constituent embeds into a realizing representation, so
its degree is at most the dimension of that representation. -/
theorem finrank_irreducible_le_of_isConstituent
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent (ClassFunction.ofRepresentation V.ρ)) :
    Module.finrank k chi.representation ≤ Module.finrank k V := by
  obtain ⟨f, hf⟩ :=
    exists_hom_ne_zero_of_isConstituent_general V chi hchi
  letI : Simple chi.representation := chi.representation_simple
  letI : Mono f := mono_of_nonzero_from_simple hf
  let fR := (forget₂ (FDRep k G) (Rep k G)).map f
  have hfR : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp (by infer_instance)
  let fLinear : chi.representation →ₗ[k] V := f.hom.hom.hom
  have hfLinear : Function.Injective fLinear := by
    exact hfR
  exact fLinear.finrank_le_finrank_of_injective hfLinear

end FDRep

end

end Submission.OddOrder.PF
