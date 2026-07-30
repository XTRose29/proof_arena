import Submission.OddOrder.PF.Section01.GeneralInducedCharacterCompatibility

/-!
# Transport of irreducible characters across group equivalences

The inertia subgroup construction in Peterfalvi 1.7 replaces `H` by its
canonical copy `H.subgroupOf T`.  This file shows that pullback across a
group equivalence preserves irreducibility and packages the resulting
equivalence of irreducible-character indexing types.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace IrreducibleCharacter

variable {A B k : Type u} [Group A] [Group B] [Field k]
  [Fintype A] [Fintype B] [IsAlgClosed k] [CharZero k]

private theorem compMulEquivFDRep_simple
    (e : A ≃* B) (V : FDRep k B) [CategoryTheory.Simple V] :
    CategoryTheory.Simple (FDRep.of (V.ρ.comp e.toMonoidHom)) := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hV := (FDRep.simple_iff_char_is_norm_one V).mp (by infer_instance)
  calc
    (∑ a : A,
        (FDRep.of (V.ρ.comp e.toMonoidHom)).character a *
          (FDRep.of (V.ρ.comp e.toMonoidHom)).character a⁻¹) =
        ∑ b : B, V.character b * V.character b⁻¹ := by
      apply Fintype.sum_equiv e.toEquiv
      intro a
      change V.character (e a) * V.character (e a⁻¹) =
        V.character (e a) * V.character (e a)⁻¹
      rw [map_inv]
    _ = (Nat.card B : k) := hV
    _ = (Nat.card A : k) := by
      exact_mod_cast (Nat.card_congr e.toEquiv).symm

/-- Pull an irreducible character back along a group equivalence. -/
def comapMulEquiv (e : A ≃* B) (chi : IrreducibleCharacter B k) :
    IrreducibleCharacter A k := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : CategoryTheory.Simple
      (FDRep.of (chi.representation.ρ.comp e.toMonoidHom)) :=
    compMulEquivFDRep_simple e chi.representation
  exact ofFDRep (FDRep.of (chi.representation.ρ.comp e.toMonoidHom))

@[simp]
theorem comapMulEquiv_apply (e : A ≃* B)
    (chi : IrreducibleCharacter B k) (a : A) :
    comapMulEquiv e chi a = chi (e a) := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  change chi.representation.character (e a) = chi (e a)
  exact representation_character chi (e a)

@[simp]
theorem comapMulEquiv_symm (e : A ≃* B)
    (chi : IrreducibleCharacter B k) :
    comapMulEquiv e.symm (comapMulEquiv e chi) = chi := by
  ext b
  simp

/-- A group equivalence gives an equivalence of irreducible-character
indexing types by pullback. -/
def equivOfMulEquiv (e : A ≃* B) :
    IrreducibleCharacter B k ≃ IrreducibleCharacter A k where
  toFun := comapMulEquiv e
  invFun := comapMulEquiv e.symm
  left_inv := comapMulEquiv_symm e
  right_inv := comapMulEquiv_symm e.symm

end IrreducibleCharacter

end

end Submission.OddOrder.PF
