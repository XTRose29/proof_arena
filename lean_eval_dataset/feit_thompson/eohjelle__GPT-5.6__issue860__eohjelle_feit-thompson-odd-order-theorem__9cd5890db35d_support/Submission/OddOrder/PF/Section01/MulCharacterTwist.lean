import Submission.OddOrder.PF.Section01.FiniteAbelianMulCharacters

/-!
# Twisting irreducible characters by scalar characters

A scalar character pulled back along a group homomorphism gives a
one-dimensional representation.  Tensoring an irreducible representation
with this line preserves its character norm and hence its irreducibility.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative
open CategoryTheory.MonoidalCategory

universe u


namespace FDRep

variable {T Q k : Type u} [Group T] [Group Q] [IsMulCommutative Q] [Fintype T]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- The one-dimensional representation obtained by pulling a scalar
character back along a group homomorphism. -/
def mulCharacterRepresentation (q : T →* Q) (chi : MulChar Q k) :
    Representation k T k where
  toFun t := chi (q t) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro z
    simp only [map_mul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      Module.End.mul_apply]
    ring

/-- Bundled finite-dimensional scalar-character line. -/
def mulCharacterLine (q : T →* Q) (chi : MulChar Q k) : FDRep k T :=
  FDRep.of (mulCharacterRepresentation q chi)

omit [Fintype T] [IsAlgClosed k] [CharZero k] in
@[simp]
theorem mulCharacterLine_character
    (q : T →* Q) (chi : MulChar Q k) (t : T) :
    (mulCharacterLine q chi).character t = chi (q t) := by
  change LinearMap.trace k k (chi (q t) • LinearMap.id) = chi (q t)
  rw [map_smul, LinearMap.trace_id]
  simp

/-- Tensoring with a scalar-character line preserves simplicity. -/
theorem simple_mulCharacterLine_tensor
    (q : T →* Q) (chi : MulChar Q k)
    (V : FDRep k T) [CategoryTheory.Simple V] :
    CategoryTheory.Simple (mulCharacterLine q chi ⊗ V) := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hV := (FDRep.simple_iff_char_is_norm_one V).mp (by infer_instance)
  calc
    (∑ t : T,
        (mulCharacterLine q chi ⊗ V).character t *
          (mulCharacterLine q chi ⊗ V).character t⁻¹) =
        ∑ t : T,
          (chi (q t) * V.character t) *
            (chi (q t⁻¹) * V.character t⁻¹) := by
      simp only [FDRep.char_tensor, Pi.mul_apply,
        mulCharacterLine_character]
    _ = ∑ t : T, V.character t * V.character t⁻¹ := by
      apply Fintype.sum_congr
      intro t
      have hchi : chi (q t) * chi (q t⁻¹) = 1 := by
        rw [← map_mul chi, ← map_mul q]
        simp
      calc
        (chi (q t) * V.character t) *
            (chi (q t⁻¹) * V.character t⁻¹) =
            (chi (q t) * chi (q t⁻¹)) *
              (V.character t * V.character t⁻¹) := by ring
        _ = V.character t * V.character t⁻¹ := by rw [hchi, one_mul]
    _ = Nat.card T := hV

end FDRep

namespace IrreducibleCharacter

variable {T Q k : Type u} [Group T] [Group Q] [IsMulCommutative Q] [Fintype T]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Twist an irreducible character by a scalar character pulled back along
`q`. -/
def mulCharacterTwist (q : T →* Q) (chi : MulChar Q k)
    (psi : IrreducibleCharacter T k) : IrreducibleCharacter T k := by
  let V := FDRep.mulCharacterLine q chi ⊗ psi.representation
  letI : CategoryTheory.Simple psi.representation :=
    psi.representation_simple
  letI : CategoryTheory.Simple V :=
    FDRep.simple_mulCharacterLine_tensor q chi psi.representation
  exact ofFDRep V

@[simp]
theorem mulCharacterTwist_apply (q : T →* Q) (chi : MulChar Q k)
    (psi : IrreducibleCharacter T k) (t : T) :
    mulCharacterTwist q chi psi t = chi (q t) * psi t := by
  letI : CategoryTheory.Simple psi.representation :=
    psi.representation_simple
  change (FDRep.mulCharacterLine q chi ⊗ psi.representation).character t = _
  rw [FDRep.char_tensor]
  simp

@[simp]
theorem mulCharacterTwist_one (q : T →* Q) (chi : MulChar Q k)
    (psi : IrreducibleCharacter T k) :
    mulCharacterTwist q chi psi 1 = psi 1 := by
  simp

end IrreducibleCharacter

end

end Submission.OddOrder.PF
