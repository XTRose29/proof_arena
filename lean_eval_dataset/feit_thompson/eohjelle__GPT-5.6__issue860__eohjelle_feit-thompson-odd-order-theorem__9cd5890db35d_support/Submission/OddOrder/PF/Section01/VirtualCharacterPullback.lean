import Submission.OddOrder.PF.Section01.QuotientInduction
import Submission.OddOrder.PF.Section01.VirtualCharacterOfFDRep

/-!
# Pullback of virtual characters

Restricting a representation along an arbitrary group homomorphism need not
preserve irreducibility.  It does, however, preserve ordinary characters.
We therefore pull an irreducible basis character back by taking the full
virtual character of the restricted representation, and extend this
construction over the free integral lattice.

This is the generic character-theoretic operation used by the Dade expansion:
the source's `cfMorph` is precomposition along the projection from a
semidirect product to its complement.  No compatibility with a star operation
is needed or asserted here.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u

namespace ClassFunction

variable {H G k : Type u} [Group H] [Group G] [Field k]

/-- Pulling back the character of a representation is the character of the
representation restricted along the same group homomorphism. -/
@[simp]
theorem comap_ofRepresentation (q : H →* G) (V : FDRep k G) :
    comap q (ofRepresentation V.ρ) =
      ofRepresentation (FDRep.of (V.ρ.comp q)).ρ := by
  ext h
  rfl

end ClassFunction

namespace VirtualCharacter

variable {H G k : Type u} [Group H] [Group G] [Field k]
  [Fintype H] [IsAlgClosed k] [CharZero k]

/-- Pull a virtual character back along a group homomorphism.

An irreducible character of `G` can become reducible on `H`, so a basis
element is sent to the virtual character of the corresponding restricted
finite-dimensional representation. -/
noncomputable def comap (q : H →* G) :
    VirtualCharacter G k →+ VirtualCharacter H k :=
  Finsupp.liftAddHom fun chi : IrreducibleCharacter G k ↦
    (smulAddHom ℤ (VirtualCharacter H k)).flip
      (ofFDRep (FDRep.of (chi.representation.ρ.comp q)))

/-- Pullback on a single irreducible basis vector. -/
@[simp]
theorem comap_single (q : H →* G) (chi : IrreducibleCharacter G k)
    (z : ℤ) :
    comap q (Finsupp.single chi z) =
      z • ofFDRep (FDRep.of (chi.representation.ρ.comp q)) := by
  rw [comap, Finsupp.liftAddHom_apply_single]
  rfl

/-- Realization of virtual-character pullback is exactly precomposition of
the realized class function. -/
theorem realize_comap (q : H →* G) (f : VirtualCharacter G k) :
    realize (comap q f) = ClassFunction.comap q (realize f) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add chi z f hchi hz ih =>
      have hsingle :
          realize (comap q (Finsupp.single chi z)) =
            ClassFunction.comap q (realize (Finsupp.single chi z)) := by
        rw [comap_single, map_zsmul, realize_ofFDRep, realize_single,
          ← Int.cast_smul_eq_zsmul k, map_smul]
        congr 1
        rw [← chi.ofRepresentation_representation,
          ClassFunction.comap_ofRepresentation]
      calc
        realize (comap q (Finsupp.single chi z + f)) =
            realize (comap q (Finsupp.single chi z)) +
              realize (comap q f) := by rw [map_add, map_add]
        _ = ClassFunction.comap q (realize (Finsupp.single chi z)) +
              ClassFunction.comap q (realize f) := by rw [hsingle, ih]
        _ = ClassFunction.comap q
              (realize (Finsupp.single chi z + f)) := by
            rw [← map_add (ClassFunction.comap q), map_add realize]

variable [Fintype G]

/-- Pullback commutes with packaging an arbitrary finite-dimensional
representation as a virtual character. -/
theorem comap_ofFDRep (q : H →* G) (V : FDRep k G) :
    comap q (ofFDRep V) = ofFDRep (FDRep.of (V.ρ.comp q)) := by
  letI : Invertible (Nat.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  apply realize_injective
  rw [realize_comap, realize_ofFDRep, realize_ofFDRep,
    ClassFunction.comap_ofRepresentation]

end VirtualCharacter

end

end Submission.OddOrder.PF
