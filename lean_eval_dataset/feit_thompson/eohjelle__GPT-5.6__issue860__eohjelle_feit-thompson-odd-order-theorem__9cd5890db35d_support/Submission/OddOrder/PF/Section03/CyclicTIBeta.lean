import Submission.OddOrder.PF.Section03.CyclicTIInduction
import Submission.OddOrder.PF.Section03.CyclicTIVirtualBasis

/-!
# The cyclic-TI beta virtual characters

This file ports the Gram-matrix prefix of Peterfalvi's cyclic-TI isometry
construction.  Inducing a four-term cyclic-TI virtual character to the
ambient group preserves its pairing; subtracting the ambient trivial
character makes it orthogonal to the trivial character and changes every
Gram entry by exactly `-1`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

variable {Γ k : Type u} [Group Γ] [Fintype Γ]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Γ}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance cyclicTIBetaInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The ambient trivial character as an element of the integral virtual-
character lattice. -/
def ambientTrivialVirtualCharacter : VirtualCharacter G k :=
  Finsupp.single
    (IrreducibleCharacter.trivial : IrreducibleCharacter G k) 1

/-- Realization of the ambient trivial virtual character. -/
@[simp]
theorem realize_ambientTrivialVirtualCharacter :
    VirtualCharacter.realize
        (ambientTrivialVirtualCharacter (G := G) (k := k)) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
        ClassFunction G k) := by
  simp [ambientTrivialVirtualCharacter]

omit [IsAlgClosed k] [CharZero k] in
private theorem characterPairing_sub_left'
    {H : Type u} [Group H] [Fintype H]
    (f g z : ClassFunction H k) :
    characterPairing (f - g) z =
      characterPairing f z - characterPairing g z := by
  change characterPairingRight z (f - g) = _
  exact map_sub (characterPairingRight z) f g

omit [IsAlgClosed k] [CharZero k] in
private theorem characterPairing_sub_right'
    {H : Type u} [Group H] [Fintype H]
    (z f g : ClassFunction H k) :
    characterPairing z (f - g) =
      characterPairing z f - characterPairing z g := by
  change characterPairingLeft z (f - g) = _
  exact map_sub (characterPairingLeft z) f g

namespace CyclicTIHypothesis

/-- The induced cyclic-TI virtual character, normalized by subtracting the
ambient trivial virtual character. -/
def cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    VirtualCharacter G k :=
  h.induceVirtualCharacter
      (cyclicTIVirtualCharacter defW p.1.1 p.2.1) -
    ambientTrivialVirtualCharacter

/-- Realization of `cyclicTIBeta` as ordinary induction minus the ambient
trivial character. -/
@[simp]
theorem realize_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    VirtualCharacter.realize (h.cyclicTIBeta p) =
      h.induceClassFunction
          (VirtualCharacter.realize
            (cyclicTIVirtualCharacter defW p.1.1 p.2.1)) -
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
          ClassFunction G k) := by
  rw [cyclicTIBeta, VirtualCharacter.realize_sub,
    h.realize_induceVirtualCharacter,
    realize_ambientTrivialVirtualCharacter]

/-- Each beta realization is orthogonal to the ambient trivial character. -/
theorem characterPairing_cyclicTIBeta_trivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    characterPairing
        (VirtualCharacter.realize (h.cyclicTIBeta p))
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
          ClassFunction G k) = 0 := by
  rw [realize_cyclicTIBeta, characterPairing_sub_left',
    h.characterPairing_induceClassFunction_trivial,
    characterPairing_cyclicTIVirtualCharacter_trivial defW
      p.1.2 p.2.2,
    IrreducibleCharacter.characterPairing_self]
  ring

/-- Exact Gram matrix of the beta realizations.  Ordinary induction preserves
the cyclic-TI pairing, while subtracting the ambient trivial character
subtracts one from every entry. -/
theorem characterPairing_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p q : CyclicTINontrivialIndex W₁ W₂ k) :
    characterPairing
        (VirtualCharacter.realize (h.cyclicTIBeta p))
        (VirtualCharacter.realize (h.cyclicTIBeta q)) =
      (if p.1 = q.1 then 2 else 1) *
          (if p.2 = q.2 then 2 else 1) - 1 := by
  have hinduced :
      characterPairing
          (h.induceClassFunction
            (VirtualCharacter.realize
              (cyclicTIVirtualCharacter defW p.1.1 p.2.1)))
          (h.induceClassFunction
            (VirtualCharacter.realize
              (cyclicTIVirtualCharacter defW q.1.1 q.2.1))) =
        (if p.1 = q.1 then 2 else 1) *
          (if p.2 = q.2 then 2 else 1) := by
    calc
      _ = characterPairing
          (VirtualCharacter.realize
            (cyclicTIVirtualCharacter defW p.1.1 p.2.1))
          (VirtualCharacter.realize
            (cyclicTIVirtualCharacter defW q.1.1 q.2.1)) :=
        h.characterPairing_induceClassFunction _ _
          (h.cyclicTIVirtualCharacter_mem_supportedOn p.1.1 p.2.1)
          (h.cyclicTIVirtualCharacter_mem_supportedOn q.1.1 q.2.1)
      _ = _ := by
        simpa only [Subtype.ext_iff] using
          (characterPairing_cyclicTIVirtualCharacter defW
            p.1.2 p.2.2 q.1.2 q.2.2)
  have hp :
      characterPairing
          (h.induceClassFunction
            (VirtualCharacter.realize
              (cyclicTIVirtualCharacter defW p.1.1 p.2.1)))
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
            ClassFunction G k) = 1 := by
    rw [h.characterPairing_induceClassFunction_trivial]
    exact characterPairing_cyclicTIVirtualCharacter_trivial defW
      p.1.2 p.2.2
  have hq :
      characterPairing
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
            ClassFunction G k)
          (h.induceClassFunction
            (VirtualCharacter.realize
              (cyclicTIVirtualCharacter defW q.1.1 q.2.1))) = 1 := by
    rw [characterPairing_comm,
      h.characterPairing_induceClassFunction_trivial]
    exact characterPairing_cyclicTIVirtualCharacter_trivial defW
      q.1.2 q.2.2
  have htrivial :
      characterPairing
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
            ClassFunction G k)
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
            ClassFunction G k) = 1 :=
    IrreducibleCharacter.characterPairing_self _
  rw [realize_cyclicTIBeta, realize_cyclicTIBeta]
  simp only [characterPairing_sub_left', characterPairing_sub_right']
  rw [hinduced, hp, hq, htrivial]
  ring

/-- Exact integral Gram matrix of the beta virtual characters. -/
theorem coeffDot_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p q : CyclicTINontrivialIndex W₁ W₂ k) :
    coeffDot (h.cyclicTIBeta p) (h.cyclicTIBeta q) =
      (if p.1 = q.1 then 2 else 1) *
          (if p.2 = q.2 then 2 else 1) - 1 := by
  apply Int.cast_injective (α := k)
  rw [← VirtualCharacter.characterPairing_realize,
    h.characterPairing_cyclicTIBeta]
  by_cases hleft : p.1 = q.1 <;>
    by_cases hright : p.2 = q.2 <;>
      norm_num [hleft, hright]

/-- Integral form of orthogonality to the ambient trivial virtual
character. -/
theorem coeffDot_cyclicTIBeta_ambientTrivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    coeffDot (h.cyclicTIBeta p)
        (ambientTrivialVirtualCharacter (G := G) (k := k)) = 0 := by
  apply Int.cast_injective (α := k)
  rw [← VirtualCharacter.characterPairing_realize,
    realize_ambientTrivialVirtualCharacter,
    h.characterPairing_cyclicTIBeta_trivial]
  norm_num

/-- Every beta virtual character has squared norm three. -/
@[simp]
theorem normSq_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    normSq (h.cyclicTIBeta p) = 3 := by
  unfold normSq
  simpa using h.coeffDot_cyclicTIBeta p p

/-- Class-function self-pairing form of the norm-three formula. -/
@[simp]
theorem characterPairing_cyclicTIBeta_self
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    characterPairing
        (VirtualCharacter.realize (h.cyclicTIBeta p))
        (VirtualCharacter.realize (h.cyclicTIBeta p)) = 3 := by
  rw [h.characterPairing_cyclicTIBeta]
  norm_num

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
