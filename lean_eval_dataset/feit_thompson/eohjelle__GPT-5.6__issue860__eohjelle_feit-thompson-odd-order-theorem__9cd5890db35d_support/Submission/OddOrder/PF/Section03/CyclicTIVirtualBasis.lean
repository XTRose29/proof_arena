import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence
import Submission.OddOrder.PF.Section01.VirtualCharacter
import Submission.OddOrder.PF.Section03.AbelianSupportedClassFunctions
import Submission.OddOrder.PF.Section03.CyclicCharacterFacts
import Submission.OddOrder.PF.Section03.CyclicTICharacters
import Submission.OddOrder.PF.Section03.CyclicTIGroupFacts

/-!
# The cyclic-TI virtual-character basis

This file ports the basis construction in Peterfalvi (3.4).  For nontrivial
factor characters `i` and `j`, the four-term virtual character

`1 - w_(i,0) - w_(0,j) + w_(i,j)`

is supported on the cyclic-TI set.  These vectors are linearly independent,
and the exact cardinality calculation from `CyclicTIGroupFacts` shows that
they form a basis of the supported class functions.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

variable {Γ k : Type u} [Group Γ] [Fintype Γ]
  [Field k] [IsAlgClosed k] [CharZero k]
  {W W₁ W₂ : Subgroup Γ}

local instance cyclicTIVirtualBasisInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- Peterfalvi's four-term virtual character
`1 - w_(i,0) - w_(0,j) + w_(i,j)`. -/
def cyclicTIVirtualCharacter
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) : VirtualCharacter W k :=
  Finsupp.single (IrreducibleCharacter.trivial :
      IrreducibleCharacter W k) 1 -
    Finsupp.single
      (IrreducibleCharacter.cyclicTICharacter defW i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k)) 1 -
    Finsupp.single
      (IrreducibleCharacter.cyclicTICharacter defW
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j) 1 +
    Finsupp.single (IrreducibleCharacter.cyclicTICharacter defW i j) 1

namespace IrreducibleCharacter

/-- A cyclic-TI character is trivial exactly when both factor characters are
trivial. -/
@[simp]
theorem cyclicTICharacter_eq_trivial_iff
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k} :
    cyclicTICharacter defW i j =
        (trivial : IrreducibleCharacter W k) ↔
      i = trivial ∧ j = trivial := by
  rw [← cyclicTICharacter_trivial defW]
  exact cyclicTICharacter_eq_iff defW

@[simp]
theorem trivial_eq_cyclicTICharacter_iff
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k} :
    (trivial : IrreducibleCharacter W k) =
        cyclicTICharacter defW i j ↔
      i = trivial ∧ j = trivial := by
  rw [eq_comm]
  exact cyclicTICharacter_eq_trivial_iff defW

end IrreducibleCharacter

/-- Realization of the four-term virtual character as the corresponding
four-term class function. -/
@[simp]
theorem realize_cyclicTIVirtualCharacter
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
          ClassFunction W k) -
        (IrreducibleCharacter.cyclicTICharacter defW i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) :
            ClassFunction W k) -
        (IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j :
            ClassFunction W k) +
        (IrreducibleCharacter.cyclicTICharacter defW i j :
          ClassFunction W k) := by
  simp [cyclicTIVirtualCharacter]

/-- Evaluation factors into the two differences from the trivial factor
characters. -/
theorem realize_cyclicTIVirtualCharacter_apply
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) (w : W) :
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j) w =
      (1 - i (defW.leftProjection w)) *
        (1 - j (defW.rightProjection w)) := by
  rw [realize_cyclicTIVirtualCharacter]
  simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
    IrreducibleCharacter.trivial_apply,
    IrreducibleCharacter.cyclicTICharacter_apply]
  ring

/-- Product-coordinate form of the evaluation formula. -/
theorem realize_cyclicTIVirtualCharacter_mulEquiv
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) (x : W₁) (y : W₂) :
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j)
        (defW.mulEquiv (x, y)) =
      (1 - i x) * (1 - j y) := by
  simp only [realize_cyclicTIVirtualCharacter_apply,
    IsInternalDirectProductIn.leftProjection_mulEquiv,
    IsInternalDirectProductIn.rightProjection_mulEquiv]

namespace CyclicTIHypothesis

variable {G : Subgroup Γ}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

/-- The four-term virtual character vanishes at the identity. -/
@[simp]
theorem realize_cyclicTIVirtualCharacter_one
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j) 1 = 0 := by
  letI : IsCyclic W₁ := h.left_cyclic
  letI : IsCyclic W₂ := h.right_cyclic
  simp

/-- The realization is supported on `W \ (W₁ ∪ W₂)`. -/
theorem cyclicTIVirtualCharacter_mem_supportedOn
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j) ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂) := by
  letI : IsCyclic W₁ := h.left_cyclic
  letI : IsCyclic W₂ := h.right_cyclic
  rw [ClassFunction.mem_supportedOn_iff]
  intro w hw
  obtain ⟨⟨x, y⟩, rfl⟩ := defW.mulEquiv.surjective w
  rw [realize_cyclicTIVirtualCharacter_mulEquiv]
  rw [mem_cyclicTISetInW,
    defW.mulEquiv_mem_left_iff, defW.mulEquiv_mem_right_iff] at hw
  by_cases hx : x = 1
  · simp [hx]
  · have hy : y = 1 := by
      by_contra hy
      exact hw ⟨hy, hx⟩
    simp [hy]

end CyclicTIHypothesis

/-- Pairing the four-term virtual character with the trivial character gives
one when both displayed factor indices are nontrivial. -/
theorem characterPairing_cyclicTIVirtualCharacter_trivial
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j))
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
          ClassFunction W k) = 1 := by
  rw [characterPairing_comm,
    VirtualCharacter.characterPairing_irreducible_realize]
  simp [cyclicTIVirtualCharacter, hi, hj]

/-- Pairing with a nontrivial character inflated from the left factor. -/
theorem characterPairing_cyclicTIVirtualCharacter_leftFactor
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i a : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k}
    (_hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (ha : a ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j))
        (IrreducibleCharacter.cyclicTICharacter defW a
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) :
            ClassFunction W k) =
      if i = a then -1 else 0 := by
  rw [characterPairing_comm,
    VirtualCharacter.characterPairing_irreducible_realize]
  by_cases hia : i = a
  · simp [cyclicTIVirtualCharacter,
      IrreducibleCharacter.cyclicTICharacter_eq_iff, hia, hj, ha]
  · simp [cyclicTIVirtualCharacter,
      IrreducibleCharacter.cyclicTICharacter_eq_iff, hia, hj, ha]

/-- Pairing with a nontrivial character inflated from the right factor. -/
theorem characterPairing_cyclicTIVirtualCharacter_rightFactor
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i : IrreducibleCharacter W₁ k}
    {j b : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (_hj : j ≠ IrreducibleCharacter.trivial)
    (hb : b ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j))
        (IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) b :
            ClassFunction W k) =
      if j = b then -1 else 0 := by
  rw [characterPairing_comm,
    VirtualCharacter.characterPairing_irreducible_realize]
  by_cases hjb : j = b
  · simp [cyclicTIVirtualCharacter,
      IrreducibleCharacter.cyclicTICharacter_eq_iff, hi, hjb, hb]
  · simp [cyclicTIVirtualCharacter,
      IrreducibleCharacter.cyclicTICharacter_eq_iff, hi, hjb, hb]

/-- Pairing with a cyclic-TI character having two nontrivial factor indices
extracts exactly the matching coefficient. -/
theorem characterPairing_cyclicTIVirtualCharacter_character
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i a : IrreducibleCharacter W₁ k}
    {j b : IrreducibleCharacter W₂ k}
    (_hi : i ≠ IrreducibleCharacter.trivial)
    (_hj : j ≠ IrreducibleCharacter.trivial)
    (ha : a ≠ IrreducibleCharacter.trivial)
    (hb : b ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j))
        (IrreducibleCharacter.cyclicTICharacter defW a b :
          ClassFunction W k) =
      if i = a ∧ j = b then 1 else 0 := by
  rw [characterPairing_comm,
    VirtualCharacter.characterPairing_irreducible_realize]
  by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp [cyclicTIVirtualCharacter,
      IrreducibleCharacter.cyclicTICharacter_eq_iff, hia, hjb, ha, hb]

/-- Exact integral Gram matrix of the four-term virtual characters. -/
theorem coeffDot_cyclicTIVirtualCharacter
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i a : IrreducibleCharacter W₁ k}
    {j b : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (ha : a ≠ IrreducibleCharacter.trivial)
    (hb : b ≠ IrreducibleCharacter.trivial) :
    coeffDot (cyclicTIVirtualCharacter defW i j)
        (cyclicTIVirtualCharacter defW a b) =
      (if i = a then 2 else 1) * (if j = b then 2 else 1) := by
  by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp [cyclicTIVirtualCharacter, sub_eq_add_neg,
      coeffDot_add_right, coeffDot_neg_right,
      IrreducibleCharacter.cyclicTICharacter_eq_iff,
      hi, hj, ha, hb, hia, hjb]

/-- Class-function form of the exact Gram matrix. -/
theorem characterPairing_cyclicTIVirtualCharacter
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i a : IrreducibleCharacter W₁ k}
    {j b : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (ha : a ≠ IrreducibleCharacter.trivial)
    (hb : b ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j))
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW a b)) =
      (if i = a then 2 else 1) * (if j = b then 2 else 1) := by
  rw [VirtualCharacter.characterPairing_realize,
    coeffDot_cyclicTIVirtualCharacter defW hi hj ha hb]
  by_cases hia : i = a <;> by_cases hjb : j = b <;> norm_num [hia, hjb]

/-- Every nontrivial-pair virtual character has squared norm four. -/
theorem normSq_cyclicTIVirtualCharacter
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    normSq (cyclicTIVirtualCharacter defW i j) = 4 := by
  unfold normSq
  simpa using
    (coeffDot_cyclicTIVirtualCharacter defW hi hj hi hj)

/-- Pairs of nontrivial irreducible characters of the two direct factors. -/
abbrev CyclicTINontrivialIndex
    (W₁ W₂ : Subgroup Γ) (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] :=
  {i : IrreducibleCharacter W₁ k //
      i ≠ IrreducibleCharacter.trivial} ×
    {j : IrreducibleCharacter W₂ k //
      j ≠ IrreducibleCharacter.trivial}

namespace CyclicTIHypothesis

variable {G : Subgroup Γ}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

/-- The nontrivial-pair index has the cardinality predicted by the two
cyclic character groups. -/
theorem card_cyclicTINontrivialIndex
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Fintype.card (CyclicTINontrivialIndex W₁ W₂ k) =
      (Nat.card W₁ - 1) * (Nat.card W₂ - 1) := by
  letI : IsCyclic W₁ := h.left_cyclic
  letI : IsCyclic W₂ := h.right_cyclic
  have hleft :
      Fintype.card {i : IrreducibleCharacter W₁ k //
          i ≠ IrreducibleCharacter.trivial} = Nat.card W₁ - 1 := by
    calc
      _ = Fintype.card (IrreducibleCharacter W₁ k) - 1 :=
        Set.card_ne_eq _
      _ = Nat.card W₁ - 1 := by
        rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
  have hright :
      Fintype.card {j : IrreducibleCharacter W₂ k //
          j ≠ IrreducibleCharacter.trivial} = Nat.card W₂ - 1 := by
    calc
      _ = Fintype.card (IrreducibleCharacter W₂ k) - 1 :=
        Set.card_ne_eq _
      _ = Nat.card W₂ - 1 := by
        rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
  simp [Fintype.card_prod, hleft, hright]

/-- The four-term realization, bundled as a class function supported on the
cyclic-TI set. -/
def cyclicTISupportedVector
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    ClassFunction.supportedOn (R := k) (cyclicTISetInW W W₁ W₂) :=
  ⟨VirtualCharacter.realize
      (cyclicTIVirtualCharacter defW p.1.1 p.2.1),
    h.cyclicTIVirtualCharacter_mem_supportedOn p.1.1 p.2.1⟩

@[simp]
theorem cyclicTISupportedVector_val
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    (cyclicTISupportedVector h p : ClassFunction W k) =
      VirtualCharacter.realize
        (cyclicTIVirtualCharacter defW p.1.1 p.2.1) :=
  rfl

/-- Pointwise product formula for the supported vectors. -/
theorem cyclicTISupportedVector_apply
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) (w : W) :
    (cyclicTISupportedVector h p : ClassFunction W k) w =
      (1 - p.1.1 (defW.leftProjection w)) *
        (1 - p.2.1 (defW.rightProjection w)) :=
  realize_cyclicTIVirtualCharacter_apply defW p.1.1 p.2.1 w

/-- The supported four-term vectors are linearly independent.  Pairing with
the irreducible character indexed by `p` extracts the coefficient at `p`. -/
theorem cyclicTISupportedVector_linearIndependent
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    LinearIndependent k (cyclicTISupportedVector (k := k) h) := by
  refine (Fintype.linearIndependent_iff
    (R := k) (v := cyclicTISupportedVector (k := k) h)).2 ?_
  intro c hc p
  let testCharacter : ClassFunction W k :=
    IrreducibleCharacter.cyclicTICharacter defW p.1.1 p.2.1
  let extract :
      ClassFunction.supportedOn (R := k) (cyclicTISetInW W W₁ W₂) →ₗ[k] k :=
    (characterPairingRight testCharacter).comp
      (ClassFunction.supportedOn (R := k)
        (cyclicTISetInW W W₁ W₂)).subtype
  have hextract (q : CyclicTINontrivialIndex W₁ W₂ k) :
      extract (cyclicTISupportedVector h q) =
        if q = p then 1 else 0 := by
    change characterPairing
        (VirtualCharacter.realize
          (cyclicTIVirtualCharacter defW q.1.1 q.2.1))
        (IrreducibleCharacter.cyclicTICharacter defW p.1.1 p.2.1 :
          ClassFunction W k) = _
    rw [characterPairing_cyclicTIVirtualCharacter_character defW
      q.1.2 q.2.2 p.1.2 p.2.2]
    simp only [Prod.ext_iff, Subtype.ext_iff]
  have hc' := congrArg extract hc
  simpa [map_sum, hextract] using hc'

/-- The nontrivial-pair index has the same cardinality as the supported
class-function space. -/
theorem card_cyclicTINontrivialIndex_eq_finrank
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Fintype.card (CyclicTINontrivialIndex W₁ W₂ k) =
      Module.finrank k
        (ClassFunction.supportedOn (R := k)
          (cyclicTISetInW W W₁ W₂)) := by
  letI : IsCyclic W := h.cyclic
  calc
    Fintype.card (CyclicTINontrivialIndex W₁ W₂ k) =
        (Nat.card W₁ - 1) * (Nat.card W₂ - 1) :=
      h.card_cyclicTINontrivialIndex
    _ = (cyclicTISetInW W W₁ W₂).ncard :=
      defW.ncard_cyclicTISetInW.symm
    _ = Module.finrank k
        (ClassFunction.supportedOn (R := k)
          (cyclicTISetInW W W₁ W₂)) :=
      (ClassFunction.finrank_abelian_supportedOn
        (k := k) (cyclicTISetInW W W₁ W₂)).symm

/-- Peterfalvi's cyclic-TI basis of the class functions supported on
`W \ (W₁ ∪ W₂)`. -/
def cyclicTIVirtualBasis
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Module.Basis (CyclicTINontrivialIndex W₁ W₂ k) k
      (ClassFunction.supportedOn (R := k)
        (cyclicTISetInW W W₁ W₂)) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (cyclicTISupportedVector (k := k) h)
    h.cyclicTISupportedVector_linearIndependent
    h.card_cyclicTINontrivialIndex_eq_finrank

@[simp]
theorem cyclicTIVirtualBasis_apply
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    h.cyclicTIVirtualBasis p = cyclicTISupportedVector h p := by
  simp [cyclicTIVirtualBasis]

/-- The basis vector is the realization of the corresponding four-term
virtual character. -/
@[simp]
theorem cyclicTIVirtualBasis_val
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    (h.cyclicTIVirtualBasis p : ClassFunction W k) =
      VirtualCharacter.realize
        (cyclicTIVirtualCharacter defW p.1.1 p.2.1) := by
  rw [cyclicTIVirtualBasis_apply]
  rfl

/-- Pointwise product formula for the cyclic-TI basis. -/
theorem cyclicTIVirtualBasis_apply_apply
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) (w : W) :
    (h.cyclicTIVirtualBasis p : ClassFunction W k) w =
      (1 - p.1.1 (defW.leftProjection w)) *
        (1 - p.2.1 (defW.rightProjection w)) := by
  rw [cyclicTIVirtualBasis_apply]
  exact cyclicTISupportedVector_apply h p w

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
