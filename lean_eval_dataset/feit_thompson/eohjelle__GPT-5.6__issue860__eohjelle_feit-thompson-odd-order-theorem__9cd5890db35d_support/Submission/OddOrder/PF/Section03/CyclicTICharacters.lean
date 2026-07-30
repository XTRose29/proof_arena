import Submission.OddOrder.PF.Section03.DirectProductCharacters
import Submission.OddOrder.PF.Section03.InternalDirectProduct
import Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport
import Submission.OddOrder.PF.Section01.QuotientDescent

/-!
# Characters of a cyclic-TI internal direct product

This file transports the direct-product classification of irreducible
characters across the canonical multiplication equivalence associated to an
internal direct product.  It is the character-side setup denoted
`cyclicTIirr` in Peterfalvi Section 3.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v

namespace ClassFunction

variable {G : Type u} {R : Type v} [Group G] [CommRing R]

/-- Pointwise multiplication of class functions. -/
def pointwiseMul (f g : ClassFunction G R) : ClassFunction G R where
  val x := f x * g x
  property x y := by
    change f (x * y * x⁻¹) * g (x * y * x⁻¹) = f y * g y
    rw [ClassFunction.conj_apply f, ClassFunction.conj_apply g]

@[simp]
theorem pointwiseMul_apply (f g : ClassFunction G R) (x : G) :
    pointwiseMul f g x = f x * g x :=
  rfl

end ClassFunction

namespace IrreducibleCharacter

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {W1 W2 W : Subgroup Gamma}

local instance cyclicTIInvertibleCardOfFintype
    {G : Type u} [Group G] [Fintype G] :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The irreducible character of `W` indexed by irreducible characters of
the two internal direct factors. -/
def cyclicTICharacter
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) :
    IrreducibleCharacter W k :=
  comapMulEquiv defW.mulEquiv.symm (externalProduct i j)

/-- Irreducible characters of the internal direct product are canonically
indexed by pairs of irreducible characters of its two factors. -/
def cyclicTICharacterEquiv
    (defW : IsInternalDirectProductIn W1 W2 W) :
    IrreducibleCharacter W1 k × IrreducibleCharacter W2 k ≃
      IrreducibleCharacter W k :=
  externalProductEquiv.trans (equivOfMulEquiv defW.mulEquiv.symm)

@[simp]
theorem cyclicTICharacterEquiv_apply
    (defW : IsInternalDirectProductIn W1 W2 W)
    (p : IrreducibleCharacter W1 k × IrreducibleCharacter W2 k) :
    cyclicTICharacterEquiv defW p =
      cyclicTICharacter defW p.1 p.2 :=
  rfl

/-- The pair of factor characters indexing an irreducible character of `W`. -/
def cyclicTICharacterIndex
    (defW : IsInternalDirectProductIn W1 W2 W)
    (chi : IrreducibleCharacter W k) :
    IrreducibleCharacter W1 k × IrreducibleCharacter W2 k :=
  (cyclicTICharacterEquiv defW).symm chi

@[simp]
theorem cyclicTICharacterIndex_character
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) :
    cyclicTICharacterIndex defW (cyclicTICharacter defW i j) = (i, j) :=
  (cyclicTICharacterEquiv defW).symm_apply_apply (i, j)

@[simp]
theorem cyclicTICharacter_index
    (defW : IsInternalDirectProductIn W1 W2 W)
    (chi : IrreducibleCharacter W k) :
    cyclicTICharacter defW
        (cyclicTICharacterIndex defW chi).1
        (cyclicTICharacterIndex defW chi).2 = chi :=
  (cyclicTICharacterEquiv defW).apply_symm_apply chi

/-- Every irreducible character of `W` has a unique pair of factor indices. -/
theorem exists_cyclicTICharacter
    (defW : IsInternalDirectProductIn W1 W2 W)
    (chi : IrreducibleCharacter W k) :
    ∃ i : IrreducibleCharacter W1 k,
      ∃ j : IrreducibleCharacter W2 k,
        chi = cyclicTICharacter defW i j := by
  exact ⟨(cyclicTICharacterIndex defW chi).1,
    (cyclicTICharacterIndex defW chi).2,
    (cyclicTICharacter_index defW chi).symm⟩

theorem cyclicTICharacter_injective
    (defW : IsInternalDirectProductIn W1 W2 W) :
    Function.Injective
      (fun p : IrreducibleCharacter W1 k × IrreducibleCharacter W2 k ↦
        cyclicTICharacter defW p.1 p.2) :=
  (cyclicTICharacterEquiv defW).injective

theorem cyclicTICharacter_eq_iff
    (defW : IsInternalDirectProductIn W1 W2 W)
    {i1 i2 : IrreducibleCharacter W1 k}
    {j1 j2 : IrreducibleCharacter W2 k} :
    cyclicTICharacter defW i1 j1 = cyclicTICharacter defW i2 j2 ↔
      i1 = i2 ∧ j1 = j2 := by
  constructor
  · intro h
    exact Prod.mk.inj (cyclicTICharacter_injective defW h)
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem cyclicTICharacter_apply
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) (w : W) :
    cyclicTICharacter defW i j w =
      i (defW.leftProjection w) * j (defW.rightProjection w) := by
  simp only [cyclicTICharacter, comapMulEquiv_apply]
  change externalProduct i j (defW.mulEquiv.symm w) =
    i ((defW.mulEquiv.symm w).1) * j ((defW.mulEquiv.symm w).2)
  exact externalProduct_apply i j _ _

@[simp]
theorem cyclicTICharacter_mulEquiv
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) (x : W1) (y : W2) :
    cyclicTICharacter defW i j (defW.mulEquiv (x, y)) = i x * j y := by
  simp

@[simp]
theorem cyclicTICharacter_leftEmbedding
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) (x : W1) :
    cyclicTICharacter defW i j (defW.leftEmbedding x) = i x * j 1 := by
  simp

@[simp]
theorem cyclicTICharacter_rightEmbedding
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) (y : W2) :
    cyclicTICharacter defW i j (defW.rightEmbedding y) = i 1 * j y := by
  simp

/-- Swapping the two internal factors only swaps the two character indices. -/
theorem cyclicTICharacter_swap
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) :
    cyclicTICharacter defW.swap j i = cyclicTICharacter defW i j := by
  ext w
  obtain ⟨⟨x, y⟩, rfl⟩ := defW.mulEquiv.surjective w
  calc
    cyclicTICharacter defW.swap j i (defW.mulEquiv (x, y)) =
        cyclicTICharacter defW.swap j i
          (defW.swap.mulEquiv (y, x)) := by
      rw [defW.swap_mulEquiv_apply]
    _ = j y * i x := cyclicTICharacter_mulEquiv defW.swap j i y x
    _ = i x * j y := mul_comm _ _
    _ = cyclicTICharacter defW i j (defW.mulEquiv (x, y)) :=
      (cyclicTICharacter_mulEquiv defW i j x y).symm

@[simp]
theorem cyclicTICharacter_trivial
    (defW : IsInternalDirectProductIn W1 W2 W) :
    cyclicTICharacter defW
        (trivial : IrreducibleCharacter W1 k)
        (trivial : IrreducibleCharacter W2 k) =
      (trivial : IrreducibleCharacter W k) := by
  ext w
  simp [trivial_apply]

/-- The character pairing of internal direct-product characters factors
through the two factors. -/
theorem characterPairing_cyclicTICharacter
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i1 i2 : IrreducibleCharacter W1 k)
    (j1 j2 : IrreducibleCharacter W2 k) :
    characterPairing
        (cyclicTICharacter defW i1 j1 : ClassFunction W k)
        (cyclicTICharacter defW i2 j2 : ClassFunction W k) =
      characterPairing (i1 : ClassFunction W1 k) (i2 : ClassFunction W1 k) *
        characterPairing (j1 : ClassFunction W2 k) (j2 : ClassFunction W2 k) := by
  simp only [characterPairing_eq_ite]
  rw [cyclicTICharacter_eq_iff]
  by_cases hi : i1 = i2 <;> by_cases hj : j1 = j2 <;> simp [hi, hj]

/-- Orthogonality in the pair indexing. -/
theorem characterPairing_cyclicTICharacter_eq_ite
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i1 i2 : IrreducibleCharacter W1 k)
    (j1 j2 : IrreducibleCharacter W2 k) :
    characterPairing
        (cyclicTICharacter defW i1 j1 : ClassFunction W k)
        (cyclicTICharacter defW i2 j2 : ClassFunction W k) =
      if i1 = i2 ∧ j1 = j2 then 1 else 0 := by
  rw [characterPairing_eq_ite, cyclicTICharacter_eq_iff]
  by_cases h : i1 = i2 ∧ j1 = j2 <;> simp [h]

/-- The character with general pair index is the pointwise product of the
two characters inflated from the factors. -/
theorem cyclicTICharacter_split
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) :
    (cyclicTICharacter defW i j : ClassFunction W k) =
      ClassFunction.pointwiseMul
        (cyclicTICharacter defW i
          (trivial : IrreducibleCharacter W2 k) : ClassFunction W k)
        (cyclicTICharacter defW
          (trivial : IrreducibleCharacter W1 k) j : ClassFunction W k) := by
  ext w
  simp [trivial_apply]

@[simp]
theorem cyclicTICharacter_leftFactor_apply
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k) (w : W) :
    cyclicTICharacter defW i
        (trivial : IrreducibleCharacter W2 k) w =
      i (defW.leftProjection w) := by
  simp [trivial_apply]

@[simp]
theorem cyclicTICharacter_rightFactor_apply
    (defW : IsInternalDirectProductIn W1 W2 W)
    (j : IrreducibleCharacter W2 k) (w : W) :
    cyclicTICharacter defW
        (trivial : IrreducibleCharacter W1 k) j w =
      j (defW.rightProjection w) := by
  simp [trivial_apply]

/-- The left factor acts trivially by translation on a character inflated
from the right factor. -/
theorem leftEmbedding_mem_translationKernel_rightFactor
    (defW : IsInternalDirectProductIn W1 W2 W)
    (j : IrreducibleCharacter W2 k) (x : W1) :
    defW.leftEmbedding x ∈
      ClassFunction.translationKernel
        (cyclicTICharacter defW
          (trivial : IrreducibleCharacter W1 k) j : ClassFunction W k) := by
  intro w
  simp [trivial_apply]

/-- The right factor acts trivially by translation on a character inflated
from the left factor. -/
theorem rightEmbedding_mem_translationKernel_leftFactor
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k) (y : W2) :
    defW.rightEmbedding y ∈
      ClassFunction.translationKernel
        (cyclicTICharacter defW i
          (trivial : IrreducibleCharacter W2 k) : ClassFunction W k) := by
  intro w
  simp [trivial_apply]

/-- Subgroup form of `leftEmbedding_mem_translationKernel_rightFactor`. -/
theorem leftEmbedding_range_le_translationKernel_rightFactor
    (defW : IsInternalDirectProductIn W1 W2 W)
    (j : IrreducibleCharacter W2 k) :
    defW.leftEmbedding.range ≤
      ClassFunction.translationKernel
        (cyclicTICharacter defW
          (trivial : IrreducibleCharacter W1 k) j : ClassFunction W k) := by
  rintro _ ⟨x, rfl⟩
  exact leftEmbedding_mem_translationKernel_rightFactor defW j x

/-- Subgroup form of `rightEmbedding_mem_translationKernel_leftFactor`. -/
theorem rightEmbedding_range_le_translationKernel_leftFactor
    (defW : IsInternalDirectProductIn W1 W2 W)
    (i : IrreducibleCharacter W1 k) :
    defW.rightEmbedding.range ≤
      ClassFunction.translationKernel
        (cyclicTICharacter defW i
          (trivial : IrreducibleCharacter W2 k) : ClassFunction W k) := by
  rintro _ ⟨y, rfl⟩
  exact rightEmbedding_mem_translationKernel_leftFactor defW i y

/-- Coefficient-field automorphisms commute with the internal direct-product
character indexing. -/
theorem cyclicTICharacter_mapRingEquiv
    (defW : IsInternalDirectProductIn W1 W2 W)
    (sigma : k ≃+* k)
    (i : IrreducibleCharacter W1 k)
    (j : IrreducibleCharacter W2 k) :
    cyclicTICharacter defW (mapRingEquiv sigma i) (mapRingEquiv sigma j) =
      mapRingEquiv sigma (cyclicTICharacter defW i j) := by
  ext w
  simp only [cyclicTICharacter_apply, mapRingEquiv_apply, map_mul]

theorem cyclicTICharacterEquiv_mapRingEquiv
    (defW : IsInternalDirectProductIn W1 W2 W)
    (sigma : k ≃+* k)
    (p : IrreducibleCharacter W1 k × IrreducibleCharacter W2 k) :
    cyclicTICharacterEquiv defW
        (mapRingEquiv sigma p.1, mapRingEquiv sigma p.2) =
      mapRingEquiv sigma (cyclicTICharacterEquiv defW p) := by
  simpa only [cyclicTICharacterEquiv_apply] using
    cyclicTICharacter_mapRingEquiv defW sigma p.1 p.2

end IrreducibleCharacter

end

end Submission.OddOrder.PF
