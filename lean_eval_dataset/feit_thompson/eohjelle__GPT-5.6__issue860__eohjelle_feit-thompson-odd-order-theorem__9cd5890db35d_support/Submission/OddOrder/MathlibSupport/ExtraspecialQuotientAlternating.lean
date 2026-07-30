import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientPairing

/-!
Alternating and skew-symmetry properties of the extraspecial quotient pairing.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

namespace IsSpecial

/-- The quotient commutator pairing is alternating. -/
@[simp]
theorem quotientCommutatorPairing_self (hG : IsSpecial G)
    (x : G ⧸ Subgroup.center G) :
    hG.quotientCommutatorPairing x x = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  exact hG.commutatorPairing_self x

/-- Swapping the arguments of the quotient pairing inverts its value. -/
theorem quotientCommutatorPairing_swap (hG : IsSpecial G)
    (x y : G ⧸ Subgroup.center G) :
    hG.quotientCommutatorPairing x y =
      (hG.quotientCommutatorPairing y x)⁻¹ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
  apply Subtype.ext
  exact (commutatorElement_inv y x).symm

/-- The quotient pairing also has trivial right radical. -/
theorem quotientCommutatorPairing_right_nondegenerate (hG : IsSpecial G)
    (y : G ⧸ Subgroup.center G)
    (hy : ∀ x : G ⧸ Subgroup.center G,
      hG.quotientCommutatorPairing x y = 1) : y = 1 := by
  apply hG.quotientCommutatorPairing_nondegenerate y
  intro x
  rw [hG.quotientCommutatorPairing_swap]
  simp [hy x]

/-- Every nonidentity quotient class is detected by the pairing. -/
theorem exists_quotientCommutatorPairing_ne_one (hG : IsSpecial G)
    {x : G ⧸ Subgroup.center G} (hx : x ≠ 1) :
    ∃ y : G ⧸ Subgroup.center G,
      hG.quotientCommutatorPairing x y ≠ 1 := by
  by_contra h
  apply hx
  apply hG.quotientCommutatorPairing_nondegenerate x
  intro y
  by_contra hy
  exact h ⟨y, hy⟩

end IsSpecial

end Submission.OddOrder.MathlibSupport
