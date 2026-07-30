import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientCard

/-!
The central commutator pairing of a special group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

namespace IsSpecial

/-- Every element commutator in a special group lies in the center. -/
theorem commutatorElement_mem_center (hG : IsSpecial G) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  rw [← hG.commutator_eq_center]
  exact Subgroup.commutator_mem_commutator
    (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G)) trivial trivial

/-- The central-valued commutator pairing of a special group. -/
def commutatorPairing (hG : IsSpecial G) (x y : G) : Subgroup.center G :=
  ⟨⁅x, y⁆, hG.commutatorElement_mem_center x y⟩

@[simp]
theorem commutatorPairing_apply (hG : IsSpecial G) (x y : G) :
    (hG.commutatorPairing x y : G) = ⁅x, y⁆ :=
  rfl

/-- Multiplicativity of the commutator in its first argument for a special
group. -/
theorem commutatorElement_mul_left (hG : IsSpecial G) (a b c : G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [_root_.commutatorElement_mul_left_eq_conj_mul]
  have hbc := Subgroup.mem_center_iff.mp
    (hG.commutatorElement_mem_center b c) a
  calc
    a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
      rw [hbc]
      group
    _ = ⁅a, c⁆ * ⁅b, c⁆ :=
      (Subgroup.mem_center_iff.mp
        (hG.commutatorElement_mem_center b c) ⁅a, c⁆).symm

/-- Multiplicativity of the commutator in its second argument for a special
group. -/
theorem commutatorElement_mul_right (hG : IsSpecial G) (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [_root_.commutatorElement_mul_right_eq_mul_conj]
  have hac := Subgroup.mem_center_iff.mp
    (hG.commutatorElement_mem_center a c) b
  calc
    ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by group
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b) * b⁻¹ := by rw [hac]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by group

@[simp]
theorem commutatorPairing_mul_left (hG : IsSpecial G) (a b c : G) :
    hG.commutatorPairing (a * b) c =
      hG.commutatorPairing a c * hG.commutatorPairing b c := by
  apply Subtype.ext
  exact hG.commutatorElement_mul_left a b c

@[simp]
theorem commutatorPairing_mul_right (hG : IsSpecial G) (a b c : G) :
    hG.commutatorPairing a (b * c) =
      hG.commutatorPairing a b * hG.commutatorPairing a c := by
  apply Subtype.ext
  exact hG.commutatorElement_mul_right a b c

@[simp]
theorem commutatorPairing_self (hG : IsSpecial G) (x : G) :
    hG.commutatorPairing x x = 1 := by
  apply Subtype.ext
  simp [commutatorPairing]

/-- Pairing with every element trivially is equivalent to belonging to the
center. -/
theorem commutatorPairing_left_radical (hG : IsSpecial G) (x : G) :
    (∀ y : G, hG.commutatorPairing x y = 1) ↔ x ∈ Subgroup.center G := by
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact (commutatorElement_eq_one_iff_commute.mp
      (congrArg Subtype.val (hx y))).eq.symm
  · intro hx y
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp hx y).symm

end IsSpecial

end Submission.OddOrder.MathlibSupport
