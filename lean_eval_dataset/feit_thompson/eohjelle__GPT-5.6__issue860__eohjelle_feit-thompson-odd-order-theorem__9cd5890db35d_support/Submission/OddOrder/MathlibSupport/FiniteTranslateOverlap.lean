import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
Double counting finite-set overlaps under group translation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [DecidableEq A]

/-- Number of elements of `S` which remain in `S` after translation by
`a`. -/
def translateOverlap (S : Finset A) (a : A) : Nat :=
  (S.filter fun x => x + a ∈ S).card

@[simp]
theorem translateOverlap_zero (S : Finset A) :
    translateOverlap S 0 = S.card := by
  simp [translateOverlap]

variable [Fintype A]

/-- Summing all translate overlaps counts every ordered pair of elements
of `S` exactly once. -/
theorem sum_translateOverlap (S : Finset A) :
    ∑ a : A, translateOverlap S a = S.card ^ 2 := by
  calc
    ∑ a : A, translateOverlap S a =
        ∑ a : A, ∑ x ∈ S, if x + a ∈ S then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp [translateOverlap]
    _ = ∑ x ∈ S, ∑ a : A, if x + a ∈ S then (1 : Nat) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _x ∈ S, S.card := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        (∑ a : A, if x + a ∈ S then (1 : Nat) else 0) =
            (∑ y : A, if y ∈ S then (1 : Nat) else 0) :=
          Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
        _ = S.card := by simp
    _ = S.card ^ 2 := by simp [pow_two]

/-- If every nonzero translate overlaps `S` in exactly all but one
element, then the ambient finite group has one more element than `S`. -/
theorem fintype_card_eq_card_add_one_of_translateOverlap
    (S : Finset A) (hS : 1 < S.card)
    (hoverlap : ∀ a : A, a ≠ 0 -> translateOverlap S a = S.card - 1) :
    Fintype.card A = S.card + 1 := by
  have hnonzero :
      ∑ a ∈ (Finset.univ.erase (0 : A)), translateOverlap S a =
        (Fintype.card A - 1) * (S.card - 1) := by
    rw [Finset.sum_const_nat (m := S.card - 1)]
    · simp
    · intro a ha
      exact hoverlap a (Finset.ne_of_mem_erase ha)
  have hsplit :
      ∑ a : A, translateOverlap S a =
        S.card + (Fintype.card A - 1) * (S.card - 1) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : A)), add_comm,
      translateOverlap_zero, hnonzero]
  have hcount := sum_translateOverlap S
  rw [hsplit] at hcount
  have hA : 1 ≤ Fintype.card A :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hScard : 1 ≤ S.card := Nat.le_of_lt hS
  have hA_sub : Fintype.card A - 1 + 1 = Fintype.card A :=
    Nat.sub_add_cancel hA
  have hS_sub : S.card - 1 + 1 = S.card :=
    Nat.sub_add_cancel hScard
  nlinarith

/-- A subset avoiding zero and containing all but one element is exactly
the complement of zero. -/
theorem eq_univ_erase_zero_of_fintype_card_eq_card_add_one
    (S : Finset A) (hzero : 0 ∉ S)
    (hcard : Fintype.card A = S.card + 1) :
    S = Finset.univ.erase 0 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun h => hzero (h ▸ hx), Finset.mem_univ x⟩
  · simp [hcard]

/-- Constant all-but-one overlap, together with omission of zero, forces
`S` to consist of every nonzero group element. -/
theorem eq_univ_erase_zero_of_translateOverlap
    (S : Finset A) (hzero : 0 ∉ S) (hS : 1 < S.card)
    (hoverlap : ∀ a : A, a ≠ 0 -> translateOverlap S a = S.card - 1) :
    S = Finset.univ.erase 0 :=
  eq_univ_erase_zero_of_fintype_card_eq_card_add_one S hzero
    (fintype_card_eq_card_add_one_of_translateOverlap S hS hoverlap)

end Submission.OddOrder.MathlibSupport
