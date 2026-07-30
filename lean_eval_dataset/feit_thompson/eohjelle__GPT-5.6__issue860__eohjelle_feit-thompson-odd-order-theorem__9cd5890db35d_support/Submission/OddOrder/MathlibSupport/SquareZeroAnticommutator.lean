import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Commute.Defs

/-!
Commutation identities for square-zero elements.

These identities are the algebraic core of the central operator constructed
from two quadratic elements in `BGappendixAB.odd_p_stable`.
-/

namespace Submission.OddOrder.MathlibSupport

variable {R : Type*} [Semiring R]

/-- The anticommutator of two elements. -/
def anticommutator (x y : R) : R := x * y + y * x

theorem commute_anticommutator_left {x y : R} (hx : x * x = 0) :
    Commute x (anticommutator x y) := by
  rw [commute_iff_eq]
  calc
    x * anticommutator x y = x * (x * y) + x * (y * x) := by
      rw [anticommutator, mul_add]
    _ = (x * x) * y + x * (y * x) := by rw [mul_assoc x x y]
    _ = x * (y * x) := by rw [hx, zero_mul, zero_add]
    _ = x * (y * x) + y * (x * x) := by rw [hx, mul_zero, add_zero]
    _ = anticommutator x y * x := by rw [anticommutator, add_mul, mul_assoc, mul_assoc]

theorem commute_anticommutator_right {x y : R} (hy : y * y = 0) :
    Commute y (anticommutator x y) := by
  rw [commute_iff_eq]
  calc
    y * anticommutator x y = y * (x * y) + y * (y * x) := by
      rw [anticommutator, mul_add]
    _ = y * (x * y) + (y * y) * x := by rw [mul_assoc y y x]
    _ = y * (x * y) := by rw [hy, zero_mul, add_zero]
    _ = x * (y * y) + y * (x * y) := by rw [hy, mul_zero, zero_add]
    _ = anticommutator x y * y := by rw [anticommutator, add_mul, mul_assoc, mul_assoc]

end Submission.OddOrder.MathlibSupport
