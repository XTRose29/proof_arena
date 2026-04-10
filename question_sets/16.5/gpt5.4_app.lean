/-
Problem 5.

Let `a, b, c` be three distinct elements in a division ring `D`.
Show that the `3 × 3` Vandermonde matrix

    V(a,b,c) = | 1   1   1 |
               | a   b   c |
               | a²  b²  c² |

is not invertible over `D` if

    (b - a) b (b - a)⁻¹ = (c - a) c (c - a)⁻¹.

We formalize this by constructing an explicit nonzero vector in the kernel,
and then proving the matrix is not a unit.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

open Matrix

noncomputable section

namespace Vandermonde3

variable {D : Type*} [DivisionRing D]

/-- The `3 × 3` Vandermonde matrix attached to `a,b,c`. -/
def V (a b c : D) : Matrix (Fin 3) (Fin 3) D :=
  fun i j =>
    match i, j with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 0 => a
    | 1, 1 => b
    | 1, 2 => c
    | 2, 0 => a * a
    | 2, 1 => b * b
    | 2, 2 => c * c

/-- The explicit kernel vector from the usual handwritten proof. -/
def kernelVec (a b c : D) : Fin 3 → D
  | 0 => 1 - (b - a)⁻¹ * (c - a)
  | 1 => (b - a)⁻¹ * (c - a)
  | 2 => -1

lemma kernelVec_ne_zero (a b c : D) : kernelVec a b c ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Fin 3)
  simp [kernelVec] at h2

lemma expr1_zero
    (a b c : D)
    (hba : b ≠ a) :
    let x : D := (b - a)⁻¹ * (c - a)
    a * (1 - x) + b * x + c * (-1 : D) = 0 := by
  let x : D := (b - a)⁻¹ * (c - a)
  have hb : b = a + (b - a) := by
    rw [add_comm, sub_add_cancel]
  have hbx : (b - a) * x = c - a := by
    dsimp [x]
    rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hba), one_mul]
  sorry

lemma expr2_zero
    (a b c : D)
    (hba : b ≠ a)
    (hca : c ≠ a)
    (hconj : (b - a) * b * (b - a)⁻¹ = (c - a) * c * (c - a)⁻¹) :
    let x : D := (b - a)⁻¹ * (c - a)
    a * a * (1 - x) + b * b * x + c * c * (-1 : D) = 0 := by
  let x : D := (b - a)⁻¹ * (c - a)

  have h1 : a * (1 - x) + b * x + c * (-1 : D) = 0 := by
    simpa [x] using expr1_zero a b c hba

  have hb : b = a + (b - a) := by
    rw [add_comm, sub_add_cancel]

  have hbbx : b * (b * x) = a * (b * x) + (b - a) * (b * x) := by
    rw [hb, add_mul]; simp

  have hmain : (b - a) * (b * x) = (c - a) * c := by
    dsimp [x]
    calc
      (b - a) * (b * ((b - a)⁻¹ * (c - a)))
          = ((b - a) * b * (b - a)⁻¹) * (c - a) := by
              simp [mul_assoc]
      _ = ((c - a) * c * (c - a)⁻¹) * (c - a) := by rw [hconj]
      _ = (c - a) * (c * ((c - a)⁻¹ * (c - a))) := by
            rw [mul_assoc, mul_assoc]
      _ = (c - a) * (c * 1) := by
            rw [inv_mul_cancel₀ (sub_ne_zero.mpr hca)]
      _ = (c - a) * c := by
            rw [mul_one]

  have hcpart : a * (c * (-1 : D)) - (c - a) * c = c * c * (-1 : D) := by
    sorry

  sorry

lemma V_mul_kernelVec_eq_zero
    (a b c : D)
    (hba : b ≠ a)
    (hca : c ≠ a)
    (hconj : (b - a) * b * (b - a)⁻¹ = (c - a) * c * (c - a)⁻¹) :
    (V a b c).mulVec (kernelVec a b c) = 0 := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, V, kernelVec, Fin.sum_univ_three]
  · simpa [Matrix.mulVec, dotProduct, V, kernelVec, Fin.sum_univ_three]
      using expr1_zero a b c hba
  · simpa [Matrix.mulVec, dotProduct, V, kernelVec, Fin.sum_univ_three]
      using expr2_zero a b c hba hca hconj

theorem not_isUnit_of_conj_eq
    (a b c : D)
    (hba : b ≠ a)
    (hca : c ≠ a)
    (hconj : (b - a) * b * (b - a)⁻¹ = (c - a) * c * (c - a)⁻¹) :
    ¬ IsUnit (V a b c) := by
  intro hU
  rcases hU with ⟨U, rfl⟩
  have hk : ((↑U : Matrix (Fin 3) (Fin 3) D)).mulVec (kernelVec a b c) = 0 := by
    simpa using V_mul_kernelVec_eq_zero a b c hba hca hconj
  have hz : kernelVec a b c = 0 := by
    calc
      kernelVec a b c
          = (1 : Matrix (Fin 3) (Fin 3) D).mulVec (kernelVec a b c) := by simp
      _ = ((((↑(U⁻¹)) : Matrix (Fin 3) (Fin 3) D) ⬝ ((↑U) : Matrix (Fin 3) (Fin 3) D))).mulVec
            (kernelVec a b c) := by simp
      _ = ((↑(U⁻¹)) : Matrix (Fin 3) (Fin 3) D).mulVec
            (((↑U) : Matrix (Fin 3) (Fin 3) D).mulVec (kernelVec a b c)) := by
            rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hk]; simp
  exact kernelVec_ne_zero a b c hz

end Vandermonde3
