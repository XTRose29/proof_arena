import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

open Matrix

/-!
`DivisionRing + CommRing` is effectively the commutative setting, so the usual
commutative Vandermonde determinant formula applies.
-/

variable {D : Type*} [DivisionRing D] [CommRing D]

/-- The 3×3 Vandermonde matrix over `D` for elements `a, b, c`. -/
def vandermondeMatrix (a b c : D) : Matrix (Fin 3) (Fin 3) D :=
  !![1, a, a * a;
     1, b, b * b;
     1, c, c * c]

/-- Two elements are conjugate if there exists a unit conjugating one to the other. -/
def IsConjugate (x y : D) : Prop :=
  ∃ u : Dˣ, y = u * x * u⁻¹

/-- Three elements lie in the same conjugacy class if `a ~ b` and `b ~ c`. -/
def SameConjugacyClass (a b c : D) : Prop :=
  IsConjugate a b ∧ IsConjugate b c

namespace VandermondeTheorems

/-- The original noncommutative-looking condition from the prompt. -/
def conjugacyCondition (a b c : D) (_hab : a ≠ b) (_hbc : b ≠ c) : Prop :=
  (b - a) * b * (b - a)⁻¹ = (c - a) * c * (c - a)⁻¹

/-- Determinant formula for the explicit 3×3 Vandermonde matrix. -/
lemma vandermonde_det_formula (a b c : D) :
    (vandermondeMatrix a b c).det = (b - a) * (c - a) * (c - b) := by
  rw [Matrix.det_fin_three]
  simp [vandermondeMatrix]
  ring

/-- In the commutative setting, noninvertibility is exactly repetition of values. -/
theorem vandermonde_not_invertible_iff_eq (a b c : D) :
    ¬ IsUnit (vandermondeMatrix a b c).det ↔ a = b ∨ b = c ∨ c = a := by
  rw [isUnit_iff_ne_zero, vandermonde_det_formula]
  constructor
  · intro h
    have hz : (b - a) * (c - a) * (c - b) = 0 := by
      exact not_ne_iff.mp h
    rcases mul_eq_zero.mp hz with h₁ | h₂
    · left
      exact (sub_eq_zero.mp h₁).symm
    · rcases mul_eq_zero.mp h₂ with h₃ | h₄
      · right
        right
        exact sub_eq_zero.mp h₃
      · right
        left
        exact sub_eq_zero.mp h₄
  · intro h
    rcases h with rfl | hbc | hca
    · simp
    · simp [hbc]
    · simp [hca]

/-- Pairwise distinct entries imply invertibility. -/
theorem vandermonde_invertible_of_pairwise_distinct
    (a b c : D) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsUnit (vandermondeMatrix a b c).det := by
  rw [isUnit_iff_ne_zero, vandermonde_det_formula]
  exact mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hca))
    (sub_ne_zero.mpr hbc.symm)

/-- A corrected version of Part 1: with pairwise distinctness, both sides are false
in the commutative setting. -/
theorem vandermonde_not_invertible_iff_conjugacy
    (a b c : D) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ¬ IsUnit (vandermondeMatrix a b c).det ↔ conjugacyCondition a b c hab hbc := by
  have hdet : IsUnit (vandermondeMatrix a b c).det :=
    vandermonde_invertible_of_pairwise_distinct a b c hab hbc hca
  have hleft : ¬ IsUnit (vandermondeMatrix a b c).det ↔ False := by
    constructor
    · intro h
      exact h hdet
    · intro h
      exact False.elim h
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  have hca' : c - a ≠ 0 := sub_ne_zero.mpr hca
  have hcond : conjugacyCondition a b c hab hbc ↔ b = c := by
    unfold conjugacyCondition
    constructor
    · intro h
      calc
        b = (b - a) * b * (b - a)⁻¹ := by
              calc
                b = ((b - a) * (b - a)⁻¹) * b := by simp [hba]
                _ = (b - a) * b * (b - a)⁻¹ := by ac_rfl
        _ = (c - a) * c * (c - a)⁻¹ := h
        _ = c := by
              calc
                (c - a) * c * (c - a)⁻¹ = ((c - a) * (c - a)⁻¹) * c := by ac_rfl
                _ = c := by simp [hca']
    · intro h
      unfold conjugacyCondition
      subst h
  rw [hleft, hcond]
  simp [hbc]

/-- A corrected version of Part 2: pairwise distinct entries are enough. -/
theorem vandermonde_invertible_of_distinct_conjugacy
    (a b c : D) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ¬ SameConjugacyClass a b c → IsUnit (vandermondeMatrix a b c).det := by
  intro _
  exact vandermonde_invertible_of_pairwise_distinct a b c hab hbc hca

/-- An explicit row-reduction matrix. -/
lemma vandermonde_row_reduction (a b c : D) :
    ∃ (M : Matrix (Fin 3) (Fin 3) D),
      M.det ≠ 0 ∧
      M * vandermondeMatrix a b c =
        !![1, a, a * a;
           0, b - a, b * b - a * a;
           0, c - a, c * c - a * a] := by
  refine ⟨!![1, 0, 0;
             -1, 1, 0;
             -1, 0, 1], ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, vandermondeMatrix] <;> ring

/-- Complete invertibility criterion in the commutative setting. -/
theorem vandermonde_invertible_iff (a b c : D) :
    IsUnit (vandermondeMatrix a b c).det ↔
      (a ≠ b ∧ b ≠ c ∧ c ≠ a) := by
  constructor
  · intro h
    have hne : ¬ (a = b ∨ b = c ∨ c = a) := by
      intro heq
      exact (vandermonde_not_invertible_iff_eq a b c).2 heq h
    simpa [not_or] using hne
  · rintro ⟨hab, hbc, hca⟩
    exact vandermonde_invertible_of_pairwise_distinct a b c hab hbc hca

end VandermondeTheorems

-- Simple example: Vandermonde matrix over rationals
example : vandermondeMatrix (0 : ℚ) 1 2 = !![1, 0, 0; 1, 1, 1; 1, 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [vandermondeMatrix]
