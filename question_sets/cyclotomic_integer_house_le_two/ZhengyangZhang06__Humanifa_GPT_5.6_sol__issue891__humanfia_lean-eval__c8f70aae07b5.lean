import Mathlib
import Submission.Helpers

open NumberField

namespace Submission

theorem cyclotomic_integer_house_le_two {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K) :
    house β ≤ 2 →
      house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) := by
  intro hβ_le
  by_cases hβ_eq : house β = 2
  · exact Or.inl hβ_eq
  right
  have hβ_lt : house β < 2 := lt_of_le_of_ne hβ_le hβ_eq
  obtain ⟨φ, hφ_norm⟩ := Helpers.exists_embedding_norm_eq_house β
  have hφ_real : ((φ β).re : ℂ) = φ β := Complex.conj_eq_iff_re.mp (hβ_real φ)
  by_cases hφ_nonneg : 0 ≤ (φ β).re
  · have hφ_re : (φ β).re = house β := by
      rw [← hφ_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ_nonneg] at hφ_norm
      exact hφ_norm
    apply Helpers.house_eq_two_mul_cos_of_embedding_eq_house hβ_int hβ_real hβ_lt φ
    rw [← hφ_real, hφ_re]
  · have hφ_nonpos : (φ β).re ≤ 0 := le_of_not_ge hφ_nonneg
    have hφ_re : -(φ β).re = house β := by
      rw [← hφ_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hφ_nonpos] at hφ_norm
      exact hφ_norm
    have hhouse_neg : house (-β) = house β := by simp [house]
    have hneg_lt : house (-β) < 2 := by rwa [hhouse_neg]
    rw [← hhouse_neg]
    apply Helpers.house_eq_two_mul_cos_of_embedding_eq_house hβ_int.neg
      ((NumberField.maximalRealSubfield K).neg_mem hβ_real) hneg_lt φ
    rw [map_neg, ← hφ_real]
    exact_mod_cast hφ_re.trans hhouse_neg.symm

end Submission
