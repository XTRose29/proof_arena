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
  intro hle
  rcases eq_or_ne (house β) 2 with h | h
  · exact Or.inl h
  · right
    rcases eq_or_ne β 0 with rfl | hβ_ne
    · exact ⟨2, by omega, by simp [house, Real.cos_pi_div_two]⟩
    · exact Submission.Helpers.house_eq_cos_core n hβ_int hβ_real hβ_ne (lt_of_le_of_ne hle h)

end Submission
