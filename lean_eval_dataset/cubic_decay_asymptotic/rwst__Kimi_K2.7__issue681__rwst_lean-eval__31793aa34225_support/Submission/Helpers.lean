import Mathlib

namespace Submission.Helpers

/-- If `y` has derivative `y'` at `t` and `y t ≠ 0`, then `1 / y²` has derivative
`-2 * y' / y t ^ 3` at `t`. -/
lemma hasDerivAt_inv_sq {y : ℝ → ℝ} {y' t : ℝ} (hy : HasDerivAt y y' t) (hyne : y t ≠ 0) :
    HasDerivAt (fun s => 1 / y s ^ 2) (-2 * y' / y t ^ 3) t := by
  have h1 : HasDerivAt (fun s => y s ^ 2) (2 * y t * y') t := by
    have h := HasDerivAt.pow hy 2
    simp at h ⊢
    exact h
  have h2 : HasDerivAt (fun s => (y s ^ 2)⁻¹) (-(2 * y t * y') / (y t ^ 2) ^ 2) t := by
    apply HasDerivAt.inv
    · exact h1
    · simp [hyne]
  have h_eq : (fun s => 1 / y s ^ 2) = (fun s => (y s ^ 2)⁻¹) := by
    funext s
    field_simp
  rw [h_eq]
  convert h2 using 1
  field_simp [hyne]

end Submission.Helpers
