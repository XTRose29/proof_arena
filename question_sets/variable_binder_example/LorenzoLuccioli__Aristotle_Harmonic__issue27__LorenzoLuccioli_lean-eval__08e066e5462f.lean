import Mathlib
import Submission.Helpers

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Submission

omit [DecidableEq n] in
theorem variable_binder_example (A : Matrix n n ℚ) (hA : A.IsHermitian) :
    A.trace = ∑ i, A i i := by
  have _ := hA
  simp [Matrix.trace, Matrix.diag]

end Submission
