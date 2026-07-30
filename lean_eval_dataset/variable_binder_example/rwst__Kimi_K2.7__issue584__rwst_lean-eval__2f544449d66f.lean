import Mathlib
import Submission.Helpers

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Submission

theorem variable_binder_example (A : Matrix n n ℚ) (hA : A.IsHermitian) :
    A.trace = ∑ i, A i i := by
  have _ := hA
  have _ := (inferInstance : DecidableEq n)
  simp [Matrix.trace]

end Submission
