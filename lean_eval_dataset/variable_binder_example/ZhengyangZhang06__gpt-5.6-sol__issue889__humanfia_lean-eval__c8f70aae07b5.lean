import Mathlib
import Submission.Helpers

variable {n : Type*} [Fintype n] [instDecidableEq : DecidableEq n]

namespace Submission

private theorem withDecidableEq {m : Type*} (_ : DecidableEq m) {p : Prop} (hp : p) : p :=
  hp

include instDecidableEq in
theorem variable_binder_example (A : Matrix n n ℚ) (hA : A.IsHermitian) :
    A.trace = ∑ i, A i i := by
  apply withDecidableEq instDecidableEq
  rw [← hA]
  rfl

end Submission
