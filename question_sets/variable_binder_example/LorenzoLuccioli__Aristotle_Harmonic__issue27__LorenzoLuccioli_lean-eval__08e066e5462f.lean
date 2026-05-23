/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: variable_binder_example
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 08e066e5462f5972e07e13ea45faf344ecad2797
issue_number: 27
-/
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
