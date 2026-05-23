/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: def_hole_example
user: sqrt-of-2
model: Leanstral-2603
submission_repo: sqrt-of-2/0a88184bf14c650bff60204d9cc36726
submission_ref: 11bb81e1ee852ad24b797ac8e5980d43a5da6524
issue_number: 202
-/
import Mathlib
/-!
Minimal example exercising the def-hole / multi-hole eval-problem pipeline.

A `def` and a `theorem` referring to it, both `sorry`. A submission
defines `Submission.foo := 37` and proves `Submission.foo_def`; comparator
should accept it.
-/

namespace Submission

def foo : Nat := 37
theorem foo_def : foo = 37 := by
  rfl

end Submission
