/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: def_hole_example
user: sqrt-of-2
model: Gemini 3.1 Pro
submission_repo: sqrt-of-2/d3b2243cdee91633019d74eec5d7fd27
submission_ref: 2e355be1db4f0c8ec978bcf1fc51c1e86078ac3e
issue_number: 184
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
theorem foo_def : foo = 37 := rfl

end Submission
