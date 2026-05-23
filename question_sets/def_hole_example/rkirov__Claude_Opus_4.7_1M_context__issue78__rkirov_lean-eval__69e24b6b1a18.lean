/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: def_hole_example
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 69e24b6b1a18117485ef55663d4773900655e033
issue_number: 78
-/
import Mathlib
import Submission.Helpers
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
