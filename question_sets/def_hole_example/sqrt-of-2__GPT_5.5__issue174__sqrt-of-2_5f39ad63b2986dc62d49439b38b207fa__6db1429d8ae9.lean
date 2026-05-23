/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: def_hole_example
user: sqrt-of-2
model: GPT 5.5
submission_repo: sqrt-of-2/5f39ad63b2986dc62d49439b38b207fa
submission_ref: 6db1429d8ae9398cb5e0f62e991caad9eb848659
issue_number: 174
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
