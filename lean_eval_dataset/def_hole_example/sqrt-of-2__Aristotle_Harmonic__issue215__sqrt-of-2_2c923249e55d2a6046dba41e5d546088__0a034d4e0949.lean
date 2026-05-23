/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: def_hole_example
user: sqrt-of-2
model: Aristotle (Harmonic)
submission_repo: sqrt-of-2/2c923249e55d2a6046dba41e5d546088
submission_ref: 0a034d4e09490f54f2638baa1bdda8819c25bb3c
issue_number: 215
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
