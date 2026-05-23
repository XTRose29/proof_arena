/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: def_hole_example
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 00b32807abe0d286c4638daf888c739e1bb4b90c
issue_number: 172
-/
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
