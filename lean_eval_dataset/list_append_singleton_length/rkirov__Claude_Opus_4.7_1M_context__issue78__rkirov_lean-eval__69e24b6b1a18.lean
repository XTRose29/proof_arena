/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 69e24b6b1a18117485ef55663d4773900655e033
issue_number: 78
-/
import Mathlib
import Submission.Helpers

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := rfl

end Submission
