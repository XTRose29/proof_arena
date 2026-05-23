/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: rkirov
model: Claude Opus 4.7
submission_repo: rkirov/lean-eval
submission_ref: 212bebf172ea4a345071d0b3fc40a978515d09c6
issue_number: 21
-/
import Mathlib
import Submission.Helpers

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := rfl

end Submission
