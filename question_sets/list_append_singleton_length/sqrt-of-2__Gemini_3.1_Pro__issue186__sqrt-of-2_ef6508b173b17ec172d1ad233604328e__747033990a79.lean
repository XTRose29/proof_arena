/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: sqrt-of-2
model: Gemini 3.1 Pro
submission_repo: sqrt-of-2/ef6508b173b17ec172d1ad233604328e
submission_ref: 747033990a7955e6fe58ab5984eb19d00d203252
issue_number: 186
-/
import Mathlib

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := rfl

end Submission
