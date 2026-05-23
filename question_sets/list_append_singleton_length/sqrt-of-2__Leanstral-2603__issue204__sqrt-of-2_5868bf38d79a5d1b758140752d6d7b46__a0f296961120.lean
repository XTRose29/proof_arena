/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: sqrt-of-2
model: Leanstral-2603
submission_repo: sqrt-of-2/5868bf38d79a5d1b758140752d6d7b46
submission_ref: a0f2969611204747b87ce949bd27f1eb2d48df84
issue_number: 204
-/
import Mathlib

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  rfl

end Submission
