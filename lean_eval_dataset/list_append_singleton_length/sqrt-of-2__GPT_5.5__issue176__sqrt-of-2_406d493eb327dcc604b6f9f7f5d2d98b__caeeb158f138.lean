/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: sqrt-of-2
model: GPT 5.5
submission_repo: sqrt-of-2/406d493eb327dcc604b6f9f7f5d2d98b
submission_ref: caeeb158f138cb943d2242be623c340ba4658dbc
issue_number: 176
-/
import Mathlib

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  rfl

end Submission
