/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: sqrt-of-2
model: Aristotle (Harmonic)
submission_repo: sqrt-of-2/bc28c5caaf5a4a74e072c4c3a90b4c9f
submission_ref: 86e25bc4e24dad53ee2bd2e50805b750b003c27b
issue_number: 224
-/
import Mathlib

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  -- The length of the list [1, 2, 3] is indeed 3.
  simp [List.length]

end Submission
