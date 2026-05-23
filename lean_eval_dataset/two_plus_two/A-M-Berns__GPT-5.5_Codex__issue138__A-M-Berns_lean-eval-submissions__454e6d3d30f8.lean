/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: two_plus_two
user: A-M-Berns
model: GPT-5.5 Codex
submission_repo: A-M-Berns/lean-eval-submissions
submission_ref: 454e6d3d30f84ca63b50e3b2e8aad58ae04cf999
issue_number: 138
-/
import Mathlib
import Submission.Helpers

namespace Submission

theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by
  norm_num

end Submission
