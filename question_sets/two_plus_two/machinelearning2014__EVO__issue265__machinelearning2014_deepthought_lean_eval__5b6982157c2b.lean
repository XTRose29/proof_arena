/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: two_plus_two
user: machinelearning2014
model: EVO
submission_repo: machinelearning2014/deepthought_lean_eval
submission_ref: 5b6982157c2bda310624556e6f0fef74f559c9e8
issue_number: 265
-/
import Mathlib
import Submission.Helpers

namespace Submission

open Submission.Helpers

  theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by
    rfl

end Submission
