/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: list_append_singleton_length
user: kim-em
model: Aristotle (Harmonic)
submission_repo: kim-em/87ef9e588d516f7901475e64a77b350d
submission_ref: e33579d39754d2fc53e00f725191eb3a17f495f8
issue_number: 59
-/
namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  decide

end Submission
