/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: pi1_circle_mulEquiv_int
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 00b32807abe0d286c4638daf888c739e1bb4b90c
issue_number: 172
-/
import Mathlib
import Submission.Helpers

namespace Submission

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
  Submission.Helpers.main_result

end Submission
