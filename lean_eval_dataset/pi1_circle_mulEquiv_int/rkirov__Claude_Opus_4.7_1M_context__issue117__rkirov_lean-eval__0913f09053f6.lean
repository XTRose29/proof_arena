/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: pi1_circle_mulEquiv_int
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 0913f09053f62427808102039c0b7f7764633291
issue_number: 117
-/
import Mathlib
import Submission.Helpers

namespace Submission

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
  ⟨Submission.Helpers.pi1CircleMulEquivIntAux⟩

end Submission
