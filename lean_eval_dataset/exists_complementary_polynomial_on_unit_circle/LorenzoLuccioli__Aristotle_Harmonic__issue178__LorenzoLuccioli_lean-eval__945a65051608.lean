/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: exists_complementary_polynomial_on_unit_circle
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 945a650516082dfeba205b6b4c2ffab1515b0669
issue_number: 178
-/
import Mathlib
import Submission.Helpers

open Polynomial

namespace Submission

theorem exists_complementary_polynomial_on_unit_circle (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 :=
  Submission.Helpers.exists_complementary_core P hP

end Submission
