/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: oppenheim_inequality
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 00b32807abe0d286c4638daf888c739e1bb4b90c
issue_number: 172
-/
import Mathlib
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det :=
  Submission.Helpers.oppenheim_general hA hB

end Submission
