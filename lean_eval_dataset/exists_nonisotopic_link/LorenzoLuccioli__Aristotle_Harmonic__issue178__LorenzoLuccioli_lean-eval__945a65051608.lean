/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: exists_nonisotopic_link
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 945a650516082dfeba205b6b4c2ffab1515b0669
issue_number: 178
-/
import ChallengeDeps
import Submission.Helpers

open LeanEval.KnotTheory

namespace Submission

theorem exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ :=
  ⟨Submission.Helpers.theUnlink, Submission.Helpers.theHopfLink,
   Submission.Helpers.unlink_not_isotopic_hopf⟩

end Submission
