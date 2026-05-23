import ChallengeDeps
import Submission.Helpers

open LeanEval.KnotTheory

namespace Submission

theorem exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ :=
  ⟨Submission.Helpers.theUnlink, Submission.Helpers.theHopfLink,
   Submission.Helpers.unlink_not_isotopic_hopf⟩

end Submission
