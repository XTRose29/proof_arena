/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: vonNeumann_doubleCommutant_tfae
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 945a650516082dfeba205b6b4c2ffab1515b0669
issue_number: 178
-/
import Mathlib
import Submission.Helpers

namespace Submission

open Submission.Helpers

theorem vonNeumann_doubleCommutant_tfae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    List.TFAE
      [ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S
      , IsClosed
          (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H)))
      , IsClosed
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
            (S : Set (H →L[ℂ] H))) ] := by
  tfae_have 1 → 2 := double_commutant_imp_wot_closed S
  tfae_have 2 → 3 := wot_closed_imp_pwconv_closed S
  tfae_have 3 → 1 := pwconv_closed_imp_double_commutant S
  tfae_finish

end Submission
