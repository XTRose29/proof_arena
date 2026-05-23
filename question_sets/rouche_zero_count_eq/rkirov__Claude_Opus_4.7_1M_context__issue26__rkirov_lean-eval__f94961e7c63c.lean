/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: rouche_zero_count_eq
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: f94961e7c63cc81d6a0e7990322d3a5eb236d6ec
issue_number: 26
-/
import Mathlib
import Submission.Helpers

open MeromorphicOn

namespace Submission

theorem rouche_zero_count_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) :=
  Submission.Helpers.rouche_zero_count_eq hR hf hg hbound

end Submission
