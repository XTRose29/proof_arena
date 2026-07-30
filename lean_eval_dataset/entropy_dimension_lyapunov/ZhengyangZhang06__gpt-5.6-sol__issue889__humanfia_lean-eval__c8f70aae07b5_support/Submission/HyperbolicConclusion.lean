import Submission.CenteredDiameterBridge
import Submission.CenteredOrbitBridge

namespace Submission.Helpers

open LeanEval.Dynamics

lemma eq_dim_mul_rate_of_approx_bounds
    {entropy dim rate : ℝ} (hdim : 0 ≤ dim)
    (hupper : ∀ epsilon, 0 < epsilon →
      entropy - epsilon ≤ dim * (rate + epsilon))
    (hlower : ∀ epsilon, 0 < epsilon →
      dim * (rate - epsilon) ≤ entropy) :
    entropy = dim * rate := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    let epsilon := (entropy - dim * rate) / (2 * (dim + 1))
    have hdenom : 0 < 2 * (dim + 1) := by positivity
    have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hlt) hdenom
    have h := hupper epsilon hepsilon
    dsimp [epsilon] at h
    have hdim_one : 0 < dim + 1 := by linarith
    field_simp [hdim_one.ne'] at h
    nlinarith
  · apply le_of_not_gt
    intro hlt
    let epsilon := (dim * rate - entropy) / (2 * (dim + 1))
    have hdenom : 0 < 2 * (dim + 1) := by positivity
    have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hlt) hdenom
    have h := hlower epsilon hepsilon
    dsimp [epsilon] at h
    have hdim_one : 0 < dim + 1 := by linarith
    field_simp [hdim_one.ne'] at h
    nlinarith

lemma young_identity_of_approx_hyperbolic_bounds
    {entropy dim lam1 lam2 : ℝ}
    (hdim : 0 ≤ dim)
    (hupper : ∀ epsilon, 0 < epsilon →
      entropy - epsilon ≤ dim * (hyperbolicRate lam1 lam2 + epsilon))
    (hlower : ∀ epsilon, 0 < epsilon →
      dim * (hyperbolicRate lam1 lam2 - epsilon) ≤ entropy) :
    entropy = dim * harmonicMeanLyapunov lam1 lam2 / 2 := by
  rw [eq_dim_mul_rate_of_approx_bounds hdim hupper hlower]
  rw [hyperbolicRate_eq_harmonicMean_div_two]
  ring

end Submission.Helpers
