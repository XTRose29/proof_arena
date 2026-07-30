import ChallengeDeps
import Submission.Convergence

open LeanEval.Dynamics
open scoped ContDiff

namespace Submission

theorem kam_invariant_curve (α : ℝ) (_hα : IsDiophantine α)
    (f : ℝ → ℝ)
    (_hf_analytic : AnalyticOnNhd ℝ f Set.univ)
    (_hf_per : Function.Periodic f 1)
    (_hf_nonconst : ¬ ∃ k : ℝ, ∀ x, f x = k)
    (_hf_mean : ∫ x in (0 : ℝ)..1, f x = 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, |c| < c₀ →
      ∃ q : ℝ → ℝ,
        ContDiff ℝ ∞ q ∧ StrictMono q ∧
        Function.Periodic (fun t => q t - t) 1 ∧
        ∀ t : ℝ, q (t + α) - 2 * q t + q (t - α) = c * f (q t) := by
  exact Majorant.exists_invariant_curve_of_small_c
    α _hα f _hf_analytic _hf_per _hf_mean

end Submission
