/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: heat_kernel_solves_heat_equation
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 7984d665265a2bde32e64599842ea98d1d7991b1
issue_number: 39
-/
import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.ODE
open Real MeasureTheory

namespace Submission

theorem heat_kernel_solves_heat_equation (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    -- The PDE on (0, ∞) × ℝ.
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    -- Initial condition recovered as a one-sided limit at t = 0.
    (∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) :=
  Submission.Helpers.heat_kernel_solves_heat_equation f hf_cont hf_bdd

end Submission
