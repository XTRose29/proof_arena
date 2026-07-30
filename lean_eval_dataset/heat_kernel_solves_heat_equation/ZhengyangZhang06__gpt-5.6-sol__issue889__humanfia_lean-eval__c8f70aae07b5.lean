import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.ODE
open Real MeasureTheory
open Submission.Helpers

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
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  obtain ⟨M, hM⟩ := hf_bdd
  constructor
  · intro t ht x
    let ux : ℝ → ℝ := fun z ↦ ∫ y, heatKernelX t z y * f y
    let uxx : ℝ := ∫ y, heatKernelXX t x y * f y
    refine ⟨ux, uxx, ?_, ?_, ?_⟩
    · intro y
      dsimp only [ux]
      exact hasDerivAt_heatSolution_space f hf_cont hM ht
    · dsimp only [ux, uxx]
      exact (integral_heatKernelX_space_deriv f hf_cont hM ht).2
    · dsimp only [uxx]
      exact hasDerivAt_heatSolution_time f hf_cont hM ht
  · intro x
    exact tendsto_heatSolution_zero f hf_cont ⟨M, hM⟩ x

end Submission
