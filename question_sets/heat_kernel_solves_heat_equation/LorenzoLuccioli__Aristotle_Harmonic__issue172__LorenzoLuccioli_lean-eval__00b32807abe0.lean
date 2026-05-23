import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.ODE
open Real MeasureTheory Filter
open Submission.Helpers

namespace Submission

private lemma heat_eq_heat' (f : ℝ → ℝ) (t x : ℝ) :
    heatSolution f t x = heatSolution' f t x := by
  simp [heatSolution, heatSolution']

theorem heat_kernel_solves_heat_equation (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    (∀ x : ℝ,
        Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  have hee : ∀ t x, heatSolution f t x = heatSolution' f t x := heat_eq_heat' f
  constructor
  · intro t ht x
    refine ⟨fun z => ((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2) *
        ∫ y : ℝ, -(z - y) / (2 * t) * exp (-((z - y) ^ 2) / (4 * t)) * f y,
      ((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2) *
        ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
          exp (-((x - y) ^ 2) / (4 * t)) * f y,
      ?_, ?_, ?_⟩
    · intro z
      have hsimp : (fun z => heatSolution f t z) = (fun z =>
          ((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2) *
            ∫ y : ℝ, exp (-((z - y) ^ 2) / (4 * t)) * f y) := by
        ext w; simp [heatSolution, ht]
      rw [hsimp]
      exact (hasDerivAt_heat_integral_x f hf_cont hf_bdd t ht z).const_mul _
    · exact (hasDerivAt_heat_integral_xx f hf_cont hf_bdd t ht x).const_mul _
    · have : HasDerivAt (fun s => heatSolution' f s x)
          (((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2) *
            ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
              exp (-((x - y) ^ 2) / (4 * t)) * f y) t :=
        heat_time_deriv_eq_space_deriv f hf_cont hf_bdd t ht x
      rwa [show (fun s => heatSolution f s x) = (fun s => heatSolution' f s x) from
        funext (fun s => hee s x)]
  · intro x
    have : Tendsto (fun t : ℝ => heatSolution' f t x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) :=
      heat_initial_condition f hf_cont hf_bdd x
    rwa [show (fun t : ℝ => heatSolution f t x) = (fun t : ℝ => heatSolution' f t x) from
      funext (fun t => hee t x)]

end Submission
