import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.RadonTransform
open MeasureTheory Real Complex

namespace Submission

theorem radon_can_be_diagonalized_and_pseudo_inverted :
    (∀ φ : SchwartzMap (ℝ × ℝ) ℂ, ∀ θ k : ℝ,
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
          fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ)) ∧
    (∃ Rinv : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
        ∀ φ : SchwartzMap (ℝ × ℝ) ℂ,
          Rinv (radon (φ : ℝ × ℝ → ℂ)) = (φ : ℝ × ℝ → ℂ)) := by
  classical
  refine ⟨Helpers.fourier_slice, ?_⟩
  let Rinv : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ) := fun g =>
    if h : ∃ φ : SchwartzMap (ℝ × ℝ) ℂ,
        radon (φ : ℝ × ℝ → ℂ) = g then
      (Classical.choose h : SchwartzMap (ℝ × ℝ) ℂ)
    else
      0
  refine ⟨Rinv, fun φ => ?_⟩
  have hφ : ∃ ψ : SchwartzMap (ℝ × ℝ) ℂ,
      radon (ψ : ℝ × ℝ → ℂ) = radon (φ : ℝ × ℝ → ℂ) := ⟨φ, rfl⟩
  simpa only [Rinv, dif_pos hφ] using
    Helpers.radon_injective (Classical.choose hφ) φ (Classical.choose_spec hφ)

end Submission
