import ChallengeDeps
import Submission.Sard

open LeanEval.Geometry.RegularValue
open MeasureTheory
open scoped ContDiff

namespace Submission

theorem regular_value_ae {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ c ∂(volume : Measure ℝ), IsRegularValue f c := by
  classical
  rw [ae_iff]
  apply measure_mono_null _ (Helpers.measure_image_criticalSet_eq_zero f hf)
  intro c hc
  change ¬IsRegularValue f c at hc
  simp only [IsRegularValue] at hc
  push Not at hc
  obtain ⟨x, hfx, hx⟩ := hc
  exact ⟨x, hx, hfx⟩

end Submission
