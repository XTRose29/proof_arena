import Submission.IntegralVertical

open MeasureTheory intervalIntegral
open scoped Interval Real

noncomputable section

namespace Submission.Helpers

lemma integral_boundary_square_inv (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ in -R..R, ((x : ℂ) - R * Complex.I)⁻¹) -
        (∫ x : ℝ in -R..R, ((x : ℂ) + R * Complex.I)⁻¹) +
        Complex.I * (∫ y : ℝ in -R..R, ((R : ℂ) + y * Complex.I)⁻¹) -
        Complex.I * (∫ y : ℝ in -R..R, ((-R : ℂ) + y * Complex.I)⁻¹) =
      2 * Real.pi * Complex.I := by
  rw [integral_inv_horizontal R hR, integral_inv_horizontal_upper R hR,
    integral_inv_vertical_right R hR, integral_inv_vertical_left R hR]
  ring

end Submission.Helpers
