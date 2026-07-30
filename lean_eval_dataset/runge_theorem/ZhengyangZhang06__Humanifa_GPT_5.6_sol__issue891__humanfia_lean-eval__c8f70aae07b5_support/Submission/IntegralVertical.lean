import Submission.IntegralUpper

open MeasureTheory intervalIntegral
open scoped Interval Real

noncomputable section

namespace Submission.Helpers

lemma integral_inv_vertical_right (R : ℝ) (hR : 0 < R) :
    (∫ y : ℝ in -R..R, ((R : ℂ) + y * Complex.I)⁻¹) =
      (Real.pi / 2 : ℂ) := by
  rw [show (fun y : ℝ => ((R : ℂ) + y * Complex.I)⁻¹) =
      fun y : ℝ => -Complex.I * (((y : ℂ) - R * Complex.I)⁻¹) by
    funext y
    have heq : (R : ℂ) + y * Complex.I =
        Complex.I * ((y : ℂ) - R * Complex.I) := by
      symm
      calc
        Complex.I * ((y : ℂ) - R * Complex.I) =
            Complex.I * (y : ℂ) - (R : ℂ) * (Complex.I * Complex.I) := by ring
        _ = (R : ℂ) + y * Complex.I := by rw [Complex.I_mul_I]; ring
    rw [heq, mul_inv_rev, Complex.inv_I]
    ring]
  rw [intervalIntegral.integral_const_mul, integral_inv_horizontal R hR]
  calc
    -Complex.I * ((Real.pi / 2 : ℂ) * Complex.I) =
        -(Real.pi / 2 : ℂ) * (Complex.I * Complex.I) := by ring
    _ = (Real.pi / 2 : ℂ) := by rw [Complex.I_mul_I]; ring

lemma integral_inv_vertical_left (R : ℝ) (hR : 0 < R) :
    (∫ y : ℝ in -R..R, ((-R : ℂ) + y * Complex.I)⁻¹) =
      -(Real.pi / 2 : ℂ) := by
  rw [show (fun y : ℝ => ((-R : ℂ) + y * Complex.I)⁻¹) =
      fun y : ℝ => -Complex.I * (((y : ℂ) + R * Complex.I)⁻¹) by
    funext y
    have heq : (-R : ℂ) + y * Complex.I =
        Complex.I * ((y : ℂ) + R * Complex.I) := by
      symm
      calc
        Complex.I * ((y : ℂ) + R * Complex.I) =
            Complex.I * (y : ℂ) + (R : ℂ) * (Complex.I * Complex.I) := by ring
        _ = (-R : ℂ) + y * Complex.I := by rw [Complex.I_mul_I]; ring
    rw [heq, mul_inv_rev, Complex.inv_I]
    ring]
  rw [intervalIntegral.integral_const_mul, integral_inv_horizontal_upper R hR]
  calc
    -Complex.I * (-(Real.pi / 2 : ℂ) * Complex.I) =
        (Real.pi / 2 : ℂ) * (Complex.I * Complex.I) := by ring
    _ = -(Real.pi / 2 : ℂ) := by rw [Complex.I_mul_I]; ring

end Submission.Helpers
