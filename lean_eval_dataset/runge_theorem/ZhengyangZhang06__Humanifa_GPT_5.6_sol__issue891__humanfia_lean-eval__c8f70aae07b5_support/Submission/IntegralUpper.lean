import Submission.IntegralHorizontal

open MeasureTheory intervalIntegral
open scoped Interval Real

noncomputable section

namespace Submission.Helpers

lemma integral_inv_horizontal_upper (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ in -R..R, ((x : ℂ) + R * Complex.I)⁻¹) =
      -(Real.pi / 2 : ℂ) * Complex.I := by
  rw [show (fun x : ℝ => ((x : ℂ) + R * Complex.I)⁻¹) =
      fun x : ℝ => -(((-x : ℝ) : ℂ) - R * Complex.I)⁻¹ by
    funext x
    have hbase : (x : ℂ) + R * Complex.I =
        -(((-x : ℝ) : ℂ) - R * Complex.I) := by
      push_cast
      ring
    simpa only [inv_neg] using congrArg Inv.inv hbase]
  rw [intervalIntegral.integral_neg]
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => ((x : ℂ) - R * Complex.I)⁻¹) (a := -R) (b := R)
  simp only [neg_neg] at hcomp
  rw [hcomp]
  simpa using congrArg Neg.neg (integral_inv_horizontal R hR)

end Submission.Helpers
