import Mathlib

open MeasureTheory intervalIntegral
open scoped Interval Real

noncomputable section

namespace Submission.Helpers

private lemma integral_odd_div_sq_add_sq (R : ℝ) :
    (∫ x : ℝ in -R..R, x / (R ^ 2 + x ^ 2)) = 0 := by
  have h := integral_comp_neg (f := fun x : ℝ => x / (R ^ 2 + x ^ 2))
    (a := -R) (b := R)
  simp only [neg_neg, neg_sq, neg_div] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

lemma integral_inv_horizontal (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ in -R..R, ((x : ℂ) - R * Complex.I)⁻¹) =
      (Real.pi / 2 : ℂ) * Complex.I := by
  have hne : ∀ x : ℝ, (x : ℂ) - R * Complex.I ≠ 0 := by
    intro x hx
    have := congrArg Complex.im hx
    simp at this
    linarith
  have hcont : Continuous fun x : ℝ => ((x : ℂ) - R * Complex.I)⁻¹ :=
    (Complex.continuous_ofReal.sub
      (continuous_const.mul continuous_const)).inv₀ hne
  apply Complex.ext
  · change RCLike.re (∫ x : ℝ in -R..R, ((x : ℂ) - R * Complex.I)⁻¹) =
      RCLike.re ((Real.pi / 2 : ℂ) * Complex.I)
    rw [← intervalIntegral_re (𝕜 := ℂ) (hcont.intervalIntegrable _ _)]
    simpa [Complex.inv_re, Complex.normSq_apply, div_eq_mul_inv, add_comm, pow_two] using
      integral_odd_div_sq_add_sq R
  · change RCLike.im (∫ x : ℝ in -R..R, ((x : ℂ) - R * Complex.I)⁻¹) =
      RCLike.im ((Real.pi / 2 : ℂ) * Complex.I)
    rw [← intervalIntegral_im (𝕜 := ℂ) (hcont.intervalIntegrable _ _)]
    simp only [RCLike.im_to_complex, Complex.inv_im, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      Complex.sub_im, Complex.mul_im, Complex.normSq_apply, mul_one, add_zero, zero_sub,
      neg_neg, neg_mul_neg]
    rw [show (fun x : ℝ => R / (x * x + R * R)) =
        fun x : ℝ => R / (R ^ 2 + x ^ 2) by
      funext x
      ring_nf]
    rw [integral_div_sq_add_sq]
    have hR0 : R ≠ 0 := ne_of_gt hR
    rw [div_self hR0, neg_div, div_self hR0, Real.arctan_one, Real.arctan_neg,
      Real.arctan_one]
    norm_num [Complex.mul_re, Complex.div_re, Complex.normSq_apply]
    ring

end Submission.Helpers
