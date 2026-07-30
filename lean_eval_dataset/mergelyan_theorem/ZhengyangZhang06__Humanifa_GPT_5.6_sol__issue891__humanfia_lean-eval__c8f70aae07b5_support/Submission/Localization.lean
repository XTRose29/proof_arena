import Submission.Runge

open Function Set
open scoped ContDiff Topology

noncomputable section

namespace Submission.Helpers

/-- A locally integrable Cauchy kernel remains integrable after multiplication
by a continuous compactly supported function. -/
theorem integrable_cauchyKernel_mul_continuous_compact
    (q : ℂ → ℂ) (hq : Continuous q) (hqc : HasCompactSupport q) (z : ℂ) :
    MeasureTheory.Integrable (fun w : ℂ ↦ (w - z)⁻¹ * q w) := by
  simpa only [smul_eq_mul] using
    (locallyIntegrable_cauchyKernel z).integrable_smul_right_of_hasCompactSupport
      hq hqc

/-- Applying Cauchy--Pompeiu to `χ · (g - c)` isolates the part of the
Cauchy--Riemann defect localized by a smooth cutoff `χ`. -/
theorem integral_cauchyKernel_mul_cutoff_crDefect
    (χ g : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g)
    (hχc : HasCompactSupport χ) (c z : ℂ) :
    (∫ w : ℂ, (w - z)⁻¹ * (χ w * crDefect g w)) =
      -((2 * Real.pi * Complex.I) * (χ z * (g z - c))) -
        ∫ w : ℂ, (w - z)⁻¹ * ((g w - c) * crDefect χ w) := by
  let F : ℂ → ℂ := fun w ↦ χ w * (g w - c)
  have hF : ContDiff ℝ ∞ F :=
    hχ.mul (hg.sub contDiff_const)
  have hFc : HasCompactSupport F := by
    exact hχc.mul_right
  have hdefect (w : ℂ) :
      crDefect F w =
        χ w * crDefect g w + (g w - c) * crDefect χ w := by
    dsimp [F]
    rw [crDefect_mul
      ((hχ.differentiable (by simp)).differentiableAt)
      ((hg.differentiable (by simp)).differentiableAt.sub_const c)]
    simp only [crDefect, fderiv_sub_const]
  have hleft :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ (w - z)⁻¹ * (χ w * crDefect g w)) := by
    apply integrable_cauchyKernel_mul_continuous_compact
    · exact hχ.continuous.mul (continuous_crDefect g hg)
    · exact hχc.mul_right
  have hright :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ (w - z)⁻¹ * ((g w - c) * crDefect χ w)) := by
    apply integrable_cauchyKernel_mul_continuous_compact
    · exact (hg.continuous.sub continuous_const).mul
        (continuous_crDefect χ hχ)
    · exact (crDefect_hasCompactSupport χ hχc).mul_left
  have hformula := cauchyPompeiu_compactSupport F hF hFc z
  simp_rw [hdefect, mul_add] at hformula
  dsimp only [F] at hformula
  rw [MeasureTheory.integral_add hleft hright] at hformula
  linear_combination hformula

/-- The norm form of the cutoff-localization identity.  Both terms on the
right are controlled by the oscillation of `g` around the chosen constant
`c` on the support of the cutoff. -/
theorem norm_integral_cauchyKernel_mul_cutoff_crDefect_le
    (χ g : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g)
    (hχc : HasCompactSupport χ) (c z : ℂ) :
    ‖∫ w : ℂ, (w - z)⁻¹ * (χ w * crDefect g w)‖ ≤
      ‖(2 * Real.pi * Complex.I : ℂ)‖ *
          (‖χ z‖ * ‖g z - c‖) +
        ∫ w : ℂ,
          ‖(w - z)⁻¹‖ * (‖g w - c‖ * ‖crDefect χ w‖) := by
  rw [integral_cauchyKernel_mul_cutoff_crDefect χ g hχ hg hχc c z]
  calc
    ‖-((2 * Real.pi * Complex.I) * (χ z * (g z - c))) -
        ∫ w : ℂ, (w - z)⁻¹ * ((g w - c) * crDefect χ w)‖
        ≤ ‖-((2 * Real.pi * Complex.I) * (χ z * (g z - c)))‖ +
            ‖∫ w : ℂ,
              (w - z)⁻¹ * ((g w - c) * crDefect χ w)‖ :=
      norm_sub_le _ _
    _ ≤ ‖-((2 * Real.pi * Complex.I) * (χ z * (g z - c)))‖ +
          ∫ w : ℂ,
            ‖(w - z)⁻¹ * ((g w - c) * crDefect χ w)‖ := by
      exact add_le_add_right
        (MeasureTheory.norm_integral_le_integral_norm
          (fun w : ℂ ↦
            (w - z)⁻¹ * ((g w - c) * crDefect χ w))) _
    _ = ‖(2 * Real.pi * Complex.I : ℂ)‖ *
          (‖χ z‖ * ‖g z - c‖) +
        ∫ w : ℂ,
          ‖(w - z)⁻¹‖ * (‖g w - c‖ * ‖crDefect χ w‖) := by
      simp only [norm_neg, norm_mul]

end Submission.Helpers
