import Submission.FrontierCorrection

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- The zeroth moment of a correction density is bounded by its `L¹`
mass, hence by the local oscillation times the mass of the cutoff defect. -/
theorem norm_integral_frontierCorrectionDensity_le_of_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (hω : 0 ≤ osc)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc) :
    ‖∫ w : ℂ, frontierCorrectionDensity χ ψ g b i w‖ ≤
      osc * ∫ w : ℂ,
        ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
  calc
    ‖∫ w : ℂ, frontierCorrectionDensity χ ψ g b i w‖
        ≤ ∫ w : ℂ,
            ‖frontierCorrectionDensity χ ψ g b i w‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ osc * ∫ w : ℂ,
          ‖crDefect (partitionedCutoff χ ψ i) w‖ :=
      integral_norm_frontierCorrectionDensity_le_of_oscillation
        χ ψ g x b r osc hψ hg hχ i hω hosc

/-- The first moment about a pole near the ball center is bounded by the
radius-plus-center-distance times the `L¹` mass of the correction density. -/
theorem norm_integral_sub_mul_frontierCorrectionDensity_le
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r s : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a : ℂ) (_hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hxa : dist (x i) a ≤ s) :
    ‖∫ w : ℂ,
        (w - a) * frontierCorrectionDensity χ ψ g b i w‖ ≤
      (r + s) *
        ∫ w : ℂ, ‖frontierCorrectionDensity χ ψ g b i w‖ := by
  let q : ℂ → ℂ := frontierCorrectionDensity χ ψ g b i
  have hq :
      MeasureTheory.Integrable q :=
    integrable_frontierCorrectionDensity
      χ ψ g x b r hψ hg hχ i
  have hq₁ :
      MeasureTheory.Integrable (fun w ↦ (w - a) * q w) := by
    simpa only [q] using
      integrable_sub_mul_frontierCorrectionDensity
        χ ψ g x b r hψ hg hχ i a
  have hpoint :
      ∀ w : ℂ, ‖(w - a) * q w‖ ≤ (r + s) * ‖q w‖ := by
    intro w
    by_cases hqw : q w = 0
    · simp [hqw]
    · have hwball : w ∈ Metric.ball (x i) r :=
        tsupport_frontierCorrectionDensity_subset_ball
          χ ψ g x b r hχ i (subset_tsupport q hqw)
      have hwa : ‖w - a‖ ≤ r + s := by
        calc
          ‖w - a‖ = dist w a := by rw [dist_eq_norm]
          _ ≤ dist w (x i) + dist (x i) a :=
            dist_triangle w (x i) a
          _ ≤ r + s :=
            add_le_add (Metric.mem_ball.mp hwball).le hxa
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hwa (norm_nonneg _)
  calc
    ‖∫ w : ℂ, (w - a) * q w‖
        ≤ ∫ w : ℂ, ‖(w - a) * q w‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ, (r + s) * ‖q w‖ := by
      apply MeasureTheory.integral_mono hq₁.norm
        (hq.norm.const_mul (r + s))
      exact hpoint
    _ = (r + s) * ∫ w : ℂ, ‖q w‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- Local oscillation also controls the first moment of a correction
density. -/
theorem norm_integral_sub_mul_frontierCorrectionDensity_le_of_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r s osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a : ℂ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hω : 0 ≤ osc)
    (hxa : dist (x i) a ≤ s)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc) :
    ‖∫ w : ℂ,
        (w - a) * frontierCorrectionDensity χ ψ g b i w‖ ≤
      (r + s) *
        (osc * ∫ w : ℂ,
          ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
  calc
    ‖∫ w : ℂ,
        (w - a) * frontierCorrectionDensity χ ψ g b i w‖
        ≤ (r + s) *
            ∫ w : ℂ,
              ‖frontierCorrectionDensity χ ψ g b i w‖ :=
      norm_integral_sub_mul_frontierCorrectionDensity_le
        χ ψ g x b r s hψ hg hχ i a hr hs hxa
    _ ≤ (r + s) *
          (osc * ∫ w : ℂ,
            ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
      exact mul_le_mul_of_nonneg_left
        (integral_norm_frontierCorrectionDensity_le_of_oscillation
          χ ψ g x b r osc hψ hg hχ i hω hosc)
        (add_nonneg hr hs)

/-- Near the source ball, bound the transform-minus-moment error by
separately bounding the transform, zeroth moment, and first moment.  This
estimate does not require the evaluation point to be separated from the
source support. -/
theorem norm_integral_frontierCorrectionDensity_sub_moments_le_of_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r s osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a z : ℂ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hω : 0 ≤ osc)
    (hxa : dist (x i) a ≤ s)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc) :
    ‖(∫ w : ℂ,
          (w - z)⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) -
        ((a - z)⁻¹ *
            (∫ w : ℂ,
              frontierCorrectionDensity χ ψ g b i w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ,
              (w - a) *
                frontierCorrectionDensity χ ψ g b i w))‖ ≤
      osc * (∫ w : ℂ,
          ‖(w - z)⁻¹‖ *
            ‖crDefect (partitionedCutoff χ ψ i) w‖) +
        (‖(a - z)⁻¹‖ *
            (osc * ∫ w : ℂ,
              ‖crDefect (partitionedCutoff χ ψ i) w‖) +
          ‖(a - z)⁻¹ ^ 2‖ *
            ((r + s) *
              (osc * ∫ w : ℂ,
                ‖crDefect (partitionedCutoff χ ψ i) w‖))) := by
  let q : ℂ → ℂ := frontierCorrectionDensity χ ψ g b i
  have htransform :
      ‖∫ w : ℂ, (w - z)⁻¹ * q w‖ ≤
        osc * ∫ w : ℂ,
          ‖(w - z)⁻¹‖ *
            ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
    simpa only [q] using
      norm_integral_cauchyKernel_mul_frontierCorrectionDensity_le
        χ ψ g x b r osc hψ hg hχ i z hω hosc
  have hzero :
      ‖∫ w : ℂ, q w‖ ≤
        osc * ∫ w : ℂ,
          ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
    simpa only [q] using
      norm_integral_frontierCorrectionDensity_le_of_oscillation
        χ ψ g x b r osc hψ hg hχ i hω hosc
  have hfirst :
      ‖∫ w : ℂ, (w - a) * q w‖ ≤
        (r + s) *
          (osc * ∫ w : ℂ,
            ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
    simpa only [q] using
      norm_integral_sub_mul_frontierCorrectionDensity_le_of_oscillation
        χ ψ g x b r s osc hψ hg hχ i a hr hs hω hxa hosc
  change
    ‖(∫ w : ℂ, (w - z)⁻¹ * q w) -
        ((a - z)⁻¹ * (∫ w : ℂ, q w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ, (w - a) * q w))‖ ≤ _
  calc
    ‖(∫ w : ℂ, (w - z)⁻¹ * q w) -
        ((a - z)⁻¹ * (∫ w : ℂ, q w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ, (w - a) * q w))‖
        ≤ ‖∫ w : ℂ, (w - z)⁻¹ * q w‖ +
            ‖(a - z)⁻¹ * (∫ w : ℂ, q w) -
              (a - z)⁻¹ ^ 2 *
                (∫ w : ℂ, (w - a) * q w)‖ :=
      norm_sub_le _ _
    _ ≤ ‖∫ w : ℂ, (w - z)⁻¹ * q w‖ +
          (‖(a - z)⁻¹ * (∫ w : ℂ, q w)‖ +
            ‖(a - z)⁻¹ ^ 2 *
              (∫ w : ℂ, (w - a) * q w)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
        (osc * ∫ w : ℂ,
          ‖(w - z)⁻¹‖ *
            ‖crDefect (partitionedCutoff χ ψ i) w‖) +
          (‖(a - z)⁻¹‖ *
              (osc * ∫ w : ℂ,
                ‖crDefect (partitionedCutoff χ ψ i) w‖) +
            ‖(a - z)⁻¹ ^ 2‖ *
              ((r + s) *
                (osc * ∫ w : ℂ,
                  ‖crDefect (partitionedCutoff χ ψ i) w‖))) := by
      rw [norm_mul, norm_mul]
      gcongr

/-- Far from the source ball, combine the second-order Laurent estimate
with the local-oscillation bound for the correction density's `L¹` mass. -/
theorem norm_integral_frontierCorrectionDensity_sub_moments_le_of_far_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a z : ℂ) (s d : ℝ)
    (hω : 0 ≤ osc)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc)
    (hca : dist (x i) a ≤ s)
    (haz : d ≤ dist a z)
    (hcz : r + d ≤ dist (x i) z)
    (hd : 0 < d) :
    ‖(∫ w : ℂ,
          (w - z)⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) -
        ((a - z)⁻¹ *
            (∫ w : ℂ,
              frontierCorrectionDensity χ ψ g b i w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ,
              (w - a) *
                frontierCorrectionDensity χ ψ g b i w))‖ ≤
      ((r + s) ^ 2 * d⁻¹ ^ 3) *
        (osc * ∫ w : ℂ,
          ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
  calc
    ‖(∫ w : ℂ,
          (w - z)⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) -
        ((a - z)⁻¹ *
            (∫ w : ℂ,
              frontierCorrectionDensity χ ψ g b i w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ,
              (w - a) *
                frontierCorrectionDensity χ ψ g b i w))‖
        ≤ ((r + s) ^ 2 * d⁻¹ ^ 3) *
            ∫ w : ℂ,
              ‖frontierCorrectionDensity χ ψ g b i w‖ :=
      norm_integral_frontierCorrectionDensity_sub_moments_le_of_far
        χ ψ g x b r hψ hg hχ i a z s d hca haz hcz hd
    _ ≤ ((r + s) ^ 2 * d⁻¹ ^ 3) *
          (osc * ∫ w : ℂ,
            ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
      apply mul_le_mul_of_nonneg_left
        (integral_norm_frontierCorrectionDensity_le_of_oscillation
          χ ψ g x b r osc hψ hg hχ i hω hosc)
      positivity

end Submission.Helpers
