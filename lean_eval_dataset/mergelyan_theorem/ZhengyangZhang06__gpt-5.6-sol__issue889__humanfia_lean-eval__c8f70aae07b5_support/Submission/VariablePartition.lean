import Submission.DefectIntegral
import Submission.FrontierCover

open Function Set
open scoped ContDiff Manifold Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- A finite cover of a compact set by balls with varying radii admits a
smooth subordinate partition of unity. -/
theorem exists_smoothPartitionOfUnity_subordinate_variable_balls
    (S : Set ℂ) (hS : IsCompact S)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (r : ι → ℝ)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (r i)) :
    ∃ χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S,
      χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)) ∧
      (∀ z ∈ S, ∑ i, χ i z = 1) ∧
      (∀ z, ∑ i, χ i z ≤ 1) := by
  obtain ⟨χ, hχ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, ℂ) hS.isClosed (fun i ↦ Metric.ball (c i) (r i))
      (fun _ ↦ Metric.isOpen_ball) hcover
  refine ⟨χ, hχ, ?_, ?_⟩
  · intro z hz
    simpa only [finsum_eq_sum_of_fintype] using
      χ.sum_eq_one hz
  · intro z
    simpa only [finsum_eq_sum_of_fintype] using
      χ.sum_le_one z

/-- A common upper bound for variable radii lets every existing
constant-radius localization identity be reused. -/
theorem smoothPartition_isSubordinate_constant_ball_of_radius_le
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (c : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) :
    χ.IsSubordinate (fun i ↦ Metric.ball (c i) R) := by
  intro i
  exact (hχ i).trans (Metric.ball_subset_ball (hrR i))

/-- Variable-radius subordination gives compact support after
complexification. -/
theorem hasCompactSupport_complexPartitionCutoff_of_subordinate_variable_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (c : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    HasCompactSupport (complexPartitionCutoff χ i) := by
  have hreal :
      HasCompactSupport (fun z : ℂ ↦ χ i z) := by
    rw [HasCompactSupport]
    exact
      (isCompact_closedBall (c i) (r i)).of_isClosed_subset
        (isClosed_tsupport _)
        ((hχ i).trans Metric.ball_subset_closedBall)
  exact hreal.comp_left Complex.ofReal_zero

/-- A complexified variable-radius cutoff remains in its subordinate
ball. -/
theorem tsupport_complexPartitionCutoff_subset_variable_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (c : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    tsupport (complexPartitionCutoff χ i) ⊆
      Metric.ball (c i) (r i) :=
  (tsupport_complexPartitionCutoff_subset χ i).trans (hχ i)

/-- Multiplication by the frontier cutoff preserves variable-radius
compact support. -/
theorem hasCompactSupport_partitionedCutoff_of_subordinate_variable_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ : ℂ → ℂ) (c : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    HasCompactSupport (partitionedCutoff χ ψ i) :=
  (hasCompactSupport_complexPartitionCutoff_of_subordinate_variable_ball
    χ c r hχ i).mul_right

/-- A partitioned variable-radius cutoff stays in its subordinate ball. -/
theorem tsupport_partitionedCutoff_subset_variable_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ : ℂ → ℂ) (c : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    tsupport (partitionedCutoff χ ψ i) ⊆
      Metric.ball (c i) (r i) :=
  (tsupport_mul_subset_left
    (f := complexPartitionCutoff χ i) (g := ψ)).trans
      (tsupport_complexPartitionCutoff_subset_variable_ball
        χ c r hχ i)

/-- A correction density attached to a variable-radius cutoff has compact
support. -/
theorem hasCompactSupport_frontierCorrectionDensity_variable
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    HasCompactSupport (frontierCorrectionDensity χ ψ g b i) := by
  have hφc :
      HasCompactSupport (partitionedCutoff χ ψ i) :=
    hasCompactSupport_partitionedCutoff_of_subordinate_variable_ball
      χ ψ c r hχ i
  have hq :
      HasCompactSupport
        (fun z ↦
          (g z - b i) *
            crDefect (partitionedCutoff χ ψ i) z) :=
    (crDefect_hasCompactSupport
      (partitionedCutoff χ ψ i) hφc).mul_left
  exact hq.comp_left neg_zero

/-- A variable-radius correction density stays in its subordinate ball. -/
theorem tsupport_frontierCorrectionDensity_subset_variable_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    tsupport (frontierCorrectionDensity χ ψ g b i) ⊆
      Metric.ball (c i) (r i) := by
  rw [show frontierCorrectionDensity χ ψ g b i =
      -(fun z ↦
        (g z - b i) *
          crDefect (partitionedCutoff χ ψ i) z) by rfl,
    tsupport_neg]
  exact
    (tsupport_mul_subset_right.trans
      (tsupport_crDefect_subset
        (partitionedCutoff χ ψ i))).trans
      (tsupport_partitionedCutoff_subset_variable_ball
        χ ψ c r hχ i)

/-- A variable-radius correction density is Bochner integrable. -/
theorem integrable_frontierCorrectionDensity_variable
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    MeasureTheory.Integrable
      (frontierCorrectionDensity χ ψ g b i) :=
  (continuous_frontierCorrectionDensity
      χ ψ g b hψ hg i).integrable_of_hasCompactSupport
    (hasCompactSupport_frontierCorrectionDensity_variable
      χ ψ g c b r hχ i)

/-- Local oscillation on one variable-radius subordinate ball bounds its
correction density pointwise. -/
theorem norm_frontierCorrectionDensity_le_of_variable_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (osc : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι)
    (hosc :
      ∀ w ∈ Metric.ball (c i) (r i), ‖g w - b i‖ ≤ osc)
    (w : ℂ) :
    ‖frontierCorrectionDensity χ ψ g b i w‖ ≤
      osc * ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
  by_cases hD : crDefect (partitionedCutoff χ ψ i) w = 0
  · simp [frontierCorrectionDensity, hD]
  · have hwball : w ∈ Metric.ball (c i) (r i) :=
      tsupport_partitionedCutoff_subset_variable_ball
        χ ψ c r hχ i
        (tsupport_crDefect_subset
          (partitionedCutoff χ ψ i)
          (subset_tsupport _ hD))
    simp only [frontierCorrectionDensity, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hosc w hwball) (norm_nonneg _)

/-- The `L¹` mass estimate remains valid for variable-radius subordinate
balls. -/
theorem integral_norm_frontierCorrectionDensity_le_of_variable_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) (_hω : 0 ≤ osc)
    (hosc :
      ∀ w ∈ Metric.ball (c i) (r i), ‖g w - b i‖ ≤ osc) :
    (∫ w : ℂ, ‖frontierCorrectionDensity χ ψ g b i w‖) ≤
      osc * ∫ w : ℂ,
        ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
  have hφ :
      ContDiff ℝ ∞ (partitionedCutoff χ ψ i) :=
    contDiff_partitionedCutoff χ ψ hψ i
  have hφc :
      HasCompactSupport (partitionedCutoff χ ψ i) :=
    hasCompactSupport_partitionedCutoff_of_subordinate_variable_ball
      χ ψ c r hχ i
  have hD :
      MeasureTheory.Integrable
        (crDefect (partitionedCutoff χ ψ i)) :=
    (continuous_crDefect _ hφ).integrable_of_hasCompactSupport
      (crDefect_hasCompactSupport _ hφc)
  calc
    (∫ w : ℂ, ‖frontierCorrectionDensity χ ψ g b i w‖)
        ≤ ∫ w : ℂ,
            osc * ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
      apply MeasureTheory.integral_mono
        (integrable_frontierCorrectionDensity_variable
          χ ψ g c b r hψ hg hχ i).norm
        (hD.norm.const_mul osc)
      intro w
      exact
        norm_frontierCorrectionDensity_le_of_variable_oscillation
          χ ψ g c b r osc hχ i hosc w
    _ = osc * ∫ w : ℂ,
        ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- The derivative-free one-piece localization identity also holds for a
variable-radius subordinate partition. -/
theorem integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized_variable
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) (i : ι) (z : ℂ) :
    (∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w) =
      (∫ w : ℂ,
        (w - z)⁻¹ *
          (partitionedCutoff χ ψ i w * crDefect g w)) +
        (2 * Real.pi * Complex.I : ℂ) *
          (partitionedCutoff χ ψ i z * (g z - b i)) :=
  integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized
    χ ψ g c b R hψ hg
      (smoothPartition_isSubordinate_constant_ball_of_radius_le
        χ c r R hχ hrR)
      i z

/-- Zeroth-moment integration by parts for a variable-radius partition. -/
theorem integral_frontierCorrectionDensity_eq_localized_crDefect_variable
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) (i : ι) :
    (∫ w : ℂ, frontierCorrectionDensity χ ψ g b i w) =
      ∫ w : ℂ,
        partitionedCutoff χ ψ i w * crDefect g w :=
  integral_frontierCorrectionDensity_eq_localized_crDefect
    χ ψ g c b R hψ hg
      (smoothPartition_isSubordinate_constant_ball_of_radius_le
        χ c r R hχ hrR)
      i

/-- First-moment integration by parts for a variable-radius partition. -/
theorem integral_sub_mul_frontierCorrectionDensity_eq_localized_crDefect_variable
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) (i : ι) (a : ℂ) :
    (∫ w : ℂ,
        (w - a) * frontierCorrectionDensity χ ψ g b i w) =
      ∫ w : ℂ,
        (w - a) *
          (partitionedCutoff χ ψ i w * crDefect g w) :=
  integral_sub_mul_frontierCorrectionDensity_eq_localized_crDefect
    χ ψ g c b R hψ hg
      (smoothPartition_isSubordinate_constant_ball_of_radius_le
        χ c r R hχ hrR)
      i a

/-- After replacing a correction transform by its first two rational
moments, the entire error is the corresponding kernel error for
`χᵢ ψ ∂̄g` plus the pointwise localization residual.  In particular, no
derivative of `χᵢ` occurs on the right-hand side. -/
theorem frontierCorrectionDensity_sub_moments_eq_localized_variable
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) (i : ι) (a z : ℂ) :
    (∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w) -
        ((a - z)⁻¹ *
            (∫ w : ℂ,
              frontierCorrectionDensity χ ψ g b i w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ,
              (w - a) *
                frontierCorrectionDensity χ ψ g b i w)) =
      ((∫ w : ℂ,
          (w - z)⁻¹ *
            (partitionedCutoff χ ψ i w * crDefect g w)) -
        ((a - z)⁻¹ *
            (∫ w : ℂ,
              partitionedCutoff χ ψ i w * crDefect g w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ,
              (w - a) *
                (partitionedCutoff χ ψ i w *
                  crDefect g w)))) +
        (2 * Real.pi * Complex.I : ℂ) *
          (partitionedCutoff χ ψ i z * (g z - b i)) := by
  rw [
    integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized_variable
      χ ψ g c b r R hψ hg hχ hrR i z,
    integral_frontierCorrectionDensity_eq_localized_crDefect_variable
      χ ψ g c b r R hψ hg hχ hrR i,
    integral_sub_mul_frontierCorrectionDensity_eq_localized_crDefect_variable
      χ ψ g c b r R hψ hg hχ hrR i a]
  ring

/-- Summing the derivative-free one-piece identities exposes exactly the
aggregate kernel error and the partition residual. -/
theorem sum_frontierCorrectionDensity_sub_moments_eq_localized_variable
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b a : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) (z : ℂ) :
    ∑ i,
        ((∫ w : ℂ,
            (w - z)⁻¹ *
              frontierCorrectionDensity χ ψ g b i w) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                frontierCorrectionDensity χ ψ g b i w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  frontierCorrectionDensity χ ψ g b i w))) =
      (∑ i,
        ((∫ w : ℂ,
            (w - z)⁻¹ *
              (partitionedCutoff χ ψ i w * crDefect g w)) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                partitionedCutoff χ ψ i w * crDefect g w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  (partitionedCutoff χ ψ i w *
                    crDefect g w))))) +
        (2 * Real.pi * Complex.I : ℂ) *
          ∑ i, partitionedCutoff χ ψ i z * (g z - b i) := by
  calc
    ∑ i,
        ((∫ w : ℂ,
            (w - z)⁻¹ *
              frontierCorrectionDensity χ ψ g b i w) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                frontierCorrectionDensity χ ψ g b i w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  frontierCorrectionDensity χ ψ g b i w))) =
      ∑ i,
        (((∫ w : ℂ,
            (w - z)⁻¹ *
              (partitionedCutoff χ ψ i w * crDefect g w)) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                partitionedCutoff χ ψ i w * crDefect g w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  (partitionedCutoff χ ψ i w *
                    crDefect g w)))) +
          (2 * Real.pi * Complex.I : ℂ) *
            (partitionedCutoff χ ψ i z * (g z - b i))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact
        frontierCorrectionDensity_sub_moments_eq_localized_variable
          χ ψ g c b r R hψ hg hχ hrR i (a i) z
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The exact finite-transform decomposition accepts variable-radius
subordination once the radii have a common upper bound. -/
theorem frontierCorrectionMap_eq_integral_sum_variable
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R)
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (z : K) :
    frontierCorrectionMap χ ψ g b hψ hg hdisj z =
      ∑ i, ∫ w : ℂ,
        (w - (z : ℂ))⁻¹ *
          frontierCorrectionDensity χ ψ g b i w :=
  frontierCorrectionMap_eq_integral_sum
    χ ψ g c b R hψ hψc hg hgc
      (smoothPartition_isSubordinate_constant_ball_of_radius_le
        χ c r R hχ hrR)
      hnearS hdisj z

/-- The pointwise residual cancels from the exact correction-map
decomposition.  Consequently, the original frontier map is exactly the sum
of the partitioned transforms of `ψ ∂̄g`, with no correction density or
partition derivative left in the formula. -/
theorem frontierDefectMap_eq_partitioned_crDefect_integral_sum_variable
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R)
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (z : K) :
    frontierDefectMap g ψ hg hdisj z =
      ∑ i, ∫ w : ℂ,
        (w - (z : ℂ))⁻¹ *
          (partitionedCutoff χ ψ i w * crDefect g w) := by
  have hcorr :=
    frontierCorrectionMap_eq_integral_sum_variable
      χ ψ g c b r R hψ hψc hg hgc hχ hrR hnearS hdisj z
  have hsum :
      (∑ i, ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) =
        (∑ i, ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            (partitionedCutoff χ ψ i w * crDefect g w)) +
          (2 * Real.pi * Complex.I : ℂ) *
            ∑ i,
              partitionedCutoff χ ψ i z * (g z - b i) := by
    calc
      (∑ i, ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) =
        ∑ i,
          ((∫ w : ℂ,
              (w - (z : ℂ))⁻¹ *
                (partitionedCutoff χ ψ i w * crDefect g w)) +
            (2 * Real.pi * Complex.I : ℂ) *
              (partitionedCutoff χ ψ i z * (g z - b i))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact
          integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized_variable
            χ ψ g c b r R hψ hg hχ hrR i (z : ℂ)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [frontierCorrectionMap_apply, hsum] at hcorr
  linear_combination hcorr

/-- Final variable-partition reduction.  Polynomial approximation now
follows from one uniform aggregate bound for the Laurent errors of the
derivative-free localized densities. -/
theorem exists_polynomial_approx_of_partitionedCrDefectAggregate_variable
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b a : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R)
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (ha : ∀ i, a i ∉ K)
    (ε : ℝ) (hε : 0 < ε)
    (haggregate :
      ∀ z : K,
        ‖∑ i,
            ((∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  (partitionedCutoff χ ψ i w *
                    crDefect g w)) -
              ((a i - (z : ℂ))⁻¹ *
                  (∫ w : ℂ,
                    partitionedCutoff χ ψ i w *
                      crDefect g w) -
                (a i - (z : ℂ))⁻¹ ^ 2 *
                  (∫ w : ℂ,
                    (w - a i) *
                      (partitionedCutoff χ ψ i w *
                        crDefect g w))))‖ <
          ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let q : ι → ℂ → ℂ :=
    fun i w ↦ partitionedCutoff χ ψ i w * crDefect g w
  let m₀ : ι → ℂ := fun i ↦ ∫ w : ℂ, q i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ, (w - a i) * q i w
  obtain ⟨u, hu⟩ :=
    exists_firstMomentRational_mem_polynomialClosure
      hKc a m₀ m₁ ha
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε u
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [(frontierDefectMap g ψ hg hdisj -
      (u : C(K, ℂ))).norm_lt_iff
    (mul_pos (norm_pos_iff.mpr hc) (half_pos hε))]
  intro z
  change
    ‖frontierDefectMap g ψ hg hdisj z -
        (u : C(K, ℂ)) z‖ <
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)
  rw [
    frontierDefectMap_eq_partitioned_crDefect_integral_sum_variable
      χ ψ g c b r R hψ hψc hg hgc hχ hrR hnearS hdisj z,
    hu z]
  dsimp only [m₀, m₁, q]
  rw [← Finset.sum_sub_distrib]
  exact haggregate z

end Submission.Helpers
