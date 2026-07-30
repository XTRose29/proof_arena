import Submission.FrontierPartition

open Function Set
open scoped ContDiff Manifold Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- Multiply one member of a smooth partition by the cutoff used in the
near/far Cauchy--Riemann-defect split. -/
def partitionedCutoff
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ : ℂ → ℂ) (i : ι) : ℂ → ℂ :=
  fun z ↦ complexPartitionCutoff χ i z * ψ z

theorem contDiff_partitionedCutoff
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (i : ι) :
    ContDiff ℝ ∞ (partitionedCutoff χ ψ i) :=
  (contDiff_complexPartitionCutoff χ i).mul hψ

theorem hasCompactSupport_partitionedCutoff
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ : ℂ → ℂ) (c : ι → ℂ) (r : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) :
    HasCompactSupport (partitionedCutoff χ ψ i) :=
  (hasCompactSupport_complexPartitionCutoff_of_subordinate_ball
    χ c r hχ i).mul_right

theorem tsupport_partitionedCutoff_subset_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ : ℂ → ℂ) (c : ι → ℂ) (r : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) :
    tsupport (partitionedCutoff χ ψ i) ⊆
      Metric.ball (c i) r :=
  (tsupport_mul_subset_left
    (f := complexPartitionCutoff χ i) (g := ψ)).trans
      (tsupport_complexPartitionCutoff_subset_ball χ c r hχ i)

/-- The correction density obtained from the cutoff-localization identity.
The sign is chosen so that its Cauchy transform equals the localized near
transform plus the small pointwise residual. -/
def frontierCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (i : ι) : ℂ → ℂ :=
  fun z ↦
    -((g z - b i) * crDefect (partitionedCutoff χ ψ i) z)

theorem continuous_frontierCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (i : ι) :
    Continuous (frontierCorrectionDensity χ ψ g b i) := by
  exact
    ((hg.continuous.sub continuous_const).mul
      (continuous_crDefect _
        (contDiff_partitionedCutoff χ ψ hψ i))).neg

theorem hasCompactSupport_frontierCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) :
    HasCompactSupport (frontierCorrectionDensity χ ψ g b i) := by
  have hφc :
      HasCompactSupport (partitionedCutoff χ ψ i) :=
    hasCompactSupport_partitionedCutoff χ ψ x r hχ i
  have hq :
      HasCompactSupport
        (fun z ↦
          (g z - b i) *
            crDefect (partitionedCutoff χ ψ i) z) :=
    (crDefect_hasCompactSupport
      (partitionedCutoff χ ψ i) hφc).mul_left
  exact hq.comp_left neg_zero

/-- A correction density stays in the same subordinate ball as its partition
cutoff.  Differentiation does not enlarge topological support. -/
theorem tsupport_frontierCorrectionDensity_subset_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) :
    tsupport (frontierCorrectionDensity χ ψ g b i) ⊆
      Metric.ball (x i) r := by
  have hsupport :
      tsupport
          (fun z ↦
            (g z - b i) *
              crDefect (partitionedCutoff χ ψ i) z) ⊆
        Metric.ball (x i) r :=
    (tsupport_mul_subset_right.trans
      (tsupport_crDefect_subset
        (partitionedCutoff χ ψ i))).trans
      (tsupport_partitionedCutoff_subset_ball
        χ ψ x r hχ i)
  rw [show frontierCorrectionDensity χ ψ g b i =
      -(fun z ↦
        (g z - b i) *
          crDefect (partitionedCutoff χ ψ i) z) by rfl,
    tsupport_neg]
  exact hsupport

/-- Each correction density is Bochner integrable. -/
theorem integrable_frontierCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) :
    MeasureTheory.Integrable
      (frontierCorrectionDensity χ ψ g b i) :=
    (continuous_frontierCorrectionDensity
      χ ψ g b hψ hg i).integrable_of_hasCompactSupport
    (hasCompactSupport_frontierCorrectionDensity
      χ ψ g x b r hχ i)

/-- Local oscillation of `g` on the subordinate ball bounds the correction
density pointwise by the cutoff's Cauchy--Riemann defect. -/
theorem norm_frontierCorrectionDensity_le_of_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r osc : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc)
    (w : ℂ) :
    ‖frontierCorrectionDensity χ ψ g b i w‖ ≤
      osc * ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
  by_cases hD : crDefect (partitionedCutoff χ ψ i) w = 0
  · simp [frontierCorrectionDensity, hD]
  · have hwball : w ∈ Metric.ball (x i) r :=
      tsupport_partitionedCutoff_subset_ball χ ψ x r hχ i
        (tsupport_crDefect_subset
          (partitionedCutoff χ ψ i)
          (subset_tsupport _ hD))
    simp only [frontierCorrectionDensity, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hosc w hwball) (norm_nonneg _)

/-- The `L¹` mass of a correction density is linear in the local
oscillation of `g`. -/
theorem integral_norm_frontierCorrectionDensity_le_of_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (_hω : 0 ≤ osc)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc) :
    (∫ w : ℂ, ‖frontierCorrectionDensity χ ψ g b i w‖) ≤
      osc * ∫ w : ℂ,
        ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
  have hφ :
      ContDiff ℝ ∞ (partitionedCutoff χ ψ i) :=
    contDiff_partitionedCutoff χ ψ hψ i
  have hφc :
      HasCompactSupport (partitionedCutoff χ ψ i) :=
    hasCompactSupport_partitionedCutoff χ ψ x r hχ i
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
        (integrable_frontierCorrectionDensity
          χ ψ g x b r hψ hg hχ i).norm
        (hD.norm.const_mul osc)
      intro w
      exact norm_frontierCorrectionDensity_le_of_oscillation
        χ ψ g x b r osc hχ i hosc w
    _ = osc * ∫ w : ℂ,
        ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- The same oscillation controls the singular Cauchy transform.  The
remaining kernel integral depends only on the partition cutoff. -/
theorem norm_integral_cauchyKernel_mul_frontierCorrectionDensity_le
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (z : ℂ) (_hω : 0 ≤ osc)
    (hosc :
      ∀ w ∈ Metric.ball (x i) r, ‖g w - b i‖ ≤ osc) :
    ‖∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w‖ ≤
      osc * ∫ w : ℂ,
        ‖(w - z)⁻¹‖ *
          ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
  have hφ :
      ContDiff ℝ ∞ (partitionedCutoff χ ψ i) :=
    contDiff_partitionedCutoff χ ψ hψ i
  have hφc :
      HasCompactSupport (partitionedCutoff χ ψ i) :=
    hasCompactSupport_partitionedCutoff χ ψ x r hχ i
  have hupper :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          (w - z)⁻¹ *
            crDefect (partitionedCutoff χ ψ i) w) :=
    integrable_cauchyKernel_mul_continuous_compact
      _ (continuous_crDefect _ hφ)
        (crDefect_hasCompactSupport _ hφc) z
  have hupperNorm :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          osc * (‖(w - z)⁻¹‖ *
            ‖crDefect (partitionedCutoff χ ψ i) w‖)) := by
    simpa only [norm_mul] using hupper.norm.const_mul osc
  calc
    ‖∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w‖
        ≤ ∫ w : ℂ,
            ‖(w - z)⁻¹ *
              frontierCorrectionDensity χ ψ g b i w‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ,
          osc * (‖(w - z)⁻¹‖ *
            ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
      apply MeasureTheory.integral_mono
        (integrable_cauchyKernel_mul_continuous_compact
          _ (continuous_frontierCorrectionDensity
            χ ψ g b hψ hg i)
          (hasCompactSupport_frontierCorrectionDensity
            χ ψ g x b r hχ i) z).norm
        hupperNorm
      intro w
      change
        ‖(w - z)⁻¹ *
            frontierCorrectionDensity χ ψ g b i w‖ ≤
          osc * (‖(w - z)⁻¹‖ *
            ‖crDefect (partitionedCutoff χ ψ i) w‖)
      rw [norm_mul]
      calc
        ‖(w - z)⁻¹‖ *
            ‖frontierCorrectionDensity χ ψ g b i w‖
            ≤ ‖(w - z)⁻¹‖ *
                (osc *
                  ‖crDefect (partitionedCutoff χ ψ i) w‖) :=
          mul_le_mul_of_nonneg_left
            (norm_frontierCorrectionDensity_le_of_oscillation
              χ ψ g x b r osc hχ i hosc w)
            (norm_nonneg _)
        _ = osc * (‖(w - z)⁻¹‖ *
              ‖crDefect (partitionedCutoff χ ψ i) w‖) := by
          ring
    _ = osc * ∫ w : ℂ,
        ‖(w - z)⁻¹‖ *
          ‖crDefect (partitionedCutoff χ ψ i) w‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- The first-moment density about any point is integrable. -/
theorem integrable_sub_mul_frontierCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a : ℂ) :
    MeasureTheory.Integrable
      (fun w ↦
        (w - a) * frontierCorrectionDensity χ ψ g b i w) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact
      (continuous_id.sub continuous_const).mul
        (continuous_frontierCorrectionDensity
          χ ψ g b hψ hg i)
  · exact
      (hasCompactSupport_frontierCorrectionDensity
        χ ψ g x b r hχ i).mul_left

/-- The second-order Laurent remainder for a correction density is
integrable; its only singular factor is a Cauchy kernel. -/
theorem integrable_frontierCorrectionDensity_secondOrder_remainder
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a z : ℂ) :
    MeasureTheory.Integrable
      (fun w ↦
        ((w - a) ^ 2 *
          ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) *
            frontierCorrectionDensity χ ψ g b i w) := by
  let q : ℂ → ℂ :=
    fun w ↦
      (w - a) ^ 2 *
        frontierCorrectionDensity χ ψ g b i w
  have hqContinuous : Continuous q :=
    ((continuous_id.sub continuous_const).pow 2).mul
      (continuous_frontierCorrectionDensity
        χ ψ g b hψ hg i)
  have hqCompact : HasCompactSupport q :=
    (hasCompactSupport_frontierCorrectionDensity
      χ ψ g x b r hχ i).mul_left
  have hbase :=
    integrable_cauchyKernel_mul_continuous_compact
      q hqContinuous hqCompact z
  have hscaled :=
    hbase.const_mul ((a - z)⁻¹ ^ 2)
  simpa only [q, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Far from a subordinate ball, the full Cauchy transform of one correction
density is controlled by its second-order moment remainder.  The source
integrals can be restricted to the closed ball because the density vanishes
off that ball. -/
theorem norm_integral_frontierCorrectionDensity_sub_moments_le_of_far
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a z : ℂ) (s d : ℝ)
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
        ∫ w : ℂ, ‖frontierCorrectionDensity χ ψ g b i w‖ := by
  let q : ℂ → ℂ :=
    frontierCorrectionDensity χ ψ g b i
  let E : Set ℂ := Metric.closedBall (x i) r
  have hqSupport : tsupport q ⊆ E := by
    exact
      (tsupport_frontierCorrectionDensity_subset_ball
        χ ψ g x b r hχ i).trans Metric.ball_subset_closedBall
  have hqzero : ∀ w, w ∉ E → q w = 0 := by
    intro w hw
    by_contra hqw
    exact hw (hqSupport (subset_tsupport q hqw))
  have hq :
      MeasureTheory.Integrable q :=
    integrable_frontierCorrectionDensity
      χ ψ g x b r hψ hg hχ i
  have hq₁ :
      MeasureTheory.Integrable (fun w ↦ (w - a) * q w) := by
    simpa only [q] using
      integrable_sub_mul_frontierCorrectionDensity
        χ ψ g x b r hψ hg hχ i a
  have hrem :
      MeasureTheory.Integrable
        (fun w ↦
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w) := by
    simpa only [q] using
      integrable_frontierCorrectionDensity_secondOrder_remainder
        χ ψ g x b r hψ hg hχ i a z
  have hwa : ∀ w ∈ E, ‖w - a‖ ≤ r + s := by
    intro w hw
    calc
      ‖w - a‖ = dist w a := by rw [dist_eq_norm]
      _ ≤ dist w (x i) + dist (x i) a :=
        dist_triangle w (x i) a
      _ ≤ r + s :=
        add_le_add (Metric.mem_closedBall.mp hw) hca
  have hwz : ∀ w ∈ E, d ≤ ‖w - z‖ := by
    intro w hw
    have hcw : dist (x i) w ≤ r := by
      simpa only [dist_comm] using Metric.mem_closedBall.mp hw
    have htri :
        dist (x i) z ≤ dist (x i) w + dist w z :=
      dist_triangle (x i) w z
    rw [← dist_eq_norm]
    linarith
  have hsetKernel :
      (∫ w : ℂ in E, (w - z)⁻¹ * q w) =
        ∫ w : ℂ, (w - z)⁻¹ * q w := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    simp only [hqzero w hw, mul_zero]
  have hsetZero :
      (∫ w : ℂ in E, q w) = ∫ w : ℂ, q w :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hqzero
  have hsetFirst :
      (∫ w : ℂ in E, (w - a) * q w) =
        ∫ w : ℂ, (w - a) * q w := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    simp only [hqzero w hw, mul_zero]
  have hsetNorm :
      (∫ w : ℂ in E, ‖q w‖) = ∫ w : ℂ, ‖q w‖ := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    simp only [hqzero w hw, norm_zero]
  change
    ‖(∫ w : ℂ, (w - z)⁻¹ * q w) -
        ((a - z)⁻¹ * (∫ w : ℂ, q w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ, (w - a) * q w))‖ ≤
      ((r + s) ^ 2 * d⁻¹ ^ 3) *
        ∫ w : ℂ, ‖q w‖
  rw [← hsetKernel, ← hsetZero, ← hsetFirst, ← hsetNorm]
  apply norm_setIntegral_cauchyKernel_sub_moments_le
    E measurableSet_closedBall q
  · intro haz'
    have : dist a z = 0 := by
      rw [haz', dist_self]
    linarith
  · exact hq.integrableOn
  · exact hq₁.integrableOn
  · exact hrem.integrableOn
  · exact hq.norm.integrableOn
  · exact hwa
  · simpa only [dist_eq_norm] using haz
  · exact hwz
  · exact hd

/-- The continuous residual left by the finite cutoff-localization
identities, bundled on `K`. -/
def frontierLocalizationResidualMap
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g) :
    C(K, ℂ) :=
  ∑ i,
    restrictTo (K := K)
      (fun z ↦ partitionedCutoff χ ψ i z * (g z - b i))
      (((contDiff_partitionedCutoff χ ψ hψ i).continuous.mul
        (hg.continuous.sub continuous_const)).continuousOn)

@[simp]
theorem frontierLocalizationResidualMap_apply
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (z : K) :
    frontierLocalizationResidualMap χ ψ g b hψ hg z =
      ∑ i, partitionedCutoff χ ψ i z * (g z - b i) := by
  simp [frontierLocalizationResidualMap]

/-- A partition residual is controlled by the common oscillation bound.
The estimate uses the nonnegativity and global `sum ≤ 1` property of a
partition of unity, so it does not lose a factor equal to the number of
frontier pieces. -/
theorem norm_frontierLocalizationResidualMap_le
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc : ℝ) (hω : 0 ≤ osc)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hosc :
      ∀ i (z : K), χ i (z : ℂ) ≠ 0 →
        ‖g z - b i‖ ≤ osc) :
    ‖frontierLocalizationResidualMap (K := K)
        χ ψ g b hψ hg‖ ≤ osc := by
  rw [(frontierLocalizationResidualMap (K := K)
    χ ψ g b hψ hg).norm_le hω]
  intro z
  rw [frontierLocalizationResidualMap_apply]
  calc
    ‖∑ i, partitionedCutoff χ ψ i z * (g z - b i)‖
        ≤ ∑ i, ‖partitionedCutoff χ ψ i z * (g z - b i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, χ i (z : ℂ) * osc := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hi : χ i (z : ℂ) = 0
      · simp [partitionedCutoff, complexPartitionCutoff, hi]
      · rw [partitionedCutoff, norm_mul, norm_mul]
        simp only [complexPartitionCutoff, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg (χ.nonneg i (z : ℂ))]
        have hχnonneg : 0 ≤ χ i (z : ℂ) :=
          χ.nonneg i (z : ℂ)
        calc
          χ i (z : ℂ) * ‖ψ z‖ * ‖g z - b i‖
              ≤ χ i (z : ℂ) * 1 * ‖g z - b i‖ := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left
                    (hψnorm (z : ℂ)) hχnonneg
                · positivity
          _ ≤ χ i (z : ℂ) * 1 * osc := by
                exact mul_le_mul_of_nonneg_left
                  (hosc i z hi)
                  (mul_nonneg hχnonneg zero_le_one)
          _ = χ i (z : ℂ) * osc := by ring
    _ = (∑ i, χ i (z : ℂ)) * osc := by
      rw [Finset.sum_mul]
    _ ≤ 1 * osc := by
      gcongr
      simpa only [finsum_eq_sum_of_fintype] using
        χ.sum_le_one (z : ℂ)
    _ = osc := one_mul osc

/-- Subordination turns a metric oscillation estimate around the ball
centers into the residual bound above. -/
theorem norm_frontierLocalizationResidualMap_le_of_subordinate
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c : ι → ℂ) (r osc : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (hω : 0 ≤ osc) (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hosc :
      ∀ i (z : K), dist (z : ℂ) (c i) < r →
        ‖g z - g (c i)‖ ≤ osc) :
    ‖frontierLocalizationResidualMap (K := K)
        χ ψ g (fun i ↦ g (c i)) hψ hg‖ ≤ osc := by
  apply norm_frontierLocalizationResidualMap_le (K := K)
    χ ψ g (fun i ↦ g (c i)) hψ hg osc hω hψnorm
  intro i z hi
  apply hosc i z
  exact Metric.mem_ball.mp
    (hχ i (subset_tsupport (fun w : ℂ ↦ χ i w) hi))

/-- The correction-transform map which the first-moment rational functions
will approximate. -/
def frontierCorrectionMap
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K) :
    C(K, ℂ) :=
  frontierDefectMap g ψ hg hdisj +
    (2 * Real.pi * Complex.I : ℂ) •
      frontierLocalizationResidualMap χ ψ g b hψ hg

@[simp]
theorem frontierCorrectionMap_apply
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (z : K) :
    frontierCorrectionMap χ ψ g b hψ hg hdisj z =
      frontierDefectMap g ψ hg hdisj z +
        (2 * Real.pi * Complex.I : ℂ) *
          ∑ i, partitionedCutoff χ ψ i z * (g z - b i) := by
  simp [frontierCorrectionMap]

/-- Controlling the localization residual controls the difference between
the original frontier map and the correction-transform map, with the exact
Cauchy--Pompeiu scalar. -/
theorem norm_frontierDefectMap_sub_frontierCorrectionMap_le
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (e₀ : ℝ)
    (hres :
      ‖frontierLocalizationResidualMap (K := K)
          χ ψ g b hψ hg‖ ≤ e₀) :
    ‖frontierDefectMap g ψ hg hdisj -
        frontierCorrectionMap χ ψ g b hψ hg hdisj‖ ≤
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀ := by
  have heq :
      frontierDefectMap g ψ hg hdisj -
          frontierCorrectionMap χ ψ g b hψ hg hdisj =
        -((2 * Real.pi * Complex.I : ℂ) •
          frontierLocalizationResidualMap χ ψ g b hψ hg) := by
    simp only [frontierCorrectionMap]
    abel
  rw [heq, norm_neg, norm_smul]
  exact mul_le_mul_of_nonneg_left hres (norm_nonneg _)

/-- The transform of one signed correction density can be written without
derivatives of the partition cutoff.  This is the quantitative form of the
cutoff-localization identity: the integral term contains only the original
Cauchy--Riemann defect, while the remaining term is pointwise. -/
theorem integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (z : ℂ) :
    (∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w) =
      (∫ w : ℂ,
        (w - z)⁻¹ *
          (partitionedCutoff χ ψ i w * crDefect g w)) +
        (2 * Real.pi * Complex.I : ℂ) *
          (partitionedCutoff χ ψ i z * (g z - b i)) := by
  have hφ :
      ContDiff ℝ ∞ (partitionedCutoff χ ψ i) :=
    contDiff_partitionedCutoff χ ψ hψ i
  have hφc :
      HasCompactSupport (partitionedCutoff χ ψ i) :=
    hasCompactSupport_partitionedCutoff χ ψ x r hχ i
  have hformula :=
    integral_cauchyKernel_mul_cutoff_crDefect
      (partitionedCutoff χ ψ i) g hφ hg hφc
      (b i) z
  have hcorr :
      (∫ w : ℂ,
          (w - z)⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) =
        -(∫ w : ℂ,
          (w - z)⁻¹ *
            ((g w - b i) *
              crDefect (partitionedCutoff χ ψ i) w)) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    simp only [frontierCorrectionDensity]
    ring
  rw [hcorr, hformula]
  ring

/-- The correction map is exactly the finite sum of Cauchy transforms of
the signed correction densities. -/
theorem frontierCorrectionMap_eq_integral_sum
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (z : K) :
    frontierCorrectionMap χ ψ g b hψ hg hdisj z =
      ∑ i, ∫ w : ℂ,
        (w - (z : ℂ))⁻¹ *
          frontierCorrectionDensity χ ψ g b i w := by
  classical
  let qnear : ℂ → ℂ := fun w ↦ ψ w * crDefect g w
  have hqeq (w : ℂ) :
      qnear w =
        ∑ i,
          partitionedCutoff χ ψ i w * crDefect g w := by
    by_cases hqw : qnear w = 0
    · calc
        qnear w = 0 := hqw
        _ = ∑ i, complexPartitionCutoff χ i w * qnear w := by
          simp only [hqw, mul_zero, Finset.sum_const_zero]
        _ = ∑ i,
            partitionedCutoff χ ψ i w *
              crDefect g w := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp only [partitionedCutoff, qnear]
          ring
    · have hwS : w ∈ S :=
        hnearS (subset_tsupport qnear hqw)
      have hsum :
          ∑ i, complexPartitionCutoff χ i w = 1 :=
        sum_complexPartitionCutoff_eq_one χ hwS
      calc
        qnear w =
            (∑ i, complexPartitionCutoff χ i w) * qnear w := by
              rw [hsum, one_mul]
        _ = ∑ i, complexPartitionCutoff χ i w * qnear w := by
          rw [Finset.sum_mul]
        _ = ∑ i,
            partitionedCutoff χ ψ i w *
              crDefect g w := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp only [partitionedCutoff, qnear]
          ring
  have hpieceIntegrable (i : ι) :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          (w - (z : ℂ))⁻¹ *
            (partitionedCutoff χ ψ i w *
              crDefect g w)) := by
    apply integrable_cauchyKernel_mul_continuous_compact
    · exact
        (contDiff_partitionedCutoff χ ψ hψ i).continuous.mul
          (continuous_crDefect g hg)
    · exact
        (hasCompactSupport_partitionedCutoff
          χ ψ x r hχ i).mul_right
  have hsplit :
      (∫ w : ℂ,
          (w - (z : ℂ))⁻¹ * qnear w) =
        ∑ i, ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            (partitionedCutoff χ ψ i w *
              crDefect g w) := by
    calc
      (∫ w : ℂ,
          (w - (z : ℂ))⁻¹ * qnear w) =
          ∫ w : ℂ, ∑ i,
            (w - (z : ℂ))⁻¹ *
              (partitionedCutoff χ ψ i w *
                crDefect g w) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with w
            rw [← Finset.mul_sum, ← hqeq w]
      _ = _ := by
        simpa only using
          MeasureTheory.integral_finsetSum Finset.univ
            (fun i _hi ↦ hpieceIntegrable i)
  have hlocal (i : ι) :
      (∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            (partitionedCutoff χ ψ i w *
              crDefect g w)) +
          (2 * Real.pi * Complex.I : ℂ) *
            (partitionedCutoff χ ψ i z *
              (g z - b i)) =
        ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            frontierCorrectionDensity χ ψ g b i w := by
    rw [
      integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized
        χ ψ g x b r hψ hg hχ i (z : ℂ)]
  rw [frontierCorrectionMap_apply,
    frontierDefectMap_apply g ψ hg hgc hψ hψc hdisj z]
  change
    (∫ w : ℂ, (w - (z : ℂ))⁻¹ * qnear w) +
        (2 * Real.pi * Complex.I : ℂ) *
          (∑ i,
            partitionedCutoff χ ψ i z * (g z - b i)) =
      ∑ i, ∫ w : ℂ,
        (w - (z : ℂ))⁻¹ *
          frontierCorrectionDensity χ ψ g b i w
  rw [hsplit, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _hi ↦ hlocal i

/-- Endpoint for the cutoff-localization construction.  Once each correction
transform is uniformly approximated by its two moment terms, this theorem
combines those errors with the partition residual and invokes the closed
polynomial-algebra endpoint. -/
theorem exists_polynomial_approx_of_frontierCorrectionPieces
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b a : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (ha : ∀ i, a i ∉ K)
    (e₀ : ℝ)
    (hres :
      ‖frontierLocalizationResidualMap (K := K)
          χ ψ g b hψ hg‖ ≤ e₀)
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hpiece :
      ∀ i (z : K),
        ‖(∫ w : ℂ,
              (w - (z : ℂ))⁻¹ *
                frontierCorrectionDensity χ ψ g b i w) -
            ((a i - (z : ℂ))⁻¹ *
                (∫ w : ℂ,
                  frontierCorrectionDensity χ ψ g b i w) -
              (a i - (z : ℂ))⁻¹ ^ 2 *
                (∫ w : ℂ,
                  (w - a i) *
                    frontierCorrectionDensity χ ψ g b i w))‖ ≤
          e i)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀ +
          ∑ i, e i <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  apply exists_polynomial_approx_of_frontierMomentPieces_of_residual
    hKc g ψ hg hgc hψ hdisj
    (fun _ ↦ Set.univ)
    (frontierCorrectionDensity χ ψ g b) a ha
    (frontierCorrectionMap χ ψ g b hψ hg hdisj)
    ?_ (‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀) ?_
    e he ?_ ε hε herror
  · intro z
    simpa only [MeasureTheory.setIntegral_univ] using
      frontierCorrectionMap_eq_integral_sum
        χ ψ g x b r hψ hψc hg hgc hχ hnearS hdisj z
  · exact
      norm_frontierDefectMap_sub_frontierCorrectionMap_le
        χ ψ g b hψ hg hdisj e₀ hres
  · intro i z
    simpa only [MeasureTheory.setIntegral_univ] using hpiece i z

/-- Aggregate endpoint for the cutoff-localization construction.  The
moment errors are bounded only after summation, allowing the partition's
finite-overlap and `sum ≤ 1` properties to be used without a cardinality
loss. -/
theorem exists_polynomial_approx_of_frontierCorrectionAggregate
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b a : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (ha : ∀ i, a i ∉ K)
    (e₀ : ℝ)
    (hres :
      ‖frontierLocalizationResidualMap (K := K)
          χ ψ g b hψ hg‖ ≤ e₀)
    (e₁ : ℝ) (he₁ : 0 ≤ e₁)
    (haggregate :
      ∀ z : K,
        ‖∑ i,
            ((∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  frontierCorrectionDensity χ ψ g b i w) -
              ((a i - (z : ℂ))⁻¹ *
                  (∫ w : ℂ,
                    frontierCorrectionDensity χ ψ g b i w) -
                (a i - (z : ℂ))⁻¹ ^ 2 *
                  (∫ w : ℂ,
                    (w - a i) *
                      frontierCorrectionDensity χ ψ g b i w)))‖ ≤
          e₁)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀ + e₁ <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  apply exists_polynomial_approx_of_frontierMomentPieces_of_aggregate
    hKc g ψ hg hgc hψ hdisj
    (fun _ ↦ Set.univ)
    (frontierCorrectionDensity χ ψ g b) a ha
    (frontierCorrectionMap χ ψ g b hψ hg hdisj)
    ?_ (‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀) ?_
    e₁ he₁ ?_ ε hε herror
  · intro z
    simpa only [MeasureTheory.setIntegral_univ] using
      frontierCorrectionMap_eq_integral_sum
        χ ψ g x b r hψ hψc hg hgc hχ hnearS hdisj z
  · exact
      norm_frontierDefectMap_sub_frontierCorrectionMap_le
        χ ψ g b hψ hg hdisj e₀ hres
  · intro z
    simpa only [MeasureTheory.setIntegral_univ] using haggregate z

end Submission.Helpers
