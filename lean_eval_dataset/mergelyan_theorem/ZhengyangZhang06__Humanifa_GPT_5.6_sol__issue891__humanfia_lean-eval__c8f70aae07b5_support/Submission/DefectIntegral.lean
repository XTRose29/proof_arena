import Submission.FrontierCorrection

open Function Set
open scoped ContDiff Interval Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- The whole-plane integral of the Cauchy--Riemann defect of a smooth
compactly supported function vanishes.  This is the integration-by-parts
identity used to remove derivatives of localization cutoffs from moment
estimates. -/
theorem integral_crDefect_eq_zero
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    (∫ z : ℂ, crDefect g z) = 0 := by
  have hD :
      MeasureTheory.Integrable (crDefect g) :=
    (continuous_crDefect g hg).integrable_of_hasCompactSupport
      (crDefect_hasCompactSupport g hgc)
  obtain ⟨R, hR, hgR⟩ :=
    hgc.isBounded.subset_ball_lt 1 (0 : ℂ)
  have hR0 : 0 < R := by linarith
  have hgzero (w : ℂ) (hw : R ≤ dist w 0) : g w = 0 := by
    by_contra hwg
    have hwt : w ∈ tsupport g := subset_tsupport g hwg
    have hwb := hgR hwt
    rw [Metric.mem_ball] at hwb
    exact (not_lt_of_ge hw) hwb
  have hboundary :
      rectBoundaryIntegral g
        ⟨-R, -R⟩ ⟨R, R⟩ = 0 := by
    apply rectBoundaryIntegral_eq_zero_of_boundary
    · intro x _hx
      apply hgzero
      calc
        R = |(x + ((-R : ℝ) : ℂ) * Complex.I).im| := by
          simp [abs_of_pos hR0]
        _ ≤ ‖x + ((-R : ℝ) : ℂ) * Complex.I‖ :=
          Complex.abs_im_le_norm _
        _ = dist (x + ((-R : ℝ) : ℂ) * Complex.I) 0 := by
          rw [dist_zero_right]
    · intro x _hx
      apply hgzero
      calc
        R = |(x + (R : ℂ) * Complex.I).im| := by
          simp [abs_of_pos hR0]
        _ ≤ ‖x + (R : ℂ) * Complex.I‖ :=
          Complex.abs_im_le_norm _
        _ = dist (x + (R : ℂ) * Complex.I) 0 := by
          rw [dist_zero_right]
    · intro y _hy
      apply hgzero
      calc
        R = |((R : ℂ) + y * Complex.I).re| := by
          simp [abs_of_pos hR0]
        _ ≤ ‖(R : ℂ) + y * Complex.I‖ :=
          Complex.abs_re_le_norm _
        _ = dist ((R : ℂ) + y * Complex.I) 0 := by
          rw [dist_zero_right]
    · intro y _hy
      apply hgzero
      calc
        R = |(((-R : ℝ) : ℂ) + y * Complex.I).re| := by
          simp [abs_of_pos hR0]
        _ ≤ ‖((-R : ℝ) : ℂ) + y * Complex.I‖ :=
          Complex.abs_re_le_norm _
        _ = dist (((-R : ℝ) : ℂ) + y * Complex.I) 0 := by
          rw [dist_zero_right]
  have hgreen :
      rectBoundaryIntegral g
          ⟨-R, -R⟩ ⟨R, R⟩ =
        rectIntegral (crDefect g)
          ⟨-R, -R⟩ ⟨R, R⟩ := by
    apply rectBoundaryIntegral_eq_rectIntegral_crDefect
    · exact (hg.differentiable (by simp)).differentiableOn
    · exact hD.integrableOn
  have hrect :
      rectIntegral (crDefect g)
        ⟨-R, -R⟩ ⟨R, R⟩ = 0 := by
    rw [hboundary] at hgreen
    exact hgreen.symm
  let Q : Set ℂ :=
    Set.Ioc (-R) R ×ℂ Set.Ioc (-R) R
  have hrectSet :
      (∫ z : ℂ in Q, crDefect g z) = 0 := by
    have heq :=
      rectIntegral_eq_setIntegral
        (crDefect g)
        (show -R ≤ R by linarith)
        (show -R ≤ R by linarith)
        hD.integrableOn
    change
      rectIntegral (crDefect g)
          ⟨-R, -R⟩ ⟨R, R⟩ =
        ∫ z : ℂ in Q, crDefect g z at heq
    rw [← heq]
    exact hrect
  have hzeroOff :
      ∀ z, z ∉ Q → crDefect g z = 0 := by
    intro z hzQ
    by_contra hzD
    have hzDt : z ∈ tsupport (crDefect g) :=
      subset_tsupport (crDefect g) hzD
    have hzgt : z ∈ tsupport g :=
      tsupport_crDefect_subset g hzDt
    have hzball := hgR hzgt
    have hznorm : ‖z‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hzball
    have hzre : |z.re| < R :=
      (Complex.abs_re_le_norm z).trans_lt hznorm
    have hzim : |z.im| < R :=
      (Complex.abs_im_le_norm z).trans_lt hznorm
    apply hzQ
    constructor
    · exact ⟨(abs_lt.mp hzre).1, (abs_lt.mp hzre).2.le⟩
    · exact ⟨(abs_lt.mp hzim).1, (abs_lt.mp hzim).2.le⟩
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    hzeroOff] at hrectSet
  exact hrectSet

/-- Integration by parts identifies the zeroth moment of a signed
correction density with the same partition cutoff applied to the original
defect. -/
theorem integral_frontierCorrectionDensity_eq_localized_crDefect
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) :
    (∫ w : ℂ, frontierCorrectionDensity χ ψ g b i w) =
      ∫ w : ℂ,
        partitionedCutoff χ ψ i w * crDefect g w := by
  let φ : ℂ → ℂ := partitionedCutoff χ ψ i
  let F : ℂ → ℂ := fun w ↦ φ w * (g w - b i)
  have hφ : ContDiff ℝ ∞ φ := by
    simpa only [φ] using
      contDiff_partitionedCutoff χ ψ hψ i
  have hφc : HasCompactSupport φ := by
    simpa only [φ] using
      hasCompactSupport_partitionedCutoff
        χ ψ x r hχ i
  have hF : ContDiff ℝ ∞ F :=
    hφ.mul (hg.sub contDiff_const)
  have hFc : HasCompactSupport F :=
    hφc.mul_right
  have hdefect (w : ℂ) :
      crDefect F w =
        φ w * crDefect g w +
          (g w - b i) * crDefect φ w := by
    dsimp only [F]
    rw [crDefect_mul
      ((hφ.differentiable (by simp)).differentiableAt)
      ((hg.differentiable (by simp)).differentiableAt.sub_const (b i))]
    simp only [crDefect, fderiv_sub_const]
  have hleft :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ φ w * crDefect g w) :=
    (hφ.continuous.mul
      (continuous_crDefect g hg)).integrable_of_hasCompactSupport
        hφc.mul_right
  have hright :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          (g w - b i) * crDefect φ w) :=
    ((hg.continuous.sub continuous_const).mul
      (continuous_crDefect φ hφ)).integrable_of_hasCompactSupport
        (crDefect_hasCompactSupport φ hφc).mul_left
  have hsum :
      (∫ w : ℂ, φ w * crDefect g w) +
          (∫ w : ℂ,
            (g w - b i) * crDefect φ w) = 0 := by
    have hzero := integral_crDefect_eq_zero F hF hFc
    have heq :
        (∫ w : ℂ, crDefect F w) =
          ∫ w : ℂ,
            φ w * crDefect g w +
              (g w - b i) * crDefect φ w := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      exact hdefect w
    rw [heq, MeasureTheory.integral_add hleft hright] at hzero
    exact hzero
  calc
    (∫ w : ℂ, frontierCorrectionDensity χ ψ g b i w) =
        -(∫ w : ℂ,
          (g w - b i) * crDefect φ w) := by
      rw [← MeasureTheory.integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      simp only [frontierCorrectionDensity, φ]
    _ = ∫ w : ℂ, φ w * crDefect g w := by
      exact (eq_neg_of_add_eq_zero_left hsum).symm
    _ = ∫ w : ℂ,
          partitionedCutoff χ ψ i w *
            crDefect g w := by
      rfl

/-- The first correction moment satisfies the analogous integration-by-parts
identity because `w ↦ w - a` is holomorphic. -/
theorem integral_sub_mul_frontierCorrectionDensity_eq_localized_crDefect
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (x b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (x i) r))
    (i : ι) (a : ℂ) :
    (∫ w : ℂ,
        (w - a) * frontierCorrectionDensity χ ψ g b i w) =
      ∫ w : ℂ,
        (w - a) *
          (partitionedCutoff χ ψ i w * crDefect g w) := by
  let G : ℂ → ℂ :=
    fun w ↦ (w - a) * (g w - b i)
  let B : ι → ℂ := fun _ ↦ 0
  have hG :
      ContDiff ℝ ∞ G :=
    (contDiff_id.sub contDiff_const).mul
      (hg.sub contDiff_const)
  have hGdefect (w : ℂ) :
      crDefect G w = (w - a) * crDefect g w := by
    have hu :
        DifferentiableAt ℝ (fun u : ℂ ↦ u - a) w :=
      ((differentiableAt_id.sub_const a).restrictScalars
        (𝕜 := ℝ) (𝕜' := ℂ))
    have hv :
        DifferentiableAt ℝ (fun u : ℂ ↦ g u - b i) w :=
      (hg.differentiable (by simp)).differentiableAt.sub_const (b i)
    rw [show G = fun u ↦ (u - a) * (g u - b i) from rfl,
      crDefect_mul hu hv]
    have hsub :
        crDefect (fun u : ℂ ↦ g u - b i) w =
          crDefect g w := by
      simp only [crDefect, fderiv_sub_const]
    have hlinear :
        crDefect (fun u : ℂ ↦ u - a) w = 0 :=
      crDefect_eq_zero_of_differentiableAt
        (differentiableAt_id.sub_const a)
    rw [hsub, hlinear, mul_zero, add_zero]
  have hbase :=
    integral_frontierCorrectionDensity_eq_localized_crDefect
      χ ψ G x B r hψ hG hχ i
  calc
    (∫ w : ℂ,
        (w - a) * frontierCorrectionDensity χ ψ g b i w) =
        ∫ w : ℂ,
          frontierCorrectionDensity χ ψ G B i w := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      simp only [frontierCorrectionDensity, G, B]
      ring
    _ = ∫ w : ℂ,
          partitionedCutoff χ ψ i w * crDefect G w :=
      hbase
    _ = ∫ w : ℂ,
          (w - a) *
            (partitionedCutoff χ ψ i w * crDefect g w) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [hGdefect]
      ring

end Submission.Helpers
