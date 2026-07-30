import Submission.RawCorrection
import Submission.ScaledPartitionBounds

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- A raw correction is supported by its own partition member. -/
theorem tsupport_rawPartitionCorrectionDensity_subset
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (i : ι) :
    tsupport (rawPartitionCorrectionDensity χ ψ g b i) ⊆
      tsupport (complexPartitionCutoff χ i) := by
  rw [tsupport]
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  have hD :
      crDefect (complexPartitionCutoff χ i) z ≠ 0 := by
    intro hD
    exact hz (by
      simp [rawPartitionCorrectionDensity, hD])
  exact tsupport_crDefect_subset _
    (subset_tsupport _ hD)

/-- Local oscillation controls a raw partition correction pointwise.  In
contrast with the full correction density, this bound contains only the
derivative of the partition member; the common cutoff contributes only its
unit norm bound. -/
theorem norm_rawPartitionCorrectionDensity_le_of_oscillation
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r osc : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (i : ι) (hω : 0 ≤ osc)
    (hosc :
      ∀ w ∈ Metric.ball (c i) r, ‖g w - b i‖ ≤ osc)
    (w : ℂ) :
    ‖rawPartitionCorrectionDensity χ ψ g b i w‖ ≤
      osc * ‖crDefect (complexPartitionCutoff χ i) w‖ := by
  by_cases hD :
      crDefect (complexPartitionCutoff χ i) w = 0
  · simp [rawPartitionCorrectionDensity, hD]
  have hw :
      w ∈ Metric.ball (c i) r := by
    exact
      tsupport_complexPartitionCutoff_subset_ball
        χ c r hχ i
        (tsupport_crDefect_subset _
          (subset_tsupport _ hD))
  rw [rawPartitionCorrectionDensity, norm_neg,
    norm_mul, norm_mul]
  calc
    ‖g w - b i‖ *
        (‖ψ w‖ *
          ‖crDefect (complexPartitionCutoff χ i) w‖)
        ≤ osc *
            (1 *
              ‖crDefect (complexPartitionCutoff χ i) w‖) := by
      gcongr
      · exact hosc w hw
      · exact hψnorm w
    _ = osc *
        ‖crDefect (complexPartitionCutoff χ i) w‖ := by
      ring

/-- Summing the preceding pointwise estimate loses no factor beyond the
aggregate derivative mass of the partition itself. -/
theorem sum_norm_rawPartitionCorrectionDensity_le_of_oscillation
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r osc : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) r →
        ‖g w - b i‖ ≤ osc)
    (w : ℂ) :
    (∑ i, ‖rawPartitionCorrectionDensity χ ψ g b i w‖) ≤
      osc *
        ∑ i, ‖crDefect (complexPartitionCutoff χ i) w‖ := by
  calc
    (∑ i, ‖rawPartitionCorrectionDensity χ ψ g b i w‖)
        ≤ ∑ i,
            osc *
              ‖crDefect
                (complexPartitionCutoff χ i) w‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact
        norm_rawPartitionCorrectionDensity_le_of_oscillation
          χ ψ g c b r osc hχ hψnorm i hω
          (hosc i) w
    _ = osc *
          ∑ i,
            ‖crDefect
              (complexPartitionCutoff χ i) w‖ := by
      rw [Finset.mul_sum]

/-- For the explicit equal-scale partition, raw correction density has a
scale-explicit aggregate pointwise bound.  The only combinatorial quantity
is the number of raw bumps active at the source point. -/
theorem sum_norm_rawPartitionCorrectionDensity_uniform_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (osc : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (w : ℂ) :
    (∑ i,
        ‖rawPartitionCorrectionDensity
          (uniformSmoothPartition S c r hr hcover)
          ψ g b i w‖) ≤
      osc *
        (4 * (activeUniformBumps c r hr w).card ^ 2 *
          ((C : ℝ) * r⁻¹)) := by
  let χ :=
    uniformSmoothPartition S c r hr hcover
  have hχ :
      χ.IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) := by
    exact uniformSmoothPartition_isSubordinate
      S c r hr hcover
  calc
    (∑ i,
        ‖rawPartitionCorrectionDensity χ ψ g b i w‖)
        ≤ osc *
            ∑ i,
              ‖crDefect
                (complexPartitionCutoff χ i) w‖ :=
      sum_norm_rawPartitionCorrectionDensity_le_of_oscillation
        χ ψ g c b (3 * r) osc hχ hψnorm hω hosc w
    _ ≤ osc *
        (4 * (activeUniformBumps c r hr w).card ^ 2 *
          ((C : ℝ) * r⁻¹)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_norm_crDefect_complexPartitionCutoff_uniform_le
          S C hC c r hr hcover w) hω

/-- A uniform overlap bound turns the preceding sourcewise estimate into
one constant valid on the whole plane. -/
theorem sum_norm_rawPartitionCorrectionDensity_uniform_le_of_card
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (osc M : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (_hM : 0 ≤ M)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (w : ℂ) :
    (∑ i,
        ‖rawPartitionCorrectionDensity
          (uniformSmoothPartition S c r hr hcover)
          ψ g b i w‖) ≤
      osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)) := by
  calc
    (∑ i,
        ‖rawPartitionCorrectionDensity
          (uniformSmoothPartition S c r hr hcover)
          ψ g b i w‖)
        ≤ osc *
            (4 * (activeUniformBumps c r hr w).card ^ 2 *
              ((C : ℝ) * r⁻¹)) :=
      sum_norm_rawPartitionCorrectionDensity_uniform_le
        S C hC c r hr hcover ψ g b osc
        hψnorm hω hosc w
    _ ≤ osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hω
      gcongr
      · exact_mod_cast hcard w

/-- A finite family of compactly supported densities with a common
pointwise mass bound has a correspondingly bounded aggregate Cauchy
transform.  This elementary integral lemma is the bridge from the
sourcewise derivative estimate to the near-field ball estimate. -/
theorem norm_sum_integral_cauchyKernel_mul_le_of_support
    {ι : Type*} (t : Finset ι) (q : ι → ℂ → ℂ)
    (z : ℂ) (R L : ℝ)
    (hq :
      ∀ i ∈ t,
        MeasureTheory.Integrable
          (fun w : ℂ ↦ (w - z)⁻¹ * q i w))
    (hsupport :
      ∀ i ∈ t, tsupport (q i) ⊆ Metric.ball z R)
    (hbound :
      ∀ w : ℂ, ∑ i ∈ t, ‖q i w‖ ≤ L) :
    ‖∑ i ∈ t, ∫ w : ℂ, (w - z)⁻¹ * q i w‖ ≤
      L * ∫ w : ℂ in Metric.ball z R, ‖(w - z)⁻¹‖ := by
  classical
  have hsumIntegrable :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          ∑ i ∈ t, (w - z)⁻¹ * q i w) :=
    MeasureTheory.integrable_finsetSum t hq
  have hkernel :
      MeasureTheory.IntegrableOn
        (fun w : ℂ ↦ ‖(w - z)⁻¹‖)
        (Metric.ball z R) :=
    MeasureTheory.IntegrableOn.mono_set
      ((locallyIntegrable_cauchyKernel z).integrableOn_isCompact
        (isCompact_closedBall z R)).norm
      Metric.ball_subset_closedBall
  have hzero :
      ∀ w ∉ Metric.ball z R,
        (∑ i ∈ t, (w - z)⁻¹ * q i w) = 0 := by
    intro w hw
    apply Finset.sum_eq_zero
    intro i hi
    have hqi : q i w = 0 := by
      by_contra hqi
      exact hw (hsupport i hi (subset_tsupport _ hqi))
    simp [hqi]
  rw [← MeasureTheory.integral_finsetSum t hq]
  calc
    ‖∫ w : ℂ, ∑ i ∈ t, (w - z)⁻¹ * q i w‖
        ≤ ∫ w : ℂ,
            ‖∑ i ∈ t, (w - z)⁻¹ * q i w‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ w : ℂ in Metric.ball z R,
          ‖∑ i ∈ t, (w - z)⁻¹ * q i w‖ := by
      symm
      apply
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hzero w hw, norm_zero]
    _ ≤ ∫ w : ℂ in Metric.ball z R,
          L * ‖(w - z)⁻¹‖ := by
      apply MeasureTheory.setIntegral_mono_on
        hsumIntegrable.norm.integrableOn
        (hkernel.const_mul L)
        measurableSet_ball
      intro w _hw
      calc
        ‖∑ i ∈ t, (w - z)⁻¹ * q i w‖
            ≤ ∑ i ∈ t,
                ‖(w - z)⁻¹ * q i w‖ :=
          norm_sum_le _ _
        _ = ‖(w - z)⁻¹‖ *
              ∑ i ∈ t, ‖q i w‖ := by
          simp only [norm_mul, Finset.mul_sum]
        _ ≤ ‖(w - z)⁻¹‖ * L :=
          mul_le_mul_of_nonneg_left
            (hbound w) (norm_nonneg _)
        _ = L * ‖(w - z)⁻¹‖ := by ring
    _ = L * ∫ w : ℂ in Metric.ball z R,
          ‖(w - z)⁻¹‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- The raw transforms whose centers are within `D * r` of an evaluation
point are controlled by one Cauchy-kernel integral over the radius
`(D + 3) * r` ball.  In particular, the estimate depends on overlap rather
than on the cardinality of the finite family. -/
theorem norm_sum_integral_rawPartitionCorrectionDensity_uniform_near_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (t : Finset ι) (z : ℂ) (D : ℝ)
    (ht :
      ∀ i ∈ t, dist (c i) z < D * r) :
    ‖∑ i ∈ t, ∫ w : ℂ,
        (w - z)⁻¹ *
          rawPartitionCorrectionDensity
            (uniformSmoothPartition S c r hr hcover)
            ψ g b i w‖ ≤
      (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹))) *
        ∫ w : ℂ in Metric.ball z ((D + 3) * r),
          ‖(w - z)⁻¹‖ := by
  let χ :=
    uniformSmoothPartition S c r hr hcover
  have hχ :
      χ.IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) :=
    uniformSmoothPartition_isSubordinate
      S c r hr hcover
  let q : ι → ℂ → ℂ :=
    fun i ↦ rawPartitionCorrectionDensity χ ψ g b i
  apply norm_sum_integral_cauchyKernel_mul_le_of_support
    t q z ((D + 3) * r)
      (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))
  · intro i hi
    exact integrable_cauchyKernel_mul_continuous_compact _
      (continuous_rawPartitionCorrectionDensity
        χ ψ g b hψ hg i)
      (hasCompactSupport_rawPartitionCorrectionDensity
        χ ψ g c b (fun _ ↦ 3 * r) hχ i) z
  · intro i hi
    refine (tsupport_rawPartitionCorrectionDensity_subset
      χ ψ g b i).trans ?_
    intro w hw
    have hwc :
        dist w (c i) < 3 * r :=
      Metric.mem_ball.mp
        (tsupport_complexPartitionCutoff_subset_ball
          χ c (3 * r) hχ i hw)
    have hciz :
        dist (c i) z < D * r :=
      ht i hi
    rw [Metric.mem_ball]
    calc
      dist w z ≤ dist w (c i) + dist (c i) z :=
        dist_triangle _ _ _
      _ < 3 * r + D * r :=
        add_lt_add hwc hciz
      _ = (D + 3) * r := by ring
  · intro w
    calc
      (∑ i ∈ t, ‖q i w‖)
          ≤ ∑ i, ‖q i w‖ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ t)
          (fun _ _ _ ↦ norm_nonneg _)
      _ ≤ osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)) := by
        exact
          sum_norm_rawPartitionCorrectionDensity_uniform_le_of_card
            S C hC c r hr hcover ψ g b osc M
            hψnorm hω hM hosc hcard w

/-- Scale-free form of the near-field aggregate estimate.  The factor
`r⁻¹` from differentiating the partition cancels the linear scaling of the
planar Cauchy-kernel integral. -/
theorem norm_sum_integral_rawPartitionCorrectionDensity_uniform_near_scaled_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (t : Finset ι) (z : ℂ) (D : ℝ)
    (ht :
      ∀ i ∈ t, dist (c i) z < D * r) :
    ‖∑ i ∈ t, ∫ w : ℂ,
        (w - z)⁻¹ *
          rawPartitionCorrectionDensity
            (uniformSmoothPartition S c r hr hcover)
            ψ g b i w‖ ≤
      osc * (4 * M ^ 2 * (C : ℝ)) *
        ∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖ := by
  calc
    ‖∑ i ∈ t, ∫ w : ℂ,
        (w - z)⁻¹ *
          rawPartitionCorrectionDensity
            (uniformSmoothPartition S c r hr hcover)
            ψ g b i w‖
        ≤ (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹))) *
            ∫ w : ℂ in Metric.ball z ((D + 3) * r),
              ‖(w - z)⁻¹‖ :=
      norm_sum_integral_rawPartitionCorrectionDensity_uniform_near_le
        S C hC c r hr hcover ψ g b hψ hg osc M
        hψnorm hω hM hosc hcard t z D ht
    _ = (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹))) *
          (r * ∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖) := by
      rw [show (D + 3) * r = r * (D + 3) by ring,
        integral_norm_inv_sub_ball_mul z (D + 3) r hr]
    _ = osc * (4 * M ^ 2 * (C : ℝ)) *
          ∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖ := by
      field_simp [hr.ne']

end Submission.Helpers
