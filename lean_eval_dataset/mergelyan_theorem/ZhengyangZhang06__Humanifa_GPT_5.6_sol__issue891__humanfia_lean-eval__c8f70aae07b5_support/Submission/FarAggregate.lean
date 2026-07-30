import Submission.RawCorrectionBounds

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- The cubic kernel is integrable outside every positive-radius ball. -/
theorem integrableOn_norm_sub_inv_pow_three_compl_ball
    (z : ℂ) (R : ℝ) (hR : 0 < R) :
    MeasureTheory.IntegrableOn
      (fun w : ℂ ↦ ‖w - z‖⁻¹ ^ 3)
      (Metric.ball z R)ᶜ := by
  let r₀ : ℝ := min R 1
  have hr₀ : 0 < r₀ := by
    exact lt_min hR zero_lt_one
  let A : Set ℂ :=
    Metric.closedBall z 1 \ Metric.ball z r₀
  have hAcompact : IsCompact A :=
    (isCompact_closedBall z 1).diff Metric.isOpen_ball
  have hAcontinuous :
      ContinuousOn (fun w : ℂ ↦ ‖w - z‖⁻¹ ^ 3) A := by
    intro w hw
    have hwz : w ≠ z := by
      intro hwz
      subst w
      exact hw.2 (by
        rw [Metric.mem_ball, dist_self]
        exact hr₀)
    exact
      (((continuousAt_id.sub continuousAt_const).norm.inv₀
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwz))).pow 3).continuousWithinAt
  have hAintegrable :
      MeasureTheory.IntegrableOn
        (fun w : ℂ ↦ ‖w - z‖⁻¹ ^ 3) A :=
    hAcontinuous.integrableOn_compact hAcompact
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.addRight (-z)
  have hpre :
      (fun w : ℂ ↦ w + -z) ⁻¹' (Metric.ball 0 1)ᶜ =
        (Metric.ball z 1)ᶜ := by
    rw [preimage_compl]
    congr 1
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm,
      sub_eq_add_neg, neg_zero, add_zero]
  have hfar :
      MeasureTheory.IntegrableOn
        (fun w : ℂ ↦ ‖w - z‖⁻¹ ^ 3)
        (Metric.ball z 1)ᶜ := by
    have h :=
      ((MeasureTheory.measurePreserving_add_right
          MeasureTheory.volume (-z)).integrableOn_comp_preimage
        e.measurableEmbedding
        (f := fun w : ℂ ↦ ‖w‖⁻¹ ^ 3)
        (s := (Metric.ball 0 1)ᶜ)).mpr
          integrableOn_norm_inv_pow_three_compl_ball
    rw [hpre] at h
    change
      MeasureTheory.IntegrableOn
        (fun w : ℂ ↦ ‖w + -z‖⁻¹ ^ 3)
        (Metric.ball z 1)ᶜ at h
    simpa only [sub_eq_add_neg] using h
  apply
    (hAintegrable.union hfar).mono_set
  intro w hw
  have hwR : R ≤ dist w z := by
    simpa only [mem_compl_iff, Metric.mem_ball, not_lt] using hw
  have hwr₀ : r₀ ≤ dist w z :=
    (min_le_left R 1).trans hwR
  by_cases hw1 : dist w z ≤ 1
  · exact Or.inl ⟨Metric.mem_closedBall.mpr hw1,
      by simpa only [Metric.mem_ball, not_lt] using hwr₀⟩
  · exact Or.inr (by
      simpa only [mem_compl_iff, Metric.mem_ball, not_lt] using
        le_of_not_ge hw1)

/-- The first moment of a raw partition correction is integrable. -/
theorem integrable_sub_mul_rawPartitionCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) (a : ℂ) :
    MeasureTheory.Integrable
      (fun w ↦
        (w - a) * rawPartitionCorrectionDensity χ ψ g b i w) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact
      (continuous_id.sub continuous_const).mul
        (continuous_rawPartitionCorrectionDensity
          χ ψ g b hψ hg i)
  · exact
      (hasCompactSupport_rawPartitionCorrectionDensity
        χ ψ g c b (fun _ ↦ r) hχ i).mul_left

/-- The exact second-order Laurent remainder of a raw correction is
integrable. -/
theorem integrable_rawPartitionCorrectionDensity_secondOrder_remainder
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) (a z : ℂ) :
    MeasureTheory.Integrable
      (fun w ↦
        ((w - a) ^ 2 *
          ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) *
            rawPartitionCorrectionDensity χ ψ g b i w) := by
  let q : ℂ → ℂ :=
    fun w ↦
      (w - a) ^ 2 *
        rawPartitionCorrectionDensity χ ψ g b i w
  have hqContinuous : Continuous q :=
    ((continuous_id.sub continuous_const).pow 2).mul
      (continuous_rawPartitionCorrectionDensity
        χ ψ g b hψ hg i)
  have hqCompact : HasCompactSupport q :=
    (hasCompactSupport_rawPartitionCorrectionDensity
      χ ψ g c b (fun _ ↦ r) hχ i).mul_left
  have hbase :=
    integrable_cauchyKernel_mul_continuous_compact
      q hqContinuous hqCompact z
  have hscaled :=
    hbase.const_mul ((a - z)⁻¹ ^ 2)
  simpa only [q, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Exact second-order Laurent expansion for the transform of one raw
partition correction. -/
theorem integral_cauchyKernel_mul_rawPartitionCorrectionDensity_eq_moments_add_remainder
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) (a z : ℂ) (haz : a ≠ z) :
    (∫ w : ℂ,
        (w - z)⁻¹ *
          rawPartitionCorrectionDensity χ ψ g b i w) =
      (a - z)⁻¹ *
          (∫ w : ℂ,
            rawPartitionCorrectionDensity χ ψ g b i w) -
        (a - z)⁻¹ ^ 2 *
          (∫ w : ℂ,
            (w - a) *
              rawPartitionCorrectionDensity χ ψ g b i w) +
        ∫ w : ℂ,
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) *
              rawPartitionCorrectionDensity χ ψ g b i w := by
  let q : ℂ → ℂ :=
    rawPartitionCorrectionDensity χ ψ g b i
  have hq : MeasureTheory.Integrable q :=
    (continuous_rawPartitionCorrectionDensity
      χ ψ g b hψ hg i).integrable_of_hasCompactSupport
        (hasCompactSupport_rawPartitionCorrectionDensity
          χ ψ g c b (fun _ ↦ r) hχ i)
  have hq₁ :
      MeasureTheory.Integrable (fun w ↦ (w - a) * q w) := by
    simpa only [q] using
      integrable_sub_mul_rawPartitionCorrectionDensity
        χ ψ g c b r hψ hg hχ i a
  have hrem :
      MeasureTheory.Integrable
        (fun w ↦
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w) := by
    simpa only [q] using
      integrable_rawPartitionCorrectionDensity_secondOrder_remainder
        χ ψ g c b r hψ hg hχ i a z
  simpa only [q, MeasureTheory.setIntegral_univ] using
    setIntegral_cauchyKernel_eq_moments_add_remainder
      Set.univ q haz hq.integrableOn hq₁.integrableOn
        hrem.integrableOn

/-- If a source and its pole are both localized at scale `r`, the
second-order kernel remainder at a far evaluation point is bounded by a
cubic kernel centered at that evaluation point. -/
theorem norm_secondOrder_remainder_le_four_mul_inv_pow_three
    {w a z c : ℂ} {r A D : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hD : 2 * A + 3 < D)
    (hwc : dist w c < 3 * r)
    (hca : dist c a ≤ A * r)
    (hcz : D * r ≤ dist c z) :
    ‖(w - a) ^ 2 *
        ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)‖ ≤
      4 * (A + 3) ^ 2 * r ^ 2 * ‖w - z‖⁻¹ ^ 3 := by
  have hscale : (2 * A + 3) * r < D * r :=
    mul_lt_mul_of_pos_right hD hr
  have hwaDist :
      dist w a ≤ (A + 3) * r := by
    have hlt : dist w a < (A + 3) * r := by
      calc
      dist w a ≤ dist w c + dist c a :=
        dist_triangle _ _ _
      _ < 3 * r + A * r :=
        add_lt_add_of_lt_of_le hwc hca
      _ = (A + 3) * r := by ring
    exact hlt.le
  have hwa :
      ‖w - a‖ ≤ (A + 3) * r := by
    simpa only [dist_eq_norm] using hwaDist
  have hazDist :
      (A + 3) * r < dist a z := by
    have htri :
        dist c z ≤ dist c a + dist a z :=
      dist_triangle _ _ _
    nlinarith
  have haz :
      (A + 3) * r < ‖a - z‖ := by
    simpa only [dist_eq_norm] using hazDist
  have hazpos : 0 < ‖a - z‖ :=
    (mul_pos (by linarith) hr).trans haz
  have hwzpos : 0 < ‖w - z‖ := by
    rw [← dist_eq_norm]
    have htri :
        dist c z ≤ dist c w + dist w z :=
      dist_triangle _ _ _
    have hcw : dist c w < 3 * r := by
      simpa only [dist_comm] using hwc
    have hD3 : 3 * r < D * r := by
      have : 3 < D := by linarith
      exact mul_lt_mul_of_pos_right this hr
    linarith
  have hwz_le :
      ‖w - z‖ ≤ 2 * ‖a - z‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]
    calc
      dist w z ≤ dist w a + dist a z :=
        dist_triangle _ _ _
      _ ≤ (A + 3) * r + dist a z :=
        add_le_add hwaDist le_rfl
      _ ≤ dist a z + dist a z := by
        linarith
      _ = 2 * dist a z := by ring
  have hinv :
      ‖a - z‖⁻¹ ≤ 2 * ‖w - z‖⁻¹ := by
    calc
      ‖a - z‖⁻¹ ≤ (‖w - z‖ / 2)⁻¹ := by
        exact
          (inv_le_inv₀ hazpos (half_pos hwzpos)).2
            (by linarith)
      _ = 2 * ‖w - z‖⁻¹ := by
        field_simp [ne_of_gt hwzpos]
  rw [norm_cauchyKernel_secondOrder_remainder]
  calc
    ‖w - a‖ ^ 2 *
          (‖a - z‖⁻¹ ^ 2 * ‖w - z‖⁻¹)
        ≤ ((A + 3) * r) ^ 2 *
            ((2 * ‖w - z‖⁻¹) ^ 2 *
              ‖w - z‖⁻¹) := by
      gcongr
    _ = 4 * (A + 3) ^ 2 * r ^ 2 *
          ‖w - z‖⁻¹ ^ 3 := by
      ring

/-- A finite family of far raw corrections has a cubic aggregate Laurent
remainder.  Finite overlap is used before integration, so the estimate is
independent of the number of partition members. -/
theorem norm_sum_integral_rawPartitionCorrectionDensity_sub_moments_far_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c a : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M A D : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hD : 2 * A + 3 < D)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (ha :
      ∀ i, dist (c i) (a i) ≤ A * r)
    (t : Finset ι) (z : ℂ)
    (ht :
      ∀ i ∈ t, D * r ≤ dist (c i) z) :
    ‖∑ i ∈ t,
        ((∫ w : ℂ,
            (w - z)⁻¹ *
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  rawPartitionCorrectionDensity
                    (uniformSmoothPartition S c r hr hcover)
                    ψ g b i w)))‖ ≤
      (4 * (A + 3) ^ 2 * r ^ 2 *
        (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))) *
        ∫ w : ℂ in (Metric.ball z ((D - 3) * r))ᶜ,
          ‖w - z‖⁻¹ ^ 3 := by
  classical
  let χ :=
    uniformSmoothPartition S c r hr hcover
  have hχ :
      χ.IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) :=
    uniformSmoothPartition_isSubordinate
      S c r hr hcover
  let q : ι → ℂ → ℂ :=
    fun i ↦ rawPartitionCorrectionDensity χ ψ g b i
  let rem : ι → ℂ → ℂ :=
    fun i w ↦
      ((w - a i) ^ 2 *
        ((a i - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q i w
  have hai (i : ι) (hi : i ∈ t) : a i ≠ z := by
    intro haiz
    have hfar := ht i hi
    have hpole := ha i
    rw [haiz] at hpole
    have hAD : A * r < D * r := by
      apply mul_lt_mul_of_pos_right _ hr
      linarith
    linarith
  have hremIntegrable (i : ι) :
      MeasureTheory.Integrable (rem i) := by
    simpa only [rem, q] using
      integrable_rawPartitionCorrectionDensity_secondOrder_remainder
        χ ψ g c b (3 * r) hψ hg hχ i (a i) z
  have herrorEq :
      (∑ i ∈ t,
          ((∫ w : ℂ, (w - z)⁻¹ * q i w) -
            ((a i - z)⁻¹ * (∫ w : ℂ, q i w) -
              (a i - z)⁻¹ ^ 2 *
                (∫ w : ℂ, (w - a i) * q i w)))) =
        ∫ w : ℂ, ∑ i ∈ t, rem i w := by
    calc
      (∑ i ∈ t,
          ((∫ w : ℂ, (w - z)⁻¹ * q i w) -
            ((a i - z)⁻¹ * (∫ w : ℂ, q i w) -
              (a i - z)⁻¹ ^ 2 *
                (∫ w : ℂ, (w - a i) * q i w)))) =
          ∑ i ∈ t, ∫ w : ℂ, rem i w := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [
          integral_cauchyKernel_mul_rawPartitionCorrectionDensity_eq_moments_add_remainder
            χ ψ g c b (3 * r) hψ hg hχ i (a i) z
              (hai i hi)]
        dsimp only [rem, q]
        ring
      _ = _ := by
        symm
        exact
          MeasureTheory.integral_finsetSum t
            (fun i _hi ↦ hremIntegrable i)
  have hsumIntegrable :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ ∑ i ∈ t, rem i w) :=
    MeasureTheory.integrable_finsetSum t
      (fun i _hi ↦ hremIntegrable i)
  have hR : 0 < (D - 3) * r := by
    apply mul_pos _ hr
    linarith
  have hzero :
      ∀ w ∉ (Metric.ball z ((D - 3) * r))ᶜ,
        (∑ i ∈ t, rem i w) = 0 := by
    intro w hw
    have hwball :
        w ∈ Metric.ball z ((D - 3) * r) := by
      simpa only [mem_compl_iff, not_not] using hw
    apply Finset.sum_eq_zero
    intro i hi
    have hqi : q i w = 0 := by
      by_contra hqi
      have hwcut :
          w ∈ tsupport (complexPartitionCutoff χ i) :=
        tsupport_rawPartitionCorrectionDensity_subset
          χ ψ g b i (subset_tsupport (q i) hqi)
      have hwc :
          dist w (c i) < 3 * r :=
        Metric.mem_ball.mp
          (tsupport_complexPartitionCutoff_subset_ball
            χ c (3 * r) hχ i hwcut)
      have hcw : dist (c i) w < 3 * r := by
        simpa only [dist_comm] using hwc
      have htri :
          dist (c i) z ≤ dist (c i) w + dist w z :=
        dist_triangle _ _ _
      have hfar := ht i hi
      have hwz :
          dist w z < (D - 3) * r := by
        simpa only [Metric.mem_ball, dist_comm] using hwball
      linarith
    simp only [rem, hqi, mul_zero]
  have hpoint :
      ∀ w : ℂ,
        ‖∑ i ∈ t, rem i w‖ ≤
          (4 * (A + 3) ^ 2 * r ^ 2 *
            (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))) *
              ‖w - z‖⁻¹ ^ 3 := by
    intro w
    calc
      ‖∑ i ∈ t, rem i w‖
          ≤ ∑ i ∈ t, ‖rem i w‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ t,
          (4 * (A + 3) ^ 2 * r ^ 2 *
            ‖w - z‖⁻¹ ^ 3) * ‖q i w‖ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hqi : q i w = 0
        · simp [rem, hqi]
        · have hwcut :
              w ∈ tsupport
                (complexPartitionCutoff χ i) :=
            tsupport_rawPartitionCorrectionDensity_subset
              χ ψ g b i (subset_tsupport (q i) hqi)
          have hwc :
              dist w (c i) < 3 * r :=
            Metric.mem_ball.mp
              (tsupport_complexPartitionCutoff_subset_ball
                χ c (3 * r) hχ i hwcut)
          dsimp only [rem]
          rw [norm_mul]
          exact
            mul_le_mul_of_nonneg_right
              (norm_secondOrder_remainder_le_four_mul_inv_pow_three
                hr hA hD hwc (ha i) (ht i hi))
              (norm_nonneg _)
      _ = (4 * (A + 3) ^ 2 * r ^ 2 *
            ‖w - z‖⁻¹ ^ 3) *
          (∑ i ∈ t, ‖q i w‖) := by
        rw [Finset.mul_sum]
      _ ≤ (4 * (A + 3) ^ 2 * r ^ 2 *
            ‖w - z‖⁻¹ ^ 3) *
          (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹))) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            (∑ i ∈ t, ‖q i w‖)
                ≤ ∑ i, ‖q i w‖ := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_univ t)
                (fun _ _ _ ↦ norm_nonneg _)
            _ ≤
                osc *
                  (4 * M ^ 2 * ((C : ℝ) * r⁻¹)) := by
              exact
                sum_norm_rawPartitionCorrectionDensity_uniform_le_of_card
                  S C hC c r hr hcover ψ g b osc M
                  hψnorm hω hM hosc hcard w
        · positivity
      _ = (4 * (A + 3) ^ 2 * r ^ 2 *
            (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))) *
              ‖w - z‖⁻¹ ^ 3 := by
        ring
  change
    ‖∑ i ∈ t,
        ((∫ w : ℂ, (w - z)⁻¹ * q i w) -
          ((a i - z)⁻¹ * (∫ w : ℂ, q i w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ, (w - a i) * q i w)))‖ ≤ _
  rw [herrorEq]
  calc
    ‖∫ w : ℂ, ∑ i ∈ t, rem i w‖
        ≤ ∫ w : ℂ, ‖∑ i ∈ t, rem i w‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ w : ℂ in (Metric.ball z ((D - 3) * r))ᶜ,
          ‖∑ i ∈ t, rem i w‖ := by
      symm
      apply
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hzero w hw, norm_zero]
    _ ≤ ∫ w : ℂ in (Metric.ball z ((D - 3) * r))ᶜ,
          (4 * (A + 3) ^ 2 * r ^ 2 *
            (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))) *
              ‖w - z‖⁻¹ ^ 3 := by
      apply MeasureTheory.setIntegral_mono_on
        hsumIntegrable.norm.integrableOn
        ((integrableOn_norm_sub_inv_pow_three_compl_ball
          z ((D - 3) * r) hR).const_mul _)
        measurableSet_ball.compl
      intro w _hw
      exact hpoint w
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]

/-- Scale-free form of the far aggregate estimate.  The two powers of
`r` in the Laurent remainder cancel the inverse partition scale and the
inverse scale of the planar cubic-kernel integral. -/
theorem norm_sum_integral_rawPartitionCorrectionDensity_sub_moments_far_scaled_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c a : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M A D : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hD : 2 * A + 3 < D)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (ha :
      ∀ i, dist (c i) (a i) ≤ A * r)
    (t : Finset ι) (z : ℂ)
    (ht :
      ∀ i ∈ t, D * r ≤ dist (c i) z) :
    ‖∑ i ∈ t,
        ((∫ w : ℂ,
            (w - z)⁻¹ *
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  rawPartitionCorrectionDensity
                    (uniformSmoothPartition S c r hr hcover)
                    ψ g b i w)))‖ ≤
      16 * (A + 3) ^ 2 * osc * M ^ 2 * (C : ℝ) *
        ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
          ‖w‖⁻¹ ^ 3 := by
  calc
    ‖∑ i ∈ t,
        ((∫ w : ℂ,
            (w - z)⁻¹ *
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w) -
          ((a i - z)⁻¹ *
              (∫ w : ℂ,
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w) -
            (a i - z)⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  rawPartitionCorrectionDensity
                    (uniformSmoothPartition S c r hr hcover)
                    ψ g b i w)))‖
        ≤
          (4 * (A + 3) ^ 2 * r ^ 2 *
            (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))) *
            ∫ w : ℂ in (Metric.ball z ((D - 3) * r))ᶜ,
              ‖w - z‖⁻¹ ^ 3 :=
      norm_sum_integral_rawPartitionCorrectionDensity_sub_moments_far_le
        S C hC c a r hr hcover ψ g b hψ hg
        osc M A D hψnorm hω hM hA hD hosc hcard ha t z ht
    _ =
        (4 * (A + 3) ^ 2 * r ^ 2 *
          (osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹)))) *
          (r⁻¹ *
            ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3) := by
      rw [show (D - 3) * r = r * (D - 3) by ring,
        integral_norm_sub_inv_pow_three_compl_ball_mul
          z (D - 3) r hr]
    _ =
        16 * (A + 3) ^ 2 * osc * M ^ 2 * (C : ℝ) *
          ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
            ‖w‖⁻¹ ^ 3 := by
      field_simp [hr.ne']
      ring

end Submission.Helpers
