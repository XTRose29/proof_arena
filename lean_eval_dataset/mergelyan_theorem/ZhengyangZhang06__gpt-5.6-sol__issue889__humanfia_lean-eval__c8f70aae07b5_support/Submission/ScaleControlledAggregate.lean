import Submission.ScaleControlledReplacement
import Submission.FarAggregate

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- Finite sums of norms of integrals are controlled by a common
pointwise density bound and a common supporting ball. -/
theorem sum_norm_integral_le_of_support_bound
    {ι : Type*} (t : Finset ι) (q : ι → ℂ → ℂ)
    (z : ℂ) (R L : ℝ) (hR : 0 ≤ R) (_hL : 0 ≤ L)
    (hq :
      ∀ i ∈ t, MeasureTheory.Integrable (q i))
    (hsupport :
      ∀ i ∈ t, tsupport (q i) ⊆ Metric.ball z R)
    (hbound :
      ∀ w : ℂ, ∑ i ∈ t, ‖q i w‖ ≤ L) :
    (∑ i ∈ t, ‖∫ w : ℂ, q i w‖) ≤
      L * Real.pi * R ^ 2 := by
  classical
  have hnormIntegrable :
      ∀ i ∈ t,
        MeasureTheory.Integrable (fun w : ℂ ↦ ‖q i w‖) :=
    fun i hi ↦ (hq i hi).norm
  have hsumIntegrable :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ ∑ i ∈ t, ‖q i w‖) :=
    MeasureTheory.integrable_finsetSum t hnormIntegrable
  have hzero :
      ∀ w ∉ Metric.ball z R,
        (∑ i ∈ t, ‖q i w‖) = 0 := by
    intro w hw
    apply Finset.sum_eq_zero
    intro i hi
    have hqi : q i w = 0 := by
      by_contra hne
      exact hw (hsupport i hi (subset_tsupport _ hne))
    rw [hqi, norm_zero]
  calc
    (∑ i ∈ t, ‖∫ w : ℂ, q i w‖)
        ≤ ∑ i ∈ t, ∫ w : ℂ, ‖q i w‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ w : ℂ, ∑ i ∈ t, ‖q i w‖ := by
      rw [MeasureTheory.integral_finsetSum t hnormIntegrable]
    _ = ∫ w : ℂ in Metric.ball z R,
          ∑ i ∈ t, ‖q i w‖ := by
      symm
      apply
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      exact hzero w hw
    _ ≤ ∫ _w : ℂ in Metric.ball z R, L := by
      apply MeasureTheory.setIntegral_mono_on
        hsumIntegrable.integrableOn
        MeasureTheory.integrableOn_const
        measurableSet_ball
      intro w _hw
      exact hbound w
    _ = L * Real.pi * R ^ 2 := by
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul]
      rw [MeasureTheory.measureReal_def, Complex.volume_ball]
      simp [ENNReal.toReal_ofReal hR]
      ring

/-- Near a fixed evaluation point, the scale-normalized zeroth and first
moments of the raw correction densities have a finite-overlap bound
independent of the cover cardinality and localization radius. -/
theorem sum_rawPartitionCorrection_momentScales_near_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c a : ι → ℂ) (r : ℝ) (hr : 0 < r)
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
    (ha : ∀ i, dist (c i) (a i) = 3 * r)
    (t : Finset ι) (z : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (ht :
      ∀ i ∈ t, dist (c i) z < D * r) :
    (∑ i ∈ t,
        (r⁻¹ *
            ‖∫ w : ℂ,
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w‖ +
          r⁻¹ ^ 2 *
            ‖∫ w : ℂ,
              (w - a i) *
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w‖)) ≤
      28 * Real.pi * (D + 3) ^ 2 *
        osc * M ^ 2 * (C : ℝ) := by
  classical
  let χ :=
    uniformSmoothPartition S c r hr hcover
  let q : ι → ℂ → ℂ :=
    fun i ↦ rawPartitionCorrectionDensity χ ψ g b i
  let L : ℝ :=
    osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹))
  let R : ℝ :=
    (D + 3) * r
  have hχ :
      χ.IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) :=
    uniformSmoothPartition_isSubordinate
      S c r hr hcover
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hqIntegrable :
      ∀ i ∈ t, MeasureTheory.Integrable (q i) := by
    intro i hi
    exact Continuous.integrable_of_hasCompactSupport
      (continuous_rawPartitionCorrectionDensity
        χ ψ g b hψ hg i)
      (hasCompactSupport_rawPartitionCorrectionDensity
        χ ψ g c b (fun _ ↦ 3 * r) hχ i)
  have hqSupport :
      ∀ i ∈ t, tsupport (q i) ⊆ Metric.ball z R := by
    intro i hi
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
    dsimp only [R]
    calc
      dist w z ≤ dist w (c i) + dist (c i) z :=
        dist_triangle _ _ _
      _ < 3 * r + D * r :=
        add_lt_add hwc hciz
      _ = (D + 3) * r := by ring
  have hqBound :
      ∀ w : ℂ, ∑ i ∈ t, ‖q i w‖ ≤ L := by
    intro w
    calc
      (∑ i ∈ t, ‖q i w‖)
          ≤ ∑ i, ‖q i w‖ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ t)
          (fun _ _ _ ↦ norm_nonneg _)
      _ ≤ L := by
        exact
          sum_norm_rawPartitionCorrectionDensity_uniform_le_of_card
            S C hC c r hr hcover ψ g b osc M
            hψnorm hω hM hosc hcard w
  have hm₀ :
      (∑ i ∈ t, ‖∫ w : ℂ, q i w‖) ≤
        L * Real.pi * R ^ 2 :=
    sum_norm_integral_le_of_support_bound
      t q z R L hR hL hqIntegrable hqSupport hqBound
  let q₁ : ι → ℂ → ℂ :=
    fun i w ↦ (w - a i) * q i w
  have hq₁Integrable :
      ∀ i ∈ t, MeasureTheory.Integrable (q₁ i) := by
    intro i hi
    exact
      integrable_sub_mul_rawPartitionCorrectionDensity
        χ ψ g c b (3 * r) hψ hg hχ i (a i)
  have hq₁Support :
      ∀ i ∈ t, tsupport (q₁ i) ⊆ Metric.ball z R := by
    intro i hi
    dsimp only [q₁]
    exact
      (tsupport_mul_subset_right
        (f := fun w : ℂ ↦ w - a i) (g := q i)).trans
          (hqSupport i hi)
  have hq₁Bound :
      ∀ w : ℂ, ∑ i ∈ t, ‖q₁ i w‖ ≤ 6 * r * L := by
    intro w
    calc
      (∑ i ∈ t, ‖q₁ i w‖)
          ≤ ∑ i ∈ t, 6 * r * ‖q i w‖ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hqi : q i w = 0
        · simp [q₁, hqi]
        · have hwSupport :
              w ∈ tsupport (q i) :=
            subset_tsupport _ hqi
          have hwCutoff :
              w ∈ tsupport (complexPartitionCutoff χ i) :=
            tsupport_rawPartitionCorrectionDensity_subset
              χ ψ g b i hwSupport
          have hwc :
              dist w (c i) < 3 * r :=
            Metric.mem_ball.mp
              (tsupport_complexPartitionCutoff_subset_ball
                χ c (3 * r) hχ i hwCutoff)
          have hwa :
              ‖w - a i‖ ≤ 6 * r := by
            rw [← dist_eq_norm]
            calc
              dist w (a i) ≤
                  dist w (c i) + dist (c i) (a i) :=
                dist_triangle _ _ _
              _ ≤ 6 * r := by
                rw [ha i]
                linarith
          dsimp only [q₁]
          rw [norm_mul]
          exact
            mul_le_mul_of_nonneg_right hwa (norm_nonneg _)
      _ = 6 * r * ∑ i ∈ t, ‖q i w‖ := by
        rw [Finset.mul_sum]
      _ ≤ 6 * r * L :=
        mul_le_mul_of_nonneg_left (hqBound w) (by positivity)
  have hm₁ :
      (∑ i ∈ t, ‖∫ w : ℂ, q₁ i w‖) ≤
        (6 * r * L) * Real.pi * R ^ 2 :=
    sum_norm_integral_le_of_support_bound
      t q₁ z R (6 * r * L) hR (by positivity)
        hq₁Integrable hq₁Support hq₁Bound
  calc
    (∑ i ∈ t,
        (r⁻¹ * ‖∫ w : ℂ, q i w‖ +
          r⁻¹ ^ 2 * ‖∫ w : ℂ, q₁ i w‖))
        =
          r⁻¹ * (∑ i ∈ t, ‖∫ w : ℂ, q i w‖) +
            r⁻¹ ^ 2 *
              (∑ i ∈ t, ‖∫ w : ℂ, q₁ i w‖) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    _ ≤
        r⁻¹ * (L * Real.pi * R ^ 2) +
          r⁻¹ ^ 2 *
            ((6 * r * L) * Real.pi * R ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hm₀ (by positivity))
        (mul_le_mul_of_nonneg_left hm₁ (by positivity))
    _ =
        28 * Real.pi * (D + 3) ^ 2 *
          osc * M ^ 2 * (C : ℝ) := by
      dsimp only [L, R]
      field_simp [hr.ne']
      ring

/-- For indices whose centers are far from the evaluation point, the
scale-normalized moments multiplied by their pole kernels have a
scale-free aggregate bound. -/
theorem sum_rawPartitionCorrection_momentScales_poleKernel_far_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c a : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M D : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M)
    (hD : 9 < D)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (ha : ∀ i, dist (c i) (a i) = 3 * r)
    (t : Finset ι) (z : ℂ)
    (ht :
      ∀ i ∈ t, D * r ≤ dist (c i) z) :
    (∑ i ∈ t,
        (r ^ 2 *
              ‖∫ w : ℂ,
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w‖ +
            r *
              ‖∫ w : ℂ,
                (w - a i) *
                  rawPartitionCorrectionDensity
                    (uniformSmoothPartition S c r hr hcover)
                    ψ g b i w‖) *
          (dist (a i) z)⁻¹ ^ 3) ≤
      224 * osc * M ^ 2 * (C : ℝ) *
        ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
          ‖w‖⁻¹ ^ 3 := by
  classical
  let χ :=
    uniformSmoothPartition S c r hr hcover
  let q : ι → ℂ → ℂ :=
    fun i ↦ rawPartitionCorrectionDensity χ ψ g b i
  let q₁ : ι → ℂ → ℂ :=
    fun i w ↦ (w - a i) * q i w
  let L : ℝ :=
    osc * (4 * M ^ 2 * ((C : ℝ) * r⁻¹))
  let e : ι → ℂ → ℝ :=
    fun i w ↦
      (r ^ 2 * ‖q i w‖ + r * ‖q₁ i w‖) *
        (dist (a i) z)⁻¹ ^ 3
  have hχ :
      χ.IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) :=
    uniformSmoothPartition_isSubordinate
      S c r hr hcover
  have hqIntegrable (i : ι) :
      MeasureTheory.Integrable (q i) :=
    Continuous.integrable_of_hasCompactSupport
      (continuous_rawPartitionCorrectionDensity
        χ ψ g b hψ hg i)
      (hasCompactSupport_rawPartitionCorrectionDensity
        χ ψ g c b (fun _ ↦ 3 * r) hχ i)
  have hq₁Integrable (i : ι) :
      MeasureTheory.Integrable (q₁ i) := by
    exact
      integrable_sub_mul_rawPartitionCorrectionDensity
        χ ψ g c b (3 * r) hψ hg hχ i (a i)
  have heIntegrable (i : ι) :
      MeasureTheory.Integrable (e i) := by
    dsimp only [e]
    exact
      (((hqIntegrable i).norm.const_mul (r ^ 2)).add
        ((hq₁Integrable i).norm.const_mul r)).mul_const _
  have hmoment (i : ι) :
      (r ^ 2 * ‖∫ w : ℂ, q i w‖ +
          r * ‖∫ w : ℂ, q₁ i w‖) *
            (dist (a i) z)⁻¹ ^ 3 ≤
        ∫ w : ℂ, e i w := by
    have h₀ :=
      MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume) (q i)
    have h₁ :=
      MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume) (q₁ i)
    have hsum :
        r ^ 2 * ‖∫ w : ℂ, q i w‖ +
              r * ‖∫ w : ℂ, q₁ i w‖
            ≤
          r ^ 2 * (∫ w : ℂ, ‖q i w‖) +
            r * (∫ w : ℂ, ‖q₁ i w‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left h₀ (sq_nonneg r))
        (mul_le_mul_of_nonneg_left h₁ hr.le)
    calc
      (r ^ 2 * ‖∫ w : ℂ, q i w‖ +
            r * ‖∫ w : ℂ, q₁ i w‖) *
              (dist (a i) z)⁻¹ ^ 3
          ≤
          (r ^ 2 * (∫ w : ℂ, ‖q i w‖) +
            r * (∫ w : ℂ, ‖q₁ i w‖)) *
              (dist (a i) z)⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = ∫ w : ℂ, e i w := by
        dsimp only [e]
        rw [MeasureTheory.integral_mul_const,
          MeasureTheory.integral_add
            ((hqIntegrable i).norm.const_mul (r ^ 2))
            ((hq₁Integrable i).norm.const_mul r),
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
  have hsumIntegrable :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ ∑ i ∈ t, e i w) :=
    MeasureTheory.integrable_finsetSum t
      (fun i _hi ↦ heIntegrable i)
  have hR : 0 < (D - 3) * r := by
    exact mul_pos (by linarith) hr
  have hzero :
      ∀ w ∉ (Metric.ball z ((D - 3) * r))ᶜ,
        (∑ i ∈ t, e i w) = 0 := by
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
      have hwz :
          dist w z < (D - 3) * r := by
        simpa only [Metric.mem_ball, dist_comm] using hwball
      linarith [ht i hi]
    simp [e, q₁, hqi]
  have hpoint :
      ∀ w : ℂ,
        (∑ i ∈ t, e i w) ≤
          (56 * r ^ 2 * L) * ‖w - z‖⁻¹ ^ 3 := by
    intro w
    calc
      (∑ i ∈ t, e i w)
          ≤ ∑ i ∈ t,
              (56 * r ^ 2 * ‖w - z‖⁻¹ ^ 3) *
                ‖q i w‖ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hqi : q i w = 0
        · simp [e, q₁, hqi]
        · have hwcut :
              w ∈ tsupport (complexPartitionCutoff χ i) :=
            tsupport_rawPartitionCorrectionDensity_subset
              χ ψ g b i (subset_tsupport (q i) hqi)
          have hwc :
              dist w (c i) < 3 * r :=
            Metric.mem_ball.mp
              (tsupport_complexPartitionCutoff_subset_ball
                χ c (3 * r) hχ i hwcut)
          have hwa :
              ‖w - a i‖ ≤ 6 * r := by
            rw [← dist_eq_norm]
            calc
              dist w (a i) ≤
                  dist w (c i) + dist (c i) (a i) :=
                dist_triangle _ _ _
              _ ≤ 6 * r := by
                rw [ha i]
                linarith
          have haz :
              (D - 3) * r ≤ dist (a i) z := by
            have htri :
                dist (c i) z ≤
                  dist (c i) (a i) + dist (a i) z :=
              dist_triangle _ _ _
            rw [ha i] at htri
            linarith [ht i hi]
          have hazpos : 0 < dist (a i) z :=
            hR.trans_le haz
          have hwzpos : 0 < ‖w - z‖ := by
            rw [← dist_eq_norm]
            have htri :
                dist (c i) z ≤
                  dist (c i) w + dist w z :=
              dist_triangle _ _ _
            have hcw : dist (c i) w < 3 * r := by
              simpa only [dist_comm] using hwc
            have : (D - 3) * r < dist w z := by
              linarith [ht i hi]
            exact hR.trans this
          have hsix :
              6 * r ≤ dist (a i) z := by
            have : 6 < D - 3 := by linarith
            exact (mul_le_mul_of_nonneg_right this.le hr.le).trans haz
          have hdist :
              ‖w - z‖ ≤ 2 * dist (a i) z := by
            rw [← dist_eq_norm]
            calc
              dist w z ≤ dist w (a i) + dist (a i) z :=
                dist_triangle _ _ _
              _ ≤ 6 * r + dist (a i) z := by
                gcongr
                simpa only [dist_eq_norm] using hwa
              _ ≤ 2 * dist (a i) z := by
                linarith
          have hinv :
              (dist (a i) z)⁻¹ ≤
                2 * ‖w - z‖⁻¹ := by
            calc
              (dist (a i) z)⁻¹ ≤
                  (‖w - z‖ / 2)⁻¹ := by
                exact
                  (inv_le_inv₀ hazpos (half_pos hwzpos)).2
                    (by linarith)
              _ = 2 * ‖w - z‖⁻¹ := by
                field_simp [ne_of_gt hwzpos]
          have hinv3 :
              (dist (a i) z)⁻¹ ^ 3 ≤
                8 * ‖w - z‖⁻¹ ^ 3 := by
            calc
              (dist (a i) z)⁻¹ ^ 3
                  ≤ (2 * ‖w - z‖⁻¹) ^ 3 :=
                pow_le_pow_left₀
                  (inv_nonneg.mpr (dist_nonneg : 0 ≤ dist (a i) z))
                  hinv 3
              _ = 8 * ‖w - z‖⁻¹ ^ 3 := by ring
          have hscale :
              r ^ 2 * ‖q i w‖ + r * ‖q₁ i w‖ ≤
                7 * r ^ 2 * ‖q i w‖ := by
            dsimp only [q₁]
            rw [norm_mul]
            calc
              r ^ 2 * ‖q i w‖ +
                    r * (‖w - a i‖ * ‖q i w‖)
                  ≤
                  r ^ 2 * ‖q i w‖ +
                    r * (6 * r * ‖q i w‖) := by
                gcongr
              _ = 7 * r ^ 2 * ‖q i w‖ := by ring
          dsimp only [e]
          calc
            (r ^ 2 * ‖q i w‖ + r * ‖q₁ i w‖) *
                  (dist (a i) z)⁻¹ ^ 3
                ≤
                (7 * r ^ 2 * ‖q i w‖) *
                  (8 * ‖w - z‖⁻¹ ^ 3) := by
              exact
                mul_le_mul hscale hinv3 (by positivity)
                  (by positivity)
            _ =
                (56 * r ^ 2 * ‖w - z‖⁻¹ ^ 3) *
                  ‖q i w‖ := by ring
      _ =
          (56 * r ^ 2 * ‖w - z‖⁻¹ ^ 3) *
            (∑ i ∈ t, ‖q i w‖) := by
        rw [Finset.mul_sum]
      _ ≤
          (56 * r ^ 2 * ‖w - z‖⁻¹ ^ 3) * L := by
        apply mul_le_mul_of_nonneg_left
        · calc
            (∑ i ∈ t, ‖q i w‖)
                ≤ ∑ i, ‖q i w‖ := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_univ t)
                (fun _ _ _ ↦ norm_nonneg _)
            _ ≤ L := by
              exact
                sum_norm_rawPartitionCorrectionDensity_uniform_le_of_card
                  S C hC c r hr hcover ψ g b osc M
                  hψnorm hω hM hosc hcard w
        · positivity
      _ =
          (56 * r ^ 2 * L) * ‖w - z‖⁻¹ ^ 3 := by
        ring
  calc
    (∑ i ∈ t,
        (r ^ 2 * ‖∫ w : ℂ, q i w‖ +
            r * ‖∫ w : ℂ, q₁ i w‖) *
          (dist (a i) z)⁻¹ ^ 3)
        ≤ ∑ i ∈ t, ∫ w : ℂ, e i w := by
      exact Finset.sum_le_sum fun i _hi ↦ hmoment i
    _ = ∫ w : ℂ, ∑ i ∈ t, e i w := by
      rw [MeasureTheory.integral_finsetSum t
        (fun i _hi ↦ heIntegrable i)]
    _ = ∫ w : ℂ in
          (Metric.ball z ((D - 3) * r))ᶜ,
          ∑ i ∈ t, e i w := by
      symm
      apply
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      exact hzero w hw
    _ ≤ ∫ w : ℂ in
          (Metric.ball z ((D - 3) * r))ᶜ,
          (56 * r ^ 2 * L) * ‖w - z‖⁻¹ ^ 3 := by
      apply MeasureTheory.setIntegral_mono_on
        hsumIntegrable.integrableOn
        ((integrableOn_norm_sub_inv_pow_three_compl_ball
          z ((D - 3) * r) hR).const_mul _)
        measurableSet_ball.compl
      intro w _hw
      exact hpoint w
    _ =
        (56 * r ^ 2 * L) *
          ∫ w : ℂ in
            (Metric.ball z ((D - 3) * r))ᶜ,
            ‖w - z‖⁻¹ ^ 3 := by
      rw [MeasureTheory.integral_const_mul]
    _ =
        224 * osc * M ^ 2 * (C : ℝ) *
          ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
            ‖w‖⁻¹ ^ 3 := by
      rw [show (D - 3) * r = r * (D - 3) by ring,
        integral_norm_sub_inv_pow_three_compl_ball_mul
          z (D - 3) r hr]
      dsimp only [L]
      field_simp [hr.ne']
      ring

/-- The bounded replacements of all far pieces retain their two Laurent
moments with a scale-free aggregate cubic error. -/
theorem norm_sum_boundedMomentReplacement_sub_moments_far_scaled_le
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c q₀ a : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M D : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M)
    (hD : 9 < D)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (ha : ∀ i, dist (c i) (a i) = 3 * r)
    (c₂ : ℂ) (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (R : ι → ℝ)
    (d : ∀ i, BoundedLaurentCapacity K (a i) (R i))
    (hδlow : ∀ i, 2 * r < ‖q₀ i - a i‖)
    (hδhigh : ∀ i, ‖q₀ i - a i‖ < 4 * r)
    (hRadius :
      ∀ i, R i = scaleCapacityRadius ρ * r)
    (hc₁ :
      ∀ i, (d i).c₁ = (q₀ i - a i) * (1 / 100))
    (hc₂ :
      ∀ i, (d i).c₂ = (q₀ i - a i) ^ 2 * c₂)
    (hLinear :
      ∀ i, (d i).L =
        4 * scaleCapacityLinearConstant c₂ B ρ * r)
    (hCubic :
      ∀ i, (d i).B = 64 * B * r ^ 3)
    (hDcap : scaleCapacityRadius ρ + 3 ≤ D)
    (t : Finset ι) (z : K)
    (ht :
      ∀ i ∈ t, D * r ≤ dist (c i) (z : ℂ)) :
    ‖∑ i ∈ t,
        ((boundedMomentReplacement (d i)
            (∫ w : ℂ,
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w)
            (∫ w : ℂ,
              (w - a i) *
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w) :
              C(K, ℂ)) z -
          ((a i - (z : ℂ))⁻¹ *
              (∫ w : ℂ,
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w) -
            (a i - (z : ℂ))⁻¹ ^ 2 *
              (∫ w : ℂ,
                (w - a i) *
                  rawPartitionCorrectionDensity
                    (uniformSmoothPartition S c r hr hcover)
                    ψ g b i w)))‖ ≤
      224 * scaleReplacementFarConstant c₂ B ρ *
        osc * M ^ 2 * (C : ℝ) *
          ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
            ‖w‖⁻¹ ^ 3 := by
  classical
  let χ :=
    uniformSmoothPartition S c r hr hcover
  let m₀ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      rawPartitionCorrectionDensity χ ψ g b i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      (w - a i) *
        rawPartitionCorrectionDensity χ ψ g b i w
  have hfar (i : ι) (hi : i ∈ t) :
      scaleCapacityRadius ρ * r ≤
        dist (a i) (z : ℂ) := by
    have htri :
        dist (c i) (z : ℂ) ≤
          dist (c i) (a i) + dist (a i) (z : ℂ) :=
      dist_triangle _ _ _
    rw [ha i] at htri
    have hscale :
        scaleCapacityRadius ρ * r ≤
          (D - 3) * r :=
      mul_le_mul_of_nonneg_right
        (by linarith : scaleCapacityRadius ρ ≤ D - 3)
        hr.le
    exact hscale.trans (by linarith [ht i hi])
  change
    ‖∑ i ∈ t,
        ((boundedMomentReplacement (d i)
            (m₀ i) (m₁ i) : C(K, ℂ)) z -
          ((a i - (z : ℂ))⁻¹ * m₀ i -
            (a i - (z : ℂ))⁻¹ ^ 2 * m₁ i))‖ ≤ _
  calc
    ‖∑ i ∈ t,
        ((boundedMomentReplacement (d i)
            (m₀ i) (m₁ i) : C(K, ℂ)) z -
          ((a i - (z : ℂ))⁻¹ * m₀ i -
            (a i - (z : ℂ))⁻¹ ^ 2 * m₁ i))‖
        ≤ ∑ i ∈ t,
            ‖((boundedMomentReplacement (d i)
                (m₀ i) (m₁ i) : C(K, ℂ)) z -
              ((a i - (z : ℂ))⁻¹ * m₀ i -
                (a i - (z : ℂ))⁻¹ ^ 2 * m₁ i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ t,
          scaleReplacementFarConstant c₂ B ρ *
            (r ^ 2 * ‖m₀ i‖ + r * ‖m₁ i‖) *
              (dist (a i) (z : ℂ))⁻¹ ^ 3 := by
      apply Finset.sum_le_sum
      intro i hi
      exact
        norm_boundedMomentReplacement_sub_moments_scale_far_le
          hr c₂ B ρ hB hρ (d i)
            (hδlow i) (hδhigh i) (hRadius i)
            (hc₁ i) (hc₂ i) (hLinear i) (hCubic i)
            (m₀ i) (m₁ i) z (hfar i hi)
    _ =
        scaleReplacementFarConstant c₂ B ρ *
          ∑ i ∈ t,
            (r ^ 2 * ‖m₀ i‖ + r * ‖m₁ i‖) *
              (dist (a i) (z : ℂ))⁻¹ ^ 3 := by
      simp only [← mul_assoc, Finset.mul_sum]
    _ ≤
        scaleReplacementFarConstant c₂ B ρ *
          (224 * osc * M ^ 2 * (C : ℝ) *
            ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3) := by
      apply mul_le_mul_of_nonneg_left
      · exact
          sum_rawPartitionCorrection_momentScales_poleKernel_far_le
            S C hC c a r hr hcover ψ g b hψ hg
              osc M D hψnorm hω hM hD hosc hcard ha
                t (z : ℂ) ht
      · exact scaleReplacementFarConstant_nonneg c₂ hB hρ.le
    _ =
        224 * scaleReplacementFarConstant c₂ B ρ *
          osc * M ^ 2 * (C : ℝ) *
            ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3 := by
      ring

/-- The global boundedness of the capacity functions controls the sum of
all replacements whose source centers are near the evaluation point. -/
theorem norm_sum_boundedMomentReplacement_near_scaled_le
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c q₀ a : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M D : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (ha : ∀ i, dist (c i) (a i) = 3 * r)
    (c₂ : ℂ)
    (R : ι → ℝ)
    (d : ∀ i, BoundedLaurentCapacity K (a i) (R i))
    (hδlow : ∀ i, 2 * r < ‖q₀ i - a i‖)
    (hδhigh : ∀ i, ‖q₀ i - a i‖ < 4 * r)
    (hc₁ :
      ∀ i, (d i).c₁ = (q₀ i - a i) * (1 / 100))
    (hc₂ :
      ∀ i, (d i).c₂ = (q₀ i - a i) ^ 2 * c₂)
    (t : Finset ι) (z : K)
    (ht :
      ∀ i ∈ t, dist (c i) (z : ℂ) < D * r) :
    ‖∑ i ∈ t,
        (boundedMomentReplacement (d i)
          (∫ w : ℂ,
            rawPartitionCorrectionDensity
              (uniformSmoothPartition S c r hr hcover)
              ψ g b i w)
          (∫ w : ℂ,
            (w - a i) *
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w) :
            C(K, ℂ)) z‖ ≤
      28 * scaleReplacementGlobalConstant c₂ *
        Real.pi * (D + 3) ^ 2 *
          osc * M ^ 2 * (C : ℝ) := by
  classical
  let χ :=
    uniformSmoothPartition S c r hr hcover
  let m₀ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      rawPartitionCorrectionDensity χ ψ g b i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      (w - a i) *
        rawPartitionCorrectionDensity χ ψ g b i w
  change
    ‖∑ i ∈ t,
        (boundedMomentReplacement (d i)
          (m₀ i) (m₁ i) : C(K, ℂ)) z‖ ≤ _
  calc
    ‖∑ i ∈ t,
        (boundedMomentReplacement (d i)
          (m₀ i) (m₁ i) : C(K, ℂ)) z‖
        ≤ ∑ i ∈ t,
            ‖(boundedMomentReplacement (d i)
              (m₀ i) (m₁ i) : C(K, ℂ)) z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ t,
          scaleReplacementGlobalConstant c₂ *
            (r⁻¹ * ‖m₀ i‖ +
              r⁻¹ ^ 2 * ‖m₁ i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact
        norm_boundedMomentReplacement_scale_le
          hr c₂ (d i) (hδlow i) (hδhigh i)
            (hc₁ i) (hc₂ i) (m₀ i) (m₁ i) z
    _ =
        scaleReplacementGlobalConstant c₂ *
          ∑ i ∈ t,
            (r⁻¹ * ‖m₀ i‖ +
              r⁻¹ ^ 2 * ‖m₁ i‖) := by
      rw [Finset.mul_sum]
    _ ≤
        scaleReplacementGlobalConstant c₂ *
          (28 * Real.pi * (D + 3) ^ 2 *
            osc * M ^ 2 * (C : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact
          sum_rawPartitionCorrection_momentScales_near_le
            S C hC c a r hr hcover ψ g b hψ hg
              osc M hψnorm hω hM hosc hcard ha
                t (z : ℂ) D hD ht
      · exact scaleReplacementGlobalConstant_nonneg c₂
    _ =
        28 * scaleReplacementGlobalConstant c₂ *
          Real.pi * (D + 3) ^ 2 *
            osc * M ^ 2 * (C : ℝ) := by
      ring

/-- Combining the bounded near field with the moment-matched far field
controls the full raw-correction replacement error by one explicit
multiple of the common oscillation. -/
theorem norm_sum_rawPartitionCorrection_sub_boundedReplacement_le
    {K : Set ℂ} [CompactSpace K]
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c q₀ a : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (osc M D : ℝ)
    (hψnorm : ∀ z, ‖ψ z‖ ≤ 1)
    (hω : 0 ≤ osc) (hM : 0 ≤ M)
    (hD : 9 < D)
    (hosc :
      ∀ i w, w ∈ Metric.ball (c i) (3 * r) →
        ‖g w - b i‖ ≤ osc)
    (hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M)
    (ha : ∀ i, dist (c i) (a i) = 3 * r)
    (c₂ : ℂ) (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (R : ι → ℝ)
    (d : ∀ i, BoundedLaurentCapacity K (a i) (R i))
    (hδlow : ∀ i, 2 * r < ‖q₀ i - a i‖)
    (hδhigh : ∀ i, ‖q₀ i - a i‖ < 4 * r)
    (hRadius :
      ∀ i, R i = scaleCapacityRadius ρ * r)
    (hc₁ :
      ∀ i, (d i).c₁ = (q₀ i - a i) * (1 / 100))
    (hc₂ :
      ∀ i, (d i).c₂ = (q₀ i - a i) ^ 2 * c₂)
    (hLinear :
      ∀ i, (d i).L =
        4 * scaleCapacityLinearConstant c₂ B ρ * r)
    (hCubic :
      ∀ i, (d i).B = 64 * B * r ^ 3)
    (hDcap : scaleCapacityRadius ρ + 3 ≤ D)
    (z : K) :
    ‖∑ i,
        ((∫ w : ℂ,
            (w - (z : ℂ))⁻¹ *
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w) -
          (boundedMomentReplacement (d i)
            (∫ w : ℂ,
              rawPartitionCorrectionDensity
                (uniformSmoothPartition S c r hr hcover)
                ψ g b i w)
            (∫ w : ℂ,
              (w - a i) *
                rawPartitionCorrectionDensity
                  (uniformSmoothPartition S c r hr hcover)
                  ψ g b i w) :
              C(K, ℂ)) z)‖ ≤
      osc *
        (4 * M ^ 2 * (C : ℝ) *
            (∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖) +
          28 * scaleReplacementGlobalConstant c₂ *
            Real.pi * (D + 3) ^ 2 * M ^ 2 * (C : ℝ) +
          576 * M ^ 2 * (C : ℝ) *
            (∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3) +
          224 * scaleReplacementFarConstant c₂ B ρ *
            M ^ 2 * (C : ℝ) *
              (∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
                ‖w‖⁻¹ ^ 3)) := by
  classical
  let χ :=
    uniformSmoothPartition S c r hr hcover
  let m₀ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      rawPartitionCorrectionDensity χ ψ g b i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      (w - a i) *
        rawPartitionCorrectionDensity χ ψ g b i w
  let T : ι → ℂ :=
    fun i ↦ ∫ w : ℂ,
      (w - (z : ℂ))⁻¹ *
        rawPartitionCorrectionDensity χ ψ g b i w
  let U : ι → ℂ :=
    fun i ↦
      (boundedMomentReplacement (d i)
        (m₀ i) (m₁ i) : C(K, ℂ)) z
  let V : ι → ℂ :=
    fun i ↦
      (a i - (z : ℂ))⁻¹ * m₀ i -
        (a i - (z : ℂ))⁻¹ ^ 2 * m₁ i
  let near : Finset ι :=
    Finset.univ.filter
      (fun i ↦ dist (c i) (z : ℂ) < D * r)
  let far : Finset ι :=
    Finset.univ.filter
      (fun i ↦ ¬ dist (c i) (z : ℂ) < D * r)
  have hfarInsert :
      (∑ i ∈ far, (T i - U i)) =
        (∑ i ∈ far, (T i - V i)) -
          (∑ i ∈ far, (U i - V i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit :
      (∑ i, (T i - U i)) =
        (∑ i ∈ near, T i) -
          (∑ i ∈ near, U i) +
        ((∑ i ∈ far, (T i - V i)) -
          (∑ i ∈ far, (U i - V i))) := by
    have hpartition :=
      Finset.sum_filter_add_sum_filter_not
        Finset.univ
          (fun i ↦ dist (c i) (z : ℂ) < D * r)
          (fun i ↦ T i - U i)
    calc
      (∑ i, (T i - U i)) =
          (∑ i ∈ near, (T i - U i)) +
            (∑ i ∈ far, (T i - U i)) := by
        dsimp only [near, far]
        exact hpartition.symm
      _ =
          (∑ i ∈ near, T i) -
              (∑ i ∈ near, U i) +
            ((∑ i ∈ far, (T i - V i)) -
              (∑ i ∈ far, (U i - V i))) := by
        rw [Finset.sum_sub_distrib, hfarInsert]
  have hnear (i : ι) (hi : i ∈ near) :
      dist (c i) (z : ℂ) < D * r := by
    exact Finset.mem_filter.mp hi |>.2
  have hfar (i : ι) (hi : i ∈ far) :
      D * r ≤ dist (c i) (z : ℂ) := by
    exact le_of_not_gt (Finset.mem_filter.mp hi |>.2)
  have hnearRaw :
      ‖∑ i ∈ near, T i‖ ≤
        osc * (4 * M ^ 2 * (C : ℝ)) *
          ∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖ := by
    exact
      norm_sum_integral_rawPartitionCorrectionDensity_uniform_near_scaled_le
        S C hC c r hr hcover ψ g b hψ hg
          osc M hψnorm hω hM hosc hcard
            near (z : ℂ) D hnear
  have hnearReplacement :
      ‖∑ i ∈ near, U i‖ ≤
        28 * scaleReplacementGlobalConstant c₂ *
          Real.pi * (D + 3) ^ 2 *
            osc * M ^ 2 * (C : ℝ) := by
    exact
      norm_sum_boundedMomentReplacement_near_scaled_le
        S C hC c q₀ a r hr hcover ψ g b hψ hg
          osc M D hψnorm hω hM (by linarith) hosc hcard ha
            c₂ R d hδlow hδhigh hc₁ hc₂
              near z hnear
  have hfarRaw :
      ‖∑ i ∈ far, (T i - V i)‖ ≤
        576 * osc * M ^ 2 * (C : ℝ) *
          ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
            ‖w‖⁻¹ ^ 3 := by
    calc
      ‖∑ i ∈ far, (T i - V i)‖ ≤
          16 * (3 + 3) ^ 2 * osc * M ^ 2 * (C : ℝ) *
            ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3 := by
        simpa only [T, V, m₀, m₁, χ] using
          norm_sum_integral_rawPartitionCorrectionDensity_sub_moments_far_scaled_le
            S C hC c a r hr hcover ψ g b hψ hg
              osc M 3 D hψnorm hω hM (by norm_num)
                (by norm_num [hD]) hosc hcard
                  (fun i ↦ (ha i).le) far (z : ℂ) hfar
      _ =
          576 * osc * M ^ 2 * (C : ℝ) *
            ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3 := by
        norm_num
  have hfarReplacement :
      ‖∑ i ∈ far, (U i - V i)‖ ≤
        224 * scaleReplacementFarConstant c₂ B ρ *
          osc * M ^ 2 * (C : ℝ) *
            ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3 := by
    simpa only [U, V, m₀, m₁, χ] using
      norm_sum_boundedMomentReplacement_sub_moments_far_scaled_le
        S C hC c q₀ a r hr hcover ψ g b hψ hg
          osc M D hψnorm hω hM hD hosc hcard ha
            c₂ B ρ hB hρ R d hδlow hδhigh
              hRadius hc₁ hc₂ hLinear hCubic hDcap
                far z hfar
  change ‖∑ i, (T i - U i)‖ ≤ _
  rw [hsplit]
  calc
    ‖(∑ i ∈ near, T i) -
          (∑ i ∈ near, U i) +
        ((∑ i ∈ far, (T i - V i)) -
          (∑ i ∈ far, (U i - V i)))‖
        ≤
          (‖∑ i ∈ near, T i‖ +
            ‖∑ i ∈ near, U i‖) +
          (‖∑ i ∈ far, (T i - V i)‖ +
            ‖∑ i ∈ far, (U i - V i)‖) := by
      exact
        (norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
    _ ≤
        (osc * (4 * M ^ 2 * (C : ℝ)) *
            (∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖) +
          28 * scaleReplacementGlobalConstant c₂ *
            Real.pi * (D + 3) ^ 2 *
              osc * M ^ 2 * (C : ℝ)) +
        (576 * osc * M ^ 2 * (C : ℝ) *
            (∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
              ‖w‖⁻¹ ^ 3) +
          224 * scaleReplacementFarConstant c₂ B ρ *
            osc * M ^ 2 * (C : ℝ) *
              (∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
                ‖w‖⁻¹ ^ 3)) :=
      add_le_add
        (add_le_add hnearRaw hnearReplacement)
        (add_le_add hfarRaw hfarReplacement)
    _ = _ := by ring

end Submission.Helpers
