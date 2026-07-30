import Submission.Helpers
import Submission.Morrey
import Submission.ProductKernel

namespace Submission.FirstOrder

open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory
open ContinuousLinearMap Filter
open scoped Convolution ENNReal NNReal Topology

namespace PK

open ProductKernel

theorem regularize_half_sub {n : ℕ} {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hdu : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    {t : ℝ} (ht : 0 < t) (x : E n) :
    regularize n (t / 2) u x - regularize n t u x =
      ∑ i : Fin n, ∫ y, du i y * bridge n t i (x - y) := by
  have ht2 : t / 2 ≠ 0 := div_ne_zero ht.ne' (by norm_num)
  have hIntKernel (s : ℝ) (hs : s ≠ 0) :
      Integrable (fun y ↦ u y * kernel n s (x - y)) volume := by
    simpa only [smul_eq_mul] using
      hu.integrable_smul_right_of_hasCompactSupport
        (reflectedKernel_contDiff n hs x).continuous
        (reflectedKernel_hasCompactSupport n hs x)
  have hIntKernel' (s : ℝ) (hs : s ≠ 0) :
      Integrable (fun y ↦ kernel n s (x - y) * u y) volume := by
    simpa only [mul_comm] using hIntKernel s hs
  have hIntBridge (i : Fin n) :
      Integrable (fun y ↦ u y * partialDeriv i (bridge n t i) (x - y)) volume := by
    have hcBase :
        ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i (bridge n t i)) := by
      have h := (bridge_contDiff n ht.ne' i).fderiv_right
        (m := (⊤ : ℕ∞)) (by simp)
      unfold partialDeriv
      exact h.clm_apply contDiff_const
    have hc :
        ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ partialDeriv i (bridge n t i) (x - y)) := by
      fun_prop
    have hcompactBase : HasCompactSupport (partialDeriv i (bridge n t i)) := by
      unfold partialDeriv
      exact (bridge_hasCompactSupport n ht.ne' i).fderiv_apply ℝ
        (EuclideanSpace.single i (1 : ℝ))
    have hcompact : HasCompactSupport
        (fun y ↦ partialDeriv i (bridge n t i) (x - y)) := by
      change HasCompactSupport
        ((partialDeriv i (bridge n t i)) ∘ Homeomorph.subLeft x)
      exact hcompactBase.comp_homeomorph (Homeomorph.subLeft x)
    simpa only [smul_eq_mul] using
      hu.integrable_smul_right_of_hasCompactSupport hc.continuous hcompact
  have hpair (i : Fin n) :
      ∫ y, u y * partialDeriv i (bridge n t i) (x - y) =
        ∫ y, du i y * bridge n t i (x - y) := by
    have h := Submission.Helpers.IsWeakDeriv.integral_mul_partialDeriv_eq_neg
      (hdu i)
      (fun y ↦ bridge n t i (x - y))
      (reflectedBridge_contDiff n ht.ne' i x)
      (reflectedBridge_hasCompactSupport n ht.ne' i x)
    simpa only [partialDeriv_reflectedBridge n ht.ne' i x, mul_neg, integral_neg,
      neg_inj] using h
  rw [regularize_apply, regularize_apply]
  calc
    (∫ y, kernel n (t / 2) (x - y) * u y) -
          ∫ y, kernel n t (x - y) * u y =
        ∫ y, u y * (kernel n (t / 2) (x - y) - kernel n t (x - y)) := by
          rw [← integral_sub (hIntKernel' (t / 2) ht2)
            (hIntKernel' t ht.ne')]
          exact integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ by ring
    _ = ∫ y, ∑ i : Fin n,
          u y * partialDeriv i (bridge n t i) (x - y) := by
          apply integral_congr_ae
          filter_upwards with y
          rw [← Finset.mul_sum, sum_partialDeriv_bridge n ht (x - y)]
    _ = ∑ i : Fin n, ∫ y,
          u y * partialDeriv i (bridge n t i) (x - y) := by
          rw [integral_finsetSum]
          intro i _
          exact hIntBridge i
    _ = ∑ i : Fin n, ∫ y, du i y * bridge n t i (x - y) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hpair i

theorem regularize_eq_swap {n : ℕ} (t : ℝ) (u : E n → ℝ) :
    regularize n t u =
      u ⋆[lsmul ℝ ℝ, volume] kernel n t := by
  funext x
  rw [regularize_apply, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [lsmul_apply, smul_eq_mul]
  ring

theorem partialDeriv_regularize {n : ℕ} {u du : E n → ℝ} {i : Fin n}
    (hu : LocallyIntegrable u volume)
    (hweak : IsWeakDeriv u du (Helpers.coordMulti i))
    {t : ℝ} (ht : t ≠ 0) (x : E n) :
    partialDeriv i (regularize n t u) x = regularize n t du x := by
  have hk1 : ContDiff ℝ 1 (kernel n t) :=
    (kernel_contDiff n ht).of_le (by simp)
  have hd :=
    (kernel_hasCompactSupport n ht).hasFDerivAt_convolution_right
      (lsmul ℝ ℝ) hu hk1 x
  have hfd :
      fderiv ℝ (regularize n t u) x =
        (u ⋆[(lsmul ℝ ℝ).precompR (E n), volume]
          fderiv ℝ (kernel n t)) x := by
    rw [regularize_eq_swap]
    exact hd.fderiv
  unfold partialDeriv
  rw [hfd]
  rw [convolution_precompR_apply (L := lsmul ℝ ℝ) hu
    ((kernel_hasCompactSupport n ht).fderiv ℝ)
    ((kernel_contDiff n ht).continuous_fderiv (by norm_num)) x
    (EuclideanSpace.single i (1 : ℝ))]
  change
    (u ⋆[lsmul ℝ ℝ, volume] partialDeriv i (kernel n t)) x =
      regularize n t du x
  rw [convolution_def, regularize_apply]
  have hpair :=
    Submission.Helpers.IsWeakDeriv.integral_mul_partialDeriv_eq_neg
      hweak
      (fun y ↦ kernel n t (x - y))
      (reflectedKernel_contDiff n ht x)
      (reflectedKernel_hasCompactSupport n ht x)
  simpa only [lsmul_apply, smul_eq_mul,
    partialDeriv_reflectedKernel n ht i x, mul_neg, integral_neg, neg_inj,
    mul_comm] using hpair

theorem bridge_reflection_eq_zero_of_notMem_ball {n : ℕ} {t : ℝ} (ht : 0 < t)
    (i : Fin n) (x y : E n)
    (hy : y ∉ Metric.ball x (((n : ℝ) + 1) * t)) :
    bridge n t i (x - y) = 0 := by
  rw [← Function.notMem_support]
  intro hsupport
  have hball := bridge_support_subset_ball n ht i hsupport
  rw [Metric.mem_ball, dist_zero_right] at hball
  apply hy
  rw [Metric.mem_ball]
  simpa only [dist_eq_norm, norm_sub_rev] using hball

theorem kernel_reflection_eq_zero_of_notMem_ball {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x y : E n) (hy : y ∉ Metric.ball x (((n : ℝ) + 1) * t)) :
    kernel n t (x - y) = 0 := by
  rw [← Function.notMem_support]
  intro hsupport
  have hball := kernel_support_subset_ball n ht hsupport
  rw [Metric.mem_ball, dist_zero_right] at hball
  apply hy
  rw [Metric.mem_ball]
  simpa only [dist_eq_norm, norm_sub_rev] using hball

theorem integral_reflectedKernel {n : ℕ} {t : ℝ} (ht : 0 < t) (x : E n) :
    ∫ y, kernel n t (x - y) = 1 := by
  calc
    ∫ y, kernel n t (x - y) =
        (kernel n t ⋆[lsmul ℝ ℝ, volume] fun _ : E n ↦ 1) x := by
          rw [convolution_eq_swap]
          simp only [lsmul_apply, smul_eq_mul, mul_one]
    _ = ∫ y, kernel n t y := by
      rw [convolution_def]
      simp only [lsmul_apply, smul_eq_mul, mul_one]
    _ = 1 := kernel_integral n ht

theorem volume_real_closedBall_scaled {n : ℕ} (x : E n) {t : ℝ}
    (ht : 0 ≤ t) :
    volume.real (Metric.closedBall x (((n : ℝ) + 1) * t)) =
      (((n : ℝ) + 1) * t) ^ n *
        volume.real (Metric.closedBall (0 : E n) 1) := by
  rw [Measure.addHaar_real_closedBall' volume x (mul_nonneg (by positivity) ht)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]

/-- The product mollifiers form an approximate identity at almost every
Lebesgue point. -/
theorem ae_tendsto_regularize {n : ℕ} {u : E n → ℝ}
    (hu : LocallyIntegrable u volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun j ↦ regularize n (Submission.Morrey.scale j) u x)
        atTop (𝓝 (u x)) := by
  obtain ⟨C, _hC, hCbound⟩ := exists_baseKernel_bound n
  let R : ℝ := (n : ℝ) + 1
  let V : ℝ := volume.real (Metric.closedBall (0 : E n) 1)
  let K : ℝ := C * R ^ n * V
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hV : 0 < V := by
    dsimp [V]
    exact ENNReal.toReal_pos
      (Metric.measure_closedBall_pos volume (0 : E n) zero_lt_one).ne'
      measure_closedBall_lt_top.ne
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hu]
      with x hx
  have hradius :
      Tendsto (fun j ↦ R * Submission.Morrey.scale j) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by
      simpa using tendsto_const_nhds.mul Submission.Morrey.tendsto_scale, ?_⟩
    exact Filter.Eventually.of_forall fun j ↦
      mul_pos hR (Submission.Morrey.scale_pos j)
  have havg :=
    ((hx.comp (Besicovitch.tendsto_filterAt volume x))).comp hradius
  have hlim := tendsto_integral_smul_of_tendsto_average_norm_sub K havg
    (Filter.Eventually.of_forall fun j ↦
      hu.integrableOn_isCompact
        (isCompact_closedBall x (R * Submission.Morrey.scale j)))
    (tendsto_const_nhds.congr fun j ↦
      (integral_reflectedKernel (Submission.Morrey.scale_pos j) x).symm)
    (Filter.Eventually.of_forall fun j ↦ by
      intro y hy
      apply Metric.ball_subset_closedBall
      by_contra hyball
      exact hy (kernel_reflection_eq_zero_of_notMem_ball
        (Submission.Morrey.scale_pos j) x y (by simpa only [R] using hyball)))
    (Filter.Eventually.of_forall fun j y ↦ by
      have ht := Submission.Morrey.scale_pos j
      have hbound := abs_kernel_le n ht hCbound (x - y)
      have hvolume :
          volume.real (Metric.closedBall x (R * Submission.Morrey.scale j)) =
            (R * Submission.Morrey.scale j) ^ n * V := by
        simpa only [R, V] using
          volume_real_closedBall_scaled x ht.le
      have heq :
          K / volume.real (Metric.closedBall x (R * Submission.Morrey.scale j)) =
            (Submission.Morrey.scale j ^ n)⁻¹ * C := by
        rw [hvolume]
        dsimp [K]
        rw [mul_pow]
        field_simp [hR.ne', ht.ne', hV.ne']
      exact hbound.trans_eq heq.symm)
  simpa only [regularize_apply, smul_eq_mul, R] using hlim

theorem abs_integral_mul_bridge_le {n : ℕ} {p q t C : ℝ}
    (hpq : p.HolderConjugate q) (ht : 0 < t)
    {v : E n → ℝ} (hv : MemLp v (ENNReal.ofReal p) volume)
    (hvloc : LocallyIntegrable v volume)
    (hC : ∀ i : Fin n, ∀ z : E n, |baseBridge n i z| ≤ C)
    (i : Fin n) (x : E n) :
    |∫ y, v y * bridge n t i (x - y)| ≤
      t ^ (1 - n : ℤ) * C *
        (volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) *
          (∫ y, ‖v y‖ ^ p) ^ (1 / p)) := by
  let B := Metric.ball x (((n : ℝ) + 1) * t)
  have hB : MeasurableSet B := measurableSet_ball
  have hscale_nonneg : 0 ≤ t ^ (1 - n : ℤ) * C := by
    have hC0 : 0 ≤ C := (abs_nonneg (baseBridge n i 0)).trans (hC i 0)
    positivity
  have hvB : IntegrableOn (fun y ↦ ‖v y‖) B volume :=
    IntegrableOn.mono_set
      ((hvloc.integrableOn_isCompact
        (isCompact_closedBall x (((n : ℝ) + 1) * t))).norm)
      Metric.ball_subset_closedBall
  calc
    |∫ y, v y * bridge n t i (x - y)| ≤
        ∫ y, |v y * bridge n t i (x - y)| := abs_integral_le_integral_abs
    _ = ∫ y in B, |v y * bridge n t i (x - y)| := by
      rw [← integral_indicator hB]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ B
      · simp [hy]
      · simp [hy, B, bridge_reflection_eq_zero_of_notMem_ball ht i x y]
    _ ≤ ∫ y in B, (t ^ (1 - n : ℤ) * C) * ‖v y‖ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun y ↦ abs_nonneg _
      · exact hvB.const_mul _
      · filter_upwards with y
        calc
          |v y * bridge n t i (x - y)| =
              ‖v y‖ * |bridge n t i (x - y)| := by
                rw [abs_mul, Real.norm_eq_abs]
          _ ≤ ‖v y‖ * (t ^ (1 - n : ℤ) * C) :=
            mul_le_mul_of_nonneg_left (abs_bridge_le n ht hC i _) (norm_nonneg _)
          _ = (t ^ (1 - n : ℤ) * C) * ‖v y‖ := mul_comm _ _
    _ = (t ^ (1 - n : ℤ) * C) * ∫ y in B, ‖v y‖ := by
      rw [integral_const_mul]
    _ ≤ (t ^ (1 - n : ℤ) * C) *
        (volume.real B ^ (1 / q) * (∫ y, ‖v y‖ ^ p) ^ (1 / p)) := by
      exact mul_le_mul_of_nonneg_left
        (Submission.Morrey.integral_norm_ball_le hpq hv x (((n : ℝ) + 1) * t))
        hscale_nonneg

theorem abs_integral_mul_kernel_le {n : ℕ} {p q t C : ℝ}
    (hpq : p.HolderConjugate q) (ht : 0 < t)
    {v : E n → ℝ} (hv : MemLp v (ENNReal.ofReal p) volume)
    (hvloc : LocallyIntegrable v volume)
    (hC : ∀ z : E n, |baseKernel n z| ≤ C) (x : E n) :
    |∫ y, kernel n t (x - y) * v y| ≤
      (t ^ n)⁻¹ * C *
        (volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) *
          (∫ y, ‖v y‖ ^ p) ^ (1 / p)) := by
  let B := Metric.ball x (((n : ℝ) + 1) * t)
  have hB : MeasurableSet B := measurableSet_ball
  have hscale_nonneg : 0 ≤ (t ^ n)⁻¹ * C := by
    have hC0 : 0 ≤ C := (abs_nonneg (baseKernel n 0)).trans (hC 0)
    positivity
  have hvB : IntegrableOn (fun y ↦ ‖v y‖) B volume :=
    IntegrableOn.mono_set
      ((hvloc.integrableOn_isCompact
        (isCompact_closedBall x (((n : ℝ) + 1) * t))).norm)
      Metric.ball_subset_closedBall
  calc
    |∫ y, kernel n t (x - y) * v y| ≤
        ∫ y, |kernel n t (x - y) * v y| := abs_integral_le_integral_abs
    _ = ∫ y in B, |kernel n t (x - y) * v y| := by
      rw [← integral_indicator hB]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ B
      · simp [hy]
      · simp [hy, B, kernel_reflection_eq_zero_of_notMem_ball ht x y]
    _ ≤ ∫ y in B, ((t ^ n)⁻¹ * C) * ‖v y‖ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun y ↦ abs_nonneg _
      · exact hvB.const_mul _
      · filter_upwards with y
        calc
          |kernel n t (x - y) * v y| =
              ‖v y‖ * |kernel n t (x - y)| := by
                rw [abs_mul, Real.norm_eq_abs, mul_comm]
          _ ≤ ‖v y‖ * ((t ^ n)⁻¹ * C) :=
            mul_le_mul_of_nonneg_left (abs_kernel_le n ht hC _) (norm_nonneg _)
          _ = ((t ^ n)⁻¹ * C) * ‖v y‖ := mul_comm _ _
    _ = ((t ^ n)⁻¹ * C) * ∫ y in B, ‖v y‖ := by
      rw [integral_const_mul]
    _ ≤ ((t ^ n)⁻¹ * C) *
        (volume.real B ^ (1 / q) * (∫ y, ‖v y‖ ^ p) ^ (1 / p)) := by
      exact mul_le_mul_of_nonneg_left
        (Submission.Morrey.integral_norm_ball_le hpq hv x (((n : ℝ) + 1) * t))
        hscale_nonneg

theorem volume_real_ball_scaled {n : ℕ} (_hn : 0 < n) (x : E n) {t : ℝ}
    (ht : 0 < t) :
    volume.real (Metric.ball x (((n : ℝ) + 1) * t)) =
      (((n : ℝ) + 1) * t) ^ n *
        volume.real (Metric.ball (0 : E n) 1) := by
  change
    (volume (Metric.ball x (((n : ℝ) + 1) * t))).toReal =
      (((n : ℝ) + 1) * t) ^ n *
        (volume (Metric.ball (0 : E n) 1)).toReal
  have hradius : 0 < ((n : ℝ) + 1) * t := mul_pos (by positivity) ht
  have hpow : 0 ≤ (((n : ℝ) + 1) * t) ^ n := pow_nonneg hradius.le n
  rw [Measure.addHaar_ball_of_pos volume x hradius]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hpow]

theorem bridge_scale_factor_eq {n : ℕ} (hn : 0 < n) {p q t C : ℝ}
    (hpq : p.HolderConjugate q) (ht : 0 < t) (x : E n) :
    t ^ (1 - n : ℤ) * C *
        volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) =
      (C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
        volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))) *
          t ^ (Submission.Morrey.morreyExponent n p) := by
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hV : 0 ≤ volume.real (Metric.ball (0 : E n) 1) := measureReal_nonneg
  have hexp :
      (((1 - n : ℤ) : ℤ) : ℝ) + (n : ℝ) / q =
        Submission.Morrey.morreyExponent n p := by
    rw [Submission.Morrey.morreyExponent]
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hpq.one_sub_inv]
    ring
  have hvolpow :
      volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) =
        ((((n : ℝ) + 1) ^ ((n : ℝ) / q) * t ^ ((n : ℝ) / q)) *
          volume.real (Metric.ball (0 : E n) 1) ^ (1 / q)) := by
    rw [volume_real_ball_scaled hn x ht,
      Real.mul_rpow (pow_nonneg (mul_nonneg hR.le ht.le) n) hV,
      ← Real.rpow_natCast,
      ← Real.rpow_mul (mul_nonneg hR.le ht.le) (n : ℝ) (1 / q),
      (show (n : ℝ) * (1 / q) = (n : ℝ) / q by ring),
      Real.mul_rpow hR.le ht.le]
  have htpow :
      t ^ (1 - n : ℤ) = t ^ ((((1 - n : ℤ) : ℤ) : ℝ)) := by
    rw [Real.rpow_intCast]
  rw [hvolpow, htpow]
  calc
    _ = (C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
          volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))) *
        (t ^ ((((1 - n : ℤ) : ℤ) : ℝ)) * t ^ ((n : ℝ) / q)) := by ring
    _ = _ := by rw [← Real.rpow_add ht, hexp]

theorem kernel_scale_factor_eq {n : ℕ} (hn : 0 < n) {p q t C : ℝ}
    (hpq : p.HolderConjugate q) (ht : 0 < t) (x : E n) :
    (t ^ n)⁻¹ * C *
        volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) =
      (C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
        volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))) *
          t ^ (-(n : ℝ) / p) := by
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hV : 0 ≤ volume.real (Metric.ball (0 : E n) 1) := measureReal_nonneg
  have hexp :
      -(n : ℝ) + (n : ℝ) / q = -(n : ℝ) / p := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hpq.one_sub_inv]
    ring
  have hvolpow :
      volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) =
        ((((n : ℝ) + 1) ^ ((n : ℝ) / q) * t ^ ((n : ℝ) / q)) *
          volume.real (Metric.ball (0 : E n) 1) ^ (1 / q)) := by
    rw [volume_real_ball_scaled hn x ht,
      Real.mul_rpow (pow_nonneg (mul_nonneg hR.le ht.le) n) hV,
      ← Real.rpow_natCast,
      ← Real.rpow_mul (mul_nonneg hR.le ht.le) (n : ℝ) (1 / q),
      (show (n : ℝ) * (1 / q) = (n : ℝ) / q by ring),
      Real.mul_rpow hR.le ht.le]
  have htpow : (t ^ n)⁻¹ = t ^ (-(n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le]
  rw [hvolpow, htpow]
  calc
    _ = (C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
          volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))) *
        (t ^ (-(n : ℝ)) * t ^ ((n : ℝ) / q)) := by ring
    _ = _ := by rw [← Real.rpow_add ht, hexp]

theorem norm_clm_le_sum_basis {n : ℕ} (L : E n →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
  intro x
  have hx :
      x = ∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ) := by
    classical
    apply PiLp.ext
    intro k
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  have hLx :
      L x = ∑ i : Fin n, x i • L (EuclideanSpace.single i (1 : ℝ)) := by
    calc
      L x = L (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) :=
        congrArg L hx
      _ = ∑ i : Fin n, x i • L (EuclideanSpace.single i (1 : ℝ)) := by
        rw [map_sum]
        simp only [map_smul]
  calc
    ‖L x‖ =
        ‖∑ i : Fin n, x i • L (EuclideanSpace.single i (1 : ℝ))‖ := by
      exact congrArg (fun z ↦ ‖z‖) hLx
    _ ≤
        ∑ i : Fin n, ‖x i • L (EuclideanSpace.single i (1 : ℝ))‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin n, ‖x i‖ * ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
      simp only [norm_smul]
    _ ≤ ∑ i : Fin n, ‖x‖ * ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact PiLp.norm_apply_le x i
    _ = (∑ i : Fin n, ‖L (EuclideanSpace.single i (1 : ℝ))‖) * ‖x‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

noncomputable def lpSize (p : ℝ) {n : ℕ} (v : E n → ℝ) : ℝ :=
  (∫ y, ‖v y‖ ^ p) ^ (1 / p)

theorem lpSize_nonneg (p : ℝ) {n : ℕ} (v : E n → ℝ) :
    0 ≤ lpSize p v := by
  have hint : 0 ≤ ∫ y, ‖v y‖ ^ p :=
    integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg (v y)) p
  exact Real.rpow_nonneg hint _

theorem exists_dyadic_bracket {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) :
    ∃ j : ℕ,
      Submission.Morrey.scale (j + 1) < d ∧
        d ≤ Submission.Morrey.scale j := by
  have hex : ∃ N : ℕ, Submission.Morrey.scale N < d :=
    ((tendsto_order.1 Submission.Morrey.tendsto_scale).2 d hd0).exists
  let N := Nat.find hex
  have hN : Submission.Morrey.scale N < d := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos h
    rw [hN0] at hN
    simp only [Submission.Morrey.scale, pow_zero] at hN
    linarith
  refine ⟨N - 1, ?_, ?_⟩
  · rwa [Nat.sub_add_cancel hNpos]
  · apply le_of_not_gt
    intro hbad
    have hle : N ≤ N - 1 := Nat.find_min' hex hbad
    omega

theorem exists_fderiv_regularize_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → ∀ x,
      ‖fderiv ℝ (regularize n t u) x‖ ≤ B * t ^ (-(n : ℝ) / p) := by
  let q := Submission.Morrey.conjugateExponent p
  have hp1 : 1 < p := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hn1.trans_lt hp
  have hpq : p.HolderConjugate q :=
    Submission.Morrey.holderConjugate_conjugateExponent hp1
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    exact hp1.le
  obtain ⟨C, hC, hCbound⟩ := exists_baseKernel_bound n
  let K : ℝ :=
    C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
      volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))
  let S : ℝ := ∑ i : Fin n, lpSize p (du i)
  refine ⟨K * S, mul_nonneg ?_
    (Finset.sum_nonneg fun i _ ↦ lpSize_nonneg p (du i)), ?_⟩
  · exact mul_nonneg hC.le
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg measureReal_nonneg _))
  intro t ht x
  apply (norm_clm_le_sum_basis (fderiv ℝ (regularize n t u) x)).trans
  calc
    ∑ i : Fin n,
        ‖fderiv ℝ (regularize n t u) x
          (EuclideanSpace.single i (1 : ℝ))‖ ≤
        ∑ i : Fin n, K * t ^ (-(n : ℝ) / p) * lpSize p (du i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← partialDeriv, partialDeriv_regularize hu (hweak i) ht.ne' x,
        Real.norm_eq_abs, regularize_apply]
      calc
        |∫ y, kernel n t (x - y) * du i y| ≤
            (t ^ n)⁻¹ * C *
              (volume.real (Metric.ball x (((n : ℝ) + 1) * t)) ^ (1 / q) *
                lpSize p (du i)) := by
                  exact abs_integral_mul_kernel_le hpq ht (hdu i)
                    ((hdu i).locallyIntegrable hpENN) hCbound x
        _ = K * t ^ (-(n : ℝ) / p) * lpSize p (du i) := by
          rw [← mul_assoc, kernel_scale_factor_eq hn hpq ht x]
    _ = K * S * t ^ (-(n : ℝ) / p) := by
      rw [show K * S * t ^ (-(n : ℝ) / p) =
        (K * t ^ (-(n : ℝ) / p)) * S by ring]
      dsimp [S]
      rw [Finset.mul_sum]

theorem exists_regularize_spatial_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → ∀ x y,
      dist (regularize n t u x) (regularize n t u y) ≤
        B * t ^ (-(n : ℝ) / p) * dist x y := by
  obtain ⟨B, hB, hderiv⟩ :=
    exists_fderiv_regularize_bound hn hp hu hweak hdu
  refine ⟨B, hB, fun ht x y ↦ ?_⟩
  have hdiff :
      Differentiable ℝ (regularize n _ u) :=
    (regularize_contDiff n ht.ne' hu).differentiable (by norm_num)
  simpa only [dist_eq_norm, norm_sub_rev] using
    (Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Set.univ) (x := x) (y := y)
      (fun z _ ↦ hdiff z)
      (fun z _ ↦ hderiv ht z)
      convex_univ (Set.mem_univ x) (Set.mem_univ y))

theorem exists_regularize_step_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ j x,
        dist (regularize n (Submission.Morrey.scale j) u x)
            (regularize n (Submission.Morrey.scale (j + 1)) u x) ≤
          A * ((1 / 2 : ℝ) ^ Submission.Morrey.morreyExponent n p) ^ j := by
  let q := Submission.Morrey.conjugateExponent p
  have hp1 : 1 < p := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hn1.trans_lt hp
  have hpq : p.HolderConjugate q :=
    Submission.Morrey.holderConjugate_conjugateExponent hp1
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    exact hp1.le
  obtain ⟨C, hC, hCbound⟩ := exists_baseBridge_bound n
  let K : ℝ :=
    C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
      volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))
  let S : ℝ := ∑ i : Fin n, lpSize p (du i)
  refine ⟨K * S, mul_nonneg ?_ (Finset.sum_nonneg fun i _ ↦ lpSize_nonneg p (du i)), ?_⟩
  · exact mul_nonneg hC.le
      (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) _)
        (Real.rpow_nonneg measureReal_nonneg _))
  intro j x
  have ht : 0 < Submission.Morrey.scale j := Submission.Morrey.scale_pos j
  have hscale_succ :
      Submission.Morrey.scale (j + 1) = Submission.Morrey.scale j / 2 := by
    simp only [Submission.Morrey.scale, pow_succ]
    ring
  have hscale_rpow :
      Submission.Morrey.scale j ^ Submission.Morrey.morreyExponent n p =
        ((1 / 2 : ℝ) ^ Submission.Morrey.morreyExponent n p) ^ j := by
    rw [Submission.Morrey.scale, ← Real.rpow_pow_comm (by norm_num :
      (0 : ℝ) ≤ 1 / 2)]
  rw [Real.dist_eq]
  calc
    |regularize n (Submission.Morrey.scale j) u x -
        regularize n (Submission.Morrey.scale (j + 1)) u x| =
        |∑ i : Fin n, ∫ y,
          du i y * bridge n (Submission.Morrey.scale j) i (x - y)| := by
            rw [hscale_succ, abs_sub_comm, regularize_half_sub hu hweak ht x]
    _ ≤ ∑ i : Fin n, |∫ y,
          du i y * bridge n (Submission.Morrey.scale j) i (x - y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,
        K * Submission.Morrey.scale j ^ Submission.Morrey.morreyExponent n p *
          lpSize p (du i) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |∫ y, du i y * bridge n (Submission.Morrey.scale j) i (x - y)| ≤
            Submission.Morrey.scale j ^ (1 - n : ℤ) * C *
              (volume.real
                  (Metric.ball x (((n : ℝ) + 1) * Submission.Morrey.scale j)) ^
                    (1 / q) *
                lpSize p (du i)) := by
                  exact abs_integral_mul_bridge_le hpq ht (hdu i)
                    ((hdu i).locallyIntegrable hpENN) hCbound i x
        _ = K * Submission.Morrey.scale j ^
              Submission.Morrey.morreyExponent n p * lpSize p (du i) := by
                rw [← mul_assoc, bridge_scale_factor_eq hn hpq ht x]
    _ = K * S * ((1 / 2 : ℝ) ^ Submission.Morrey.morreyExponent n p) ^ j := by
      rw [← hscale_rpow]
      rw [show K * S *
          Submission.Morrey.scale j ^ Submission.Morrey.morreyExponent n p =
        (K * Submission.Morrey.scale j ^
          Submission.Morrey.morreyExponent n p) * S by ring]
      dsimp [S]
      rw [Finset.mul_sum]

noncomputable def morreyRep (n : ℕ) (u : E n → ℝ) : E n → ℝ :=
  fun x ↦ limUnder atTop
    (fun j ↦ regularize n (Submission.Morrey.scale j) u x)

theorem regularize_cauchy {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume)
    (x : E n) :
    CauchySeq (fun j ↦ regularize n (Submission.Morrey.scale j) u x) := by
  obtain ⟨A, _hA, hstep⟩ :=
    exists_regularize_step_bound hn hp hu hweak hdu
  let ρ : ℝ :=
    (1 / 2 : ℝ) ^ Submission.Morrey.morreyExponent n p
  have hβ : 0 < Submission.Morrey.morreyExponent n p :=
    Submission.Morrey.morreyExponent_pos hn hp
  have hρ : ρ < 1 := by
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  exact cauchySeq_of_le_geometric ρ A hρ fun j ↦ hstep j x

theorem tendsto_regularize_morreyRep {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume)
    (x : E n) :
    Tendsto (fun j ↦ regularize n (Submission.Morrey.scale j) u x)
      atTop (𝓝 (morreyRep n u x)) := by
  exact (regularize_cauchy hn hp hu hweak hdu x).tendsto_limUnder

theorem tendstoUniformly_regularize_morreyRep {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    TendstoUniformly
      (fun j x ↦ regularize n (Submission.Morrey.scale j) u x)
      (morreyRep n u) atTop := by
  obtain ⟨A, _hA, hstep⟩ :=
    exists_regularize_step_bound hn hp hu hweak hdu
  let ρ : ℝ :=
    (1 / 2 : ℝ) ^ Submission.Morrey.morreyExponent n p
  have hβ : 0 < Submission.Morrey.morreyExponent n p :=
    Submission.Morrey.morreyExponent_pos hn hp
  have hρ0 : 0 ≤ ρ :=
    Real.rpow_nonneg (by norm_num) _
  have hρ : ρ < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have htend (x : E n) :
      Tendsto (fun j ↦ regularize n (Submission.Morrey.scale j) u x)
        atTop (𝓝 (morreyRep n u x)) :=
    (cauchySeq_of_le_geometric ρ A hρ fun j ↦ hstep j x).tendsto_limUnder
  have htail (j : ℕ) (x : E n) :
      dist (regularize n (Submission.Morrey.scale j) u x) (morreyRep n u x) ≤
        A * ρ ^ j / (1 - ρ) :=
    dist_le_of_le_geometric_of_tendsto ρ A hρ (fun j ↦ hstep j x)
      (htend x) j
  have htail_tendsto :
      Tendsto (fun j ↦ A * ρ ^ j / (1 - ρ)) atTop (𝓝 0) := by
    convert
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ)).div_const (1 - ρ) using 1
    simp
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 htail_tendsto).2 ε hε] with j hj
  intro x
  rw [dist_comm]
  exact (htail j x).trans_lt hj

theorem exists_regularize_morreyRep_tail_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ j x,
      dist (regularize n (Submission.Morrey.scale j) u x) (morreyRep n u x) ≤
        T * Submission.Morrey.scale j ^
          Submission.Morrey.morreyExponent n p := by
  obtain ⟨A, hA, hstep⟩ :=
    exists_regularize_step_bound hn hp hu hweak hdu
  let β := Submission.Morrey.morreyExponent n p
  let ρ : ℝ := (1 / 2 : ℝ) ^ β
  have hβ : 0 < β := Submission.Morrey.morreyExponent_pos hn hp
  have hρ : ρ < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hdenom : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ.le
  refine ⟨A / (1 - ρ), div_nonneg hA hdenom, fun j x ↦ ?_⟩
  have htend :
      Tendsto (fun j ↦ regularize n (Submission.Morrey.scale j) u x)
        atTop (𝓝 (morreyRep n u x)) :=
    (cauchySeq_of_le_geometric ρ A hρ fun j ↦ hstep j x).tendsto_limUnder
  have htail :=
    dist_le_of_le_geometric_of_tendsto ρ A hρ
      (fun j ↦ hstep j x) htend j
  have hscale :
      Submission.Morrey.scale j ^ β = ρ ^ j := by
    rw [Submission.Morrey.scale, ← Real.rpow_pow_comm (by norm_num :
      (0 : ℝ) ≤ 1 / 2)]
  rw [hscale]
  simpa only [β, ρ, div_mul_eq_mul_div] using htail

theorem morreyRep_continuous {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    Continuous (morreyRep n u) := by
  apply (tendstoUniformly_regularize_morreyRep hn hp hu hweak hdu).continuous
  exact Eventually.frequently <| Eventually.of_forall fun j ↦
    (regularize_contDiff n (Submission.Morrey.scale_pos j).ne' hu).continuous

theorem ae_eq_morreyRep {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    u =ᵐ[volume] morreyRep n u := by
  filter_upwards [ae_tendsto_regularize hu] with x hx
  exact tendsto_nhds_unique hx
    (tendsto_regularize_morreyRep hn hp hu hweak hdu x)

theorem exists_morreyRep_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (huLp : MemLp u (ENNReal.ofReal p) volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖morreyRep n u x‖ ≤ M := by
  obtain ⟨T, hT, htail⟩ :=
    exists_regularize_morreyRep_tail_bound hn hp hu hweak hdu
  let q := Submission.Morrey.conjugateExponent p
  have hp1 : 1 < p := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hn1.trans_lt hp
  have hpq : p.HolderConjugate q :=
    Submission.Morrey.holderConjugate_conjugateExponent hp1
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    exact hp1.le
  obtain ⟨C, hC, hCbound⟩ := exists_baseKernel_bound n
  let K : ℝ :=
    C * (((n : ℝ) + 1) ^ ((n : ℝ) / q) *
      volume.real (Metric.ball (0 : E n) 1) ^ (1 / q))
  have hK : 0 ≤ K := by
    exact mul_nonneg hC.le
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg measureReal_nonneg _))
  have hreg (x : E n) :
      ‖regularize n 1 u x‖ ≤ K * lpSize p u := by
    rw [Real.norm_eq_abs, regularize_apply]
    calc
      |∫ y, kernel n 1 (x - y) * u y| ≤
          ((1 : ℝ) ^ n)⁻¹ * C *
            (volume.real (Metric.ball x (((n : ℝ) + 1) * 1)) ^ (1 / q) *
              lpSize p u) := by
                exact abs_integral_mul_kernel_le hpq zero_lt_one huLp
                  (huLp.locallyIntegrable hpENN) hCbound x
      _ = K * lpSize p u := by
        rw [← mul_assoc, kernel_scale_factor_eq hn hpq zero_lt_one x]
        simp only [Real.one_rpow, mul_one]
        rfl
  refine ⟨K * lpSize p u + T,
    add_nonneg (mul_nonneg hK (lpSize_nonneg p u)) hT, fun x ↦ ?_⟩
  calc
    ‖morreyRep n u x‖ =
        ‖regularize n 1 u x +
          (morreyRep n u x - regularize n 1 u x)‖ := by ring_nf
    _ ≤ ‖regularize n 1 u x‖ +
        ‖morreyRep n u x - regularize n 1 u x‖ := norm_add_le _ _
    _ ≤ K * lpSize p u + T := by
      apply add_le_add (hreg x)
      simpa only [Submission.Morrey.scale, pow_zero, Real.one_rpow, mul_one,
        dist_eq_norm, norm_sub_rev] using htail 0 x

theorem exists_morreyRep_holder_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (huLp : MemLp u (ENNReal.ofReal p) volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y,
      dist (morreyRep n u x) (morreyRep n u y) ≤
        H * dist x y ^ Submission.Morrey.morreyExponent n p := by
  obtain ⟨T, hT, htail⟩ :=
    exists_regularize_morreyRep_tail_bound hn hp hu hweak hdu
  obtain ⟨B, hB, hspatial⟩ :=
    exists_regularize_spatial_bound hn hp hu hweak hdu
  obtain ⟨M, hM, hbound⟩ :=
    exists_morreyRep_bound hn hp hu huLp hweak hdu
  let β := Submission.Morrey.morreyExponent n p
  have hβ : 0 < β := Submission.Morrey.morreyExponent_pos hn hp
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  have hβ1 : β < 1 := by
    dsimp [β, Submission.Morrey.morreyExponent]
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have : 0 < (n : ℝ) / p := div_pos hn0 hp0
    linarith
  let Hlocal : ℝ := 2 * T * (2 : ℝ) ^ β + B
  let Hglobal : ℝ := 2 * M
  have hHlocal : 0 ≤ Hlocal := by
    dsimp [Hlocal]
    positivity
  have hHglobal : 0 ≤ Hglobal := by
    dsimp [Hglobal]
    positivity
  refine ⟨max Hlocal Hglobal, hHlocal.trans (le_max_left _ _), fun x y ↦ ?_⟩
  by_cases hxy : x = y
  · subst y
    simp only [dist_self]
    rw [Real.zero_rpow (Submission.Morrey.morreyExponent_pos hn hp).ne']
    simp
  let d := dist x y
  have hd0 : 0 < d := dist_pos.mpr hxy
  by_cases hd1 : d < 1
  · obtain ⟨j, hjlow, hjhigh⟩ := exists_dyadic_bracket hd0 hd1
    let t := Submission.Morrey.scale j
    have ht : 0 < t := Submission.Morrey.scale_pos j
    have htsucc :
        Submission.Morrey.scale (j + 1) = t / 2 := by
      dsimp [t, Submission.Morrey.scale]
      rw [pow_succ]
      ring
    have ht2d : t < 2 * d := by
      rw [htsucc] at hjlow
      linarith
    have htβ :
        t ^ β ≤ (2 : ℝ) ^ β * d ^ β := by
      calc
        t ^ β ≤ (2 * d) ^ β :=
          Real.rpow_le_rpow ht.le ht2d.le hβ.le
        _ = (2 : ℝ) ^ β * d ^ β :=
          Real.mul_rpow (by norm_num) hd0.le
    have hexp : -(n : ℝ) / p = β - 1 := by
      dsimp [β, Submission.Morrey.morreyExponent]
      ring
    have hpowneg :
        t ^ (β - 1) ≤ d ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hd0 hjhigh (by linarith)
    have hpowmul : d ^ (β - 1) * d = d ^ β := by
      calc
        d ^ (β - 1) * d = d ^ (β - 1) * d ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = d ^ ((β - 1) + 1) := by
          rw [Real.rpow_add hd0]
        _ = d ^ β := by
          congr 1
          ring
    have htailx :
        dist (morreyRep n u x) (regularize n t u x) ≤ T * t ^ β := by
      simpa only [t, β, dist_comm] using htail j x
    have htailx' :
        dist (morreyRep n u x) (regularize n t u x) ≤
          T * ((2 : ℝ) ^ β * d ^ β) :=
      htailx.trans (mul_le_mul_of_nonneg_left htβ hT)
    have htail_y :
        dist (regularize n t u y) (morreyRep n u y) ≤ T * t ^ β := by
      simpa only [t, β] using htail j y
    have htail_y' :
        dist (regularize n t u y) (morreyRep n u y) ≤
          T * ((2 : ℝ) ^ β * d ^ β) :=
      htail_y.trans (mul_le_mul_of_nonneg_left htβ hT)
    have hspace :
        dist (regularize n t u x) (regularize n t u y) ≤
          B * t ^ (β - 1) * d := by
      simpa only [d, hexp] using hspatial ht x y
    have hspace' :
        dist (regularize n t u x) (regularize n t u y) ≤
          B * d ^ β := by
      calc
        dist (regularize n t u x) (regularize n t u y) ≤
            B * t ^ (β - 1) * d := hspace
        _ ≤ B * d ^ (β - 1) * d := by
          gcongr
        _ = B * d ^ β := by rw [mul_assoc, hpowmul]
    calc
      dist (morreyRep n u x) (morreyRep n u y) ≤
          dist (morreyRep n u x) (regularize n t u x) +
            dist (regularize n t u x) (regularize n t u y) +
              dist (regularize n t u y) (morreyRep n u y) :=
        dist_triangle4 _ _ _ _
      _ ≤ T * ((2 : ℝ) ^ β * d ^ β) +
            B * d ^ β + T * ((2 : ℝ) ^ β * d ^ β) :=
        add_le_add (add_le_add htailx' hspace') htail_y'
      _ = Hlocal * d ^ β := by
        dsimp [Hlocal]
        ring
      _ ≤ max Hlocal Hglobal * d ^ β :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd0.le _)
  · have hd1' : 1 ≤ d := le_of_not_gt hd1
    have hdpow : 1 ≤ d ^ β := Real.one_le_rpow hd1' hβ.le
    calc
      dist (morreyRep n u x) (morreyRep n u y) ≤
          ‖morreyRep n u x‖ + ‖morreyRep n u y‖ :=
        dist_le_norm_add_norm _ _
      _ ≤ M + M := add_le_add (hbound x) (hbound y)
      _ = Hglobal := by
        dsimp [Hglobal]
        ring
      _ ≤ Hglobal * d ^ β := by
        nlinarith
      _ ≤ max Hlocal Hglobal * d ^ β :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd0.le _)

theorem morreyRep_holder {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (huLp : MemLp u (ENNReal.ofReal p) volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    ∃ C : NNReal,
      HolderWith C (Submission.Morrey.morreyExponent n p).toNNReal
        (morreyRep n u) := by
  obtain ⟨H, hH, hholder⟩ :=
    exists_morreyRep_holder_bound hn hp hu huLp hweak hdu
  have hβ :
      0 ≤ Submission.Morrey.morreyExponent n p :=
    (Submission.Morrey.morreyExponent_pos hn hp).le
  refine ⟨H.toNNReal, fun x y ↦ ?_⟩
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ NNReal.zero_le_coe,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  change
    dist (morreyRep n u x) (morreyRep n u y) ≤
      (H.toNNReal : ℝ) *
        dist x y ^ ((Submission.Morrey.morreyExponent n p).toNNReal : ℝ)
  simpa only [Real.coe_toNNReal _ hH, Real.coe_toNNReal _ hβ] using
    hholder x y

theorem morreyRep_memHolder_zero {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : (n : ℝ) < p) {u : E n → ℝ} {du : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume)
    (huLp : MemLp u (ENNReal.ofReal p) volume)
    (hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume) :
    MemHolder 0 (Submission.Morrey.morreyExponent n p) (morreyRep n u) := by
  have hcont := morreyRep_continuous hn hp hu hweak hdu
  obtain ⟨C, hholder⟩ :=
    morreyRep_holder hn hp hu huLp hweak hdu
  obtain ⟨M, _hM, hbound⟩ :=
    exists_morreyRep_bound hn hp hu huLp hweak hdu
  refine ⟨contDiff_zero.mpr hcont, ?_, ?_⟩
  · refine ⟨C, ?_⟩
    rw [iteratedFDeriv_zero_eq_comp]
    have hiso :
        HolderWith 1 1
      (continuousMultilinearCurryFin0 ℝ (E n) ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ (E n) ℝ).symm.isometry.lipschitz.holderWith
    simpa only [one_mul, NNReal.coe_one, NNReal.rpow_one] using
      hiso.comp hholder
  · intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    refine ⟨M, fun x ↦ ?_⟩
    simpa only [norm_iteratedFDeriv_zero] using hbound x

end PK

end Submission.FirstOrder
