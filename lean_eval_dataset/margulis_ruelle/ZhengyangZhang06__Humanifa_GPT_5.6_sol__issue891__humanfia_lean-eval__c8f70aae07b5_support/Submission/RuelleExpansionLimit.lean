import Submission.RuelleAlignedGrid
import Submission.LyapunovTimeReversal

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology
open scoped Real

lemma normalized_derivativeExpansion_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    derivativeExpansion (T^[n]) (T_inv^[n]) x / n =
      max 0 (Real.log ‖fderiv ℝ (T^[n]) x‖ / n) +
        max 0 (-Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) := by
  cases n with
  | zero =>
      simp [derivativeExpansion, fderiv_id]
  | succ n =>
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hbackpos :
          0 < ‖fderiv ℝ (T_inv^[n + 1]) (T^[n + 1] x)‖ :=
        norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
          hT_right hT_left (n + 1) (T^[n + 1] x)
      have hmax_div (a : ℝ) :
          max 0 a / ((n + 1 : ℕ) : ℝ) =
            max 0 (a / ((n + 1 : ℕ) : ℝ)) := by
        calc
          max 0 a / ((n + 1 : ℕ) : ℝ) =
              max (0 / ((n + 1 : ℕ) : ℝ))
                (a / ((n + 1 : ℕ) : ℝ)) :=
            (max_div_div_right hn.le 0 a).symm
          _ = max 0 (a / ((n + 1 : ℕ) : ℝ)) := by rw [zero_div]
      rw [derivativeExpansion,
        fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right,
        Real.posLog_apply, Real.posLog_apply,
        Real.log_div one_ne_zero hbackpos.ne', Real.log_one, zero_sub,
        add_div]
      simp only [hmax_div]

theorem tendsto_integral_normalized_derivativeExpansion
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu)
    (hErg : Ergodic T mu) :
    Tendsto
      (fun n : ℕ =>
        ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x / n ∂mu)
      atTop
      (nhds
        (max 0 (∫ x, lyapunovUpperAt T x ∂mu) +
          max 0 (∫ x, lyapunovLowerAt T x ∂mu))) := by
  obtain ⟨C, hC_one, hC⟩ :=
    compact_fderiv_bound T hT_smooth hK_compact
  let F : ℕ → EucPlane → ℝ := fun n x =>
    derivativeExpansion (T^[n]) (T_inv^[n]) x / n
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) mu := by
    exact ((continuous_derivativeExpansion
      (T^[n]) (T_inv^[n])
      (contDiff_iterate T hT_smooth n)
      (contDiff_iterate T_inv hT_inv_smooth n)
      (hT_left.iterate n) (hT_right.iterate n)).measurable.div_const n)
        |>.aestronglyMeasurable
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC_one
  have hF_bound (n : ℕ) :
      ∀ᵐ x ∂mu, ‖F n x‖ ≤ 2 * Real.log C := by
    filter_upwards [mem_ae_iff.mpr hmu_supp] with x hx
    change ‖derivativeExpansion (T^[n]) (T_inv^[n]) x / n‖ ≤
      2 * Real.log C
    rw [normalized_derivativeExpansion_eq
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
    have hu := log_norm_fderiv_iterate_div_le
      T hT_smooth hK_inv hC_one hC n hx
    have hv := neg_log_le_log_norm_fderiv_iterate_inverse_div
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_inv hC_one hC n hx
    have hu_nonneg :
        0 ≤ max 0 (Real.log ‖fderiv ℝ (T^[n]) x‖ / n) :=
      le_max_left _ _
    have hv_nonneg :
        0 ≤ max 0 (-Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) :=
      le_max_left _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hu_nonneg hv_nonneg)]
    have hu' :
        max 0 (Real.log ‖fderiv ℝ (T^[n]) x‖ / n) ≤ Real.log C :=
      max_le hlogC hu
    have hv' :
        max 0 (-Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) ≤
          Real.log C :=
      max_le hlogC (by
        simpa only [neg_div, neg_neg] using neg_le_neg hv)
    linarith
  have hupper :=
    ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hlower :=
    ae_tendsto_log_norm_fderiv_iterate_inverse_div_neg_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hupper_const :=
    lyapunovUpperAt_ae_eq_integral
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hErg
  have hlower_const :=
    lyapunovLowerAt_ae_eq_integral
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hErg
  have hF_lim :
      ∀ᵐ x ∂mu, Tendsto (fun n => F n x) atTop
        (nhds
          (max 0 (∫ y, lyapunovUpperAt T y ∂mu) +
            max 0 (∫ y, lyapunovLowerAt T y ∂mu))) := by
    filter_upwards [hupper, hlower, hupper_const, hlower_const] with
      x hxupper hxlower hxupper_const hxlower_const
    have hu :
        Tendsto
          (fun n : ℕ => max 0
            (Real.log ‖fderiv ℝ (T^[n]) x‖ / n))
          atTop
          (nhds (max 0 (∫ y, lyapunovUpperAt T y ∂mu))) := by
      simpa [hxupper_const] using tendsto_const_nhds.max hxupper
    have hv :
        Tendsto
          (fun n : ℕ => max 0
            (-Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n))
          atTop
          (nhds (max 0 (∫ y, lyapunovLowerAt T y ∂mu))) := by
      have hxlower' :
          Tendsto
            (fun n : ℕ =>
              -(Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n))
            atTop (nhds (lyapunovLowerAt T x)) := by
        simpa using hxlower.neg
      have hzero :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds
      simpa [hxlower_const, neg_div] using hzero.max hxlower'
    simpa [F, normalized_derivativeExpansion_eq
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right] using hu.add hv
  simpa [F] using
    tendsto_integral_of_dominated_convergence
      (fun _ : EucPlane => 2 * Real.log C)
      hF_meas (integrable_const (2 * Real.log C)) hF_bound hF_lim

theorem kolmogorovSinaiEntropy_le_lyapunov_positive_parts
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu)
    (hErg : Ergodic T mu) :
    kolmogorovSinaiEntropy mu T ≤
      max 0 (∫ x, lyapunovUpperAt T x ∂mu) +
        max 0 (∫ x, lyapunovLowerAt T x ∂mu) := by
  let L :=
    max 0 (∫ x, lyapunovUpperAt T x ∂mu) +
      max 0 (∫ x, lyapunovLowerAt T x ∂mu)
  have hexpansion :
      Tendsto
        (fun n : ℕ =>
          ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x / n ∂mu)
        atTop (nhds L) := by
    simpa [L] using
      tendsto_integral_normalized_derivativeExpansion
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv mu hmu_supp hT hErg
  have hpenalty :
      Tendsto (fun n : ℕ => Real.log 3969 / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have htotal :
      Tendsto
        (fun n : ℕ =>
          Real.log 3969 / n +
            ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x / n ∂mu)
        atTop (nhds L) := by
    simpa using hpenalty.add hexpansion
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        kolmogorovSinaiEntropy mu T ≤
          Real.log 3969 / n +
            ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x / n ∂mu := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    calc
      kolmogorovSinaiEntropy mu T ≤
          (Real.log 3969 +
            ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x ∂mu) / n :=
        kolmogorovSinaiEntropy_le_finiteDerivativeExpansion
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv mu hmu_supp hT hn
      _ = Real.log 3969 / n +
          ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x / n ∂mu := by
        rw [add_div, integral_div]
  exact ge_of_tendsto htotal hbound

end Submission.Helpers
