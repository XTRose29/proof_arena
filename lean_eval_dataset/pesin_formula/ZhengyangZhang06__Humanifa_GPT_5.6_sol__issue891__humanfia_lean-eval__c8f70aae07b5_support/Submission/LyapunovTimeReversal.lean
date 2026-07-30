import Submission.LyapunovGrowth
import Submission.LyapunovLimit

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma integrable_log_norm_fderiv_iterate_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0) (n : ℕ) :
    Integrable (fun x => Real.log ‖fderiv ℝ (T^[n]) x‖ / n) mu := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  apply integrable_of_full_measure_bounds mu hmu_supp
    (measurable_log_norm_fderiv_iterate_div T hT_smooth n)
  · exact fun x hx => neg_log_le_log_norm_fderiv_iterate_div
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right hK_inv
        hD_one hD n hx
  · exact fun x hx => log_norm_fderiv_iterate_div_le
      T hT_smooth hK_inv hC_one hC n hx

lemma integral_log_norm_fderiv_iterate_inverse_eq_inverse_iterate
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0) (hT : MeasurePreserving T mu mu)
    (n : ℕ) :
    (∫ x, Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n ∂mu) =
      ∫ x, Real.log ‖fderiv ℝ (T_inv^[n]) x‖ / n ∂mu := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hint : Integrable
      (fun x => Real.log ‖fderiv ℝ (T_inv^[n]) x‖ / n) mu :=
    integrable_log_norm_fderiv_iterate_div T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left hK_compact hK_inv_inv mu hmu_supp n
  calc
    (∫ x, Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n ∂mu) =
        ∫ x, Real.log ‖fderiv ℝ (T_inv^[n]) (T^[n] x)‖ / n ∂mu := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n =
          Real.log ‖fderiv ℝ (T_inv^[n]) (T^[n] x)‖ / n
        rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right]
    _ = ∫ x, Real.log ‖fderiv ℝ (T_inv^[n]) x‖ / n ∂mu :=
      integral_comp_measurePreserving (hT.iterate n) hint

theorem integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    (∫ x, lyapunovUpperAt T_inv x ∂mu) =
      -∫ x, lyapunovLowerAt T x ∂mu := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  let B : ℝ := max (Real.log C) (Real.log D)
  let u : ℕ → EucPlane → ℝ := fun n x =>
    Real.log ‖fderiv ℝ (T_inv^[n]) x‖ / n
  let v : ℕ → EucPlane → ℝ := fun n x =>
    Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n
  have hu_meas (n : ℕ) : AEStronglyMeasurable (u n) mu := by
    exact (measurable_log_norm_fderiv_iterate_div T_inv hT_inv_smooth n).aestronglyMeasurable
  have hv_meas (n : ℕ) : AEStronglyMeasurable (v n) mu := by
    exact (measurable_log_norm_fderiv_iterate_inverse_div
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right n).aestronglyMeasurable
  have hu_bound (n : ℕ) : ∀ᵐ x ∂mu, ‖u n x‖ ≤ B := by
    filter_upwards [mem_ae_iff.mpr hmu_supp] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · calc
        -B ≤ -Real.log C := neg_le_neg (le_max_left _ _)
        _ ≤ u n x := by
          exact neg_log_le_log_norm_fderiv_iterate_div
            T_inv T hT_inv_smooth hT_smooth hT_right hT_left hK_inv_inv
              hC_one hC n hx
    · calc
        u n x ≤ Real.log D := by
          exact log_norm_fderiv_iterate_div_le
            T_inv hT_inv_smooth hK_inv_inv hD_one hD n hx
        _ ≤ B := le_max_right _ _
  have hv_bound (n : ℕ) : ∀ᵐ x ∂mu, ‖v n x‖ ≤ B := by
    filter_upwards [mem_ae_iff.mpr hmu_supp] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · calc
        -B ≤ -Real.log C := neg_le_neg (le_max_left _ _)
        _ ≤ v n x := by
          exact neg_log_le_log_norm_fderiv_iterate_inverse_div
            T T_inv hT_smooth hT_inv_smooth hT_left hT_right hK_inv
              hC_one hC n hx
    · calc
        v n x ≤ Real.log D := by
          exact log_norm_fderiv_iterate_inverse_div_le
            T T_inv hT_smooth hT_inv_smooth hT_left hT_right hK_inv
              hD_one hD n hx
        _ ≤ B := le_max_right _ _
  have hu_lim : ∀ᵐ x ∂mu, Tendsto (fun n => u n x) atTop
      (nhds (lyapunovUpperAt T_inv x)) := by
    simpa [u] using
      (ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
        T_inv T hT_inv_smooth hT_smooth hT_right hT_left K
          hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv)
  have hv_lim : ∀ᵐ x ∂mu, Tendsto (fun n => v n x) atTop
      (nhds (-lyapunovLowerAt T x)) := by
    simpa [v] using
      (ae_tendsto_log_norm_fderiv_iterate_inverse_div_neg_lyapunovLowerAt
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
          hK_compact hK_inv mu hmu_supp hT hErg)
  have hu_tend := tendsto_integral_of_dominated_convergence
    (fun _ : EucPlane => B) hu_meas (integrable_const B) hu_bound hu_lim
  have hv_tend := tendsto_integral_of_dominated_convergence
    (fun _ : EucPlane => B) hv_meas (integrable_const B) hv_bound hv_lim
  have huv (n : ℕ) : (∫ x, u n x ∂mu) = ∫ x, v n x ∂mu := by
    symm
    simpa [u, v] using
      integral_log_norm_fderiv_iterate_inverse_eq_inverse_iterate
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          hK_compact hK_inv mu hmu_supp hT n
  have hu_tend' : Tendsto (fun n => ∫ x, v n x ∂mu) atTop
      (nhds (∫ x, lyapunovUpperAt T_inv x ∂mu)) := by
    convert hu_tend using 1
    funext n
    exact (huv n).symm
  have hlimits := tendsto_nhds_unique hu_tend' hv_tend
  simpa [integral_neg] using hlimits

theorem ae_lyapunovUpperAt_inverse_eq_neg_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    ∀ᵐ x ∂mu, lyapunovUpperAt T_inv x = -lyapunovLowerAt T x := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hupper := lyapunovUpperAt_ae_eq_integral
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hErg_inv
  have hlower := lyapunovLowerAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg
  have hint := integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
  filter_upwards [hupper, hlower] with x hxupper hxlower
  rw [hxupper, hxlower, hint]

theorem ae_tendsto_log_norm_fderiv_inverse_iterate_div_neg_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T_inv^[n]) x‖ / n)
      atTop (nhds (-lyapunovLowerAt T x)) := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hconv := ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left K
      hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have heq := ae_lyapunovUpperAt_inverse_eq_neg_lyapunovLowerAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
  filter_upwards [hconv, heq] with x hxconv hxeq
  simpa [hxeq] using hxconv

theorem ae_eventually_norm_fderiv_inverse_iterate_lt_exp_neg_integral_add
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T_inv^[n]) x‖ <
        Real.exp ((-(∫ y, lyapunovLowerAt T y ∂mu) + epsilon) * n) := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hbound := ae_eventually_norm_fderiv_iterate_lt_exp_integral_add
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left K
      hK_compact hK_inv_inv mu hmu_supp hErg_inv hepsilon
  have hint := integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
  rw [hint] at hbound
  exact hbound

end Submission.Helpers
