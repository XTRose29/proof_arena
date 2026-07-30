import Submission.CenteredLyapunovSubsequence
import Submission.HyperbolicBalance
import Submission.PlaneTwoSidedLinear

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma integral_logJacobian_inverse_eq_neg_lyapunov_sum
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    (∫ x, logJacobian T_inv x ∂mu) =
      -((∫ x, lyapunovUpperAt T x ∂mu) +
        ∫ x, lyapunovLowerAt T x ∂mu) := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hsum := integral_logJacobian_eq_integral_lyapunovUpper_add_lower
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left K
      hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have hupper := integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hT hErg
  have hswap := integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left K
      hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  rw [hsum, hupper]
  have hlower : (∫ x, lyapunovLowerAt T_inv x ∂mu) =
      -∫ x, lyapunovUpperAt T x ∂mu := by
    linarith
  rw [hlower]
  ring

lemma ae_tendsto_balancedForward_log_norm_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (_hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0) :
    ∀ᵐ x ∂mu, Tendsto
      (fun L => Real.log
        ‖fderiv ℝ (T^[balancedForward lam1 lam2 L]) x‖ / L)
      atTop (nhds (hyperbolicRate lam1 lam2)) := by
  have hconv := ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hT hErg
  have hexp := lyapunovUpperAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hErg
  have hindex := tendsto_balancedForward_atTop hlam1_pos hlam2_neg
  have hratio := tendsto_balancedForward_div hlam1_pos hlam2_neg
  filter_upwards [hconv, hexp] with x hxconv hxexp
  have hscaled := (hxconv.comp hindex).mul hratio
  have hlimit : lyapunovUpperAt T x * ((-lam2) / (lam1 - lam2)) =
      hyperbolicRate lam1 lam2 := by
    have hdenom : lam1 - lam2 ≠ 0 :=
      (sub_pos.mpr (hlam2_neg.trans hlam1_pos)).ne'
    rw [hxexp, ← hlam1]
    rw [hyperbolicRate]
    field_simp [hdenom]
  rw [hlimit] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 0,
    (eventually_gt_atTop 0).filter_mono hindex] with L hL hforward
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hforwardReal : (0 : ℝ) < balancedForward lam1 lam2 L := by
    exact_mod_cast hforward
  simp only [Function.comp_apply]
  field_simp [hLreal.ne', hforwardReal.ne']

lemma ae_tendsto_balancedBackward_log_norm_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 : ℝ}
    (_hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0) :
    ∀ᵐ x ∂mu, Tendsto
      (fun L => Real.log
        ‖fderiv ℝ (T_inv^[balancedBackward lam1 lam2 L]) x‖ / L)
      atTop (nhds (hyperbolicRate lam1 lam2)) := by
  have hconv := ae_tendsto_log_norm_fderiv_inverse_iterate_div_neg_lyapunovLowerAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hT hErg
  have hexp := lyapunovLowerAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hErg
  have hindex := tendsto_balancedBackward_atTop hlam1_pos hlam2_neg
  have hratio := tendsto_balancedBackward_div hlam1_pos hlam2_neg
  filter_upwards [hconv, hexp] with x hxconv hxexp
  have hscaled := (hxconv.comp hindex).mul hratio
  have hlimit : (-lyapunovLowerAt T x) * (lam1 / (lam1 - lam2)) =
      hyperbolicRate lam1 lam2 := by
    rw [hxexp, ← hlam2]
    simp [hyperbolicRate]
    ring
  rw [hlimit] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 0,
    (eventually_gt_atTop 0).filter_mono hindex] with L hL hbackward
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hbackwardReal : (0 : ℝ) < balancedBackward lam1 lam2 L := by
    exact_mod_cast hbackward
  simp only [Function.comp_apply]
  field_simp [hLreal.ne', hbackwardReal.ne']

lemma ae_tendsto_balancedBackward_logJacobian_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0) :
    ∀ᵐ x ∂mu, Tendsto
      (fun L => logJacobianIterate T_inv
        (balancedBackward lam1 lam2 L) x / L)
      atTop (nhds (-(lam1 + lam2) * (lam1 / (lam1 - lam2)))) := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hconv := ae_tendsto_logJacobianIterate_div_integral
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left hK_compact
      mu hmu_supp hT_inv hErg_inv
  have hJ := integral_logJacobian_inverse_eq_neg_lyapunov_sum
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hT hErg
  have hindex := tendsto_balancedBackward_atTop hlam1_pos hlam2_neg
  have hratio := tendsto_balancedBackward_div hlam1_pos hlam2_neg
  filter_upwards [hconv] with x hxconv
  have hscaled := (hxconv.comp hindex).mul hratio
  have hlimit : (∫ y, logJacobian T_inv y ∂mu) *
      (lam1 / (lam1 - lam2)) =
      -(lam1 + lam2) * (lam1 / (lam1 - lam2)) := by
    rw [hJ, ← hlam1, ← hlam2]
  rw [hlimit] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 0,
    (eventually_gt_atTop 0).filter_mono hindex] with L hL hbackward
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hbackwardReal : (0 : ℝ) < balancedBackward lam1 lam2 L := by
    exact_mod_cast hbackward
  simp only [Function.comp_apply]
  field_simp [hLreal.ne', hbackwardReal.ne']

theorem exists_balanced_centered_linear_rate_subsequence
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ᵐ x ∂mu,
      Tendsto
        (fun k => Real.log
          ‖fderiv ℝ (T^[balancedForward lam1 lam2 (N k)]) x‖ / (N k))
        atTop (nhds (hyperbolicRate lam1 lam2)) ∧
      Tendsto
        (fun k => Real.log
          ‖fderiv ℝ (T_inv^[balancedBackward lam1 lam2 (N k)]) x‖ / (N k))
        atTop (nhds (hyperbolicRate lam1 lam2)) ∧
      Tendsto
        (fun k => logJacobianIterate T_inv
          (balancedBackward lam1 lam2 (N k)) x / (N k))
        atTop (nhds (-(lam1 + lam2) * (lam1 / (lam1 - lam2)))) ∧
      Tendsto
        (fun k => Real.log
          ‖centeredFderiv T T_inv
            (balancedBackward lam1 lam2 (N k))
            (balancedForward lam1 lam2 (N k)) x‖ / (N k))
        atTop (nhds lam1) := by
  obtain ⟨N, hNmono, hcenter⟩ := exists_centeredLyapunov_subsequence
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
      hK_inv mu hmu_supp hT hErg
      (balancedBackward lam1 lam2) (balancedForward lam1 lam2)
      (balancedBackward_add_balancedForward hlam1_pos hlam2_neg)
  have hforward := ae_tendsto_balancedForward_log_norm_div
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
      hK_inv mu hmu_supp hT hErg hlam1 hlam2 hlam1_pos hlam2_neg
  have hbackward := ae_tendsto_balancedBackward_log_norm_div
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
      hK_inv mu hmu_supp hT hErg hlam1 hlam2 hlam1_pos hlam2_neg
  have hjac := ae_tendsto_balancedBackward_logJacobian_div
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
      hK_inv mu hmu_supp hT hErg hlam1 hlam2 hlam1_pos hlam2_neg
  refine ⟨N, hNmono, ?_⟩
  filter_upwards [hforward, hbackward, hjac, hcenter]
    with x hxforward hxbackward hxjac hxcenter
  exact ⟨hxforward.comp hNmono.tendsto_atTop,
    hxbackward.comp hNmono.tendsto_atTop,
    hxjac.comp hNmono.tendsto_atTop, by simpa [← hlam1] using hxcenter⟩

end Submission.Helpers
