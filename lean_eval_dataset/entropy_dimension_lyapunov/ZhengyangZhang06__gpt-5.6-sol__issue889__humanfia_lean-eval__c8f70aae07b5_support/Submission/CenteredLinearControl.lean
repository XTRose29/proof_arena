import Submission.BalancedLyapunovRates

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma twoSided_linear_control_of_exponential_bounds
    (A B B_inv : EucPlane →L[ℝ] EucPlane)
    (hB_left : B_inv ∘L B = ContinuousLinearMap.id ℝ EucPlane)
    (z : EucPlane) {L : ℕ} {rate topRate detRate eta : ℝ}
    (_heta : 0 < eta)
    (hrates : 2 * detRate + 2 * topRate = 4 * rate)
    (hA : ‖A‖ ≤ Real.exp ((rate + eta) * L))
    (hB : ‖B‖ ≤ Real.exp ((rate + eta) * L))
    (hdet : Real.exp ((detRate - eta) * L) ≤ |B.toLinearMap.det|)
    (hfull : Real.exp ((topRate - eta) * L) ≤ ‖A ∘L B_inv‖)
    (hfour : 4 ≤ Real.exp (eta * L)) :
    ‖z‖ ≤ Real.exp (-(rate - 8 * eta) * L) * max ‖A z‖ ‖B z‖ := by
  let E : ℝ := Real.exp ((rate + eta) * L)
  let C : ℝ := Real.exp ((4 * rate - 4 * eta) * L)
  let M : ℝ := max ‖A z‖ ‖B z‖
  have hdet_sq : Real.exp (2 * ((detRate - eta) * L)) ≤
      B.toLinearMap.det ^ 2 := by
    calc
      Real.exp (2 * ((detRate - eta) * L)) =
          Real.exp ((detRate - eta) * L) ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ |B.toLinearMap.det| ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hdet 2
      _ = B.toLinearMap.det ^ 2 := sq_abs _
  have hfull_sq : Real.exp (2 * ((topRate - eta) * L)) ≤
      ‖A ∘L B_inv‖ ^ 2 := by
    calc
      Real.exp (2 * ((topRate - eta) * L)) =
          Real.exp ((topRate - eta) * L) ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ ‖A ∘L B_inv‖ ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hfull 2
  have hcoef : C ≤ B.toLinearMap.det ^ 2 * ‖A ∘L B_inv‖ ^ 2 := by
    calc
      C = Real.exp (2 * ((detRate - eta) * L)) *
          Real.exp (2 * ((topRate - eta) * L)) := by
        dsimp [C]
        rw [← Real.exp_add]
        congr 1
        nlinarith
      _ ≤ B.toLinearMap.det ^ 2 * ‖A ∘L B_inv‖ ^ 2 :=
        mul_le_mul hdet_sq hfull_sq (by positivity) (sq_nonneg _)
  have hA_sq : ‖A‖ ^ 2 ≤ E ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg A) hA 2
  have hB_sq : ‖B‖ ^ 2 ≤ E ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg B) hB 2
  have hsquares : ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ 2 * E ^ 2 := by
    linarith
  have hsums : ‖A‖ + ‖B‖ ≤ 2 * E := by
    linarith
  have hpoly : (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) * M ≤
      4 * Real.exp ((3 * rate + 3 * eta) * L) * M := by
    have hM : 0 ≤ M := (norm_nonneg (A z)).trans (le_max_left _ _)
    have hpow : E ^ 2 * E = Real.exp ((3 * rate + 3 * eta) * L) := by
      calc
        E ^ 2 * E = E ^ 3 := by ring
        _ = Real.exp (3 * ((rate + eta) * L)) := by
          dsimp [E]
          simpa using
            (Real.exp_nat_mul ((rate + eta) * (L : ℝ)) 3).symm
        _ = Real.exp ((3 * rate + 3 * eta) * L) := by
          congr 1
          ring
    calc
      (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) * M ≤
          (2 * E ^ 2) * (2 * E) * M := by
        gcongr
      _ = 4 * Real.exp ((3 * rate + 3 * eta) * L) * M := by
        rw [show (2 * E ^ 2) * (2 * E) * M = 4 * (E ^ 2 * E) * M by ring,
          hpow]
  have hconstant : 4 * Real.exp ((3 * rate + 3 * eta) * L) ≤
      C * Real.exp (-(rate - 8 * eta) * L) := by
    calc
      4 * Real.exp ((3 * rate + 3 * eta) * L) ≤
          Real.exp (eta * L) * Real.exp ((3 * rate + 3 * eta) * L) := by
        gcongr
      _ = C * Real.exp (-(rate - 8 * eta) * L) := by
        dsimp [C]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hlinear := twoSided_linear_control A B B_inv hB_left z
  have hscaled : C * ‖z‖ ≤
      C * (Real.exp (-(rate - 8 * eta) * L) * M) := by
    calc
      C * ‖z‖ ≤
          (B.toLinearMap.det ^ 2 * ‖A ∘L B_inv‖ ^ 2) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg z)
      _ ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) * M := hlinear
      _ ≤ 4 * Real.exp ((3 * rate + 3 * eta) * L) * M := hpoly
      _ ≤ (C * Real.exp (-(rate - 8 * eta) * L)) * M := by
        exact mul_le_mul_of_nonneg_right hconstant
          ((norm_nonneg (A z)).trans (le_max_left _ _))
      _ = C * (Real.exp (-(rate - 8 * eta) * L) * M) := by ring
  exact le_of_mul_le_mul_left hscaled (show 0 < C by positivity)

lemma eventually_le_exp_add_of_tendsto_log_div
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {a : ℕ → ℝ} {rate eta : ℝ} (heta : 0 < eta)
    (ha : Tendsto (fun k => Real.log (a k) / N k)
      atTop (nhds rate)) :
    ∀ᶠ k : ℕ in atTop,
      a k ≤ Real.exp ((rate + eta) * N k) := by
  have hupper := (tendsto_order.1 ha).2 (rate + eta) (by linarith)
  filter_upwards [hupper, (eventually_gt_atTop 0).filter_mono hN]
    with k hk hNk
  have hNk_real : (0 : ℝ) < N k := by exact_mod_cast hNk
  apply Real.le_exp_of_log_le
  exact ((div_lt_iff₀ hNk_real).mp hk).le

lemma eventually_exp_sub_le_of_tendsto_log_div
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {a : ℕ → ℝ} (ha_pos : ∀ k, 0 < a k)
    {rate eta : ℝ} (heta : 0 < eta)
    (ha : Tendsto (fun k => Real.log (a k) / N k)
      atTop (nhds rate)) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp ((rate - eta) * N k) ≤ a k := by
  have hlower := (tendsto_order.1 ha).1 (rate - eta) (by linarith)
  filter_upwards [hlower, (eventually_gt_atTop 0).filter_mono hN]
    with k hk hNk
  have hNk_real : (0 : ℝ) < N k := by exact_mod_cast hNk
  apply (Real.le_log_iff_exp_le (ha_pos k)).mp
  exact ((lt_div_iff₀ hNk_real).mp hk).le

theorem exists_ae_eventually_balanced_twoSided_linear_control
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ᵐ x ∂mu, ∀ᶠ k : ℕ in atTop,
      ∀ z : EucPlane,
        ‖z‖ ≤ Real.exp
            (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k) *
          max
            ‖fderiv ℝ (T^[balancedForward lam1 lam2 (N k)]) x z‖
            ‖fderiv ℝ (T_inv^[balancedBackward lam1 lam2 (N k)]) x z‖ := by
  obtain ⟨N, hNmono, hconv⟩ := exists_balanced_centered_linear_rate_subsequence
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
      hK_inv mu hmu_supp hT hErg hlam1 hlam2 hlam1_pos hlam2_neg
  let rate := hyperbolicRate lam1 lam2
  let detRate := -(lam1 + lam2) * (lam1 / (lam1 - lam2))
  let topRate := lam1
  have hdenom : lam1 - lam2 ≠ 0 :=
    (sub_pos.mpr (hlam2_neg.trans hlam1_pos)).ne'
  have hrates : 2 * detRate + 2 * topRate = 4 * rate := by
    dsimp [detRate, topRate, rate, hyperbolicRate]
    field_simp [hdenom]
    ring
  have hNreal : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNmono.tendsto_atTop
  have hetaN : Tendsto (fun k => eta * (N k : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos heta).2 hNreal
  have hfour : ∀ᶠ k : ℕ in atTop, 4 ≤ Real.exp (eta * N k) :=
    tendsto_atTop.1 (Real.tendsto_exp_atTop.comp hetaN) 4
  refine ⟨N, hNmono, ?_⟩
  filter_upwards [hconv] with x hx
  obtain ⟨hforward, hbackward, hjacobian, hcentered⟩ := hx
  have hA := eventually_le_exp_add_of_tendsto_log_div
    N hNmono.tendsto_atTop heta (by simpa [rate] using hforward)
  have hB := eventually_le_exp_add_of_tendsto_log_div
    N hNmono.tendsto_atTop heta (by simpa [rate] using hbackward)
  have hdet := eventually_exp_sub_le_of_tendsto_log_div
    N hNmono.tendsto_atTop
      (fun k => abs_pos.mpr (det_fderiv_iterate_ne_zero
        T_inv T hT_inv_smooth hT_smooth hT_right hT_left
          (balancedBackward lam1 lam2 (N k)) x))
      heta (by simpa [logJacobianIterate, detRate] using hjacobian)
  have hfull := eventually_exp_sub_le_of_tendsto_log_div
    (a := fun k => ‖centeredFderiv T T_inv
      (balancedBackward lam1 lam2 (N k))
      (balancedForward lam1 lam2 (N k)) x‖)
    N hNmono.tendsto_atTop
      (fun k => by
        rw [centeredFderiv_eq_fderiv_iterate T T_inv hT_smooth
          hT_inv_smooth hT_left hT_right]
        exact norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right _ _)
      heta (by simpa [topRate, ← hlam1] using hcentered)
  filter_upwards [hA, hB, hdet, hfull, hfour]
    with k hkA hkB hkdet hkfull hkfour
  intro z
  let A := fderiv ℝ (T^[balancedForward lam1 lam2 (N k)]) x
  let B := fderiv ℝ (T_inv^[balancedBackward lam1 lam2 (N k)]) x
  have hB_left : B.inverse ∘L B = ContinuousLinearMap.id ℝ EucPlane := by
    dsimp [B]
    exact fderiv_iterate_inverse_comp T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left _ x
  have hkdet' : Real.exp ((detRate - eta) * N k) ≤
      |B.toLinearMap.det| := by
    dsimp [B, detRate]
    convert hkdet using 1
    ring_nf
  simpa [A, B, centeredFderiv, rate, detRate, topRate] using
    twoSided_linear_control_of_exponential_bounds
      A B B.inverse hB_left z heta hrates hkA hkB hkdet' hkfull hkfour

end Submission.Helpers
