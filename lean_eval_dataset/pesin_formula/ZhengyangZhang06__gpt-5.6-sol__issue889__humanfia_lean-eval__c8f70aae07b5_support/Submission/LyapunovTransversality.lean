import Submission.LyapunovStableContraction

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

theorem ae_stableProjection_inverse_transverse
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
    (heta : 0 < eta)
    (hgap : 2 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ z : EucPlane,
      stableProjection T x z = z →
      stableProjection T_inv x z = z → z = 0 := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  obtain ⟨N, hNmono, hlinear⟩ :=
    exists_ae_eventually_balanced_twoSided_linear_control
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
  have hforward := ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
  have hinverse :=
    ae_tendsto_log_norm_fderiv_iterate_inverse_div_neg_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hforward_inv :=
    ae_tendsto_log_norm_fderiv_inverse_iterate_div_neg_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hinverse_inv :=
    ae_tendsto_log_norm_fderiv_iterate_inverse_div_neg_lyapunovLowerAt
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have hupper := lyapunovUpperAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg
  have hlower := lyapunovLowerAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg
  have hswap := ae_lyapunovUpperAt_inverse_eq_neg_lyapunovLowerAt
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have hforward_time : Tendsto
      (fun k => balancedForward lam1 lam2 (N k)) atTop atTop :=
    (tendsto_balancedForward_atTop hlam1_pos hlam2_neg).comp
      hNmono.tendsto_atTop
  have hbackward_time : Tendsto
      (fun k => balancedBackward lam1 lam2 (N k)) atTop atTop :=
    (tendsto_balancedBackward_atTop hlam1_pos hlam2_neg).comp
      hNmono.tendsto_atTop
  filter_upwards [hlinear, hforward, hinverse, hforward_inv, hinverse_inv,
      hupper, hlower, hswap, mem_ae_iff.mpr hmu_supp]
    with x hxlinear hxforward hxinverse hxforward_inv hxinverse_inv
      hxupper hxlower hxswap hxK
  have hxforward' : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds lam1) := by
    simpa [hxupper, ← hlam1] using hxforward
  have hxinverse' : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lam2)) := by
    simpa [hxlower, ← hlam2] using hxinverse
  have hxforward_inv' : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T_inv^[n]) x‖ / n)
      atTop (nhds (-lam2)) := by
    simpa [hxlower, ← hlam2] using hxforward_inv
  have hxinverse_inv' : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T_inv^[n]) x).inverse‖ / n)
      atTop (nhds lam1) := by
    simpa [← hxswap, hxupper, ← hlam1] using hxinverse_inv
  have hxinverse_inv'' : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T_inv^[n]) x).inverse‖ / n)
      atTop (nhds (-(-lam1))) := by
    simpa only [neg_neg] using hxinverse_inv'
  have hstable := eventually_norm_fderiv_comp_stableProjection_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hxK heta hgap hxforward' hxinverse'
  have hunstable := eventually_norm_fderiv_comp_stableProjection_le_exp
    (lam1 := -lam2) (lam2 := -lam1)
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      hK_compact hK_inv_inv hxK heta (by linarith)
      hxforward_inv' hxinverse_inv''
  have hstable_balanced := hforward_time.eventually hstable
  have hunstable_balanced := hbackward_time.eventually hunstable
  have hNpos := hNmono.tendsto_atTop.eventually (eventually_gt_atTop 0)
  obtain ⟨k, hk⟩ :=
    (hxlinear.and (hstable_balanced.and
      (hunstable_balanced.and hNpos))).exists
  rcases hk with ⟨hklinear, hkstable, hkunstable, hkN⟩
  intro z hzstable hzunstable
  let A := fderiv ℝ (T^[balancedForward lam1 lam2 (N k)]) x
  let B := fderiv ℝ (T_inv^[balancedBackward lam1 lam2 (N k)]) x
  have hAz : ‖A z‖ ≤ ‖z‖ := by
    calc
      ‖A z‖ = ‖(A ∘L stableProjection T x) z‖ := by
        rw [ContinuousLinearMap.comp_apply, hzstable]
      _ ≤ ‖A ∘L stableProjection T x‖ * ‖z‖ :=
        (A ∘L stableProjection T x).le_opNorm z
      _ ≤ Real.exp ((lam2 + 5 * eta) *
            balancedForward lam1 lam2 (N k)) * ‖z‖ := by
        gcongr
      _ ≤ 1 * ‖z‖ := by
        gcongr
        exact (Real.exp_le_one_iff).2
          (mul_nonpos_of_nonpos_of_nonneg hstable_neg.le
            (Nat.cast_nonneg _))
      _ = ‖z‖ := one_mul _
  have hBz : ‖B z‖ ≤ ‖z‖ := by
    calc
      ‖B z‖ = ‖(B ∘L stableProjection T_inv x) z‖ := by
        rw [ContinuousLinearMap.comp_apply, hzunstable]
      _ ≤ ‖B ∘L stableProjection T_inv x‖ * ‖z‖ :=
        (B ∘L stableProjection T_inv x).le_opNorm z
      _ ≤ Real.exp ((-lam1 + 5 * eta) *
            balancedBackward lam1 lam2 (N k)) * ‖z‖ := by
        gcongr
      _ ≤ 1 * ‖z‖ := by
        gcongr
        exact (Real.exp_le_one_iff).2
          (mul_nonpos_of_nonpos_of_nonneg hunstable_neg.le
            (Nat.cast_nonneg _))
      _ = ‖z‖ := one_mul _
  have hmain : ‖z‖ ≤
      Real.exp (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k) * ‖z‖ := by
    calc
      ‖z‖ ≤ Real.exp
            (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k) *
          max ‖A z‖ ‖B z‖ := by
        simpa [A, B] using hklinear z
      _ ≤ Real.exp
            (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k) * ‖z‖ := by
        gcongr
        exact max_le hAz hBz
  have hfactor :
      Real.exp (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k) < 1 := by
    apply (Real.exp_lt_one_iff).2
    have hkNreal : (0 : ℝ) < N k := by exact_mod_cast hkN
    have hproduct : 0 < (hyperbolicRate lam1 lam2 - 8 * eta) * N k :=
      mul_pos (by linarith) hkNreal
    nlinarith
  have hnorm_zero : ‖z‖ = 0 := by
    apply le_antisymm
    · by_contra hzpos
      have hnorm_pos : 0 < ‖z‖ := lt_of_not_ge hzpos
      have hstrict :
          Real.exp (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k) * ‖z‖ <
            ‖z‖ := by
        nlinarith [Real.exp_pos
          (-(hyperbolicRate lam1 lam2 - 8 * eta) * N k)]
      exact (not_lt_of_ge hmain) hstrict
    · exact norm_nonneg z
  exact norm_eq_zero.mp hnorm_zero

end Submission.Helpers
