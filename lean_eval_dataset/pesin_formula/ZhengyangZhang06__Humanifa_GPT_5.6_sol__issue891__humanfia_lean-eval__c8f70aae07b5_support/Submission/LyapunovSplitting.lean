import Submission.PlaneProjectionSplitting

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

noncomputable def lyapunovProjectionSum
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  stableProjection T x + stableProjection T_inv x

noncomputable def lyapunovSplittingCondition
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  ‖(lyapunovProjectionSum T T_inv x).inverse‖

def lyapunovSplittingSet
    (T T_inv : EucPlane → EucPlane) : Set EucPlane :=
  {x | (lyapunovProjectionSum T T_inv x).det ≠ 0}

lemma measurable_lyapunovProjectionSum
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    Measurable (lyapunovProjectionSum T T_inv) := by
  have hP := stronglyMeasurable_stableProjection
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  have hU := stronglyMeasurable_stableProjection
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
  exact (hP.add hU).measurable

lemma measurable_lyapunovSplittingCondition
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    Measurable (lyapunovSplittingCondition T T_inv) := by
  exact (measurable_planeCLM_inverse.comp
    (measurable_lyapunovProjectionSum T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right)).norm

lemma measurableSet_lyapunovSplittingSet
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    MeasurableSet (lyapunovSplittingSet T T_inv) := by
  have hdet : Measurable fun x => (lyapunovProjectionSum T T_inv x).det :=
    ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_lyapunovProjectionSum T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right)
  exact (measurableSet_eq_fun hdet measurable_const).compl

theorem ae_lyapunovProjectionSum_isInvertible
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
    ∀ᵐ x ∂mu, (lyapunovProjectionSum T T_inv x).IsInvertible := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have htransverse := ae_stableProjection_inverse_transverse
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap hstable_neg
      hunstable_neg hrate
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
  filter_upwards [htransverse, hforward, hinverse, hforward_inv,
      hinverse_inv, hupper, hlower, hswap, mem_ae_iff.mpr hmu_supp]
    with x hxtransverse hxforward hxinverse hxforward_inv hxinverse_inv
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
      atTop (nhds (-(-lam1))) := by
    simpa [← hxswap, hxupper, ← hlam1] using hxinverse_inv
  have hPs :=
    (tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv hxK heta hgap hxforward' hxinverse').2
  have hPu :=
    (tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
      (lam1 := -lam2) (lam2 := -lam1)
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        hK_compact hK_inv_inv hxK heta (by linarith)
        hxforward_inv' hxinverse_inv').2
  change (stableProjection T x + stableProjection T_inv x).IsInvertible
  exact projection_sum_isInvertible_of_transverse
    (stableProjection T x) (stableProjection T_inv x)
    (stableProjection_idempotent_of_tendsto hPs)
    (stableProjection_idempotent_of_tendsto hPu)
    (stableProjection_adjoint_of_tendsto hPs)
    (stableProjection_adjoint_of_tendsto hPu)
    (stableProjection_comp_quarterTurn_of_tendsto hPs)
    (stableProjection_comp_quarterTurn_of_tendsto hPu)
    hxtransverse

theorem ae_mem_lyapunovSplittingSet
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
    ∀ᵐ x ∂mu, x ∈ lyapunovSplittingSet T T_inv := by
  have hinv := ae_lyapunovProjectionSum_isInvertible
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap hstable_neg
      hunstable_neg hrate
  filter_upwards [hinv] with x hx
  intro hdet
  have hker : (lyapunovProjectionSum T T_inv x).toLinearMap.ker ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  exact hker (LinearMap.ker_eq_bot.mpr hx.injective)

end Submission.Helpers
