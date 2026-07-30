import Submission.LyapunovComponents

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

theorem ae_eventually_norm_fderiv_comp_lyapunovStableComponent_le_exp
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
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x ∘L lyapunovStableComponent T T_inv x‖ ≤
        Real.exp ((lam2 + 6 * eta) * n) := by
  have hgap_two : 2 * eta < lam1 - lam2 := by
    linarith [hstable_neg, hunstable_neg]
  have hinputs := ae_tendsto_fderiv_rates_eq_integrals_and_map_mem
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap_two
      hstable_neg hunstable_neg hrate
  filter_upwards [hinputs, hsource] with x hx hxsource
  have hprojection := eventually_norm_fderiv_comp_stableProjection_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hx.1 heta hgap_two hx.2.1.1 hx.2.1.2
  have hconstant := eventually_const_mul_exp_le_exp_add
    ‖lyapunovStableComponent T T_inv x‖ (lam2 + 5 * eta) eta heta
  filter_upwards [hprojection, hconstant] with n hn hconst
  let A := fderiv ℝ (T^[n]) x
  let P := stableProjection T x
  let U := stableProjection T_inv x
  let S := lyapunovStableComponent T T_inv x
  have hfixed : P ∘L S = S := by
    simpa [P, U, S, lyapunovStableComponent] using
      stableComponent_fixed P U hxsource.stableIdempotent
  calc
    ‖A ∘L S‖ = ‖(A ∘L P) ∘L S‖ := by
      rw [ContinuousLinearMap.comp_assoc, hfixed]
    _ ≤ ‖A ∘L P‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp ((lam2 + 5 * eta) * n) * ‖S‖ := by
      exact mul_le_mul_of_nonneg_right (by simpa [A, P] using hn) (norm_nonneg S)
    _ = ‖S‖ * Real.exp ((lam2 + 5 * eta) * n) := mul_comm _ _
    _ ≤ Real.exp (((lam2 + 5 * eta) + eta) * n) := by
      simpa [S, lyapunovStableComponent] using hconst
    _ = Real.exp ((lam2 + 6 * eta) * n) := by ring_nf

theorem ae_eventually_norm_fderiv_inverse_comp_lyapunovUnstableComponent_le_exp
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
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T_inv^[n]) x ∘L lyapunovUnstableComponent T T_inv x‖ ≤
        Real.exp ((-lam1 + 6 * eta) * n) := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hupper_inv :=
    integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hupper_swap :=
    integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have hlam1_inv : -lam2 = ∫ x, lyapunovUpperAt T_inv x ∂mu := by
    calc
      -lam2 = -∫ x, lyapunovLowerAt T x ∂mu := congrArg Neg.neg hlam2
      _ = ∫ x, lyapunovUpperAt T_inv x ∂mu := hupper_inv.symm
  have hlam2_inv : -lam1 = ∫ x, lyapunovLowerAt T_inv x ∂mu := by
    rw [← hlam1] at hupper_swap
    linarith
  have hrate_inv :
      8 * eta < hyperbolicRate (-lam2) (-lam1) := by
    convert hrate using 1
    dsimp [hyperbolicRate]
    ring
  have hinverse :=
    ae_eventually_norm_fderiv_comp_lyapunovStableComponent_le_exp
      (lam1 := -lam2) (lam2 := -lam1)
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
        hlam1_inv hlam2_inv (neg_pos.mpr hlam2_neg) (neg_neg_of_pos hlam1_pos)
        heta hunstable_neg (by simpa using hstable_neg) hrate_inv
  filter_upwards [hinverse] with x hx
  have hcomponent : lyapunovStableComponent T_inv T x =
      lyapunovUnstableComponent T T_inv x := by
    unfold lyapunovStableComponent lyapunovUnstableComponent
    unfold stableComponent unstableComponent
    rw [add_comm]
  rw [hcomponent] at hx
  exact hx

end Submission.Helpers
