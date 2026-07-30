import Submission.ComponentLowerBound

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

theorem ae_eventually_exp_le_norm_fderiv_comp_lyapunovStableComponent
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
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam2 - 2 * eta) * n) ≤
        ‖fderiv ℝ (T^[n]) x ∘L
          lyapunovStableComponent T T_inv x‖ := by
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hsource_all := ae_all_iterates_of_ae hT.quasiMeasurePreserving hsource
  have hunstable := ae_unstableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  have hunstable_all := ae_all_iterates_of_ae hT.quasiMeasurePreserving hunstable
  have heq := ae_all_inverse_component_norm_eq
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hnorm := ae_eventually_norm_fderiv_iterate_lt_exp_integral_add
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg heta
  have hjacobian := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact mu hmu_supp hT hErg
  have hJ : (∫ x, logJacobian T x ∂mu) = lam1 + lam2 := by
    rw [integral_logJacobian_eq_integral_lyapunovUpper_add_lower
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg]
    rw [← hlam1, ← hlam2]
  filter_upwards [hsource_all, hunstable_all, heq, hnorm, hjacobian]
    with x hxsource hxunstable hxeq hxnorm hxjacobian
  have hdet := eventually_exp_sub_le_of_tendsto_log_div
    (a := fun n => |(fderiv ℝ (T^[n]) x).det|)
    (fun n : ℕ => n) tendsto_id
      (fun n => abs_pos.mpr (det_fderiv_iterate_ne_zero
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right n x))
      heta (by simpa [logJacobianIterate, hJ] using hxjacobian)
  filter_upwards [hxnorm, hdet] with n hnorm_n hdet_n
  let D := fderiv ℝ (T^[n]) x
  let U := lyapunovUnstableComponent T T_inv (T^[n] x)
  have hD : D.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := D.inverse)
    · exact fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
    · exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
  have hU : 1 ≤ ‖U‖ := by
    let z := T^[n] x
    simpa [U, lyapunovUnstableComponent] using
      one_le_norm_unstableComponent
        (stableProjection T z) (stableProjection T_inv z)
        (hxsource n).invertible (hxsource n).stableIdempotent
        (hxsource n).unstableIdempotent (hxsource n).transverse
        (hxunstable n).2.2.1
  have hnorm_n' : ‖D‖ ≤ Real.exp ((lam1 + eta) * n) := by
    dsimp [D]
    rw [hlam1]
    exact hnorm_n.le
  have hdet_n' : Real.exp ((lam1 + lam2 - eta) * n) ≤ |D.det| := by
    simpa [D] using hdet_n
  have hlower := exp_sub_le_norm_of_adjugate_eq
    D U hD hU (hxeq n).1 hdet_n' hnorm_n'
  convert hlower using 1
  ring_nf

theorem ae_eventually_exp_le_norm_fderiv_inverse_comp_lyapunovUnstableComponent
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
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam1 - 2 * eta) * n) ≤
        ‖fderiv ℝ (T_inv^[n]) x ∘L
          lyapunovUnstableComponent T T_inv x‖ := by
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
  have hgap_inv : 8 * eta < -lam2 - -lam1 := by
    linarith only [hgap]
  have hlower :=
    ae_eventually_exp_le_norm_fderiv_comp_lyapunovStableComponent
      (lam1 := -lam2) (lam2 := -lam1)
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
        hlam1_inv hlam2_inv (neg_pos.mpr hlam2_neg)
        (neg_neg_of_pos hlam1_pos) heta hgap_inv
        hunstable_neg (by simpa using hstable_neg) (by
          convert hrate using 1
          dsimp [hyperbolicRate]
          ring)
  filter_upwards [hlower] with x hx
  filter_upwards [hx] with n hn
  have hswap : lyapunovStableComponent T_inv T x =
      lyapunovUnstableComponent T T_inv x := by
    unfold lyapunovStableComponent lyapunovUnstableComponent
    unfold stableComponent unstableComponent
    rw [add_comm]
  rw [hswap] at hn
  exact hn

theorem ae_eventually_exp_le_norm_fderiv_inverse_comp_futureUnstable
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
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam1 - 3 * eta) * n) ≤
        ‖(fderiv ℝ (T^[n]) x).inverse ∘L
          lyapunovUnstableComponent T T_inv (T^[n] x)‖ := by
  have heq := ae_all_inverse_component_norm_eq
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hstable :=
    ae_eventually_exp_le_norm_fderiv_comp_lyapunovStableComponent
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
        hstable_neg hunstable_neg hrate
  have hjacobian := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact mu hmu_supp hT hErg
  have hJ : (∫ x, logJacobian T x ∂mu) = lam1 + lam2 := by
    rw [integral_logJacobian_eq_integral_lyapunovUpper_add_lower
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg]
    rw [← hlam1, ← hlam2]
  filter_upwards [heq, hstable, hjacobian]
    with x hxeq hxstable hxjacobian
  have hdet := eventually_le_exp_add_of_tendsto_log_div
    (a := fun n => |(fderiv ℝ (T^[n]) x).det|)
    (fun n : ℕ => n) tendsto_id heta
      (by simpa [logJacobianIterate, hJ] using hxjacobian)
  filter_upwards [hxstable, hdet] with n hstable_n hdet_n
  let D := fderiv ℝ (T^[n]) x
  let U := lyapunovUnstableComponent T T_inv (T^[n] x)
  have hproduct :
      Real.exp ((lam2 - 2 * eta) * n) ≤
        Real.exp ((lam1 + lam2 + eta) * n) *
          ‖D.inverse ∘L U‖ := by
    calc
      Real.exp ((lam2 - 2 * eta) * n) ≤
          ‖D ∘L lyapunovStableComponent T T_inv x‖ := by
        simpa [D] using hstable_n
      _ = |D.det| * ‖D.inverse ∘L U‖ := (hxeq n).1.symm
      _ ≤ Real.exp ((lam1 + lam2 + eta) * n) *
          ‖D.inverse ∘L U‖ :=
        mul_le_mul_of_nonneg_right (by simpa [D] using hdet_n) (norm_nonneg _)
  have hdiv :
      Real.exp ((lam2 - 2 * eta) * n) /
          Real.exp ((lam1 + lam2 + eta) * n) ≤
        ‖D.inverse ∘L U‖ := by
    exact (div_le_iff₀ (Real.exp_pos _)).2
      (by simpa [mul_comm] using hproduct)
  calc
    Real.exp ((-lam1 - 3 * eta) * n) =
        Real.exp ((lam2 - 2 * eta) * n) /
          Real.exp ((lam1 + lam2 + eta) * n) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ ‖D.inverse ∘L U‖ := hdiv

end Submission.Helpers
