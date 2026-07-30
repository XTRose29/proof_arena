import Submission.LyapunovComponentOrbit
import Submission.LyapunovComponentContraction
import Submission.LyapunovJacobian

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

lemma abs_det_mul_norm_targetComponent_le
    (A A_inv S₀ S₁ : EucPlane →L[ℝ] EucPlane)
    (hleft : A_inv ∘L A = ContinuousLinearMap.id ℝ EucPlane)
    (hright : A ∘L A_inv = ContinuousLinearMap.id ℝ EucPlane)
    (hcov : S₁ ∘L A = A ∘L S₀) :
    |A.toLinearMap.det| * ‖S₁‖ ≤ ‖A ∘L S₀‖ * ‖A‖ := by
  have hS₁ : S₁ = (A ∘L S₀) ∘L A_inv := by
    calc
      S₁ = S₁ ∘L ContinuousLinearMap.id ℝ EucPlane := by simp
      _ = S₁ ∘L (A ∘L A_inv) := by rw [hright]
      _ = (S₁ ∘L A) ∘L A_inv :=
        (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = (A ∘L S₀) ∘L A_inv := by rw [hcov]
  have hnorm : ‖S₁‖ ≤ ‖A ∘L S₀‖ * ‖A_inv‖ := by
    rw [hS₁]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  calc
    |A.toLinearMap.det| * ‖S₁‖ ≤
        |A.toLinearMap.det| * (‖A ∘L S₀‖ * ‖A_inv‖) :=
      mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
    _ = ‖A ∘L S₀‖ *
        (|A.toLinearMap.det| * ‖A_inv‖) := by ring
    _ = ‖A ∘L S₀‖ * ‖A‖ := by
      rw [← norm_eq_abs_det_mul_norm_inverse A A_inv hleft]

theorem ae_eventually_norm_lyapunovComponents_iterate_le_exp
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
      ‖lyapunovStableComponent T T_inv (T^[n] x)‖ ≤
          Real.exp (9 * eta * n) ∧
        ‖lyapunovUnstableComponent T T_inv (T^[n] x)‖ ≤
          Real.exp (9 * eta * n) := by
  have hcov := ae_all_lyapunovComponents_fderiv_iterate_covariant
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hsplitting := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hsplitting_all := ae_all_iterates_of_ae
    hT.quasiMeasurePreserving hsplitting
  have hstable :=
    ae_eventually_norm_fderiv_comp_lyapunovStableComponent_le_exp
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        hstable_neg hunstable_neg hrate
  have hrates := ae_tendsto_fderiv_rates_eq_integrals
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2
  have hjacobian := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact mu hmu_supp hT hErg
  have hJ : (∫ x, logJacobian T x ∂mu) = lam1 + lam2 := by
    rw [integral_logJacobian_eq_integral_lyapunovUpper_add_lower
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg]
    rw [← hlam1, ← hlam2]
  filter_upwards [hcov, hsplitting_all, hstable, hrates, hjacobian]
    with x hxcov hxsplit hxstable hxrates hxjac
  have hnorm := eventually_le_exp_add_of_tendsto_log_div
    (fun n : ℕ => n) tendsto_id heta hxrates.1
  have hdet := eventually_exp_sub_le_of_tendsto_log_div
    (a := fun n => |(fderiv ℝ (T^[n]) x).toLinearMap.det|)
    (fun n : ℕ => n) tendsto_id
      (fun n => abs_pos.mpr (det_fderiv_iterate_ne_zero
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right n x))
      heta (by simpa [logJacobianIterate, hJ] using hxjac)
  have htwo := eventually_const_mul_exp_le_exp_add
    2 (8 * eta) eta heta
  filter_upwards [hxstable, hnorm, hdet, htwo] with n hstable_n hnorm_n hdet_n htwo_n
  let A := fderiv ℝ (T^[n]) x
  let S₀ := lyapunovStableComponent T T_inv x
  let S₁ := lyapunovStableComponent T T_inv (T^[n] x)
  let U₁ := lyapunovUnstableComponent T T_inv (T^[n] x)
  have hleft : A.inverse ∘L A = ContinuousLinearMap.id ℝ EucPlane := by
    dsimp [A]
    exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have hright : A ∘L A.inverse = ContinuousLinearMap.id ℝ EucPlane := by
    dsimp [A]
    exact fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have hdet_component : |A.toLinearMap.det| * ‖S₁‖ ≤
      ‖A ∘L S₀‖ * ‖A‖ := by
    exact abs_det_mul_norm_targetComponent_le A A.inverse S₀ S₁
      hleft hright (hxcov n).1
  have hS₁ : ‖S₁‖ ≤ Real.exp (8 * eta * n) := by
    have hmul : Real.exp ((lam1 + lam2 - eta) * n) * ‖S₁‖ ≤
        Real.exp ((lam2 + 6 * eta) * n) *
          Real.exp ((lam1 + eta) * n) := by
      calc
        Real.exp ((lam1 + lam2 - eta) * n) * ‖S₁‖ ≤
            |A.toLinearMap.det| * ‖S₁‖ :=
          mul_le_mul_of_nonneg_right hdet_n (norm_nonneg _)
        _ ≤ ‖A ∘L S₀‖ * ‖A‖ := hdet_component
        _ ≤ Real.exp ((lam2 + 6 * eta) * n) *
            Real.exp ((lam1 + eta) * n) := by
          exact mul_le_mul hstable_n hnorm_n (norm_nonneg _) (Real.exp_nonneg _)
    have hscaled : Real.exp ((lam1 + lam2 - eta) * n) * ‖S₁‖ ≤
        Real.exp ((lam1 + lam2 - eta) * n) *
          Real.exp (8 * eta * n) := by
      calc
        Real.exp ((lam1 + lam2 - eta) * n) * ‖S₁‖ ≤
            Real.exp ((lam2 + 6 * eta) * n) *
            Real.exp ((lam1 + eta) * n) := hmul
        _ = Real.exp ((lam1 + lam2 - eta) * n) *
            Real.exp (8 * eta * n) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    exact le_of_mul_le_mul_left hscaled
      (Real.exp_pos ((lam1 + lam2 - eta) * n))
  have hS₁' : ‖S₁‖ ≤ Real.exp (9 * eta * n) := by
    exact hS₁.trans (Real.exp_le_exp.mpr (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith))
  have hadd : S₁ + U₁ = ContinuousLinearMap.id ℝ EucPlane := by
    exact lyapunovComponents_add T T_inv (hxsplit n)
  have hU₁ : ‖U₁‖ ≤ Real.exp (9 * eta * n) := by
    have hUeq : U₁ = ContinuousLinearMap.id ℝ EucPlane - S₁ := by
      apply eq_sub_of_add_eq
      simpa [add_comm] using hadd
    calc
      ‖U₁‖ = ‖ContinuousLinearMap.id ℝ EucPlane - S₁‖ := by rw [hUeq]
      _ ≤ ‖ContinuousLinearMap.id ℝ EucPlane‖ + ‖S₁‖ := norm_sub_le _ _
      _ = 1 + ‖S₁‖ := by rw [ContinuousLinearMap.norm_id]
      _ ≤ 2 * Real.exp (8 * eta * n) := by
        have hone : 1 ≤ Real.exp (8 * eta * n) := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          positivity
        linarith
      _ ≤ Real.exp ((8 * eta + eta) * n) := htwo_n
      _ = Real.exp (9 * eta * n) := by ring_nf
  exact ⟨hS₁', hU₁⟩

theorem ae_eventually_norm_lyapunovComponents_inverse_iterate_le_exp
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
      ‖lyapunovStableComponent T T_inv (T_inv^[n] x)‖ ≤
          Real.exp (9 * eta * n) ∧
        ‖lyapunovUnstableComponent T T_inv (T_inv^[n] x)‖ ≤
          Real.exp (9 * eta * n) := by
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
  have hinverse := ae_eventually_norm_lyapunovComponents_iterate_le_exp
    (lam1 := -lam2) (lam2 := -lam1)
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam1_inv hlam2_inv (neg_pos.mpr hlam2_neg)
      (neg_neg_of_pos hlam1_pos) heta hunstable_neg
      (by simpa using hstable_neg) hrate_inv
  filter_upwards [hinverse] with x hx
  filter_upwards [hx] with n hn
  have hstable_swap : lyapunovStableComponent T_inv T (T_inv^[n] x) =
      lyapunovUnstableComponent T T_inv (T_inv^[n] x) := by
    unfold lyapunovStableComponent lyapunovUnstableComponent
    unfold stableComponent unstableComponent
    rw [add_comm]
  have hunstable_swap : lyapunovUnstableComponent T_inv T (T_inv^[n] x) =
      lyapunovStableComponent T T_inv (T_inv^[n] x) := by
    unfold lyapunovStableComponent lyapunovUnstableComponent
    unfold stableComponent unstableComponent
    rw [add_comm]
  exact ⟨by simpa [hunstable_swap] using hn.2,
    by simpa [hstable_swap] using hn.1⟩

end Submission.Helpers
