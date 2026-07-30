import Submission.PlaneLinearAlgebra

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma logJacobianIterate_eq_log_norm_sub_log_norm_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    logJacobianIterate T n x =
      Real.log ‖fderiv ℝ (T^[n]) x‖ -
        Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ := by
  unfold logJacobianIterate
  exact log_abs_det_eq_log_norm_sub_log_norm_inverse
    (fderiv ℝ (T^[n]) x) (fderiv ℝ (T^[n]) x).inverse
      (fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x)
      (det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x)

lemma limsup_add_eq_add_of_tendsto
    {α : Type*} {f : Filter α} [f.NeBot]
    {u v : α → ℝ} {c : ℝ}
    (hu_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) f u)
    (hu_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) f u)
    (hv : Tendsto v f (nhds c)) :
    limsup (u + v) f = limsup u f + c := by
  apply le_antisymm
  · calc
      limsup (u + v) f ≤ limsup u f + limsup v f :=
        limsup_add_le hu_lower hu_upper hv.isCoboundedUnder_le hv.isBoundedUnder_le
      _ = limsup u f + c := by rw [hv.limsup_eq]
  · calc
      limsup u f + c = limsup u f + liminf v f := by rw [hv.liminf_eq]
      _ ≤ limsup (u + v) f :=
        le_limsup_add hu_upper hu_lower.isCobounded_flip
          hv.isBoundedUnder_le hv.isBoundedUnder_ge

lemma lyapunovUpperAt_add_lyapunovLowerAt_eq_of_jacobian_tendsto
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hx : x ∈ K) {J : ℝ}
    (hJ : Tendsto (fun n : ℕ => logJacobianIterate T n x / n)
      atTop (nhds J)) :
    lyapunovUpperAt T x + lyapunovLowerAt T x = J := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  let u : ℕ → ℝ := fun n =>
    Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n
  let j : ℕ → ℝ := fun n => logJacobianIterate T n x / n
  have hu_lower : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
      neg_log_le_log_norm_fderiv_iterate_inverse_div T T_inv
        hT_smooth hT_inv_smooth hT_left hT_right hK_inv hC_one hC n hx)
  have hu_upper : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      log_norm_fderiv_iterate_inverse_div_le T T_inv
        hT_smooth hT_inv_smooth hT_left hT_right hK_inv hD_one hD n hx)
  have hsum := limsup_add_eq_add_of_tendsto hu_lower hu_upper (show Tendsto j atTop (nhds J) from hJ)
  have heq : (fun n : ℕ =>
      Real.log ‖fderiv ℝ (T^[n]) x‖ / n) = u + j := by
    funext n
    simp only [Pi.add_apply, u, j]
    rw [logJacobianIterate_eq_log_norm_sub_log_norm_inverse
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
    ring
  rw [← heq] at hsum
  rw [lyapunovUpperAt, lyapunovLowerAt]
  dsimp [u] at hsum
  linarith

lemma ae_lyapunovUpperAt_add_lyapunovLowerAt_eq_integral_logJacobian
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    ∀ᵐ x ∂mu, lyapunovUpperAt T x + lyapunovLowerAt T x =
      ∫ y, logJacobian T y ∂mu := by
  have hJacobian := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact mu hmu_supp hT hErg
  filter_upwards [mem_ae_iff.mpr hmu_supp, hJacobian] with x hx hJ
  exact lyapunovUpperAt_add_lyapunovLowerAt_eq_of_jacobian_tendsto
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hx hJ

lemma integral_logJacobian_eq_integral_lyapunovUpper_add_lower
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    (∫ y, logJacobian T y ∂mu) =
      (∫ y, lyapunovUpperAt T y ∂mu) +
        ∫ y, lyapunovLowerAt T y ∂mu := by
  have hsum := ae_lyapunovUpperAt_add_lyapunovLowerAt_eq_integral_logJacobian
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv mu hmu_supp hT hErg
  have hupperInt := integrable_lyapunovUpperAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp
  have hlowerInt := integrable_lyapunovLowerAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp
  calc
    (∫ y, logJacobian T y ∂mu) =
        ∫ _y : EucPlane, (∫ y, logJacobian T y ∂mu) ∂mu := by
      rw [integral_const]
      simp [measureReal_def]
    _ = ∫ y, lyapunovUpperAt T y + lyapunovLowerAt T y ∂mu :=
      integral_congr_ae (hsum.mono fun _y hy => hy.symm)
    _ = (∫ y, lyapunovUpperAt T y ∂mu) +
        ∫ y, lyapunovLowerAt T y ∂mu :=
      integral_add hupperInt hlowerInt

end Submission.Helpers
