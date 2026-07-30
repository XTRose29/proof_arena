import Submission.LyapunovStableProjection

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

lemma eventually_const_mul_exp_le_exp_add
    (C rate eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.exp (rate * n) ≤ Real.exp ((rate + eta) * n) := by
  have hetaN : Tendsto (fun n : ℕ => eta * (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos heta).2 tendsto_natCast_atTop_atTop
  have hC : ∀ᶠ n : ℕ in atTop, C ≤ Real.exp (eta * n) :=
    tendsto_atTop.1 (Real.tendsto_exp_atTop.comp hetaN) C
  filter_upwards [hC] with n hn
  calc
    C * Real.exp (rate * n) ≤
        Real.exp (eta * n) * Real.exp (rate * n) := by gcongr
    _ = Real.exp ((rate + eta) * n) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem eventually_norm_fderiv_comp_stableProjection_le_exp
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hxK : x ∈ K)
    {lam1 lam2 eta : ℝ} (heta : 0 < eta)
    (hgap : 2 * eta < lam1 - lam2)
    (hforward : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds lam1))
    (hinverse : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lam2))) :
    ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x ∘L stableProjection T x‖ ≤
        Real.exp ((lam2 + 5 * eta) * n) := by
  obtain ⟨Q, n0, hQ, hQbound⟩ :=
    exists_stableProjection_limit_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv hxK heta hgap hforward hinverse
  have hstable :=
    (tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv hxK heta hgap hforward hinverse).2
  have hQeq : Q = stableProjection T x := tendsto_nhds_unique hQ hstable
  subst Q
  let gamma := lam1 - lam2 - 2 * eta
  let D := (compact_fderiv_bound T_inv hT_inv_smooth hK_compact).choose
  let C₀ := 2 * Real.sqrt 2 * D * Real.exp (lam2 + eta)
  let C := C₀ / (1 - Real.exp (-gamma))
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hdenom_pos : 0 < 1 - Real.exp (-gamma) := by
    exact sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hgamma))
  have hprojection : ∀ᶠ n : ℕ in atTop,
      ‖stableApproxProjection T n x - stableProjection T x‖ ≤
        C * Real.exp (-gamma * n) := by
    rw [eventually_atTop]
    refine ⟨n0, ?_⟩
    intro n hn
    let k := n - n0
    have hkn : k + n0 = n := Nat.sub_add_cancel hn
    have hk := hQbound k
    rw [hkn] at hk
    calc
      ‖stableApproxProjection T n x - stableProjection T x‖ ≤
          ((2 * Real.sqrt 2 * D * Real.exp (lam2 + eta)) *
              Real.exp (-gamma * n0)) *
            Real.exp (-gamma) ^ k /
              (1 - Real.exp (-gamma)) := by
        simpa [D, C₀, gamma] using hk
      _ = C * Real.exp (-gamma * n) := by
        rw [← Real.exp_nat_mul, div_eq_mul_inv]
        dsimp [C, C₀]
        rw [div_eq_mul_inv]
        have hcast : (k : ℝ) + n0 = n := by exact_mod_cast hkn
        have hexp : Real.exp (-gamma * n0) *
            Real.exp ((k : ℝ) * (-gamma)) = Real.exp (-gamma * n) := by
          rw [← Real.exp_add]
          congr 1
          rw [← hcast]
          ring
        calc
          2 * Real.sqrt 2 * D * Real.exp (lam2 + eta) *
                Real.exp (-gamma * n0) * Real.exp ((k : ℝ) * (-gamma)) *
              (1 - Real.exp (-gamma))⁻¹ =
              2 * Real.sqrt 2 * D * Real.exp (lam2 + eta) *
                (1 - Real.exp (-gamma))⁻¹ *
                  (Real.exp (-gamma * n0) *
                    Real.exp ((k : ℝ) * (-gamma))) := by ring
          _ = 2 * Real.sqrt 2 * D * Real.exp (lam2 + eta) *
                (1 - Real.exp (-gamma))⁻¹ * Real.exp (-gamma * n) := by
            rw [hexp]
  have hnorm_upper : ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x‖ ≤ Real.exp ((lam1 + eta) * n) :=
    eventually_le_exp_add_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id heta hforward
  have hinverse_lower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam2 - eta) * n) ≤
        ‖(fderiv ℝ (T^[n]) x).inverse‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => by
        rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right]
        exact norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
          hT_right hT_left n (T^[n] x))
      heta hinverse
  have herror := eventually_const_mul_exp_le_exp_add
    C (lam2 + 3 * eta) eta heta
  have htwo := eventually_const_mul_exp_le_exp_add
    2 (lam2 + 4 * eta) eta heta
  filter_upwards [hprojection, hnorm_upper, hinverse_lower, herror, htwo]
    with n hprojection_n hnorm_n hinverse_n herror_n htwo_n
  let A := fderiv ℝ (T^[n]) x
  have hA_det : A.toLinearMap.det ≠ 0 := by
    dsimp [A]
    exact det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have hA_left : A.inverse ∘L A = ContinuousLinearMap.id ℝ EucPlane := by
    dsimp [A]
    exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have hmin : ‖A (planeSingularBasis A 1)‖ ≤
      Real.exp ((lam2 + eta) * n) := by
    rw [norm_minSingular_eq_one_div_norm_inverse A A.inverse hA_det hA_left]
    calc
      1 / ‖A.inverse‖ ≤ 1 / Real.exp ((-lam2 - eta) * n) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hinverse_n
      _ = Real.exp ((lam2 + eta) * n) := by
        rw [div_eq_mul_inv, one_mul, ← Real.exp_neg]
        congr 1
        ring
  have hsmall_exp : Real.exp ((lam2 + eta) * n) ≤
      Real.exp ((lam2 + 4 * eta) * n) := by
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hprojection_rev :
      ‖stableProjection T x - stableApproxProjection T n x‖ ≤
        C * Real.exp (-gamma * n) := by
    simpa [norm_sub_rev] using hprojection_n
  have herror_n' : C * Real.exp ((lam2 + 3 * eta) * n) ≤
      Real.exp ((lam2 + 4 * eta) * n) := by
    convert herror_n using 1
    all_goals ring_nf
  have htwo_n' : 2 * Real.exp ((lam2 + 4 * eta) * n) ≤
      Real.exp ((lam2 + 5 * eta) * n) := by
    convert htwo_n using 1
    all_goals ring_nf
  calc
    ‖A ∘L stableProjection T x‖ =
        ‖A ∘L stableApproxProjection T n x +
          A ∘L (stableProjection T x - stableApproxProjection T n x)‖ := by
      rw [← ContinuousLinearMap.comp_add]
      congr 2
      abel
    _ ≤ ‖A ∘L stableApproxProjection T n x‖ +
        ‖A ∘L (stableProjection T x - stableApproxProjection T n x)‖ :=
      norm_add_le _ _
    _ ≤ ‖A (planeSingularBasis A 1)‖ +
        ‖A‖ * ‖stableProjection T x - stableApproxProjection T n x‖ := by
      change ‖A ∘L planeMinProjection A‖ +
          ‖A ∘L (stableProjection T x - stableApproxProjection T n x)‖ ≤ _
      rw [norm_comp_planeMinProjection]
      exact add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ Real.exp ((lam2 + eta) * n) +
        Real.exp ((lam1 + eta) * n) *
          (C * Real.exp (-gamma * n)) := by gcongr
    _ = Real.exp ((lam2 + eta) * n) +
        C * Real.exp ((lam2 + 3 * eta) * n) := by
      dsimp [gamma]
      rw [show Real.exp ((lam1 + eta) * (n : ℝ)) *
          (C * Real.exp (-(lam1 - lam2 - 2 * eta) * (n : ℝ))) =
        C * (Real.exp ((lam1 + eta) * (n : ℝ)) *
          Real.exp (-(lam1 - lam2 - 2 * eta) * (n : ℝ))) by ring]
      rw [← Real.exp_add]
      congr 2
      ring_nf
    _ ≤ Real.exp ((lam2 + 4 * eta) * n) +
        Real.exp ((lam2 + 4 * eta) * n) := add_le_add hsmall_exp herror_n'
    _ = 2 * Real.exp ((lam2 + 4 * eta) * n) := by ring
    _ ≤ Real.exp ((lam2 + 5 * eta) * n) := htwo_n'

end Submission.Helpers
