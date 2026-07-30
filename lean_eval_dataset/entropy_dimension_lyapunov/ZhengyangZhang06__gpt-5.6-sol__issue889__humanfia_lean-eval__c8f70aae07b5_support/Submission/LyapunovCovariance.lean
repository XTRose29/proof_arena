import Submission.LyapunovStableCharacterization

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

theorem stableProjection_fderiv_fixed_of_lyapunov_limits
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hxK : x ∈ K)
    {lam1 lam2 eta : ℝ} (heta : 0 < eta)
    (hgap : 7 * eta < lam1 - lam2)
    (hforward_x : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds lam1))
    (hinverse_x : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lam2)))
    (hforward_Tx : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n)
      atTop (nhds lam1))
    (hinverse_Tx : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n)
      atTop (nhds (-lam2)))
    (z : EucPlane) :
    stableProjection T (T x)
        (fderiv ℝ T x (stableProjection T x z)) =
      fderiv ℝ T x (stableProjection T x z) := by
  let v := stableProjection T x z
  let w := fderiv ℝ T x v
  by_cases hw : w = 0
  · change stableProjection T (T x) w = w
    rw [hw]
    exact map_zero _
  have hstable := eventually_norm_fderiv_comp_stableProjection_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hxK heta (by linarith) hforward_x hinverse_x
  have hstable_succ := (tendsto_add_atTop_nat 1).eventually hstable
  have hP_Tx :=
    (tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv
        (by rw [← hK_inv]; exact ⟨x, hxK, rfl⟩)
        heta (by linarith) hforward_Tx hinverse_Tx).2
  have htop_Tx : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam1 - eta) * n) ≤ ‖fderiv ℝ (T^[n]) (T x)‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n (T x))
      heta hforward_Tx
  let rate := lam2 + 5 * eta
  let C := Real.exp rate * ‖z‖ / ‖w‖
  have hw_norm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hconst := eventually_const_mul_exp_le_exp_add C rate eta heta
  have hw_growth : ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) (T x) w‖ ≤
        Real.exp ((lam2 + 6 * eta) * n) * ‖w‖ := by
    filter_upwards [hstable_succ, hconst] with n hstable_n hconst_n
    have hcocycle : fderiv ℝ (T^[n]) (T x) ∘L fderiv ℝ T x =
        fderiv ℝ (T^[n + 1]) x := by
      simpa [Function.iterate_one, Nat.add_comm] using
        (fderiv_iterate_add_eq T hT_smooth n 1 x).symm
    have hcocycle_apply :
        fderiv ℝ (T^[n]) (T x)
            (fderiv ℝ T x (stableProjection T x z)) =
          fderiv ℝ (T^[n + 1]) x (stableProjection T x z) := by
      simpa only [ContinuousLinearMap.comp_apply] using
        congrArg (fun L : EucPlane →L[ℝ] EucPlane =>
          L (stableProjection T x z)) hcocycle
    have hstable_n' :
        ‖fderiv ℝ (T^[n + 1]) x ∘L stableProjection T x‖ ≤
          Real.exp (rate * (n + 1)) := by
      simpa [rate, Nat.cast_add, Nat.cast_one] using hstable_n
    calc
      ‖fderiv ℝ (T^[n]) (T x) w‖ =
          ‖(fderiv ℝ (T^[n + 1]) x ∘L stableProjection T x) z‖ := by
        dsimp [w, v]
        rw [hcocycle_apply]
        rfl
      _ ≤ ‖fderiv ℝ (T^[n + 1]) x ∘L stableProjection T x‖ *
          ‖z‖ :=
        (fderiv ℝ (T^[n + 1]) x ∘L stableProjection T x).le_opNorm z
      _ ≤ Real.exp (rate * (n + 1)) * ‖z‖ := by
        gcongr
      _ = C * Real.exp (rate * n) * ‖w‖ := by
        dsimp [C]
        rw [show rate * ((n : ℝ) + 1) = rate + rate * (n : ℝ) by ring,
          Real.exp_add]
        field_simp [hw_norm.ne']
      _ ≤ Real.exp ((rate + eta) * n) * ‖w‖ := by gcongr
      _ = Real.exp ((lam2 + 6 * eta) * n) * ‖w‖ := by
        congr 2
        dsimp [rate]
        ring
  exact stableProjection_apply_eq_of_eventual_subtop_growth
    (top := lam1) (rate := lam2 + 6 * eta) (eta := eta)
    (by linarith) hP_Tx htop_Tx hw_growth

theorem stableProjection_fderiv_inverse_at_image_fixed_of_lyapunov_limits
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hxK : x ∈ K)
    {lam1 lam2 eta : ℝ} (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hforward_x : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds lam1))
    (hinverse_x : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lam2)))
    (hforward_Tx : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n)
      atTop (nhds lam1))
    (hinverse_Tx : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n)
      atTop (nhds (-lam2)))
    (z : EucPlane) :
    stableProjection T x
        (fderiv ℝ T_inv (T x) (stableProjection T (T x) z)) =
      fderiv ℝ T_inv (T x) (stableProjection T (T x) z) := by
  let v := stableProjection T (T x) z
  let w := fderiv ℝ T_inv (T x) v
  by_cases hw : w = 0
  · change stableProjection T x w = w
    rw [hw]
    exact map_zero _
  have hstable_Tx := eventually_norm_fderiv_comp_stableProjection_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv
      (by rw [← hK_inv]; exact ⟨x, hxK, rfl⟩)
      heta (by linarith) hforward_Tx hinverse_Tx
  have hP_x :=
    (tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv hxK heta (by linarith)
        hforward_x hinverse_x).2
  have htop_x : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam1 - eta) * n) ≤ ‖fderiv ℝ (T^[n]) x‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x)
      heta hforward_x
  let rate := lam2 + 5 * eta
  let targetRate := lam2 + 7 * eta
  let C := ‖z‖ / (Real.exp targetRate * ‖w‖)
  have hw_norm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hdenom : 0 < Real.exp targetRate * ‖w‖ :=
    mul_pos (Real.exp_pos _) hw_norm
  have hconst := eventually_const_mul_exp_le_exp_add
    C rate (2 * eta) (by positivity)
  have hderiv_inv : fderiv ℝ T_inv (T x) = (fderiv ℝ T x).inverse := by
    symm
    simpa [Function.iterate_one] using
      (fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x)
  have hw_growth_succ : ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n + 1]) x w‖ ≤
        Real.exp (targetRate * (n + 1)) * ‖w‖ := by
    filter_upwards [hstable_Tx, hconst] with n hstable_n hconst_n
    have hcocycle : fderiv ℝ (T^[n + 1]) x ∘L
        fderiv ℝ T_inv (T x) = fderiv ℝ (T^[n]) (T x) := by
      rw [hderiv_inv]
      exact (fderiv_iterate_at_image_eq T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x).symm
    have hcocycle_apply :
        fderiv ℝ (T^[n + 1]) x
            (fderiv ℝ T_inv (T x) (stableProjection T (T x) z)) =
          fderiv ℝ (T^[n]) (T x) (stableProjection T (T x) z) := by
      simpa only [ContinuousLinearMap.comp_apply] using
        congrArg (fun L : EucPlane →L[ℝ] EucPlane =>
          L (stableProjection T (T x) z)) hcocycle
    calc
      ‖fderiv ℝ (T^[n + 1]) x w‖ =
          ‖(fderiv ℝ (T^[n]) (T x) ∘L stableProjection T (T x)) z‖ := by
        change ‖fderiv ℝ (T^[n + 1]) x
            (fderiv ℝ T_inv (T x) (stableProjection T (T x) z))‖ =
          ‖fderiv ℝ (T^[n]) (T x) (stableProjection T (T x) z)‖
        exact congrArg norm hcocycle_apply
      _ ≤ ‖fderiv ℝ (T^[n]) (T x) ∘L stableProjection T (T x)‖ *
          ‖z‖ :=
        (fderiv ℝ (T^[n]) (T x) ∘L stableProjection T (T x)).le_opNorm z
      _ ≤ Real.exp (rate * n) * ‖z‖ := by
        dsimp [rate]
        gcongr
      _ = (C * Real.exp (rate * n)) *
          (Real.exp targetRate * ‖w‖) := by
        dsimp [C]
        field_simp [hdenom.ne']
      _ ≤ Real.exp ((rate + 2 * eta) * n) *
          (Real.exp targetRate * ‖w‖) := by gcongr
      _ = Real.exp (targetRate * (n + 1)) * ‖w‖ := by
        have hrateeq : rate + 2 * eta = targetRate := by
          dsimp [rate, targetRate]
          ring_nf
        rw [hrateeq]
        calc
          Real.exp (targetRate * (n : ℝ)) *
              (Real.exp targetRate * ‖w‖) =
              (Real.exp (targetRate * (n : ℝ)) *
                Real.exp targetRate) * ‖w‖ := by ring
          _ = Real.exp (targetRate * (n : ℝ) + targetRate) * ‖w‖ := by
            exact congrArg (fun t : ℝ => t * ‖w‖)
              (Real.exp_add (targetRate * (n : ℝ)) targetRate).symm
          _ = Real.exp (targetRate * ((n : ℝ) + 1)) * ‖w‖ := by
            congr 2
            ring_nf
  have hw_growth : ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x w‖ ≤
        Real.exp (targetRate * n) * ‖w‖ := by
    rw [eventually_atTop] at hw_growth_succ ⊢
    obtain ⟨N, hN⟩ := hw_growth_succ
    refine ⟨N + 1, ?_⟩
    intro n hn
    let q := n - 1
    have hqN : N ≤ q := by dsimp [q]; omega
    have hqn : q + 1 = n := by dsimp [q]; omega
    have h := hN q hqN
    rw [hqn] at h
    have hqn_real : (q : ℝ) + 1 = n := by exact_mod_cast hqn
    calc
      ‖fderiv ℝ (T^[n]) x w‖ ≤
          Real.exp (targetRate * ((q : ℝ) + 1)) * ‖w‖ := h
      _ = Real.exp (targetRate * (n : ℝ)) * ‖w‖ := by rw [hqn_real]
  exact stableProjection_apply_eq_of_eventual_subtop_growth
    (top := lam1) (rate := targetRate) (eta := eta)
    (by dsimp [targetRate]; linarith) hP_x htop_x hw_growth

theorem ae_tendsto_fderiv_rates_eq_integrals
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
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu) :
    ∀ᵐ x ∂mu,
      Tendsto (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
          atTop (nhds lam1) ∧
        Tendsto
          (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
          atTop (nhds (-lam2)) := by
  have hforward := ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
  have hinverse :=
    ae_tendsto_log_norm_fderiv_iterate_inverse_div_neg_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hupper := lyapunovUpperAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg
  have hlower := lyapunovLowerAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg
  filter_upwards [hforward, hinverse, hupper, hlower]
    with x hxforward hxinverse hxupper hxlower
  constructor
  · simpa [hxupper, ← hlam1] using hxforward
  · simpa [hxlower, ← hlam2] using hxinverse

lemma ae_and_map_mem_of_ae
    {M : Type*} [MeasurableSpace M]
    {mu : Measure M} {T : M → M}
    (hT : Measure.QuasiMeasurePreserving T mu mu)
    {K : Set M} {p : M → Prop}
    (hK : ∀ᵐ x ∂mu, x ∈ K) (hp : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ x ∂mu, x ∈ K ∧ p x ∧ p (T x) :=
  hK.and (hp.and (hT.tendsto_ae hp))

theorem ae_tendsto_fderiv_rates_eq_integrals_and_map_mem
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
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu) :
    ∀ᵐ x ∂mu,
      x ∈ K ∧
        (Tendsto (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
            atTop (nhds lam1) ∧
          Tendsto
            (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
            atTop (nhds (-lam2))) ∧
        (Tendsto (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n)
            atTop (nhds lam1) ∧
          Tendsto
            (fun n : ℕ =>
              Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n)
            atTop (nhds (-lam2))) := by
  have hlimits := ae_tendsto_fderiv_rates_eq_integrals
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2
  exact ae_and_map_mem_of_ae hT.quasiMeasurePreserving
    (mem_ae_iff.mpr hmu_supp) hlimits

theorem ae_stableProjection_fderiv_fixed
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
    (heta : 0 < eta) (hgap : 7 * eta < lam1 - lam2) :
    ∀ᵐ x ∂mu, ∀ z : EucPlane,
      stableProjection T (T x)
          (fderiv ℝ T x (stableProjection T x z)) =
        fderiv ℝ T x (stableProjection T x z) := by
  have hinputs := ae_tendsto_fderiv_rates_eq_integrals_and_map_mem
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2
  filter_upwards [hinputs] with x hx
  exact stableProjection_fderiv_fixed_of_lyapunov_limits
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hx.1 heta hgap hx.2.1.1 hx.2.1.2
      hx.2.2.1 hx.2.2.2

theorem ae_stableProjection_fderiv_inverse_at_image_fixed
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
    (heta : 0 < eta) (hgap : 8 * eta < lam1 - lam2) :
    ∀ᵐ x ∂mu, ∀ z : EucPlane,
      stableProjection T x
          (fderiv ℝ T_inv (T x) (stableProjection T (T x) z)) =
        fderiv ℝ T_inv (T x) (stableProjection T (T x) z) := by
  have hinputs := ae_tendsto_fderiv_rates_eq_integrals_and_map_mem
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2
  filter_upwards [hinputs] with x hx
  exact stableProjection_fderiv_inverse_at_image_fixed_of_lyapunov_limits
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hx.1 heta hgap hx.2.1.1 hx.2.1.2
      hx.2.2.1 hx.2.2.2

theorem ae_unstableProjection_fderiv_inverse_fixed
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
    (heta : 0 < eta) (hgap : 7 * eta < lam1 - lam2) :
    ∀ᵐ x ∂mu, ∀ z : EucPlane,
      stableProjection T_inv (T_inv x)
          (fderiv ℝ T_inv x (stableProjection T_inv x z)) =
        fderiv ℝ T_inv x (stableProjection T_inv x z) := by
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
  exact ae_stableProjection_fderiv_fixed
    (lam1 := -lam2) (lam2 := -lam1)
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam1_inv hlam2_inv heta (by linarith)

end Submission.Helpers
