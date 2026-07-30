import Submission.LyapunovSplitting

namespace Submission.Helpers

open LeanEval.Dynamics Filter Topology

lemma stableProjection_apply_eq_of_eventual_subtop_growth
    {T : EucPlane → EucPlane} {x z : EucPlane}
    {top rate eta : ℝ}
    (hrate : rate < top - eta)
    (hP : Tendsto (fun n => stableApproxProjection T n x)
      atTop (nhds (stableProjection T x)))
    (htop : ∀ᶠ n : ℕ in atTop,
      Real.exp ((top - eta) * n) ≤ ‖fderiv ℝ (T^[n]) x‖)
    (hz : ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x z‖ ≤ Real.exp (rate * n) * ‖z‖) :
    stableProjection T x z = z := by
  let gamma := top - eta - rate
  have hgamma : 0 < gamma := by dsimp [gamma]; linarith
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖z - stableApproxProjection T n x z‖ ≤
        Real.exp (-gamma * n) * ‖z‖ := by
    filter_upwards [htop, hz] with n htop_n hz_n
    let A := fderiv ℝ (T^[n]) x
    have hbasic := norm_mul_norm_sub_planeMinProjection_le_norm_apply A z
    have hscaled : Real.exp ((top - eta) * n) *
        ‖z - stableApproxProjection T n x z‖ ≤ ‖A z‖ := by
      calc
        Real.exp ((top - eta) * n) *
            ‖z - stableApproxProjection T n x z‖ ≤
            ‖A‖ * ‖z - stableApproxProjection T n x z‖ := by
          gcongr
        _ ≤ ‖A z‖ := by
          simpa [stableApproxProjection, A] using hbasic
    apply (mul_le_mul_iff_of_pos_left
      (Real.exp_pos ((top - eta) * n))).mp
    calc
      Real.exp ((top - eta) * n) *
          ‖z - stableApproxProjection T n x z‖ ≤ ‖A z‖ := hscaled
      _ ≤ Real.exp (rate * n) * ‖z‖ := hz_n
      _ = Real.exp ((top - eta) * n) *
          (Real.exp (-gamma * n) * ‖z‖) := by
        dsimp [gamma]
        rw [show Real.exp ((top - eta) * (n : ℝ)) *
            (Real.exp (-(top - eta - rate) * (n : ℝ)) * ‖z‖) =
          (Real.exp ((top - eta) * (n : ℝ)) *
            Real.exp (-(top - eta - rate) * (n : ℝ))) * ‖z‖ by ring]
        rw [← Real.exp_add]
        congr 2
        ring
  have hdecay : Tendsto (fun n : ℕ => Real.exp (-gamma * n) * ‖z‖)
      atTop (nhds 0) := by
    have hr : Real.exp (-gamma) < 1 :=
      (Real.exp_lt_one_iff).2 (neg_neg_of_pos hgamma)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_nonneg (-gamma)) hr
    have hscaled := hpow.mul_const ‖z‖
    convert hscaled using 1
    · funext n
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    · simp
  have hdist : Tendsto
      (fun n => dist (stableApproxProjection T n x z) z)
      atTop (nhds 0) := by
    have hnorm : Tendsto
        (fun n => ‖z - stableApproxProjection T n x z‖)
        atTop (nhds 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        hbound hdecay
    simpa [dist_eq_norm, norm_sub_rev] using hnorm
  have hPz : Tendsto (fun n => stableApproxProjection T n x z)
      atTop (nhds (stableProjection T x z)) := by
    have happly := ((ContinuousLinearMap.apply ℝ EucPlane) z).continuous
    apply ((happly.tendsto (stableProjection T x)).comp hP).congr'
    filter_upwards [] with n
    rfl
  have hzlim : Tendsto (fun _ : ℕ => z) atTop
      (nhds (stableProjection T x z)) := hPz.congr_dist hdist
  exact tendsto_nhds_unique hzlim tendsto_const_nhds

end Submission.Helpers
