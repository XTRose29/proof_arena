import Submission.GeometricBoundaryScale
import Submission.Orbit

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma eventually_norm_fderiv_iterate_lt_exp
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hx : x ∈ K) {a : ℝ}
    (ha : lyapunovUpperAt T x < a) :
    ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x‖ < Real.exp (a * n) := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  let u : ℕ → ℝ := fun n => Real.log ‖fderiv ℝ (T^[n]) x‖ / n
  have hu_upper : ∀ n, u n ≤ Real.log C := by
    intro n
    exact log_norm_fderiv_iterate_div_le
      T hT_smooth hK_inv hC_one hC n hx
  have hu_bounded : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hu_upper)
  have hu_eventually : ∀ᶠ n in atTop, u n < a := by
    apply eventually_lt_of_limsup_lt
    · simpa [lyapunovUpperAt, u] using ha
    · exact hu_bounded
  filter_upwards [hu_eventually, eventually_gt_atTop 0] with n hn hnpos
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog : Real.log ‖fderiv ℝ (T^[n]) x‖ < a * n := by
    exact (div_lt_iff₀ hnpos_real).mp hn
  have hnorm_pos : 0 < ‖fderiv ℝ (T^[n]) x‖ :=
    norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  rw [← Real.exp_log hnorm_pos]
  exact Real.exp_lt_exp.mpr hlog

lemma eventually_norm_fderiv_iterate_inverse_lt_exp
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hx : x ∈ K) {a : ℝ}
    (ha : -lyapunovLowerAt T x < a) :
    ∀ᶠ n : ℕ in atTop,
      ‖(fderiv ℝ (T^[n]) x).inverse‖ < Real.exp (a * n) := by
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  let u : ℕ → ℝ := fun n =>
    Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n
  have hu_upper : ∀ n, u n ≤ Real.log D := by
    intro n
    exact log_norm_fderiv_iterate_inverse_div_le T T_inv
      hT_smooth hT_inv_smooth hT_left hT_right hK_inv hD_one hD n hx
  have hu_bounded : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hu_upper)
  have hu_eventually : ∀ᶠ n in atTop, u n < a := by
    apply eventually_lt_of_limsup_lt
    · simpa [lyapunovLowerAt, u] using ha
    · exact hu_bounded
  filter_upwards [hu_eventually, eventually_gt_atTop 0] with n hn hnpos
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog : Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ < a * n := by
    exact (div_lt_iff₀ hnpos_real).mp hn
  have hnorm_pos : 0 < ‖(fderiv ℝ (T^[n]) x).inverse‖ := by
    rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left n (T^[n] x)
  rw [← Real.exp_log hnorm_pos]
  exact Real.exp_lt_exp.mpr hlog

lemma ae_eventually_norm_fderiv_iterate_lt_exp_integral_add
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0) (hmu_erg : Ergodic T mu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x‖ <
        Real.exp (((∫ y, lyapunovUpperAt T y ∂mu) + epsilon) * n) := by
  filter_upwards
      [lyapunovUpperAt_ae_eq_integral T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right K hK_compact hK_inv mu hmu_supp hmu_erg,
       mem_ae_iff.mpr hmu_supp] with x hxexp hxK
  apply eventually_norm_fderiv_iterate_lt_exp T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right hK_compact hK_inv hxK
  rw [hxexp]
  linarith

lemma ae_eventually_norm_fderiv_iterate_inverse_lt_exp_neg_integral_add
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0) (hmu_erg : Ergodic T mu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ‖(fderiv ℝ (T^[n]) x).inverse‖ <
        Real.exp ((-(∫ y, lyapunovLowerAt T y ∂mu) + epsilon) * n) := by
  filter_upwards
      [lyapunovLowerAt_ae_eq_integral T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right K hK_compact hK_inv mu hmu_supp hmu_erg,
       mem_ae_iff.mpr hmu_supp] with x hxexp hxK
  apply eventually_norm_fderiv_iterate_inverse_lt_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hxK
  rw [hxexp]
  linarith

end Submission.Helpers
