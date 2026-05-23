import Mathlib
import Submission.Helpers

open Filter Topology Set

namespace Submission

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hcongr : ∀ᶠ t : ℝ in atTop, y t * Real.sqrt t = Real.sqrt (t / (1 + 2*t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht_le : 0 ≤ t := ht.le
    have hy_p : 0 < y t := Submission.Helpers.y_pos hy_diff hy_cont hy0 ht_le
    have hy_sq : (y t)^2 = 1 / (1 + 2*t) :=
      Submission.Helpers.y_sq_eq hy_diff hy_cont hy0 ht_le
    have hsqrt_t : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hsq : (y t * Real.sqrt t)^2 = t / (1 + 2*t) := by
      rw [mul_pow, Real.sq_sqrt ht_le, hy_sq]
      field_simp
    have hpos : 0 ≤ y t * Real.sqrt t := mul_nonneg hy_p.le hsqrt_t
    rw [show y t * Real.sqrt t = Real.sqrt ((y t * Real.sqrt t)^2) from
        (Real.sqrt_sq hpos).symm, hsq]
  refine Tendsto.congr' (.symm hcongr) ?_
  have hlimit : Tendsto (fun t : ℝ => Real.sqrt (t / (1 + 2*t))) atTop
      (𝓝 (Real.sqrt (1/2))) :=
    (Real.continuous_sqrt.tendsto _).comp Submission.Helpers.tendsto_t_div_one_plus_two_t
  have h12 : Real.sqrt (1/2) = 1 / Real.sqrt 2 := by
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.sqrt_inv,
        show ((1 : ℝ) / Real.sqrt 2 : ℝ) = (Real.sqrt 2)⁻¹ by rw [one_div]]
  rw [← h12]
  exact hlimit

end Submission
