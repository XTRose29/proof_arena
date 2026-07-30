import Mathlib
import Submission.Helpers

open Filter Topology

namespace Submission

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  let z : ℝ → ℝ := fun t => 1 / Real.sqrt (1 + 2 * t)
  have hz_diff (t : ℝ) (ht : 0 ≤ t) : HasDerivAt z (-(z t) ^ 3) t := by
    simpa only [z] using Helpers.explicitSolution_hasDerivAt t ht
  have hy_cont_on : ContinuousOn y (Set.Ici 0) := by
    intro t ht
    change 0 ≤ t at ht
    rcases eq_or_lt_of_le ht with rfl | ht
    · exact hy_cont
    · exact (hy_diff t ht).continuousAt.continuousWithinAt
  have hz_cont_on : ContinuousOn z (Set.Ici 0) := by
    intro t ht
    exact (hz_diff t ht).continuousAt.continuousWithinAt
  let e : ℝ → ℝ := fun t => y t - z t
  let e' : ℝ → ℝ := fun t => -(y t) ^ 3 - (-(z t) ^ 3)
  let d : ℝ → ℝ := fun t => e t * e t
  have hd_cont : ContinuousOn d (Set.Ici 0) := by
    exact (hy_cont_on.sub hz_cont_on).mul (hy_cont_on.sub hz_cont_on)
  let d' : ℝ → ℝ := fun t => e' t * e t + e t * e' t
  have hd_diff (t : ℝ) (ht : t ∈ interior (Set.Ici (0 : ℝ))) :
      HasDerivWithinAt d (d' t) (interior (Set.Ici (0 : ℝ))) t := by
    rw [interior_Ici] at ht ⊢
    have hy := hy_diff t ht
    have hz := hz_diff t ht.le
    dsimp [d, d', e, e']
    convert ((hy.sub hz).mul (hy.sub hz)).hasDerivWithinAt using 1 <;> rfl
  have hd_nonpos (t : ℝ) (_ht : t ∈ interior (Set.Ici (0 : ℝ))) : d' t ≤ 0 := by
    have hq : 0 ≤ y t ^ 2 + y t * z t + z t ^ 2 := by
      nlinarith [sq_nonneg (2 * y t + z t), sq_nonneg (z t)]
    have hfactor : d' t =
        -2 * (y t - z t) ^ 2 * (y t ^ 2 + y t * z t + z t ^ 2) := by
      dsimp [d', e, e']
      ring
    rw [hfactor]
    have hp : 0 ≤ 2 * (y t - z t) ^ 2 * (y t ^ 2 + y t * z t + z t ^ 2) :=
      mul_nonneg (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) (sq_nonneg _)) hq
    nlinarith
  have hd_anti : AntitoneOn d (Set.Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) hd_cont hd_diff hd_nonpos
  have hy_eq_z (t : ℝ) (ht : 0 ≤ t) : y t = z t := by
    have hle : d t ≤ d 0 := hd_anti (by simp) ht ht
    have hd0 : d 0 = 0 := by simp [d, e, z, hy0]
    rw [hd0] at hle
    dsimp [d, e] at hle
    nlinarith [sq_nonneg (y t - z t)]
  have hratio :
      Tendsto (fun t : ℝ => t / (1 + 2 * t)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hdenom : Tendsto (fun t : ℝ => t⁻¹ + 2) atTop (𝓝 (0 + 2)) :=
      tendsto_inv_atTop_zero.add tendsto_const_nhds
    have hdiv : Tendsto (fun t : ℝ => 1 / (t⁻¹ + 2)) atTop (𝓝 (1 / (0 + 2))) :=
      tendsto_const_nhds.div hdenom (by norm_num)
    have heq :
        (fun t : ℝ => 1 / (t⁻¹ + 2)) =ᶠ[atTop] (fun t : ℝ => t / (1 + 2 * t)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp [ht.ne']
    simpa only [zero_add] using hdiv.congr' heq
  have hsqrt_ratio :
      Tendsto (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) atTop
        (𝓝 (1 / Real.sqrt 2)) := by
    convert hratio.sqrt using 1
    · norm_num [Real.sqrt_div]
  apply hsqrt_ratio.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [hy_eq_z t ht]
  dsimp [z]
  rw [Real.sqrt_div ht]
  ring

end Submission
