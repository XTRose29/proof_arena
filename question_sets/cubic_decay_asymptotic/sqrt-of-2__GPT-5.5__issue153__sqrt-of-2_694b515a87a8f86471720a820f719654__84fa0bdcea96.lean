import Mathlib

open Filter Topology

namespace Submission

lemma cubic_explicit_deriv {a c t : ℝ} (hat : a ≤ t) :
    HasDerivAt (fun x : ℝ => c * (1 + 2 * c ^ 2 * (x - a)) ^ (-(1 : ℝ) / 2))
      (-(c * (1 + 2 * c ^ 2 * (t - a)) ^ (-(1 : ℝ) / 2)) ^ 3) t := by
  have hbase_pos : 0 < 1 + 2 * c ^ 2 * (t - a) := by
    nlinarith [sq_nonneg c, sub_nonneg.mpr hat]
  have hpow : ((1 + 2 * c ^ 2 * (t - a) : ℝ) ^ (-(1 : ℝ) / 2)) ^ 3 =
      (1 + 2 * c ^ 2 * (t - a) : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_pos.le]
    ring_nf
  have hinner : HasDerivAt (fun x : ℝ => 1 + 2 * c ^ 2 * (x - a)) (2 * c ^ 2) t := by
    simpa using (((hasDerivAt_id t).sub_const a).const_mul (2 * c ^ 2)).const_add 1
  have hrpow := hinner.rpow_const (p := (-(1 : ℝ) / 2)) (Or.inl hbase_pos.ne')
  convert hrpow.const_mul c using 1
  rw [show (-(1 : ℝ) / 2 - 1) = (-(3 : ℝ) / 2) by ring]
  rw [← hpow]
  ring_nf

lemma cubic_explicit_eq_on_interval (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    {a b c : ℝ} (ha : 0 < a) (hc : y a = c) :
    Set.EqOn y (fun t : ℝ => c * (1 + 2 * c ^ 2 * (t - a)) ^ (-(1 : ℝ) / 2))
      (Set.Icc a b) := by
  let z : ℝ → ℝ := fun t => c * (1 + 2 * c ^ 2 * (t - a)) ^ (-(1 : ℝ) / 2)
  have hyc : ContinuousOn y (Set.Icc a b) := by
    exact HasDerivAt.continuousOn fun t ht => hy_diff t (lt_of_lt_of_le ha ht.1)
  have hzc : ContinuousOn z (Set.Icc a b) := by
    exact HasDerivAt.continuousOn fun t ht => (cubic_explicit_deriv (a := a) (c := c) ht.1)
  obtain ⟨Cy, hCy⟩ := isCompact_Icc.exists_bound_of_continuousOn hyc
  obtain ⟨Cz, hCz⟩ := isCompact_Icc.exists_bound_of_continuousOn hzc
  let M : ℝ := max Cy Cz
  obtain ⟨K, hK⟩ :
      ∃ K, LipschitzOnWith K (fun x : ℝ => -x ^ 3) (Set.Icc (-M) M) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    exact ((by fun_prop : ContDiff ℝ 1 (fun x : ℝ => -x ^ 3)).locallyLipschitz.locallyLipschitzOn)
  apply ODE_solution_unique_of_mem_Icc_right
    (K := K) (v := fun _ x : ℝ => -x ^ 3) (s := fun _ => Set.Icc (-M) M)
  · intro _ _; exact hK
  · exact hyc
  · intro t ht
    exact (hy_diff t (lt_of_lt_of_le ha ht.1)).hasDerivWithinAt
  · intro t ht
    have hnorm := hCy t (Set.Ico_subset_Icc_self ht)
    have hleM : ‖y t‖ ≤ M := hnorm.trans (le_max_left _ _)
    rw [Real.norm_eq_abs] at hleM
    exact abs_le.mp hleM
  · exact hzc
  · intro t ht
    exact (cubic_explicit_deriv (a := a) (c := c) (Set.Ico_subset_Icc_self ht).1).hasDerivWithinAt
  · intro t ht
    have hnorm := hCz t (Set.Ico_subset_Icc_self ht)
    have hleM : ‖z t‖ ≤ M := hnorm.trans (le_max_right _ _)
    rw [Real.norm_eq_abs] at hleM
    exact abs_le.mp hleM
  · simpa [hc]

lemma cubic_ratio_tendsto {k d : ℝ} (hk : k ≠ 0) :
    Tendsto (fun t : ℝ => t / (k * t + d)) atTop (𝓝 (1 / k)) := by
  have hzero : Tendsto (fun t : ℝ => d / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hden : Tendsto (fun t : ℝ => k + d / t) atTop (𝓝 k) := by
    simpa using (tendsto_const_nhds (x := k)).add hzero
  have hmain : Tendsto (fun t : ℝ => (1 : ℝ) / (k + d / t)) atTop (𝓝 (1 / k)) :=
    tendsto_const_nhds.div hden hk
  refine hmain.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp [ht]

lemma cubic_limit_const {c : ℝ} (hc : 0 < c) :
    c * (1 / (2 * c ^ 2)) ^ ((1 : ℝ) / 2) = 1 / Real.sqrt 2 := by
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1) (2 * c ^ 2)]
  rw [Real.sqrt_one]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) (c ^ 2)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]
  field_simp [hc.ne', (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)).ne']

lemma cubic_explicit_tendsto {a c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (c * (1 + 2 * c ^ 2 * (t - a)) ^ (-(1 : ℝ) / 2)) *
      Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hk : (2 * c ^ 2 : ℝ) ≠ 0 := by positivity
  have hratio : Tendsto
      (fun t : ℝ => t / ((2 * c ^ 2) * t + (1 - 2 * c ^ 2 * a)))
      atTop (𝓝 (1 / (2 * c ^ 2))) :=
    cubic_ratio_tendsto hk
  have hlimpos : (1 / (2 * c ^ 2) : ℝ) ≠ 0 := by positivity
  have hroot : Tendsto
      (fun t : ℝ => (t / ((2 * c ^ 2) * t + (1 - 2 * c ^ 2 * a))) ^ ((1 : ℝ) / 2))
      atTop (𝓝 ((1 / (2 * c ^ 2)) ^ ((1 : ℝ) / 2))) :=
    hratio.rpow_const (Or.inl hlimpos)
  have hmain := hroot.const_mul c
  rw [cubic_limit_const hc] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (max 0 a)] with t ht
  have ht0 : 0 ≤ t := le_trans (le_max_left 0 a) ht
  have hat : a ≤ t := le_trans (le_max_right 0 a) ht
  have hden_pos : 0 < 1 + 2 * c ^ 2 * (t - a) := by
    nlinarith [sq_pos_of_pos hc, sub_nonneg.mpr hat]
  rw [Real.sqrt_eq_rpow]
  rw [show ((2 * c ^ 2) * t + (1 - 2 * c ^ 2 * a)) =
      1 + 2 * c ^ 2 * (t - a) by ring]
  calc
    c * (t / (1 + 2 * c ^ 2 * (t - a))) ^ ((1 : ℝ) / 2)
        = c * (t ^ ((1 : ℝ) / 2) / (1 + 2 * c ^ 2 * (t - a)) ^ ((1 : ℝ) / 2)) := by
          rw [Real.div_rpow ht0 hden_pos.le ((1 : ℝ) / 2)]
    _ = (c * (1 + 2 * c ^ 2 * (t - a)) ^ (-(1 : ℝ) / 2)) * t ^ ((1 : ℝ) / 2) := by
          rw [div_eq_mul_inv]
          rw [← Real.rpow_neg hden_pos.le]
          ring_nf

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have htarget : {x : ℝ | 0 < x} ∈ 𝓝 (y 0) := by
    rw [hy0]
    change Set.Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ)
    exact isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) from by norm_num)
  have hev : ∀ᶠ t in 𝓝[Set.Ici 0] 0, 0 < y t := hy_cont htarget
  have hev' : ∀ᶠ t in 𝓝 0, t ∈ Set.Ici (0 : ℝ) → 0 < y t :=
    eventually_nhdsWithin_iff.mp hev
  rcases Metric.eventually_nhds_iff.mp hev' with ⟨ε, hε, hball⟩
  let a : ℝ := ε / 2
  have ha : 0 < a := by positivity
  have hya : 0 < y a := by
    apply hball
    · rw [dist_eq_norm]
      simp [a, abs_of_pos hε]
      linarith
    · simp [a, le_of_lt ha]
  have hz := cubic_explicit_tendsto (a := a) (c := y a) hya
  refine hz.congr' ?_
  filter_upwards [eventually_ge_atTop a] with t ht
  have heq := cubic_explicit_eq_on_interval y hy_diff (a := a) (b := t) (c := y a) ha rfl
  have hyt : y t = (y a) * (1 + 2 * (y a) ^ 2 * (t - a)) ^ (-(1 : ℝ) / 2) :=
    heq ⟨ht, le_rfl⟩
  rw [hyt]

end Submission
