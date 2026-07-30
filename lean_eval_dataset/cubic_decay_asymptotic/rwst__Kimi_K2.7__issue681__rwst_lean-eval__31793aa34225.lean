import Mathlib
import Submission.Helpers

open Filter Topology

namespace Submission

-- bring the helper into the current namespace
open Submission.Helpers

 theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hy_cont_Ioi : ∀ t, 0 < t → ContinuousAt y t := by
    intro t ht
    exact (hy_diff t ht).continuousAt

  have hy_cont_Ici : ContinuousOn y (Set.Ici 0) := by
    intro t ht
    have ht' : 0 ≤ t := ht
    rcases lt_or_eq_of_le ht' with (ht_pos | rfl)
    · exact (hy_cont_Ioi t ht_pos).continuousWithinAt
    · exact hy_cont

  have hy_pos : ∀ t, 0 ≤ t → y t > 0 := by
    intro t ht
    by_contra h
    push Not at h

    have ht_pos : 0 < t := by
      by_contra h'
      push Not at h'
      have : t = 0 := by linarith
      rw [this] at h
      linarith [hy0]

    -- Find a zero in (0, t].
    have h_zero : ∃ t2, 0 < t2 ∧ t2 ≤ t ∧ y t2 = 0 := by
      by_cases h_eq : y t = 0
      · exact ⟨t, ht_pos, by rfl, h_eq⟩
      · have ht_neg : y t < 0 := by
          apply lt_of_le_of_ne
          · exact h
          · exact h_eq
        have h_cont_Icc : ContinuousOn y (Set.Icc 0 t) := by
          apply ContinuousOn.mono hy_cont_Ici
          intro x hx
          simp at hx ⊢
          linarith [hx.1, hx.2, show 0 ≤ t by linarith]
        have : ∃ c, c ∈ Set.Icc 0 t ∧ y c = 0 := by
          have h_neg_cont : ContinuousOn (fun x => -y x) (Set.Icc 0 t) := h_cont_Icc.neg
          have h_neg0 : -y 0 ≤ 0 := by linarith [hy0]
          have h_neg1 : 0 ≤ -y t := by linarith [ht_neg]
          have h_ivt : Set.Icc (-y 0) (-y t) ⊆ (fun x => -y x) '' Set.Icc 0 t :=
            intermediate_value_Icc ht_pos.le h_neg_cont
          have h0_in : 0 ∈ Set.Icc (-y 0) (-y t) := ⟨h_neg0, h_neg1⟩
          rcases h_ivt h0_in with ⟨c, hc, hyc⟩
          use c, hc
          linarith
        rcases this with ⟨c, hc, hyc⟩
        have hc_pos : 0 < c := by
          by_contra h'
          push Not at h'
          have : c = 0 := by linarith [hc.1, h']
          rw [this] at hyc
          linarith [hy0]
        exact ⟨c, hc_pos, hc.2, hyc⟩

    rcases h_zero with ⟨c, hc_pos, hc_le, hyc⟩

    -- Let t3 be the least zero in [0, t].
    let S := {s : ℝ | 0 ≤ s ∧ s ≤ t ∧ y s = 0}
    have hS_eq : S = Set.Icc 0 t ∩ y ⁻¹' {0} := by
      ext s
      simp [S]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    have hS_compact : IsCompact S := by
      rw [hS_eq]
      apply Metric.isCompact_of_isClosed_isBounded
      · -- closed
        apply ContinuousOn.preimage_isClosed_of_isClosed
        · apply ContinuousOn.mono hy_cont_Ici
          intro x hx
          simp at hx ⊢
          linarith [hx.1, hx.2, show 0 ≤ t by linarith]
        · exact isClosed_Icc
        · exact isClosed_singleton
      · -- bounded
        apply Bornology.IsBounded.subset (Metric.isBounded_Icc (0 : ℝ) t)
        intro s hs
        simp at hs ⊢
        exact hs.1
    have hS_nonempty : S.Nonempty := ⟨c, by exact ⟨hc_pos.le, hc_le, hyc⟩⟩
    have ht3_least : IsLeast S (sInf S) := IsCompact.isLeast_sInf hS_compact hS_nonempty
    let t3 := sInf S
    have ht3_mem : t3 ∈ S := ht3_least.1
    have ht3_le : ∀ s ∈ S, t3 ≤ s := ht3_least.2

    have ht3_nonneg : 0 ≤ t3 := ht3_mem.1
    have ht3_le_t : t3 ≤ t := ht3_mem.2.1
    have ht3_zero : y t3 = 0 := ht3_mem.2.2
    have ht3_pos : 0 < t3 := by
      by_contra h'
      push Not at h'
      have : t3 = 0 := by linarith
      rw [this] at ht3_zero
      linarith [hy0]

    -- y is positive on [0, t3).
    have ht3_pos_interval : ∀ s, 0 ≤ s ∧ s < t3 → y s > 0 := by
      intro s hs
      have hs_nonneg : 0 ≤ s := hs.1
      have hs_lt : s < t3 := hs.2
      have hs_notin_S : s ∉ S := by
        intro h
        have : t3 ≤ s := ht3_le s h
        linarith
      have hs_ne_zero : y s ≠ 0 := by
        intro h
        apply hs_notin_S
        exact ⟨hs_nonneg, by linarith [hs_lt, ht3_le_t], h⟩
      by_contra h_neg
      push Not at h_neg
      have : y s < 0 := by
        apply lt_of_le_of_ne
        · linarith
        · exact hs_ne_zero
      have h_cont_Icc : ContinuousOn y (Set.Icc 0 s) := by
        apply ContinuousOn.mono hy_cont_Ici
        intro x hx
        simp at hx ⊢
        linarith [hx.1, hx.2, show 0 ≤ s by linarith, show s ≤ t by linarith [hs_lt, ht3_le_t]]
      have : ∃ c, c ∈ Set.Icc 0 s ∧ y c = 0 := by
        have h_neg_cont : ContinuousOn (fun x => -y x) (Set.Icc 0 s) := h_cont_Icc.neg
        have h_neg0 : -y 0 ≤ 0 := by linarith [hy0]
        have h_neg1 : 0 ≤ -y s := by linarith
        have h_ivt : Set.Icc (-y 0) (-y s) ⊆ (fun x => -y x) '' Set.Icc 0 s :=
          intermediate_value_Icc (show 0 ≤ s by linarith) h_neg_cont
        have h0_in : 0 ∈ Set.Icc (-y 0) (-y s) := ⟨h_neg0, h_neg1⟩
        rcases h_ivt h0_in with ⟨c, hc, hyc⟩
        use c, hc
        linarith
      rcases this with ⟨c, hc, hyc⟩
      have hc_pos : 0 < c := by
        by_contra h'
        push Not at h'
        have : c = 0 := by linarith [hc.1, h']
        rw [this] at hyc
        linarith [hy0]
      have hc_le_s : c ≤ s := hc.2
      have hc_in_S : c ∈ S := ⟨by linarith, by linarith [hc_le_s, hs_lt, ht3_le_t], hyc⟩
      have : t3 ≤ c := ht3_le c hc_in_S
      linarith

    let z := fun s : ℝ => 1 / y s ^ 2

    -- z'(s) = 2 on (0, t3).
    have hz_deriv : ∀ s, 0 < s ∧ s < t3 → HasDerivAt z 2 s := by
      intro s hs
      have hs_pos : 0 < s := hs.1
      have hs_lt : s < t3 := hs.2
      have hyne : y s ≠ 0 := by linarith [ht3_pos_interval s ⟨by linarith, hs_lt⟩]
      have h1 : HasDerivAt y (-(y s) ^ 3) s := hy_diff s hs_pos
      have h2 : HasDerivAt z (-2 * (-(y s) ^ 3) / y s ^ 3) s := by
        apply Submission.Helpers.hasDerivAt_inv_sq h1 hyne
      convert h2 using 1
      field_simp [hyne]

    -- z(s) = 1 + 2s on [0, t3) by the mean value theorem.
    have hz_eq : ∀ s, 0 ≤ s ∧ s < t3 → z s = 1 + 2 * s := by
      intro s hs
      have hs_nonneg : 0 ≤ s := hs.1
      have hs_lt : s < t3 := hs.2
      rcases lt_or_eq_of_le hs_nonneg with (hs_pos | hs_zero)
      · -- 0 < s < t3
        have h_cont : ContinuousOn z (Set.Icc 0 s) := by
          have h1 : ContinuousOn (fun x => y x ^ 2) (Set.Icc 0 s) := by
            apply ContinuousOn.pow
            apply ContinuousOn.mono hy_cont_Ici
            intro x hx
            simp at hx ⊢
            linarith [hx.1, hx.2, show 0 ≤ s by linarith, show s ≤ t by linarith [hs_lt, ht3_le_t]]
          apply ContinuousOn.div
          · exact continuousOn_const
          · exact h1
          · intro x hx
            have : y x > 0 := ht3_pos_interval x ⟨by simp at hx ⊢; linarith, by linarith [hx.2, hs_lt]⟩
            nlinarith
        have h_diff : ∀ x ∈ Set.Ioo 0 s, HasDerivAt z 2 x := by
          intro x hx
          exact hz_deriv x ⟨hx.1, by linarith [hx.2, hs_lt]⟩
        rcases exists_hasDerivAt_eq_slope z (fun _ => 2) (show 0 < s by linarith) h_cont h_diff with ⟨c, hc, hzc⟩
        have hz0 : z 0 = 1 := by
          simp [z, hy0]
        have hzc' : 2 = (z s - z 0) / (s - 0) := by linarith
        rw [hz0] at hzc'
        field_simp at hzc'
        linarith
      · -- s = 0
        rw [←hs_zero]
        simp [z, hy0]

    -- From z(s) = 1 + 2s we get y(s) → 1/√(1 + 2 t3) as s → t3-.
    have h_y_tendsto_pos : Tendsto y (𝓝[<] t3) (𝓝 (1 / Real.sqrt (1 + 2 * t3))) := by
      have h_eq : ∀ᶠ s in 𝓝[<] t3, y s = 1 / Real.sqrt (z s) := by
        have : Set.Ioo (t3 / 2) t3 ∈ 𝓝[<] t3 := Ioo_mem_nhdsLT (by linarith)
        apply Filter.mem_of_superset this
        intro s hs
        have hs_nonneg : 0 ≤ s := by linarith [hs.1]
        have hs_lt : s < t3 := hs.2
        have h_pos : y s > 0 := ht3_pos_interval s ⟨hs_nonneg, hs_lt⟩
        have h_z_eq : z s = (1 / y s) ^ 2 := by
          simp [z]
        have h_sqrt : Real.sqrt (z s) = 1 / y s := by
          rw [h_z_eq]
          rw [Real.sqrt_sq (by positivity)]
        have h : y s = 1 / Real.sqrt (z s) := by
          rw [h_sqrt]
          field_simp [h_pos.ne']
        simpa using h
      have h_z_tendsto : Tendsto z (𝓝[<] t3) (𝓝 (1 + 2 * t3)) := by
        have h_eq' : ∀ᶠ s in 𝓝[<] t3, z s = 1 + 2 * s := by
          have : Set.Ioo (t3 / 2) t3 ∈ 𝓝[<] t3 := Ioo_mem_nhdsLT (by linarith)
          apply Filter.mem_of_superset this
          intro s hs
          have hs_nonneg : 0 ≤ s := by linarith [hs.1]
          exact hz_eq s ⟨hs_nonneg, hs.2⟩
        have h_tendsto : Tendsto (fun s => 1 + 2 * s) (𝓝[<] t3) (𝓝 (1 + 2 * t3)) := by
          apply Tendsto.mono_left _ nhdsWithin_le_nhds
          · apply Continuous.tendsto
            continuity
        have h_eq'' : (fun s => 1 + 2 * s) =ᶠ[𝓝[<] t3] z := by
          filter_upwards [h_eq'] with s hs
          linarith [hs]
        exact Tendsto.congr' h_eq'' h_tendsto
      have h_sqrt_tendsto : Tendsto (fun s => Real.sqrt (z s)) (𝓝[<] t3) (𝓝 (Real.sqrt (1 + 2 * t3))) := by
        apply Tendsto.comp
        · exact (Real.continuous_sqrt.tendsto _)
        · exact h_z_tendsto
      have h_aux : Tendsto (fun s => 1 / Real.sqrt (z s)) (𝓝[<] t3) (𝓝 (1 / Real.sqrt (1 + 2 * t3))) := by
        apply Tendsto.div tendsto_const_nhds h_sqrt_tendsto
        · -- denominator limit is nonzero
          have h : Real.sqrt (1 + 2 * t3) > 0 := Real.sqrt_pos.mpr (by linarith)
          exact ne_of_gt h
      have h_eq'' : y =ᶠ[𝓝[<] t3] (fun s => 1 / Real.sqrt (z s)) := by
        filter_upwards [h_eq] with s hs
        linarith [hs]
      exact Tendsto.congr' h_eq''.symm h_aux

    -- But y is continuous at t3 and y(t3) = 0, so y(s) → 0 as s → t3-.
    have h_y_tendsto_0 : Tendsto y (𝓝[<] t3) (𝓝 0) := by
      have : Tendsto y (𝓝 t3) (𝓝 (y t3)) := (hy_cont_Ioi t3 ht3_pos).tendsto
      rw [ht3_zero] at this
      exact Tendsto.mono_left this nhdsWithin_le_nhds

    -- Limits are unique in ℝ, so 1/√(1 + 2 t3) = 0, contradicting positivity.
    have h_unique : 0 = 1 / Real.sqrt (1 + 2 * t3) := by
      apply tendsto_nhds_unique' _ h_y_tendsto_0 h_y_tendsto_pos
      apply nhdsWithin_Iio_neBot'
      · use t3 - 1
        simp
      · exact le_rfl
    have h_pos' : 1 / Real.sqrt (1 + 2 * t3) > 0 := by
      apply div_pos
      · norm_num
      · apply Real.sqrt_pos.mpr
        linarith
    linarith

  have hy_eq : ∀ t, 0 ≤ t → y t = 1 / Real.sqrt (1 + 2 * t) := by
    intro t ht
    rcases lt_or_eq_of_le ht with (ht_pos | rfl)
    · -- t > 0: apply the mean value theorem to z on [0, t]
      let z := fun s : ℝ => 1 / y s ^ 2
      have hz0 : z 0 = 1 := by
        simp [z, hy0]
      have hz_deriv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt z 2 s := by
        intro s hs
        have hs_pos : 0 < s := hs.1
        have hyne : y s ≠ 0 := (hy_pos s hs_pos.le).ne'
        have h1 : HasDerivAt y (-(y s) ^ 3) s := hy_diff s hs_pos
        have h2 : HasDerivAt z (-2 * (-(y s) ^ 3) / y s ^ 3) s := by
          apply Submission.Helpers.hasDerivAt_inv_sq h1 hyne
        convert h2 using 1
        field_simp [hyne]
      have h_cont : ContinuousOn z (Set.Icc 0 t) := by
        have h1 : ContinuousOn (fun x => y x ^ 2) (Set.Icc 0 t) := by
          apply ContinuousOn.pow
          apply ContinuousOn.mono hy_cont_Ici
          intro x hx
          simp at hx ⊢
          linarith [hx.1, hx.2, show 0 ≤ t by linarith]
        apply ContinuousOn.div
        · exact continuousOn_const
        · exact h1
        · intro x hx
          have : y x > 0 := hy_pos x (by simp at hx ⊢; linarith [hx.1, hx.2, show 0 ≤ t by linarith])
          nlinarith
      rcases exists_hasDerivAt_eq_slope z (fun _ => 2) ht_pos h_cont hz_deriv with ⟨c, hc, hzc⟩
      have hz_t : z t = 1 + 2 * t := by
        have hz0' : z 0 = 1 := hz0
        have h_eq : 2 = (z t - z 0) / (t - 0) := by linarith
        rw [hz0'] at h_eq
        field_simp at h_eq
        linarith
      have h_pos : y t > 0 := hy_pos t ht
      have h_z_eq : z t = (1 / y t) ^ 2 := by
        simp [z]
      rw [hz_t] at h_z_eq
      have h_sqrt : Real.sqrt (1 + 2 * t) = 1 / y t := by
        have h : (1 / y t) ^ 2 = 1 + 2 * t := by linarith [h_z_eq]
        have h_nonneg : 0 ≤ 1 / y t := by positivity
        rw [←h]
        exact Real.sqrt_sq h_nonneg
      rw [h_sqrt]
      field_simp [h_pos.ne']
    · -- t = 0
      rw [hy0]
      norm_num

  have h_lim : Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
    have h_eq : (fun t => y t * Real.sqrt t) =ᶠ[atTop] (fun t => Real.sqrt (t / (1 + 2 * t))) := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [hy_eq t ht]
      have h_pos2 : 0 < 1 + 2 * t := by linarith
      have h_alg : (1 / Real.sqrt (1 + 2 * t)) * Real.sqrt t = Real.sqrt t / Real.sqrt (1 + 2 * t) := by
        ring
      rw [h_alg]
      rw [Real.sqrt_div (by linarith)]
    have h_inner : Tendsto (fun (t : ℝ) => t / (1 + 2 * t)) atTop (𝓝 (1 / 2)) := by
      have h_eq : (fun (t : ℝ) => t / (1 + 2 * t)) =ᶠ[atTop] (fun (t : ℝ) => 1 / (2 + 1 / t)) := by
        filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with t ht
        field_simp [ht]
        ring
      have h_denom : Tendsto (fun (t : ℝ) => 2 + 1 / t) atTop (𝓝 2) := by
        have h_inv : Tendsto (fun (t : ℝ) => 1 / t) atTop (𝓝 0) := by
          simpa using tendsto_inv_atTop_zero
        have h_const : Tendsto (fun (_ : ℝ) => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
        simpa only [add_zero] using Tendsto.add h_const h_inv
      have h_quot : Tendsto (fun (t : ℝ) => 1 / (2 + 1 / t)) atTop (𝓝 (1 / 2)) := by
        apply Tendsto.div tendsto_const_nhds h_denom (by norm_num)
      exact Tendsto.congr' h_eq.symm h_quot
    have h_sqrt_tendsto : Tendsto (fun (t : ℝ) => Real.sqrt (t / (1 + 2 * t))) atTop (𝓝 (Real.sqrt (1 / 2))) := by
      apply Tendsto.comp
      · exact (Real.continuous_sqrt.tendsto _)
      · exact h_inner
    have h_target : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
      rw [Real.sqrt_div (by norm_num)]
      norm_num
    rw [h_target] at h_sqrt_tendsto
    exact Tendsto.congr' h_eq.symm h_sqrt_tendsto

  exact h_lim

end Submission
