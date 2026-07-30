import Mathlib

namespace Submission

open Filter Topology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) :=
/-ResultProofBegin-/by
  -- The particular factor below avoids any division by the (a priori) unknown solution.
  -- It satisfies a linear equation, and hence is forced to be constant.
  let f : ℝ → ℝ := fun t => 2 * (y t) ^ 2
  let g : ℝ → ℝ := fun t => (1 + 2*t) * (y t) ^ 2 - 1
  have hyIcc : ∀ (b : ℝ), 0 ≤ b → ContinuousOn y (Set.Icc 0 b) := by
    intro b hb x hx
    by_cases h0x : x = 0
    · subst x
      exact hy_cont.mono (by
        intro z hz
        exact hz.1)
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0x)
      exact (hy_diff x hxpos).continuousAt.continuousWithinAt
  have hypos : ContinuousOn y (Set.Ioi 0) := by
    intro x hx
    exact (hy_diff x hx).continuousAt.continuousWithinAt
  have hfpos : ContinuousOn f (Set.Ioi 0) := by
    dsimp [f]
    exact (hypos.pow 2).const_mul 2
  have hfcAt : ∀ (x : ℝ), 0 < x → ContinuousAt f x := by
    intro x hx
    dsimp [f]
    exact ((hy_diff x hx).continuousAt.pow 2).const_mul 2
  have hA : ∀ (x : ℝ), 0 < x →
      HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, f s) (f x) x := by
    intro x hx
    have hfi : ContinuousOn f (Set.Icc 0 x) := by
      dsimp [f]
      exact ((hyIcc x hx.le).pow 2).const_mul 2
    have hInt : IntervalIntegrable f MeasureTheory.volume 0 x :=
      ContinuousOn.intervalIntegrable_of_Icc hx.le hfi
    have hmeas : StronglyMeasurableAtFilter f (𝓝 x) MeasureTheory.volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hfpos x hx
    exact intervalIntegral.integral_hasDerivAt_right hInt hmeas (hfcAt x hx)
  have hg' : ∀ (x : ℝ), 0 < x → HasDerivAt g (-(f x) * g x) x := by
    intro x hx
    have hlin : HasDerivAt (fun t : ℝ => 1 + 2*t) 2 x := by
      simpa using (((hasDerivAt_id x).const_mul (2:ℝ)).const_add (1:ℝ))
    have hp' : HasDerivAt (fun t : ℝ => (y t)^2)
          ((2:ℝ) * (y x) * (-(y x)^3)) x := by
      convert (hy_diff x hx).mul (hy_diff x hx) using 1
      · rfl
      · rfl
      · ext t; simp [pow_two]
      · ring
    have hsub := (hlin.mul hp').sub_const (1:ℝ)
    have heq : (2:ℝ) * (y x)^2 + (1 + 2*x) * ((2:ℝ) * (y x) * (-(y x)^3)) =
          -(f x) * g x := by
      simp [f, g]
      ring
    rw [heq] at hsub
    simpa [g] using hsub
  let A : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, f s
  let H : ℝ → ℝ := fun u => Real.exp (A u) * g u
  have hH' : ∀ (x : ℝ), 0 < x → HasDerivAt H 0 x := by
    intro x hx
    have hAx : HasDerivAt A (f x) x := by
      exact hA x hx
    have hm := hAx.exp.mul (hg' x hx)
    have hz : (Real.exp (A x) * (f x)) * (g x) +
        Real.exp (A x) * (-(f x) * g x) = 0 := by ring
    rw [hz] at hm
    -- change the pointwise product into the notation used for `H`
    convert hm using 1
    · rfl
    · rfl
    · ext t; rfl
  have hgcont : ∀ (b : ℝ), 0 ≤ b → ContinuousOn g (Set.Icc 0 b) := by
    intro b hb
    dsimp [g]
    have hlinC : Continuous (fun t : ℝ => 1 + 2*t) := by fun_prop
    exact (hlinC.continuousOn.fun_mul ((hyIcc b hb).pow 2)).sub continuousOn_const
  have hAcont : ∀ (b : ℝ), 0 ≤ b → ContinuousOn A (Set.Icc 0 b) := by
    intro b hb
    have hfi : ContinuousOn f (Set.Icc 0 b) := by
      dsimp [f]
      exact ((hyIcc b hb).pow 2).const_mul 2
    have hi : MeasureTheory.IntegrableOn f (Set.Icc 0 b) MeasureTheory.volume :=
      hfi.integrableOn_Icc
    have hi' : MeasureTheory.IntegrableOn f (Set.uIcc (0:ℝ) b) MeasureTheory.volume := by
      simpa [Set.uIcc_of_le hb] using hi
    have hc := intervalIntegral.continuousOn_primitive_interval hi'
    simpa [A, Set.uIcc_of_le hb] using hc
  have hHcont : ∀ (b : ℝ), 0 ≤ b → ContinuousOn H (Set.Icc 0 b) := by
    intro b hb
    have hec : ContinuousOn (fun x : ℝ => Real.exp (A x)) (Set.Icc 0 b) :=
      Real.continuous_exp.comp_continuousOn (hAcont b hb)
    exact hec.fun_mul (hgcont b hb)
  have hHzero : ∀ (t : ℝ), 0 ≤ t → H t = H 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht with (rfl | htpos)
    · rfl
    · obtain ⟨c, hc, hcval⟩ :=
        exists_hasDerivAt_eq_slope H (fun _ : ℝ => (0:ℝ)) htpos
          (hHcont t ht) (by
            intro x hx
            exact hH' x hx.1)
      have hquot : (H t - H 0) / (t - 0) = 0 := hcval.symm
      have htne : t - 0 ≠ 0 := sub_ne_zero.mpr htpos.ne'
      have hsub0 : H t - H 0 = 0 := (div_eq_zero_iff).1 hquot |>.resolve_right htne
      exact sub_eq_zero.mp hsub0
  have hgzero : ∀ (t : ℝ), 0 ≤ t → g t = 0 := by
    intro t ht
    have h := hHzero t ht
    have hg0 : g 0 = 0 := by simp [g, hy0]
    have hA0 : A 0 = 0 := by simp [A]
    -- the exponential never vanishes; here both values at zero are explicit
    simpa [H, hA0, hg0] using h
  have hF : ∀ (t : ℝ), 0 ≤ t → (1 + 2*t) * (y t)^2 = 1 := by
    intro t ht
    have h := hgzero t ht
    change (1 + 2*t) * (y t)^2 - 1 = 0 at h
    linarith
  have hyne : ∀ (t : ℝ), 0 ≤ t → y t ≠ 0 := by
    intro t ht hz
    have hf := hF t ht
    rw [hz] at hf
    norm_num at hf
  have hypositive : ∀ (t : ℝ), 0 ≤ t → 0 < y t := by
    intro t ht
    by_contra hn
    have hle : y t ≤ 0 := le_of_not_gt hn
    have hlt : y t < 0 := lt_of_le_of_ne hle (hyne t ht)
    have hzmem : (0:ℝ) ∈ Set.Icc (y t) (y 0) := by
      constructor
      · exact hle
      · simp [hy0]
    obtain ⟨z, hz, hval⟩ :=
      (intermediate_value_Icc' ht (hyIcc t ht)) hzmem
    exact (hyne z hz.1) hval
  have hform : ∀ (t : ℝ), 0 < t →
      y t * Real.sqrt t = 1 / Real.sqrt (t⁻¹ + 2) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.le
    have ha : 0 < 1 + 2*t := by linarith
    have hsq : (y t)^2 = 1 / (1 + 2*t) := by
      apply (eq_div_iff (ne_of_gt ha)).2
      nlinarith [hF t ht0]
    have hroot : (1 / Real.sqrt (1 + 2*t))^2 = 1 / (1 + 2*t) := by
      rw [div_pow]
      norm_num
      rw [Real.sq_sqrt ha.le]
    have hyexpr : y t = 1 / Real.sqrt (1 + 2*t) := by
      apply (sq_eq_sq₀ (le_of_lt (hypositive t ht0)) (by
        have : 0 < Real.sqrt (1 + 2*t) := Real.sqrt_pos.2 ha
        positivity)).1
      calc
        (y t)^2 = 1 / (1 + 2*t) := hsq
        _ = (1 / Real.sqrt (1 + 2*t))^2 := hroot.symm
    rw [hyexpr]
    have hbpos : 0 < t⁻¹ + 2 := by
      have hi : 0 < t⁻¹ := inv_pos.2 ht
      linarith
    have hm : t * (t⁻¹ + 2) = 1 + 2*t := by
      field_simp
    have hsqrtfact : Real.sqrt (1 + 2*t) =
          Real.sqrt t * Real.sqrt (t⁻¹ + 2) := by
      rw [← hm]
      exact Real.sqrt_mul (le_of_lt ht) _
    rw [hsqrtfact]
    have htn : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
    have hbn : Real.sqrt (t⁻¹ + 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hbpos)
    field_simp
  have hlim : Tendsto (fun t : ℝ => (1:ℝ) / Real.sqrt (t⁻¹ + 2)) atTop
        (𝓝 (1 / Real.sqrt 2)) := by
    have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero
    have ha : Tendsto (fun t : ℝ => t⁻¹ + 2) atTop (𝓝 ((0:ℝ) + 2)) :=
      hi.add tendsto_const_nhds
    have hs : Tendsto (fun t : ℝ => Real.sqrt (t⁻¹ + 2)) atTop
          (𝓝 (Real.sqrt 2)) := by
      convert ha.sqrt using 1 <;> norm_num
    exact tendsto_const_nhds.div hs (by positivity)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact (hform t ht).symm
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
