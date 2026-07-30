import Mathlib
import Submission.Helpers

open Filter Topology
open Set

namespace Submission

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  let φ : ℝ → ℝ := fun t => (1 + 2*t)*(y t)^2 - 1
  let ψ : ℝ → ℝ := fun t => φ t ^ 2

  have hψ_nonneg : ∀ t, ψ t ≥ 0 := by
    intro t; dsimp [ψ]; apply pow_two_nonneg

  have hψ0 : ψ 0 = 0 := by
    dsimp [ψ, φ]; rw [hy0]; norm_num

  have hy_sq_deriv : ∀ t > 0, HasDerivAt (fun t : ℝ => (y t)^2) (-2*(y t)^4) t := by
    intro t ht
    have h := (hy_diff t ht).pow 2
    have h' : HasDerivAt (fun t : ℝ => y t ^ 2) (-(2 * y t * y t ^ 3)) t := by
      simpa [show (fun t : ℝ => y t ^ 2) = y ^ 2 from rfl] using h
    simpa [show -(2 * y t * y t ^ 3) = -2*(y t)^4 from by ring] using h'

  have h_id_deriv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 + 2*t) 2 t := by
    intro t
    have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t :=
      hasDerivAt_const t (1 : ℝ)
    have h_two : HasDerivAt (fun x : ℝ => 2*x) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have hsum : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) + (fun x : ℝ => 2*x)) (0 + 2) t :=
      h_one.add h_two
    have heq : ((fun _ : ℝ => (1 : ℝ)) + (fun x : ℝ => 2*x)) = (fun t : ℝ => 1 + 2*t) := by
      ext x; simp
    have hsum' : HasDerivAt (fun t : ℝ => 1 + 2*t) (0 + 2) t := by
      simpa [heq] using hsum
    simpa [add_zero] using hsum'

  have hφ_deriv : ∀ t > 0, HasDerivAt φ (-2*(y t)^2*φ t) t := by
    intro t ht
    dsimp [φ]
    have hprod := (h_id_deriv t).mul (hy_sq_deriv t ht)
    have hprod_simp : 2 * y t ^ 2 + -((1 + 2 * t) * (2 * y t ^ 4)) = -2*(y t)^2*(((1 + 2*t)*(y t)^2 - 1)) := by ring
    have heq : ((fun t : ℝ => 1 + 2*t) * (fun t : ℝ => (y t)^2)) = (fun t : ℝ => (1 + 2*t)*(y t)^2) := by
      ext t; simp
    have hprod' : HasDerivAt (fun t : ℝ => (1 + 2*t)*(y t)^2) (-2*(y t)^2*(((1 + 2*t)*(y t)^2 - 1))) t := by
      simpa [hprod_simp, heq] using hprod
    have hsub : HasDerivAt (fun t : ℝ => (1 + 2*t)*(y t)^2 - 1) (-2*(y t)^2*(((1 + 2*t)*(y t)^2 - 1)) - 0) t :=
      hprod'.sub (hasDerivAt_const t 1)
    simpa [sub_zero] using hsub

  have hψ_deriv : ∀ t > 0, HasDerivAt ψ (-4*(y t)^2*ψ t) t := by
    intro t ht
    have h := hφ_deriv t ht
    have hsq := h.pow 2
    have h' : HasDerivAt (fun t : ℝ => φ t ^ 2) (-(2 * φ t * (2 * y t ^ 2 * φ t))) t := by
      simpa [show (fun t : ℝ => φ t ^ 2) = φ ^ 2 from rfl] using hsq
    have hsimp : -(2 * φ t * (2 * y t ^ 2 * φ t)) = -4*(y t)^2*(φ t)^2 := by ring
    simpa [ψ, hsimp] using h'

  have hψ_deriv_nonpos : ∀ t > 0, deriv ψ t ≤ 0 := by
    intro t ht
    have h := hψ_deriv t ht
    have hderiv : deriv ψ t = -4*(y t)^2*ψ t := h.deriv
    rw [hderiv]
    have hy_sq_nonneg : (y t)^2 ≥ 0 := by nlinarith
    have hψ_nonneg_t : ψ t ≥ 0 := hψ_nonneg t
    nlinarith

  have hψ_antitoneOn : AntitoneOn ψ (Ioi 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0) (f' := fun x : ℝ => -4*(y x)^2*ψ x) ?_ ?_ ?_
    · intro x hx
      have hy_cont_x : ContinuousAt y x := (hy_diff x hx).continuousAt
      have hφ_cont_x : ContinuousAt φ x := by
        dsimp [φ]
        refine ContinuousAt.sub ?_ continuousAt_const
        refine ContinuousAt.mul ?_ (hy_cont_x.pow 2)
        refine ContinuousAt.add continuousAt_const ?_
        exact continuousAt_id.const_mul 2
      exact (hφ_cont_x.pow 2).continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hψ_deriv x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hy_sq_nonneg : (y x)^2 ≥ 0 := by nlinarith
      have hψ_nonneg_x : ψ x ≥ 0 := hψ_nonneg x
      nlinarith

  have hy_cont_sq : ContinuousWithinAt (fun t : ℝ => (y t)^2) (Set.Ici 0) 0 :=
    hy_cont.pow 2

  have h_id_cont : ContinuousWithinAt (fun t : ℝ => 1 + 2*t) (Set.Ici 0) 0 := by
    refine ContinuousWithinAt.add ?_ ?_
    · exact (continuousAt_const (x := (0 : ℝ))).continuousWithinAt
    · refine ((continuousAt_id.const_mul (2 : ℝ)).continuousWithinAt :
        ContinuousWithinAt (fun t : ℝ => 2*t) (Set.Ici 0) 0)

  have hφ_cont : ContinuousWithinAt φ (Set.Ici 0) 0 := by
    dsimp [φ]
    refine ContinuousWithinAt.sub (h_id_cont.mul hy_cont_sq) ?_
    exact (continuousAt_const (x := (0 : ℝ))).continuousWithinAt

  have hψ_cont_at_zero : ContinuousWithinAt ψ (Set.Ici 0) 0 :=
    hφ_cont.pow 2

  have h_subset : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx; exact Set.mem_Ici.mpr (le_of_lt hx)

  have hlim : Tendsto ψ (𝓝[Ioi 0] 0) (𝓝 0) := by
    have := hψ_cont_at_zero.tendsto.mono_left (nhdsWithin_mono 0 h_subset)
    simpa [hψ0] using this

  have hψ_eq_zero : ∀ t ≥ 0, ψ t = 0 := by
    intro t ht
    rcases ht.lt_or_eq with (hpos | hzero)
    · by_contra! hpos_psi
      have hψ_nonneg_t : ψ t ≥ 0 := hψ_nonneg t
      have hψ_pos : ψ t > 0 := by
        by_contra! hle
        have : ψ t = 0 := by nlinarith
        exact hpos_psi this
      have hball : Set.Ioo (-(ψ t / 2)) (ψ t / 2) ∈ 𝓝 (0 : ℝ) := by
        apply isOpen_Ioo.mem_nhds
        constructor <;> nlinarith
      have hpre : ψ ⁻¹' (Set.Ioo (-(ψ t / 2)) (ψ t / 2)) ∈ 𝓝[Ioi 0] 0 := hlim hball
      rcases mem_nhdsGT_iff_exists_Ioc_subset.mp hpre with ⟨δ, hδ_pos, hsub⟩
      set ε := min (δ/2) (t/2) with hε_def
      have hδ_pos' : δ > 0 := Set.mem_Ioi.mp hδ_pos
      have hε_pos : 0 < ε := by
        refine lt_min_iff.mpr ⟨by nlinarith, by nlinarith⟩
      have hε_le_δ : ε ≤ δ := by
        have : ε ≤ δ/2 := min_le_left _ _
        nlinarith
      have hε_mem : ε ∈ Set.Ioc (0 : ℝ) δ := ⟨hε_pos, hε_le_δ⟩
      have hψ_ε : ψ ε ∈ Set.Ioo (-(ψ t / 2)) (ψ t / 2) :=
        hsub hε_mem
      have hψ_ε_lt : ψ ε < ψ t / 2 := hψ_ε.2
      have hε_lt_t : ε < t := by
        have : ε ≤ t/2 := min_le_right _ _
        nlinarith
      have h_compare : ψ t ≤ ψ ε :=
        hψ_antitoneOn (Set.mem_Ioi.mpr hε_pos) (Set.mem_Ioi.mpr hpos) (by nlinarith)
      nlinarith
    · subst hzero; exact hψ0

  have h_identity : ∀ t ≥ 0, (1 + 2*t)*(y t)^2 = 1 := by
    intro t ht
    have hψ_t : ψ t = 0 := hψ_eq_zero t ht
    dsimp [ψ, φ] at hψ_t
    have hzero_sq : ((1 + 2*t)*(y t)^2 - 1)^2 = 0 := hψ_t
    have hzero : (1 + 2*t)*(y t)^2 - 1 = 0 := by
      nlinarith
    nlinarith

  have hy_sq_pos : ∀ t ≥ 0, (y t)^2 > 0 := by
    intro t ht
    have h_eq : (1 + 2*t)*(y t)^2 = 1 := h_identity t ht
    have h_pos : 0 < 1 + 2*t := by nlinarith
    nlinarith

  have hy_nonzero : ∀ t ≥ 0, y t ≠ 0 := by
    intro t ht
    have h_sq_pos : (y t)^2 > 0 := hy_sq_pos t ht
    nlinarith

  have hy_cont_on : ∀ t : ℝ, ContinuousOn y (Set.Icc 0 t) := by
    intro t x hx
    rcases hx.1.lt_or_eq with (hpos | hzero)
    · exact (hy_diff x hpos).continuousAt.continuousWithinAt
    · subst hzero
      have hsubset : Set.Icc (0 : ℝ) t ⊆ Set.Ici (0 : ℝ) := by
        intro x hx; exact hx.1
      exact hy_cont.mono hsubset

  have hy_pos : ∀ t ≥ 0, y t > 0 := by
    intro t ht
    by_contra! h
    have h_neg : y t < 0 := by
      by_contra! hge
      have : y t = 0 := by nlinarith
      exact hy_nonzero t ht this
    have h_cont_on : ContinuousOn y (Set.Icc 0 t) := hy_cont_on t
    have hsubset : Set.Icc (y t) (y 0) ⊆ y '' (Set.Icc 0 t) :=
      intermediate_value_Icc' (by nlinarith) h_cont_on
    have hzero_in_interval : (0 : ℝ) ∈ Set.Icc (y t) (y 0) := by
      rw [hy0]
      constructor <;> nlinarith
    have h_ivt : (0 : ℝ) ∈ y '' (Set.Icc 0 t) := hsubset hzero_in_interval
    rcases h_ivt with ⟨c, hc, hc_val⟩
    have hc_sq_pos : (y c)^2 > 0 := hy_sq_pos c hc.1
    rw [hc_val] at hc_sq_pos
    norm_num at hc_sq_pos

  have h_sq_tendsto : Tendsto (fun t : ℝ => t*(y t)^2) atTop (𝓝 (1/2 : ℝ)) := by
    have h_expr : ∀ t ≥ 0, t*(y t)^2 = t/(1 + 2*t) := by
      intro t ht
      have h_eq : (1 + 2*t)*(y t)^2 = 1 := h_identity t ht
      have h_nonzero : 1 + 2*t ≠ 0 := by nlinarith
      field_simp [h_nonzero]
      nlinarith

    have h_mem_atTop : Set.Ioi (0 : ℝ) ∈ (atTop : Filter ℝ) := by
      refine mem_atTop_sets.mpr ?_
      refine ⟨1, fun x hx => ?_⟩
      exact Set.mem_Ioi.mpr (by linarith)

    have h_eventually : (fun t : ℝ => t/(1 + 2*t)) =ᶠ[atTop] (fun t : ℝ => t*(y t)^2) := by
      filter_upwards [h_mem_atTop] with t ht
      have ht_nonneg : 0 ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
      symm; exact h_expr t ht_nonneg

    have h_limit : Tendsto (fun t : ℝ => t/(1 + 2*t)) atTop (𝓝 (1/2 : ℝ)) := by
      have h_sub_tendsto : Tendsto (fun t : ℝ => t/(1 + 2*t) - (1/2 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
        have h_denom : Tendsto (fun t : ℝ => 1 + 2*t) atTop atTop := by
          have h : Tendsto (fun t : ℝ => 2*t) atTop atTop := by
            simpa [mul_comm] using (tendsto_id (x := atTop)).atTop_mul_const (by norm_num : (0 : ℝ) < 2)
          have h' : Tendsto (fun t : ℝ => (2*t) + 1) atTop atTop :=
            tendsto_atTop_add_const_right atTop 1 h
          simpa [add_comm] using h'
        have h_inv : Tendsto (fun t : ℝ => 1/(1 + 2*t)) atTop (𝓝 0) := by
          have := tendsto_inv_atTop_zero.comp h_denom
          convert this using 1
          ext t; simp
        have h_main_tendsto : Tendsto (fun t : ℝ => (-1/2) * (1/(1 + 2*t))) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul h_inv)
        have h_eq : (fun t : ℝ => t/(1 + 2*t) - (1/2 : ℝ)) =ᶠ[atTop] (fun t : ℝ => (-1/2) * (1/(1 + 2*t))) := by
          filter_upwards [h_mem_atTop] with t ht
          have ht_pos : t > 0 := Set.mem_Ioi.mp ht
          have ht' : t ≠ -1/2 := by
            intro h; nlinarith
          field_simp [ht']
          ring
        exact h_main_tendsto.congr' h_eq.symm
      have := h_sub_tendsto.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1/2 : ℝ)) atTop (𝓝 (1/2 : ℝ)))
      simpa [sub_add_cancel] using this

    exact h_limit.congr' h_eventually

  have h_sqrt_tendsto : Tendsto (fun t : ℝ => Real.sqrt (t*(y t)^2)) atTop (𝓝 (Real.sqrt (1/2 : ℝ))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp h_sq_tendsto

  have h_sqrt_simp : Real.sqrt (1/2 : ℝ) = 1 / Real.sqrt 2 := by
    calc
      Real.sqrt (1/2 : ℝ) = Real.sqrt 1 / Real.sqrt 2 := by
        simpa using Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) 2
      _ = 1 / Real.sqrt 2 := by norm_num

  have h_main : ∀ t ≥ 0, y t * Real.sqrt t = Real.sqrt (t*(y t)^2) := by
    intro t ht
    have hy_t_pos : y t ≥ 0 := by linarith [hy_pos t ht]
    calc
      y t * Real.sqrt t = Real.sqrt ((y t)^2) * Real.sqrt t := by
        rw [Real.sqrt_sq hy_t_pos]
      _ = Real.sqrt ((y t)^2 * t) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ (y t)^2)]
      _ = Real.sqrt (t*(y t)^2) := by ring

  have h_mem_atTop' : Set.Ioi (0 : ℝ) ∈ (atTop : Filter ℝ) := by
    refine mem_atTop_sets.mpr ?_
    refine ⟨1, fun x hx => ?_⟩
    exact Set.mem_Ioi.mpr (by linarith)

  have h_eventually_main : (fun t : ℝ => Real.sqrt (t*(y t)^2)) =ᶠ[atTop] (fun t : ℝ => y t * Real.sqrt t) := by
    filter_upwards [h_mem_atTop'] with t ht
    have ht_nonneg : 0 ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    symm; exact h_main t ht_nonneg

  simpa [h_sqrt_simp] using (h_sqrt_tendsto.congr' h_eventually_main)

end Submission
