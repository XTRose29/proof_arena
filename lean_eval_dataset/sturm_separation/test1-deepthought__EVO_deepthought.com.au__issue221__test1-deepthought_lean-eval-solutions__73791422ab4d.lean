import Mathlib
open Set
open Filter

lemma exists_bound_on_abs (p : ℝ → ℝ) (a' b' : ℝ) (hle : a' ≤ b') (hp : ContinuousOn p (Set.Icc a' b')) :
    ∃ (K : NNReal), ∀ t ∈ Set.Icc a' b', |p t| ≤ (K : ℝ) := by
  have h_nonempty : (Set.Icc a' b').Nonempty := Set.nonempty_Icc.mpr hle
  have h_cont_abs : ContinuousOn (fun x : ℝ => |p x|) (Set.Icc a' b') := hp.abs
  rcases IsCompact.exists_isMaxOn isCompact_Icc h_nonempty h_cont_abs with ⟨t0, ht0, h_max⟩
  refine ⟨⟨|p t0|, abs_nonneg _⟩, ?_⟩
  intro t ht
  simpa using h_max ht

lemma LipschitzOnWith.mono_const {α β : Type _} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K₁ K₂ : NNReal} {f : α → β} {s : Set α} (hf : LipschitzOnWith K₁ f s) (h : K₁ ≤ K₂) :
    LipschitzOnWith K₂ f s := by
  intro x hx y hy
  have h_edist := hf hx hy
  have hK : (K₁ : ENNReal) ≤ (K₂ : ENNReal) := by exact_mod_cast h
  calc
    edist (f x) (f y) ≤ (K₁ : ENNReal) * edist x y := h_edist
    _ ≤ (K₂ : ENNReal) * edist x y := mul_le_mul_of_nonneg_right hK (by positivity)

lemma linear_ode_zero_at_point (a f : ℝ → ℝ) (c d : ℝ) (hcd : c < d) (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Set.Ioo c d) (ht₂ : t₂ ∈ Set.Ioo c d)
    (ha_cont : ContinuousOn a (Set.Icc c d))
    (hf : ∀ t ∈ Set.Ioo c d, HasDerivAt f (a t * f t) t)
    (hf_t₂ : f t₂ = 0) : f t₁ = 0 := by
  rcases exists_bound_on_abs a c d (by linarith) ha_cont with ⟨K, hK⟩
  set v : ℝ → ℝ → ℝ := fun t' y => a t' * y with hv_def
  set s : ℝ → Set ℝ := fun _ => Set.univ with hs_def
  have hv_lip : ∀ t' ∈ Set.Ioo c d, LipschitzOnWith K (v t') (s t') := by
    intro t' ht'
    have ht'_icc : t' ∈ Set.Icc c d := Set.mem_Icc.mpr ⟨by
      have := ht'.1; linarith, by
      have := ht'.2; linarith⟩
    have h_bound : |a t'| ≤ (K : ℝ) := hK t' ht'_icc
    have h_smul : LipschitzWith (‖a t'‖₊) (fun (y : ℝ) => (a t') • y) := lipschitzWith_smul (a t')
    have h_smul' : LipschitzWith (⟨|a t'|, abs_nonneg _⟩ : NNReal) (fun (y : ℝ) => a t' * y) := by
      simpa using h_smul
    have h_lip : LipschitzOnWith (⟨|a t'|, abs_nonneg _⟩ : NNReal) (fun (y : ℝ) => a t' * y) Set.univ :=
      h_smul'.lipschitzOnWith
    have hK_le : (⟨|a t'|, abs_nonneg _⟩ : NNReal) ≤ K := by exact_mod_cast h_bound
    have h_lip' : LipschitzOnWith K (fun (y : ℝ) => a t' * y) Set.univ := h_lip.mono_const hK_le
    dsimp [v, s]
    exact h_lip'
  have hf' : ∀ t ∈ Set.Ioo c d, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    intro t ht; refine ⟨hf t ht, trivial⟩
  have hzero : ∀ t ∈ Set.Ioo c d, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (v t ((fun _ : ℝ => (0 : ℝ)) t)) t ∧ (fun _ : ℝ => (0 : ℝ)) t ∈ s t := by
    intro t ht
    refine ⟨by
      have h_deriv : HasDerivAt (fun (_ : ℝ) => (0 : ℝ)) (0 : ℝ) t := hasDerivAt_const _ _
      simpa [hv_def, hs_def] using h_deriv, trivial⟩
  have h_unique : EqOn f (fun _ : ℝ => (0 : ℝ)) (Set.Ioo c d) :=
    ODE_solution_unique_of_mem_Ioo hv_lip ht₂ hf' hzero hf_t₂
  exact h_unique ht₁

lemma exists_open_interval_containing_two_points (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (x y : ℝ) (hx : x ∈ J) (hy : y ∈ J) (hxy : x ≠ y) :
    ∃ (c d : ℝ), c < d ∧ Set.Icc c d ⊆ J ∧ x ∈ Set.Ioo c d ∧ y ∈ Set.Ioo c d := by
  have hx_nh : ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ⊆ J := by
    have h := hJ_open.mem_nhds hx
    rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro z hz; rcases hz with ⟨hz1, hz2⟩; apply hball
    rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith
  have hy_nh : ∃ ε > 0, Set.Ioo (y - ε) (y + ε) ⊆ J := by
    have h := hJ_open.mem_nhds hy
    rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro z hz; rcases hz with ⟨hz1, hz2⟩; apply hball
    rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith
  rcases hx_nh with ⟨ε₀, hε₀, hx_ball⟩; rcases hy_nh with ⟨ε₁, hε₁, hy_ball⟩
  let δ := min ε₀ ε₁; have hδ_pos : δ > 0 := lt_min_iff.mpr ⟨hε₀, hε₁⟩
  have hδ_le_ε₀ : δ ≤ ε₀ := min_le_left _ _; have hδ_le_ε₁ : δ ≤ ε₁ := min_le_right _ _
  have hJ_ord : J.OrdConnected := isPreconnected_iff_ordConnected.mp hJ_conn
  let c' := min x y - δ; let d' := max x y + δ; let c := min x y - δ / 2; let d := max x y + δ / 2
  have h_min_lt_max : min x y < max x y := by
    by_cases hx_le_y : x ≤ y
    · rw [min_eq_left hx_le_y, max_eq_right hx_le_y]; by_contra! hle; exact hxy (by linarith)
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; by_contra! hle; exact hxy (by linarith)
  have hcd : c < d := by dsimp [c, d]; nlinarith
  have hIoo_c'd'_sub_J : Set.Ioo c' d' ⊆ J := by
    intro z hz; rcases hz with ⟨hcz, hzd⟩; dsimp [c', d'] at hcz hzd
    by_cases hz_ge_min : min x y ≤ z
    · by_cases hz_le_max : z ≤ max x y
      · have hz_icc : z ∈ Set.Icc (min x y) (max x y) := Set.mem_Icc.mpr ⟨hz_ge_min, hz_le_max⟩
        have hIcc_sub_J' : Set.Icc (min x y) (max x y) ⊆ J := by
          by_cases hxy' : x ≤ y
          · rw [min_eq_left hxy', max_eq_right hxy']; exact hJ_ord.out hx hy
          · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; exact hJ_ord.out hy hx
        exact hIcc_sub_J' hz_icc
      · by_cases hx_max : x ≤ y
        · rw [max_eq_right hx_max] at hzd hz_le_max
          have hz_gt_y : y < z := by
            by_contra! hle; exact hz_le_max hle
          exact hy_ball ⟨by nlinarith, by nlinarith⟩
        · rw [max_eq_left (by linarith)] at hzd hz_le_max
          have hz_gt_x : x < z := by
            by_contra! hle; exact hz_le_max hle
          exact hx_ball ⟨by nlinarith, by nlinarith⟩
    · by_cases hx_min : x ≤ y
      · rw [min_eq_left hx_min] at hcz hz_ge_min
        have hz_lt_x : z < x := by
          by_contra! hge; exact hz_ge_min hge
        exact hx_ball ⟨by nlinarith, by nlinarith⟩
      · rw [min_eq_right (by linarith)] at hcz hz_ge_min
        have hz_lt_y : z < y := by
          by_contra! hge; exact hz_ge_min hge
        exact hy_ball ⟨by nlinarith, by nlinarith⟩
  have hIcc_sub_J : Set.Icc c d ⊆ J := by
    intro z hz; rcases hz with ⟨hcz, hzd⟩; dsimp [c, d] at hcz hzd
    have hcz' : c' < z := by dsimp [c']; nlinarith
    have hzd' : z < d' := by dsimp [d']; nlinarith
    exact hIoo_c'd'_sub_J ⟨hcz', hzd'⟩
  have hx_mem : x ∈ Set.Ioo c d := by
    dsimp [c, d]; have hx_low : min x y - δ / 2 < x := by
      have : min x y ≤ x := min_le_left _ _; nlinarith
    have hx_high : x < max x y + δ / 2 := by
      have : x ≤ max x y := le_max_left _ _; nlinarith
    exact ⟨hx_low, hx_high⟩
  have hy_mem : y ∈ Set.Ioo c d := by
    dsimp [c, d]; have hy_low : min x y - δ / 2 < y := by
      have : min x y ≤ y := min_le_right _ _; nlinarith
    have hy_high : y < max x y + δ / 2 := by
      have : y ≤ max x y := le_max_right _ _; nlinarith
    exact ⟨hy_low, hy_high⟩
  exact ⟨c, d, hcd, hIcc_sub_J, hx_mem, hy_mem⟩

lemma deriv_nonneg_at_right (f : ℝ → ℝ) (a : ℝ) (hf : HasDerivAt f (deriv f a) a) (hfa : f a = 0)
    (hpos : ∀ᶠ x in nhdsWithin a (Set.Ioi a), f x > 0) : deriv f a ≥ 0 := by
  have h_slope_nonneg : ∀ᶠ x in nhdsWithin a (Set.Ioi a), 0 ≤ slope f a x := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hxpos hxmem
    dsimp [slope]; rw [hfa, sub_zero]
    have hxpos' : x > a := hxmem
    have : 0 ≤ f x / (x - a) := div_nonneg (by linarith) (by linarith)
    simpa [div_eq_inv_mul] using this
  have h_nhdsWithin_sub : nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {x | x ≠ a} :=
    nhdsWithin_mono _ (by intro x hx; exact Set.mem_setOf.mpr (ne_of_gt hx))
  have h_slope_tendsto : Tendsto (slope f a) (nhdsWithin a (Set.Ioi a)) (nhds (deriv f a)) :=
    hf.tendsto_slope.mono_left h_nhdsWithin_sub
  exact ge_of_tendsto h_slope_tendsto h_slope_nonneg

lemma deriv_nonpos_at_left (f : ℝ → ℝ) (b : ℝ) (hf : HasDerivAt f (deriv f b) b) (hfb : f b = 0)
    (hpos : ∀ᶠ x in nhdsWithin b (Set.Iio b), f x > 0) : deriv f b ≤ 0 := by
  have h_slope_nonpos : ∀ᶠ x in nhdsWithin b (Set.Iio b), slope f b x ≤ 0 := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hxpos hxmem
    dsimp [slope]; rw [hfb, sub_zero]
    have hxpos' : x < b := hxmem
    have : f x / (x - b) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    simpa [div_eq_inv_mul] using this
  have h_nhdsWithin_sub : nhdsWithin b (Set.Iio b) ≤ nhdsWithin b {x | x ≠ b} :=
    nhdsWithin_mono _ (by intro x hx; exact Set.mem_setOf.mpr (ne_of_lt hx))
  have h_slope_tendsto : Tendsto (slope f b) (nhdsWithin b (Set.Iio b)) (nhds (deriv f b)) :=
    hf.tendsto_slope.mono_left h_nhdsWithin_sub
  exact le_of_tendsto h_slope_tendsto h_slope_nonpos

lemma Ioo_mem_nhdsWithin_Ioi (a b : ℝ) (hab : a < b) : Set.Ioo a b ∈ nhdsWithin a (Set.Ioi a) := by
  rw [Metric.mem_nhdsWithin_iff]; refine ⟨b - a, by linarith, ?_⟩
  intro x hx; rcases hx with ⟨hx1, hx2⟩; rw [Metric.mem_ball, Real.dist_eq] at hx1
  rcases abs_lt.mp hx1 with ⟨hx_low, hx_high⟩; have hx_lt_b : x < b := by nlinarith
  exact ⟨hx2, hx_lt_b⟩

lemma Ioo_mem_nhdsWithin_Iio (a b : ℝ) (hab : a < b) : Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := by
  rw [Metric.mem_nhdsWithin_iff]; refine ⟨b - a, by linarith, ?_⟩
  intro x hx; rcases hx with ⟨hx1, hx2⟩; rw [Metric.mem_ball, Real.dist_eq] at hx1
  rcases abs_lt.mp hx1 with ⟨hx_low, hx_high⟩; have hx_gt_a : a < x := by nlinarith
  exact ⟨hx_gt_a, hx2⟩

lemma strictMonoOn_of_deriv_pos_on_Ioo (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo a b, 0 < f' x) :
    StrictMonoOn f (Ioo a b) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo a b) (f' := f')
  · intro x hx; exact (hf x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by
      simpa [interior_Ioo] using hx
    exact (hf x hx').hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by
      simpa [interior_Ioo] using hx
    exact hf' x hx'

lemma strictAntiOn_of_deriv_neg_on_Ioo (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo a b, f' x < 0) :
    StrictAntiOn f (Ioo a b) := by
  have h_neg_pos : ∀ x ∈ Ioo a b, 0 < -f' x := by intro x hx; linarith [hf' x hx]
  have h_strict_mono_neg : StrictMonoOn (-f) (Ioo a b) :=
    strictMonoOn_of_deriv_pos_on_Ioo (-f) (-f') a b hab (fun x hx => (hf x hx).neg) h_neg_pos
  intro x hx y hy hlt; have hneg : (-f) x < (-f) y := h_strict_mono_neg hx hy hlt
  have : -(f x) < -(f y) := hneg; linarith

lemma const_sign_on_Ioo (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : ∀ x ∈ Ioo a b, ContinuousAt f x)
    (hf_nonzero : ∀ x ∈ Ioo a b, f x ≠ 0) : (∀ x ∈ Ioo a b, f x > 0) ∨ (∀ x ∈ Ioo a b, f x < 0) := by
  by_cases hpos : ∃ x ∈ Ioo a b, f x > 0
  · rcases hpos with ⟨x₀, hx₀, hpos⟩
    refine Or.inl ?_
    intro x hx
    by_cases hxpos : f x > 0; · exact hxpos
    have hx_neg : f x < 0 := by
      by_contra! hge
      have : f x = 0 := by nlinarith
      exact hf_nonzero x hx this
    by_cases hxx₀ : x ≤ x₀
    · -- x ≤ x₀; apply IVT on [x, x₀]
      have h_cont : ContinuousOn f (Icc x x₀) := by
        intro z hz
        have hz_Ioo : z ∈ Ioo a b := by
          have hz1 : x ≤ z := hz.1
          have hz2 : z ≤ x₀ := hz.2
          have hx_z : a < z := lt_of_lt_of_le hx.1 hz1
          have hz_x₀ : z < b := lt_of_le_of_lt hz2 hx₀.2
          exact ⟨hx_z, hz_x₀⟩
        exact (hf z hz_Ioo).continuousWithinAt
      have h0_mem : (0 : ℝ) ∈ Ioo (f x) (f x₀) := ⟨hx_neg, hpos⟩
      have h_ivt : Ioo (f x) (f x₀) ⊆ f '' Ioo x x₀ :=
        intermediate_value_Ioo hxx₀ h_cont
      have h0_mem' : (0 : ℝ) ∈ f '' Ioo x x₀ := h_ivt h0_mem
      have htemp : ∃ z : ℝ, z ∈ Ioo x x₀ ∧ f z = 0 := by
        simpa [Set.mem_image] using h0_mem'
      rcases htemp with ⟨z, hz_and, hz_eq⟩
      rcases hz_and with ⟨hz1, hz2⟩
      have hz_Ioo : z ∈ Ioo a b := ⟨hx.1.trans hz1, hz2.trans hx₀.2⟩
      exact absurd hz_eq (hf_nonzero z hz_Ioo)
    · -- x₀ ≤ x; apply IVT on [x₀, x]
      have hx₀_le_x : x₀ ≤ x := by linarith
      have h_cont : ContinuousOn f (Icc x₀ x) := by
        intro z hz
        have hz_Ioo : z ∈ Ioo a b := by
          have hz1 : x₀ ≤ z := hz.1
          have hz2 : z ≤ x := hz.2
          have hx₀_z : a < z := lt_of_lt_of_le hx₀.1 hz1
          have hz_x : z < b := lt_of_le_of_lt hz2 hx.2
          exact ⟨hx₀_z, hz_x⟩
        exact (hf z hz_Ioo).continuousWithinAt
      have h0_mem : (0 : ℝ) ∈ Ioo (f x) (f x₀) := ⟨hx_neg, hpos⟩
      have h_ivt : Ioo (f x) (f x₀) ⊆ f '' Ioo x₀ x :=
        intermediate_value_Ioo' hx₀_le_x h_cont
      have h0_mem' : (0 : ℝ) ∈ f '' Ioo x₀ x := h_ivt h0_mem
      have htemp : ∃ z : ℝ, z ∈ Ioo x₀ x ∧ f z = 0 := by
        simpa [Set.mem_image] using h0_mem'
      rcases htemp with ⟨z, hz_and, hz_eq⟩
      rcases hz_and with ⟨hz1, hz2⟩
      have hz_Ioo : z ∈ Ioo a b := ⟨hx₀.1.trans hz1, hz2.trans hx.2⟩
      exact absurd hz_eq (hf_nonzero z hz_Ioo)
  · push_neg at hpos
    refine Or.inr ?_
    intro x hx
    have hx_nonzero : f x ≠ 0 := hf_nonzero x hx
    have hxle : f x ≤ 0 := hpos x hx
    by_contra! hge
    have : f x = 0 := by nlinarith
    exact hx_nonzero this

lemma pos_at_endpoint_of_pos_on_Ioo (y : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hy_diff : HasDerivAt y (deriv y a) a)
    (hy_pos : ∀ x ∈ Ioo a b, y x > 0) (hy_nonzero : y a ≠ 0) : y a > 0 := by
  have hcont : ContinuousAt y a := hy_diff.continuousAt
  have hpos_right : ∀ᶠ x in nhdsWithin a (Set.Ioi a), y x > 0 := by
    have hmid : a < (a+b)/2 := by nlinarith
    have h_nhd : Ioo a ((a+b)/2) ∈ nhdsWithin a (Set.Ioi a) :=
      Ioo_mem_nhdsWithin_Ioi a ((a+b)/2) hmid
    filter_upwards [h_nhd] with x hx
    have hx_lt_b : x < b := by
      have hx_lt_mid : x < (a+b)/2 := hx.2
      nlinarith
    exact hy_pos x ⟨hx.1, hx_lt_b⟩
  have hy_nonneg : 0 ≤ y a := by
    have hlim : Tendsto y (nhdsWithin a (Set.Ioi a)) (nhds (y a)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hpos_nonneg : ∀ᶠ x in nhdsWithin a (Set.Ioi a), (0 : ℝ) ≤ y x := by
      filter_upwards [hpos_right] with x hx; linarith
    exact ge_of_tendsto hlim hpos_nonneg
  by_contra! hle
  have hy_eq_zero : y a = 0 := by nlinarith
  exact hy_nonzero hy_eq_zero

lemma pos_at_endpoint_of_pos_on_Ioo_right (y : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hy_diff : HasDerivAt y (deriv y b) b)
    (hy_pos : ∀ x ∈ Ioo a b, y x > 0) (hy_nonzero : y b ≠ 0) : y b > 0 := by
  have hcont : ContinuousAt y b := hy_diff.continuousAt
  have hpos_left : ∀ᶠ x in nhdsWithin b (Set.Iio b), y x > 0 := by
    have hmid : (a+b)/2 < b := by nlinarith
    have h_nhd : Ioo ((a+b)/2) b ∈ nhdsWithin b (Set.Iio b) :=
      Ioo_mem_nhdsWithin_Iio ((a+b)/2) b hmid
    filter_upwards [h_nhd] with x hx
    have hx_gt_a : a < x := by
      have hx_gt_mid : (a+b)/2 < x := hx.1
      nlinarith
    exact hy_pos x ⟨hx_gt_a, hx.2⟩
  have hy_nonneg : 0 ≤ y b := by
    have hlim : Tendsto y (nhdsWithin b (Set.Iio b)) (nhds (y b)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hpos_nonneg : ∀ᶠ x in nhdsWithin b (Set.Iio b), (0 : ℝ) ≤ y x := by
      filter_upwards [hpos_left] with x hx; linarith
    exact ge_of_tendsto hlim hpos_nonneg
  by_contra! hle
  have hy_eq_zero : y b = 0 := by nlinarith
  exact hy_nonzero hy_eq_zero

lemma neg_at_endpoint_of_neg_on_Ioo (y : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hy_diff : HasDerivAt y (deriv y a) a)
    (hy_neg : ∀ x ∈ Ioo a b, y x < 0) (hy_nonzero : y a ≠ 0) : y a < 0 := by
  have hpos : (-y) a > 0 := by
    apply pos_at_endpoint_of_pos_on_Ioo (-y) a b hab (by
      simpa [deriv.neg] using hy_diff.neg)
    · intro x hx; simpa using hy_neg x hx
    · intro h; apply hy_nonzero; simpa using h
  have : -(y a) > 0 := by simpa using hpos
  linarith

lemma neg_at_endpoint_of_neg_on_Ioo_right (y : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hy_diff : HasDerivAt y (deriv y b) b)
    (hy_neg : ∀ x ∈ Ioo a b, y x < 0) (hy_nonzero : y b ≠ 0) : y b < 0 := by
  have hpos : (-y) b > 0 := by
    apply pos_at_endpoint_of_pos_on_Ioo_right (-y) a b hab (by
      simpa [deriv.neg] using hy_diff.neg)
    · intro x hx; simpa using hy_neg x hx
    · intro h; apply hy_nonzero; simpa using h
  have : -(y b) > 0 := by simpa using hpos
  linarith

set_option maxHeartbeats 600000

namespace Submission

theorem sturm_separation_pos (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)
    (hy₁_pos : ∀ x ∈ Ioo a b, y₁ x > 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  rcases hW with ⟨x₀, hx₀J, hW₀⟩
  set W : ℝ → ℝ := fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x with hWdef
  have haJ : a ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.left_mem_Icc.mpr (by linarith))
  have hbJ : b ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.right_mem_Icc.mpr (by linarith))
  have hJ_ord : J.OrdConnected := isPreconnected_iff_ordConnected.mp hJ_conn
  have hW_deriv : ∀ x ∈ J, HasDerivAt W (-(p x) * W x) x := by
    intro x hxJ
    dsimp [W]
    have hy₁_x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hxJ
    have hy₁'_x : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x := hy₁' x hxJ
    have hy₂_x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x hxJ
    have hy₂'_x : HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x := hy₂' x hxJ
    have h1 : HasDerivAt (fun x : ℝ => y₁ x * deriv y₂ x) (deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) x :=
      HasDerivAt.mul hy₁_x hy₂'_x
    have h2 : HasDerivAt (fun x : ℝ => y₂ x * deriv y₁ x) (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) x :=
      HasDerivAt.mul hy₂_x hy₁'_x
    have hsub : HasDerivAt (fun x : ℝ => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x)
      ((deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) - (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x :=
      HasDerivAt.sub h1 h2
    have hsimpl : ((deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) - (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) = -(p x) * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) := by ring
    rw [hsimpl] at hsub; exact hsub
  have hW_nonzero : ∀ x ∈ J, W x ≠ 0 := by
    intro x hxJ
    by_contra! hWx
    by_cases hxx₀ : x = x₀
    · subst hxx₀; exact hW₀ hWx
    · rcases exists_open_interval_containing_two_points J hJ_open hJ_conn x x₀ hxJ hx₀J hxx₀ with ⟨c, d, hcd, hIcc_sub, hx_mem, hx₀_mem⟩
      have hp_cont : ContinuousOn (-p) (Icc c d) := (hp.mono hIcc_sub).neg
      have hW_deriv_on : ∀ t ∈ Ioo c d, HasDerivAt W (-(p t) * W t) t := by
        intro t ht; have htJ : t ∈ J := hIcc_sub (Set.Ioo_subset_Icc_self ht); exact hW_deriv t htJ
      have hWx₀ : W x₀ = 0 :=
        linear_ode_zero_at_point (-p) W c d hcd x₀ x hx₀_mem hx_mem hp_cont hW_deriv_on hWx
      exact hW₀ hWx₀
  have hWa_nonzero : W a ≠ 0 := hW_nonzero a haJ
  have hWb_nonzero : W b ≠ 0 := hW_nonzero b hbJ
  have hy₁_cont : ∀ x ∈ Ioo a b, ContinuousAt y₁ x := by
    intro x hx; have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx); exact (hy₁ x hxJ).continuousAt
  have hy₂_cont : ∀ x ∈ Ioo a b, ContinuousAt y₂ x := by
    intro x hx; have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx); exact (hy₂ x hxJ).continuousAt
  have hy₁_deriv_a_pos : deriv y₁ a > 0 := by
    have h_nonneg : 0 ≤ deriv y₁ a := by
      have hpos : ∀ᶠ x in nhdsWithin a (Set.Ioi a), y₁ x > 0 := by
        have ha_min : a < min b (a+1) := lt_min_iff.mpr ⟨hab, by nlinarith⟩
        have h_nhd : Ioo a (min b (a+1)) ∈ nhdsWithin a (Set.Ioi a) :=
          Ioo_mem_nhdsWithin_Ioi a (min b (a+1)) ha_min
        filter_upwards [h_nhd] with x hx
        rcases hx with ⟨hxa, hxmin⟩
        have hx_Ioo : x ∈ Ioo a b := ⟨hxa, by
          calc
            x < min b (a+1) := hxmin
            _ ≤ b := min_le_left _ _⟩
        exact hy₁_pos x hx_Ioo
      have h_deriv : HasDerivAt y₁ (deriv y₁ a) a := hy₁ a haJ
      exact deriv_nonneg_at_right y₁ a h_deriv hza hpos
    have h_nonzero : deriv y₁ a ≠ 0 := by
      intro hzero; apply hWa_nonzero
      dsimp [W]
      calc
        y₁ a * deriv y₂ a - y₂ a * deriv y₁ a = 0 * deriv y₂ a - y₂ a * deriv y₁ a := by rw [hza]
        _ = -(y₂ a) * deriv y₁ a := by ring
        _ = -(y₂ a) * 0 := by rw [hzero]
        _ = 0 := by ring
    exact lt_of_le_of_ne h_nonneg h_nonzero.symm
  have hy₁_deriv_b_neg : deriv y₁ b < 0 := by
    have h_nonpos : deriv y₁ b ≤ 0 := by
      have hpos : ∀ᶠ x in nhdsWithin b (Set.Iio b), y₁ x > 0 := by
        have hb_max : max a (b-1) < b := max_lt_iff.mpr ⟨hab, by nlinarith⟩
        have h_nhd : Ioo (max a (b-1)) b ∈ nhdsWithin b (Set.Iio b) :=
          Ioo_mem_nhdsWithin_Iio (max a (b-1)) b hb_max
        filter_upwards [h_nhd] with x hx
        rcases hx with ⟨hxmax, hxb⟩
        have hx_Ioo : x ∈ Ioo a b := ⟨by
          have : max a (b-1) ≥ a := le_max_left _ _
          linarith, hxb⟩
        exact hy₁_pos x hx_Ioo
      have h_deriv : HasDerivAt y₁ (deriv y₁ b) b := hy₁ b hbJ
      exact deriv_nonpos_at_left y₁ b h_deriv hzb hpos
    have h_nonzero : deriv y₁ b ≠ 0 := by
      intro hzero; apply hWb_nonzero
      dsimp [W]
      calc
        y₁ b * deriv y₂ b - y₂ b * deriv y₁ b = 0 * deriv y₂ b - y₂ b * deriv y₁ b := by rw [hzb]
        _ = -(y₂ b) * deriv y₁ b := by ring
        _ = -(y₂ b) * 0 := by rw [hzero]
        _ = 0 := by ring
    exact lt_of_le_of_ne h_nonpos h_nonzero
  have hy₂a_nonzero : y₂ a ≠ 0 := by
    intro hy₂a; apply hWa_nonzero
    dsimp [W]
    calc
      y₁ a * deriv y₂ a - y₂ a * deriv y₁ a = 0 * deriv y₂ a - y₂ a * deriv y₁ a := by rw [hza]
      _ = -(y₂ a) * deriv y₁ a := by ring
      _ = 0 := by simp [hy₂a]
  have hy₂b_nonzero : y₂ b ≠ 0 := by
    intro hy₂b; apply hWb_nonzero
    dsimp [W]
    calc
      y₁ b * deriv y₂ b - y₂ b * deriv y₁ b = 0 * deriv y₂ b - y₂ b * deriv y₁ b := by rw [hzb]
      _ = -(y₂ b) * deriv y₁ b := by ring
      _ = 0 := by simp [hy₂b]
  have h_exists : ∃ c ∈ Ioo a b, y₂ c = 0 := by
    by_contra! h_no_zero
    have hy₂_const_sign : (∀ x ∈ Ioo a b, y₂ x > 0) ∨ (∀ x ∈ Ioo a b, y₂ x < 0) :=
      const_sign_on_Ioo y₂ a b hab hy₂_cont h_no_zero
    rcases hy₂_const_sign with (hy₂_pos | hy₂_neg)
    · -- y₂ > 0 on (a,b)
      have hWa_eq : W a = -(y₂ a) * deriv y₁ a := by
        dsimp [W]; rw [hza]; ring
      have hWb_eq : W b = -(y₂ b) * deriv y₁ b := by
        dsimp [W]; rw [hzb]; ring
      have hy₂a_pos : y₂ a > 0 :=
        pos_at_endpoint_of_pos_on_Ioo y₂ a b hab (hy₂ a haJ) hy₂_pos hy₂a_nonzero
      have hy₂b_pos : y₂ b > 0 :=
        pos_at_endpoint_of_pos_on_Ioo_right y₂ a b hab (hy₂ b hbJ) hy₂_pos hy₂b_nonzero
      have hW_a_neg : W a < 0 := by
        rw [hWa_eq]
        have : -(y₂ a) < 0 := by linarith
        have hpos_deriv : deriv y₁ a > 0 := hy₁_deriv_a_pos
        nlinarith
      have hW_b_pos : 0 < W b := by
        rw [hWb_eq]
        have : -(y₂ b) < 0 := by linarith
        have hneg_deriv : deriv y₁ b < 0 := hy₁_deriv_b_neg
        nlinarith
      have hW_cont : ContinuousOn W (Icc a b) := by
        intro x hx; have hxJ : x ∈ J := hJ_sub hx; exact (hW_deriv x hxJ).continuousAt.continuousWithinAt
      have hIVT : ∃ x ∈ Ioo a b, W x = 0 := by
        have h0_mem : (0 : ℝ) ∈ Ioo (W a) (W b) := ⟨hW_a_neg, hW_b_pos⟩
        have himage : Ioo (W a) (W b) ⊆ W '' (Ioo a b) :=
          intermediate_value_Ioo (by nlinarith) hW_cont
        rcases himage h0_mem with ⟨x, hx, hx_eq⟩
        exact ⟨x, hx, hx_eq⟩
      rcases hIVT with ⟨x, hx, hx_eq⟩
      have hxJ : x ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)
      exact hW_nonzero x hxJ hx_eq
    · -- y₂ < 0 on (a,b)
      have hWa_eq : W a = -(y₂ a) * deriv y₁ a := by
        dsimp [W]; rw [hza]; ring
      have hWb_eq : W b = -(y₂ b) * deriv y₁ b := by
        dsimp [W]; rw [hzb]; ring
      have hy₂a_neg : y₂ a < 0 :=
        neg_at_endpoint_of_neg_on_Ioo y₂ a b hab (hy₂ a haJ) hy₂_neg hy₂a_nonzero
      have hy₂b_neg : y₂ b < 0 :=
        neg_at_endpoint_of_neg_on_Ioo_right y₂ a b hab (hy₂ b hbJ) hy₂_neg hy₂b_nonzero
      have hW_a_pos : 0 < W a := by
        rw [hWa_eq]
        have : -(y₂ a) > 0 := by linarith
        have hpos_deriv : deriv y₁ a > 0 := hy₁_deriv_a_pos
        positivity
      have hW_b_neg : W b < 0 := by
        rw [hWb_eq]
        have : -(y₂ b) > 0 := by linarith
        have hneg_deriv : deriv y₁ b < 0 := hy₁_deriv_b_neg
        nlinarith
      have hW_cont : ContinuousOn W (Icc a b) := by
        intro x hx; have hxJ : x ∈ J := hJ_sub hx; exact (hW_deriv x hxJ).continuousAt.continuousWithinAt
      have hIVT : ∃ x ∈ Ioo a b, W x = 0 := by
        have h0_mem : (0 : ℝ) ∈ Ioo (W b) (W a) := ⟨hW_b_neg, hW_a_pos⟩
        have himage : Ioo (W b) (W a) ⊆ W '' (Ioo a b) :=
          intermediate_value_Ioo' (by nlinarith) hW_cont
        rcases himage h0_mem with ⟨x, hx, hx_eq⟩
        exact ⟨x, hx, hx_eq⟩
      rcases hIVT with ⟨x, hx, hx_eq⟩
      have hxJ : x ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)
      exact hW_nonzero x hxJ hx_eq
  have h_unique : ∀ c d, c ∈ Ioo a b → d ∈ Ioo a b → y₂ c = 0 → y₂ d = 0 → c = d := by
    intro c d hc hd hc0 hd0
    by_contra! hcd
    have hlt_or : c < d ∨ d < c := Ne.lt_or_gt hcd
    rcases hlt_or with (hlt | hlt)
    · -- c < d
      have h_deriv_ratio : ∀ x ∈ Ioo a b, HasDerivAt (fun x => y₂ x / y₁ x) (W x / (y₁ x)^2) x := by
        intro x hx
        have hy1x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x (hJ_sub (Set.Ioo_subset_Icc_self hx))
        have hy2x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x (hJ_sub (Set.Ioo_subset_Icc_self hx))
        have hy1x_ne : y₁ x ≠ 0 := hne x hx
        have hdiv : HasDerivAt (y₂ / y₁) ((deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / (y₁ x)^2) x :=
          HasDerivAt.div hy2x hy1x hy1x_ne
        have hnum : deriv y₂ x * y₁ x - y₂ x * deriv y₁ x = W x := by dsimp [W]; ring
        rw [hnum] at hdiv; exact hdiv
      have hW_nonzero_on_Ioo : ∀ x ∈ Ioo a b, W x ≠ 0 := by
        intro x hx; have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx); exact hW_nonzero x hxJ
      have hW_const_sign : (∀ x ∈ Ioo a b, W x > 0) ∨ (∀ x ∈ Ioo a b, W x < 0) :=
        const_sign_on_Ioo W a b hab (fun x hx => (hW_deriv x (hJ_sub (Set.Ioo_subset_Icc_self hx))).continuousAt) hW_nonzero_on_Ioo
      rcases hW_const_sign with (hW_pos | hW_neg)
      · -- W > 0
        have h_ratio_deriv_pos : ∀ x ∈ Ioo a b, 0 < W x / (y₁ x)^2 := by
          intro x hx; have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy₁_pos x hx) 2
          exact div_pos (hW_pos x hx) hy1_sq_pos
        have h_strict_mono : StrictMonoOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
          strictMonoOn_of_deriv_pos_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_pos
        have h_eq : (fun x => y₂ x / y₁ x) c = (fun x => y₂ x / y₁ x) d := by simp [hc0, hd0]
        have hc_eq_d : c = d := (h_strict_mono.eq_iff_eq hc hd).mp h_eq
        exact hcd hc_eq_d
      · -- W < 0
        have h_ratio_deriv_neg : ∀ x ∈ Ioo a b, W x / (y₁ x)^2 < 0 := by
          intro x hx
          have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy₁_pos x hx) 2
          have hW_neg_x : W x < 0 := hW_neg x hx
          exact (div_neg_iff.mpr (Or.inr ⟨hW_neg_x, hy1_sq_pos⟩))
        have h_strict_anti : StrictAntiOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
          strictAntiOn_of_deriv_neg_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_neg
        have h_eq : (fun x => y₂ x / y₁ x) c = (fun x => y₂ x / y₁ x) d := by simp [hc0, hd0]
        have h_d_eq_c : d = c := (h_strict_anti.eq_iff_eq hc hd).mp h_eq
        exact hcd h_d_eq_c.symm
    · -- d < c, symmetric
      have h_deriv_ratio : ∀ x ∈ Ioo a b, HasDerivAt (fun x => y₂ x / y₁ x) (W x / (y₁ x)^2) x := by
        intro x hx
        have hy1x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x (hJ_sub (Set.Ioo_subset_Icc_self hx))
        have hy2x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x (hJ_sub (Set.Ioo_subset_Icc_self hx))
        have hy1x_ne : y₁ x ≠ 0 := hne x hx
        have hdiv : HasDerivAt (y₂ / y₁) ((deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / (y₁ x)^2) x :=
          HasDerivAt.div hy2x hy1x hy1x_ne
        have hnum : deriv y₂ x * y₁ x - y₂ x * deriv y₁ x = W x := by dsimp [W]; ring
        rw [hnum] at hdiv; exact hdiv
      have hW_nonzero_on_Ioo : ∀ x ∈ Ioo a b, W x ≠ 0 := by
        intro x hx; have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx); exact hW_nonzero x hxJ
      have hW_const_sign : (∀ x ∈ Ioo a b, W x > 0) ∨ (∀ x ∈ Ioo a b, W x < 0) :=
        const_sign_on_Ioo W a b hab (fun x hx => (hW_deriv x (hJ_sub (Set.Ioo_subset_Icc_self hx))).continuousAt) hW_nonzero_on_Ioo
      rcases hW_const_sign with (hW_pos | hW_neg)
      · have h_ratio_deriv_pos : ∀ x ∈ Ioo a b, 0 < W x / (y₁ x)^2 := by
          intro x hx; have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy₁_pos x hx) 2
          exact div_pos (hW_pos x hx) hy1_sq_pos
        have h_strict_mono : StrictMonoOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
          strictMonoOn_of_deriv_pos_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_pos
        have h_eq : (fun x => y₂ x / y₁ x) c = (fun x => y₂ x / y₁ x) d := by simp [hc0, hd0]
        have h_d_eq_c : d = c := (h_strict_mono.eq_iff_eq hd hc).mp h_eq.symm
        exact hcd h_d_eq_c.symm
      · have h_ratio_deriv_neg : ∀ x ∈ Ioo a b, W x / (y₁ x)^2 < 0 := by
          intro x hx
          have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy₁_pos x hx) 2
          have hW_neg_x : W x < 0 := hW_neg x hx
          exact (div_neg_iff.mpr (Or.inr ⟨hW_neg_x, hy1_sq_pos⟩))
        have h_strict_anti : StrictAntiOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
          strictAntiOn_of_deriv_neg_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_neg
        have h_eq : (fun x => y₂ x / y₁ x) c = (fun x => y₂ x / y₁ x) d := by simp [hc0, hd0]
        have h_c_eq_d : c = d := (h_strict_anti.eq_iff_eq hd hc).mp h_eq.symm
        exact hcd h_c_eq_d
  rcases h_exists with ⟨c, hc, hc0⟩
  refine ⟨c, ⟨hc, hc0⟩, ?_⟩
  intro d ⟨hd, hd0⟩
  exact (h_unique c d hc hd hc0 hd0).symm

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  rcases hW with ⟨x₀, hx₀J, hW₀⟩
  have haJ : a ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.left_mem_Icc.mpr (by linarith))
  have hbJ : b ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.right_mem_Icc.mpr (by linarith))
  have hy₁_cont : ∀ x ∈ Ioo a b, ContinuousAt y₁ x := by
    intro x hx; have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx); exact (hy₁ x hxJ).continuousAt
  have hy₁_sign : (∀ x ∈ Ioo a b, y₁ x > 0) ∨ (∀ x ∈ Ioo a b, y₁ x < 0) :=
    const_sign_on_Ioo y₁ a b hab hy₁_cont hne
  rcases hy₁_sign with (hy₁_pos | hy₁_neg)
  · -- y₁ > 0 on (a,b)
    exact sturm_separation_pos p q y₁ y₂ a b hab J hJ_open hJ_conn hJ_sub hp hq hy₁ hy₁' hy₂ hy₂'
      ⟨x₀, hx₀J, hW₀⟩ hza hzb hne hy₁_pos
  · -- y₁ < 0 on (a,b) — apply sturm_separation_pos to (-y₁, -y₂)
    have h_neg_y₁_pos : ∀ x ∈ Ioo a b, (-y₁) x > 0 := by
      intro x hx; simpa using hy₁_neg x hx
    have h_neg_y₁_ne : ∀ x ∈ Ioo a b, (-y₁) x ≠ 0 := by
      intro x hx; simpa using hne x hx
    have h_neg_za : (-y₁) a = 0 := by simpa [hza]
    have h_neg_zb : (-y₁) b = 0 := by simpa [hzb]
    have hW_neg : ∃ x₀' ∈ J, (-y₁) x₀' * deriv (-y₂) x₀' - (-y₂) x₀' * deriv (-y₁) x₀' ≠ 0 := by
      refine ⟨x₀, hx₀J, ?_⟩
      calc
        (-y₁) x₀ * deriv (-y₂) x₀ - (-y₂) x₀ * deriv (-y₁) x₀
            = (-(y₁ x₀)) * (-(deriv y₂ x₀)) - (-(y₂ x₀)) * (-(deriv y₁ x₀)) := by simp
        _ = y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ := by ring
        _ ≠ 0 := hW₀
    have h_neg_hy₁ : ∀ x ∈ J, HasDerivAt (-y₁) (deriv (-y₁) x) x := by
      intro x hxJ; simpa using (hy₁ x hxJ).neg
    have h_neg_hy₁' : ∀ x ∈ J, HasDerivAt (deriv (-y₁)) (-(p x * deriv (-y₁) x + q x * (-y₁) x)) x := by
      intro x hxJ
      simpa [deriv.neg, mul_neg, neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (hy₁' x hxJ).neg
    have h_neg_hy₂ : ∀ x ∈ J, HasDerivAt (-y₂) (deriv (-y₂) x) x := by
      intro x hxJ; simpa using (hy₂ x hxJ).neg
    have h_neg_hy₂' : ∀ x ∈ J, HasDerivAt (deriv (-y₂)) (-(p x * deriv (-y₂) x + q x * (-y₂) x)) x := by
      intro x hxJ
      simpa [deriv.neg, mul_neg, neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (hy₂' x hxJ).neg
    have h_result : ∃! c, c ∈ Set.Ioo a b ∧ (-y₂) c = 0 :=
      sturm_separation_pos p q (-y₁) (-y₂) a b hab J hJ_open hJ_conn hJ_sub hp hq
        h_neg_hy₁ h_neg_hy₁' h_neg_hy₂ h_neg_hy₂' hW_neg h_neg_za h_neg_zb h_neg_y₁_ne h_neg_y₁_pos
    rcases h_result with ⟨c, hc, huniq⟩
    rcases hc with ⟨hc_mem, hc0⟩
    refine ⟨c, ⟨hc_mem, ?_⟩, ?_⟩
    · simpa using hc0
    · intro d ⟨hd, hd0⟩
      apply huniq d ⟨hd, ?_⟩
      simpa using hd0

end Submission