import Mathlib
import Submission.Helpers

open Set Filter Topology

namespace Submission

set_option maxHeartbeats 600000

-- Second derivative of (y - 1/2)² equals 2
lemma g2 (y : ℝ) : (deriv^[2] (fun (z : ℝ) => (z - 1/2)^2)) y = 2 := by
  have h1 : deriv (fun (z : ℝ) => (z - 1/2)^2) = fun (z : ℝ) => 2*(z - 1/2) := by ext z; simp
  have h2 : deriv (fun (z : ℝ) => 2*(z - 1/2)) = fun (_ : ℝ) => (2 : ℝ) := by ext z; simp
  calc
    (deriv^[2] (fun (z : ℝ) => (z - 1/2)^2)) y = deriv (deriv (fun (z : ℝ) => (z - 1/2)^2)) y := by
      simp [Function.iterate_succ_apply]
    _ = deriv (fun (z : ℝ) => 2*(z - 1/2)) y := by rw [h1]
    _ = 2 := by rw [h2]

-- (y - 1/2)² is convex on (0,1)
lemma convex_quadratic : ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun (y : ℝ) => (y - 1/2)^2) := by
  have h_g2 : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ (deriv^[2] (fun (y : ℝ) => (y - 1/2)^2)) y := by
    intro y hy; rw [g2 y]; norm_num
  apply convexOn_of_deriv2_nonneg' (convex_Ioo 0 1) ?_ ?_ h_g2
  · intro y hy
    have h_diff : DifferentiableAt ℝ (fun (y : ℝ) => (y - 1/2)^2) y := by
      apply DifferentiableAt.pow; exact (differentiableAt_id.sub (differentiableAt_const (1/2)))
    exact h_diff.differentiableWithinAt
  · intro y hy
    have h_diff2 : DifferentiableAt ℝ (deriv (fun (y : ℝ) => (y - 1/2)^2)) y := by
      have h1 : deriv (fun (y : ℝ) => (y - 1/2)^2) = fun (y : ℝ) => 2*(y - 1/2) := by ext y; simp
      rw [h1]; exact ((differentiableAt_id.sub (differentiableAt_const (1/2))).const_mul 2)
    exact h_diff2.differentiableWithinAt

-- If f is convex and ε ≥ 0, then ε·f is convex
lemma convex_mul_const (f : ℝ → ℝ) (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hf : ConvexOn ℝ (Ioo (0 : ℝ) 1) f) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun (y : ℝ) => ε * f y) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hsum
  have h_conv := hf.2 hx hy ha hb hsum
  calc
    (fun (y : ℝ) => ε * f y) (a • x + b • y) = ε * f (a • x + b • y) := rfl
    _ ≤ ε * (a • f x + b • f y) := mul_le_mul_of_nonneg_left h_conv hε_nonneg
    _ = ε * (a * f x + b * f y) := by simp
    _ = a * (ε * f x) + b * (ε * f y) := by ring
    _ = a • (ε * f x) + b • (ε * f y) := by simp
    _ = a • (fun (y : ℝ) => ε * f y) x + b • (fun (y : ℝ) => ε * f y) y := rfl

-- A convex function on (0,1) with an interior maximum is constant
lemma convex_const_of_interior_max {φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioo (0 : ℝ) 1) φ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hc_max : ∀ y ∈ Ioo (0 : ℝ) 1, φ y ≤ φ c) : ∀ y ∈ Ioo (0 : ℝ) 1, φ y = φ c := by
  have hc0 : 0 < c := hc.1; have hc1 : c < 1 := hc.2
  -- Fraction-free convexity inequality: (b-a)·φ(p) ≤ (b-p)·φ(a) + (p-a)·φ(b) for a < p < b
  have h_ineq : ∀ (a p b : ℝ), a ∈ Ioo (0 : ℝ) 1 → p ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a < p → p < b → 
      (b - a) * φ p ≤ (b - p) * φ a + (p - a) * φ b := by
    intro a p b ha hp hb ha_p hp_b
    have ha0 : 0 < a := ha.1; have hb0 : 0 < b := hb.1
    have h_alpha_nonneg : 0 ≤ (b - p) / (b - a) := div_nonneg (by nlinarith) (by nlinarith)
    have h_beta_nonneg : 0 ≤ (p - a) / (b - a) := div_nonneg (by nlinarith) (by nlinarith)
    have h_sum : (b - p) / (b - a) + (p - a) / (b - a) = 1 := by
      field_simp [show b - a ≠ 0 from by nlinarith]; ring
    have h_conv := hconv.2 ha hb h_alpha_nonneg h_beta_nonneg h_sum
    have h_point : ((b - p)/(b - a))*a + ((p - a)/(b - a))*b = p := by
      field_simp [show b - a ≠ 0 from by nlinarith]; ring
    have h_conv_simp : φ p ≤ ((b - p)/(b - a)) * φ a + ((p - a)/(b - a)) * φ b := by
      simpa [smul_eq_mul, h_point] using h_conv
    have h_pos : b - a > 0 := by nlinarith
    have h_mul : (b - a) * φ p ≤ (b - a) * (((b - p)/(b - a)) * φ a + ((p - a)/(b - a)) * φ b) :=
      mul_le_mul_of_nonneg_left h_conv_simp h_pos.le
    have h_simp : (b - a) * (((b - p)/(b - a)) * φ a + ((p - a)/(b - a)) * φ b) = (b - p) * φ a + (p - a) * φ b := by
      field_simp [show b - a ≠ 0 from by nlinarith]
    nlinarith
  -- For any a < c < b, φ(a) = φ(c) = φ(b)
  have h_eq_around_c : ∀ (a b : ℝ), a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a < c → c < b → φ a = φ c ∧ φ b = φ c := by
    intro a b ha hb ha_c hc_b
    have ha0 : 0 < a := ha.1; have hb0 : 0 < b := hb.1
    have hineq := h_ineq a c b ha hc hb ha_c hc_b
    have ha_le_c : φ a ≤ φ c := hc_max a ha
    have hb_le_c : φ b ≤ φ c := hc_max b hb
    have h_pos1 : b - c > 0 := by nlinarith
    have h_pos2 : c - a > 0 := by nlinarith
    have h_eq_val : (b - c) * φ a + (c - a) * φ b = (b - a) * φ c := by nlinarith
    have ha_eq : φ a = φ c := by nlinarith
    have hb_eq : φ b = φ c := by nlinarith
    exact ⟨ha_eq, hb_eq⟩
  intro y hy
  have hy0 : 0 < y := hy.1; have hy1 : y < 1 := hy.2
  by_cases hy_eq_c : y = c
  · subst y; rfl
  · have h_φy_le_φc : φ y ≤ φ c := hc_max y hy
    have h_φc_le_φy : φ c ≤ φ y := by
      by_cases hy_lt_c : y < c
      · set b := (c+1)/2 with hb_def
        have hbIoo : b ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
        have c_lt_b : c < b := by nlinarith
        set a := y/2 with ha_def
        have haIoo : a ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
        have ha_lt_c : a < c := by nlinarith
        rcases h_eq_around_c a b haIoo hbIoo ha_lt_c c_lt_b with ⟨ha_eq_c, hb_eq_c⟩
        have h := h_ineq y c b hy hc hbIoo hy_lt_c c_lt_b
        rw [hb_eq_c] at h; nlinarith
      · have hc_lt_y : c < y := by by_contra! hle; exact hy_eq_c (le_antisymm hle (by nlinarith))
        set a := c/2 with ha_def
        have haIoo : a ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
        have ha_lt_c : a < c := by nlinarith
        set b := (y+1)/2 with hb_def
        have hbIoo : b ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
        rcases h_eq_around_c a b haIoo hbIoo ha_lt_c (by nlinarith) with ⟨ha_eq_c, hb_eq_c⟩
        have h := h_ineq a c y haIoo hc hy ha_lt_c hc_lt_y
        rw [ha_eq_c] at h; nlinarith
    nlinarith

-- Continuity lemma: if f is constant on (0,1) and continuous at 0, then f(0) = f(c)
lemma const_at_zero_of_const_near {f : ℝ → ℝ} {c : ℝ} (hf_cont : ContinuousAt f 0) (h_const : ∀ y ∈ Ioo (0 : ℝ) 1, f y = f c) : f 0 = f c := by
  by_contra! hne
  have hpos : |f 0 - f c| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
  rcases Metric.continuousAt_iff.mp hf_cont (|f 0 - f c| / 2) (by linarith) with ⟨δ, hδ_pos, hδ⟩
  set y := min (δ/2) (1/2) with hy_def
  have hy_pos : 0 < y := lt_min_iff.mpr ⟨by nlinarith, by norm_num⟩
  have hy_lt_δ : y < δ := by
    have : y ≤ δ/2 := min_le_left _ _; nlinarith
  have hy_lt_1 : y < 1 := by
    have : y ≤ 1/2 := min_le_right _ _; nlinarith
  have hy_in_Ioo : y ∈ Ioo (0 : ℝ) 1 := ⟨hy_pos, hy_lt_1⟩
  have h_fy_eq_fc : f y = f c := h_const y hy_in_Ioo
  have h_dist : dist y 0 < δ := by
    rw [Real.dist_eq, sub_zero]; have : |y| = y := abs_of_pos hy_pos; rw [this]; exact hy_lt_δ
  have h_f_dist : dist (f y) (f 0) < |f 0 - f c| / 2 := hδ h_dist
  rw [h_fy_eq_fc, Real.dist_eq] at h_f_dist
  have h_symm : |f c - f 0| = |f 0 - f c| := abs_sub_comm _ _
  rw [h_symm] at h_f_dist; nlinarith

-- φ is differentiable (hence continuous) at 0
lemma phi_cont_at_0 (u v : ℝ → ℝ) (J : Set ℝ) (hJ_sub : Icc (0 : ℝ) 1 ⊆ J)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x) (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x) (ε : ℝ) : 
    ContinuousAt (fun (y : ℝ) => (u y - v y) + ε * ((y - 1/2)^2)) 0 := by
  have h0J : (0 : ℝ) ∈ J := hJ_sub ⟨by norm_num, by norm_num⟩
  have h_diff_u : DifferentiableAt ℝ u 0 := (hu 0 h0J).differentiableAt
  have h_diff_v : DifferentiableAt ℝ v 0 := (hv 0 h0J).differentiableAt
  have h_diff_quad : DifferentiableAt ℝ (fun (y : ℝ) => (y - 1/2)^2) 0 := by
    apply DifferentiableAt.pow; exact (differentiableAt_id.sub (differentiableAt_const (1/2)))
  have h_diff_φ : DifferentiableAt ℝ (fun (y : ℝ) => (u y - v y) + ε * ((y - 1/2)^2)) 0 :=
    (h_diff_u.sub h_diff_v).add (h_diff_quad.const_smul ε)
  exact h_diff_φ.continuousAt

theorem bvp_comparison (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  set w := u - v with hw
  have hw0 : w 0 ≤ 0 := by dsimp [w]; linarith
  have hw1 : w 1 ≤ 0 := by dsimp [w]; linarith
  -- Show w'' ≥ 0 on (0,1) from hineq
  have hwpp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ (deriv^[2] w) x := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub ⟨hx.1.le, hx.2.le⟩
    have h_diff_deriv_u : DifferentiableAt ℝ (deriv u) x := (hu' x hxJ).differentiableAt
    have h_diff_deriv_v : DifferentiableAt ℝ (deriv v) x := (hv' x hxJ).differentiableAt
    have h_eq_near : deriv (u - v) =ᶠ[nhds x] (deriv u - deriv v) := by
      have h_open : Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      have h_eq_on : ∀ y ∈ Ioo (0 : ℝ) 1, deriv (u - v) y = (deriv u - deriv v) y := by
        intro y hy
        have hyJ : y ∈ J := hJ_sub ⟨hy.1.le, hy.2.le⟩
        simp [deriv_sub ((hu y hyJ).differentiableAt) ((hv y hyJ).differentiableAt)]
      exact Filter.eventually_of_mem h_open h_eq_on
    have h_eq : (deriv^[2] w) x = deriv (deriv u) x - deriv (deriv v) x := by
      calc
        (deriv^[2] w) x = deriv (deriv (u - v)) x := by simp [w, Function.iterate_succ_apply]
        _ = deriv (deriv u - deriv v) x := by rw [h_eq_near.deriv_eq]
        _ = deriv (deriv u) x - deriv (deriv v) x := by rw [deriv_sub h_diff_deriv_u h_diff_deriv_v]
    rw [h_eq]; have hi := hineq x hx; linarith
  -- Hence w is convex on (0,1)
  have hw_conv : ConvexOn ℝ (Ioo (0 : ℝ) 1) w := by
    apply convexOn_of_deriv2_nonneg' (convex_Ioo 0 1) ?_ ?_ hwpp
    · intro y hy
      have hyJ : y ∈ J := hJ_sub ⟨hy.1.le, hy.2.le⟩
      have h_diff_u : DifferentiableAt ℝ u y := (hu y hyJ).differentiableAt
      have h_diff_v : DifferentiableAt ℝ v y := (hv y hyJ).differentiableAt
      exact (h_diff_u.sub h_diff_v).differentiableWithinAt
    · intro y hy
      have hyJ : y ∈ J := hJ_sub ⟨hy.1.le, hy.2.le⟩
      have h_diff_deriv_u : DifferentiableAt ℝ (deriv u) y := (hu' y hyJ).differentiableAt
      have h_diff_deriv_v : DifferentiableAt ℝ (deriv v) y := (hv' y hyJ).differentiableAt
      have h_deriv_w_eq : deriv w =ᶠ[nhds y] (deriv u - deriv v) := by
        have h_open : Ioo (0 : ℝ) 1 ∈ nhds y := IsOpen.mem_nhds isOpen_Ioo hy
        have h_eq_on : ∀ z ∈ Ioo (0 : ℝ) 1, deriv w z = (deriv u - deriv v) z := by
          intro z hz; dsimp [w]
          have hzJ : z ∈ J := hJ_sub ⟨hz.1.le, hz.2.le⟩
          simp [deriv_sub ((hu z hzJ).differentiableAt) ((hv z hzJ).differentiableAt)]
        exact Filter.eventually_of_mem h_open h_eq_on
      have h_diff_deriv_w : DifferentiableAt ℝ (deriv w) y :=
        ((h_diff_deriv_u.sub h_diff_deriv_v).congr_of_eventuallyEq h_deriv_w_eq)
      exact h_diff_deriv_w.differentiableWithinAt
  rintro x ⟨hx0, hx1⟩
  by_cases hx0' : x = 0
  · subst x; exact hu0
  by_cases hx1' : x = 1
  · subst x; exact hu1
  have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx0 (Ne.symm hx0'), lt_of_le_of_ne hx1 hx1'⟩
  by_contra! hpos
  have hpos_w : w x > 0 := by dsimp [w]; linarith
  -- Barrier function φ(y) = w(y) + ε*(y-1/2)² with ε = w(x)/4 > 0
  set ε := w x / 4 with hε_def
  have hε_pos : ε > 0 := by nlinarith
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  set φ := (fun (y : ℝ) => w y + ε * ((y - 1/2)^2)) with hφ_def
  -- φ is convex on (0,1): sum of convex w and convex ε·g where g(y) = (y-1/2)²
  have hφ_conv : ConvexOn ℝ (Ioo (0 : ℝ) 1) φ := by
    dsimp [φ]
    have h_eps_quad_conv : ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun (y : ℝ) => ε * ((y - 1/2)^2)) :=
      convex_mul_const (fun (y : ℝ) => (y - 1/2)^2) ε hε_nonneg convex_quadratic
    have h_sum_conv : ConvexOn ℝ (Ioo (0 : ℝ) 1) (w + (fun (y : ℝ) => ε * ((y - 1/2)^2))) :=
      hw_conv.add h_eps_quad_conv
    simpa using h_sum_conv
  -- φ(x) > φ(0) and φ(x) > φ(1)
  have hφx_gt_φ0 : φ x > φ 0 := by
    dsimp [φ]
    have h_sq_x : (x - 1/2)^2 ≥ 0 := by nlinarith
    have h_sq0_val : ε * ((0 - 1/2)^2) = ε/4 := by ring
    rw [h_sq0_val]
    have h_upper : w 0 + ε/4 ≤ ε/4 := by nlinarith
    have h_lower : w x + ε * ((x - 1/2)^2) ≥ w x := by nlinarith
    nlinarith
  have hφx_gt_φ1 : φ x > φ 1 := by
    dsimp [φ]
    have h_sq_x : (x - 1/2)^2 ≥ 0 := by nlinarith
    have h_sq1_val : ε * ((1 - 1/2)^2) = ε/4 := by ring
    rw [h_sq1_val]
    have h_upper : w 1 + ε/4 ≤ ε/4 := by nlinarith
    have h_lower : w x + ε * ((x - 1/2)^2) ≥ w x := by nlinarith
    nlinarith
  -- φ attains a maximum on [0,1] at some c (by EVT, since φ is continuous)
  have hφ_cont : ContinuousOn φ (Icc (0 : ℝ) 1) := by
    have hw_cont : ContinuousOn w (Icc (0 : ℝ) 1) := by
      intro z hz
      have hzJ : z ∈ J := hJ_sub hz
      have h_diff_u : DifferentiableAt ℝ u z := (hu z hzJ).differentiableAt
      have h_diff_v : DifferentiableAt ℝ v z := (hv z hzJ).differentiableAt
      exact (h_diff_u.sub h_diff_v).continuousAt.continuousWithinAt
    refine hw_cont.add ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).continuousOn)
  have h_compact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have h_nonempty : (Icc (0 : ℝ) 1).Nonempty := ⟨0, left_mem_Icc.mpr (by norm_num)⟩
  rcases h_compact.exists_isMaxOn h_nonempty hφ_cont with ⟨c, hc, hc_max⟩
  -- Since φ(x) > φ(0), φ(1), the maximum c must be in (0,1)
  have hcIoo : c ∈ Ioo (0 : ℝ) 1 := by
    rcases hc with ⟨hc0, hc1⟩
    have hc_not_0 : c ≠ 0 := by
      intro hceq; subst hceq
      have hφ_x_le_φ_0 : φ x ≤ φ 0 := hc_max ⟨hx0, hx1⟩; linarith
    have hc_not_1 : c ≠ 1 := by
      intro hceq; subst hceq
      have hφ_x_le_φ_1 : φ x ≤ φ 1 := hc_max ⟨hx0, hx1⟩; linarith
    exact ⟨lt_of_le_of_ne hc0 (Ne.symm hc_not_0), lt_of_le_of_ne hc1 hc_not_1⟩
  -- For any y ∈ Ioo (0,1), φ(y) ≤ φ(c)
  have hc_max_open : ∀ y ∈ Ioo (0 : ℝ) 1, φ y ≤ φ c := by
    intro y hy; apply hc_max; exact ⟨hy.1.le, hy.2.le⟩
  -- By the key lemma, φ is constant on (0,1)
  have hφ_const : ∀ y ∈ Ioo (0 : ℝ) 1, φ y = φ c :=
    convex_const_of_interior_max hφ_conv c hcIoo hc_max_open
  -- Therefore φ(x) = φ(c) (since x ∈ (0,1))
  have hφx_eq_φc : φ x = φ c := hφ_const x hxIoo
  -- φ is continuous at 0, and constant on (0,1), so φ(0) = φ(c)
  have hφ_cont_at_0 : ContinuousAt φ 0 := by
    dsimp [φ]; exact phi_cont_at_0 u v J hJ_sub hu hv ε
  have hφ0_eq_φc : φ 0 = φ c := const_at_zero_of_const_near hφ_cont_at_0 hφ_const
  -- But φ(x) > φ(0), contradiction
  have h_contra : φ x = φ 0 :=
    calc
      φ x = φ c := hφx_eq_φc
      _ = φ 0 := Eq.symm hφ0_eq_φc
  linarith

end Submission
