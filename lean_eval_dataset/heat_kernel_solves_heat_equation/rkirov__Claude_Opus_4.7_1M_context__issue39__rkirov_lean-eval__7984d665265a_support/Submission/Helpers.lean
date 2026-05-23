import Mathlib
import ChallengeDeps

open LeanEval.Analysis.ODE Real MeasureTheory Filter Topology

namespace Submission.Helpers

/-!
Proof of `heat_kernel_solves_heat_equation`.

The Gaussian heat kernel
  `K t u := (4 π t)^{-1/2} · exp(-u² / (4t))`
satisfies the heat equation `∂_t K = ∂_u² K` pointwise. Convolving with continuous
bounded `f` preserves this identity (differentiation under the integral sign), and
the kernel acts as an approximate identity at `t = 0`.

The proof is split into:

* `K`: the explicit kernel function.
* `heatSolution_eq_integral` (PROVED): for `t > 0`, `heatSolution f t x = ∫ K t (x-y) · f y dy`.
* `heatSolution_eq_integral_sub` (PROVED): equivalent form `∫ K t u · f (x - u) du` via
  the additive substitution `u = x - y`.
* `integral_K_eq_one` (PROVED): `∫ K t = 1` (Gaussian normalisation), using
  `integral_gaussian` from Mathlib.
* `kernel_pde_pointwise` (STUB): pointwise heat-equation identity for the kernel.
* `tendsto_heatSolution_at_zero` (SORRY): the initial-condition limit `u(t, x) → f x`
  as `t → 0⁺`. Uses `integral_K_eq_one` and an ε-δ split.
* `pde_solved_at` (SORRY): the PDE statement at a given `(t, x)` with `t > 0`.
-/

/-- The 1-D heat kernel `K t u = (4πt)^{-1/2} · exp(-u²/(4t))`. -/
noncomputable def K (t u : ℝ) : ℝ :=
  (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(u ^ 2) / (4 * t))

/-- For `t > 0`, the heat solution is the convolution of `f` with `K t`. -/
lemma heatSolution_eq_integral (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y : ℝ, K t (x - y) * f y := by
  unfold heatSolution K
  rw [if_pos ht]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- For `t > 0`, an alternative form of the heat solution after substituting `u = x - y`. -/
lemma heatSolution_eq_integral_sub (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ u : ℝ, K t u * f (x - u) := by
  rw [heatSolution_eq_integral f ht x]
  -- ∫ y, K t (x - y) * f y = ∫ u, K t u * f (x - u)
  -- Substitution u = x - y. Use `integral_sub_left_eq_self`.
  have : (fun y : ℝ => K t (x - y) * f y) =
      (fun y => (fun u : ℝ => K t u * f (x - u)) (x - y)) := by
    funext y; simp
  rw [this]
  exact integral_sub_left_eq_self (fun u : ℝ => K t u * f (x - u)) volume x

/-- **Pointwise spatial derivative of the kernel.** For `t > 0`:
`∂_u K(t, u) = -(u / (2t)) · K(t, u)`. -/
lemma K_hasDerivAt_spatial {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun u => K t u) (-(u / (2 * t)) * K t u) u := by
  unfold K
  have h1 : HasDerivAt (fun u : ℝ => -(u^2) / (4 * t))
      ((-(2 * u)) / (4 * t)) u := by
    have hpow : HasDerivAt (fun u : ℝ => u^2) (2 * u) u := by
      simpa using (hasDerivAt_id u).pow 2
    exact hpow.neg.div_const (4 * t)
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(u^2) / (4 * t)))
      (Real.exp (-(u^2) / (4 * t)) * ((-(2 * u)) / (4 * t))) u :=
    h1.exp
  have h3 := h2.const_mul ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))
  convert h3 using 1
  field_simp
  ring

/-- **Time derivative of the kernel.** For `s > 0`:
`∂_s K(s, u) = ((u² - 2s) / (4s²)) · K(s, u)`. -/
lemma K_hasDerivAt_temporal {s : ℝ} (hs : 0 < s) (u : ℝ) :
    HasDerivAt (fun s => K s u) (((u^2 - 2 * s) / (4 * s^2)) * K s u) s := by
  -- Strategy: write K(s, u) = exp(L(s)) where L(s) = -(1/2)·log(4πs) - u²/(4s) (s > 0).
  -- Differentiate exp(L), then transfer to K via congr_of_eventuallyEq.
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have h_4πs_pos : (0 : ℝ) < 4 * Real.pi * s := by positivity
  have h_4πs_ne : (4 * Real.pi * s) ≠ 0 := ne_of_gt h_4πs_pos
  -- (4πs')^{-1/2} = exp(-(1/2)·log(4πs')) for s' > 0.
  have h_rpow_exp : ∀ s' : ℝ, 0 < s' →
      (4 * Real.pi * s')⁻¹ ^ ((1 : ℝ) / 2) =
        Real.exp (-(1/2) * Real.log (4 * Real.pi * s')) := by
    intro s' hs'
    have h4πs' : (0 : ℝ) < 4 * Real.pi * s' := by positivity
    rw [Real.rpow_def_of_pos (inv_pos.mpr h4πs')]
    congr 1
    rw [Real.log_inv]
    ring
  -- K(s', u) = exp(L(s')) for s' > 0.
  have h_K_eq : ∀ s' : ℝ, 0 < s' →
      K s' u = Real.exp (-(1/2) * Real.log (4 * Real.pi * s') - u^2 / (4 * s')) := by
    intro s' hs'
    unfold K
    rw [h_rpow_exp s' hs', ← Real.exp_add]
    congr 1
    ring
  -- Derivative of log(4πs') at s: 1/s.
  have h_log : HasDerivAt (fun s' : ℝ => Real.log (4 * Real.pi * s')) (s⁻¹) s := by
    have h_inner : HasDerivAt (fun s' : ℝ => 4 * Real.pi * s') (4 * Real.pi) s := by
      simpa using (hasDerivAt_id s).const_mul (4 * Real.pi)
    have h := h_inner.log h_4πs_ne
    convert h using 1
    field_simp
  -- Derivative of u²/(4s') at s: -u²/(4s²).
  have h_inv_s : HasDerivAt (fun s' : ℝ => s'⁻¹) (-(s^2)⁻¹) s := by
    simpa using hasDerivAt_inv hs_ne
  have h_g : HasDerivAt (fun s' : ℝ => u^2 / (4 * s')) (-(u^2 / (4 * s^2))) s := by
    have h_eq : (fun s' : ℝ => u^2 / (4 * s')) = (fun s' => u^2 / 4 * s'⁻¹) := by
      funext s'; field_simp
    rw [h_eq]
    have h_step := h_inv_s.const_mul (u^2 / 4)
    convert h_step using 1
    field_simp
  -- L'(s) = -(1/2)·(1/s) - (-u²/(4s²)) = -1/(2s) + u²/(4s²).
  have h_L : HasDerivAt
      (fun s' : ℝ => -(1/2) * Real.log (4 * Real.pi * s') - u^2 / (4 * s'))
      (-(1/2) * s⁻¹ - (-(u^2 / (4 * s^2)))) s :=
    (h_log.const_mul (-(1/2))).sub h_g
  -- exp(L) has derivative exp(L(s)) · L'(s).
  have h_expL : HasDerivAt
      (fun s' : ℝ => Real.exp (-(1/2) * Real.log (4 * Real.pi * s') - u^2 / (4 * s')))
      (Real.exp (-(1/2) * Real.log (4 * Real.pi * s) - u^2 / (4 * s)) *
        (-(1/2) * s⁻¹ - (-(u^2 / (4 * s^2))))) s :=
    h_L.exp
  -- Transfer derivative from exp(L) to K via eventual equality.
  have h_eventually :
      (fun s' : ℝ => K s' u) =ᶠ[nhds s]
        (fun s' => Real.exp (-(1/2) * Real.log (4 * Real.pi * s') - u^2 / (4 * s'))) := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    exact h_K_eq s' hs'
  have h_K_deriv := h_expL.congr_of_eventuallyEq h_eventually
  -- Match the derivative values.
  convert h_K_deriv using 1
  rw [h_K_eq s hs]
  field_simp
  ring

/-- **Second spatial derivative.** The first derivative `u → -(u/(2t)) · K(t, u)`
has derivative `((u² - 2t) / (4t²)) · K(t, u)`. -/
lemma K_hasDerivAt_spatial_second {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun u => -(u / (2 * t)) * K t u)
               (((u^2 - 2 * t) / (4 * t^2)) * K t u) u := by
  have h_K_deriv : HasDerivAt (fun u => K t u) (-(u / (2 * t)) * K t u) u :=
    K_hasDerivAt_spatial ht u
  have h_lin : HasDerivAt (fun u : ℝ => -(u / (2 * t))) (-(1 / (2 * t))) u := by
    have : HasDerivAt (fun u : ℝ => u / (2 * t)) (1 / (2 * t)) u := by
      simpa using (hasDerivAt_id u).div_const (2 * t)
    exact this.neg
  have := h_lin.mul h_K_deriv
  convert this using 1
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp
  ring

/-- The heat kernel `K t` has integral `1` for `t > 0`. -/
lemma integral_K_eq_one {t : ℝ} (ht : 0 < t) : ∫ u : ℝ, K t u = 1 := by
  unfold K
  rw [integral_const_mul]
  -- ∫ exp(-(u²)/(4t)) du = ∫ exp(-(1/(4t)) * u²) du = √(π/(1/(4t))) = √(4πt)
  have h_eq : (fun u : ℝ => Real.exp (-(u ^ 2) / (4 * t))) =
      (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u ^ 2)) := by
    funext u
    congr 1
    field_simp
  rw [h_eq, integral_gaussian]
  rw [show (Real.pi / (1 / (4 * t))) = 4 * Real.pi * t from by field_simp]
  -- Now: (4πt)⁻¹ ^ (1/2) * √(4πt) = 1
  have h4πt_pos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  rw [← Real.sqrt_eq_rpow ((4 * Real.pi * t)⁻¹)]
  rw [Real.sqrt_inv]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr h4πt_pos).ne'

/-- After substituting `u = 2√t · w`, the heat solution becomes
  `(1/√π) · ∫ exp(-w²) · f(x - 2√t·w) dw`.

This form has a `t`-independent integrable dominator (the Gaussian `exp(-w²)`), making
dominated convergence applicable as `t → 0⁺`. -/
lemma heatSolution_eq_rescaled (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x =
      (1 / Real.sqrt Real.pi) *
        ∫ w : ℝ, Real.exp (-(w ^ 2)) * f (x - 2 * Real.sqrt t * w) := by
  rw [heatSolution_eq_integral_sub f ht x]
  have ht_sqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h2t_pos : 0 < 2 * Real.sqrt t := by positivity
  -- Apply ∫ u, K t u * f (x - u) = (2√t) * ∫ w, K t (2√t·w) * f (x - 2√t·w).
  -- Use integral_comp_mul_left: ∫ x_1, g(a * x_1) = |a⁻¹| · ∫ y, g y.
  have h_subst :
      (∫ u : ℝ, K t u * f (x - u)) =
        (2 * Real.sqrt t) *
          ∫ w : ℝ, K t (2 * Real.sqrt t * w) * f (x - 2 * Real.sqrt t * w) := by
    have := Measure.integral_comp_mul_left
      (fun u : ℝ => K t u * f (x - u)) (2 * Real.sqrt t)
    -- this : ∫ x_1, (fun u => K t u * f (x - u)) (2√t * x_1) = |(2√t)⁻¹| • ∫ y, K t y * f (x - y)
    rw [abs_of_pos (inv_pos.mpr h2t_pos)] at this
    simp only [smul_eq_mul] at this
    -- this : ∫ w, K t (2√t * w) * f (x - 2√t * w) = (2√t)⁻¹ * ∫ u, K t u * f (x - u)
    rw [this]
    field_simp
  rw [h_subst]
  -- Compute K t (2√t · w) = (4πt)^{-1/2} · exp(-w²).
  have hK_at : ∀ w : ℝ, K t (2 * Real.sqrt t * w) =
      (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(w ^ 2)) := by
    intro w
    unfold K
    congr 1
    -- show exp(-(2√t·w)²/(4t)) = exp(-w²)
    congr 1
    have h_sq : (2 * Real.sqrt t * w) ^ 2 = 4 * t * w ^ 2 := by
      rw [mul_pow, mul_pow]
      rw [Real.sq_sqrt ht.le]
      ring
    rw [h_sq]
    field_simp
  simp_rw [hK_at]
  -- Now: (2√t) · ∫ w, ((4πt)^{-1/2} · exp(-w²)) · f(x - 2√t·w) dw
  --    = (2√t · (4πt)^{-1/2}) · ∫ w, exp(-w²) · f(x - 2√t·w) dw
  rw [show (fun w : ℝ =>
        ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(w ^ 2))) *
          f (x - 2 * Real.sqrt t * w)) =
       (fun w : ℝ =>
        (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
          (Real.exp (-(w ^ 2)) * f (x - 2 * Real.sqrt t * w)))
      from by funext w; ring]
  rw [integral_const_mul]
  -- Now: (2√t) · ((4πt)^{-1/2} · ∫ exp(-w²) · f(x - 2√t·w) dw)
  -- Need: (2√t) · (4πt)^{-1/2} = 1/√π.
  have h_const : (2 * Real.sqrt t) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) =
      1 / Real.sqrt Real.pi := by
    have h4πt_pos : (0 : ℝ) < 4 * Real.pi * t := by positivity
    rw [← Real.sqrt_eq_rpow ((4 * Real.pi * t)⁻¹), Real.sqrt_inv]
    -- 2√t / √(4πt) = 2√t / (2 · √π · √t) = 1/√π
    rw [show (4 : ℝ) * Real.pi * t = (2 * Real.sqrt t)^2 * Real.pi from by
        rw [mul_pow]
        rw [Real.sq_sqrt ht.le]
        ring]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * Real.sqrt t)^2)]
    rw [Real.sqrt_sq h2t_pos.le]
    field_simp
  -- Now: 2√t · ((4πt)^{-1/2} · ∫ ...) = (1/√π) · ∫ ...
  rw [← mul_assoc, h_const]

/-- **Initial-condition limit.** For continuous bounded `f`, `heatSolution f t x → f x`
as `t → 0⁺`.

Sketch. Write `heatSolution f t x = ∫ K t u · f (x - u) du` (change of variable
`u = x - y`). The kernel `K t` has integral `1`, is nonneg, and concentrates at `0`
as `t → 0⁺` (the Gaussian normalisation). Since `f` is continuous at `x` and bounded,
the convolution converges to `f x` by an ε-δ split argument:

  `|∫ K t u · (f (x - u) - f x) du|`
    `≤ ε · ∫_{|u|<δ} K t u du + 2M · ∫_{|u|≥δ} K t u du → ε + 0`.

Both `∫ K t = 1` and the Gaussian tail bound `∫_{|u|≥δ} K t → 0` come from
`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` (in particular
`integral_gaussian`). -/
lemma tendsto_heatSolution_at_zero (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun t : ℝ => heatSolution f t x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (f x)) := by
  obtain ⟨M, hM⟩ := hf_bdd
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hsqrtπ_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ_pos
  -- Step 1: the Gaussian integral with constant f(x) factor gives √π · f x.
  have h_gauss_const : (∫ w : ℝ, Real.exp (-(w^2)) * f x) = Real.sqrt Real.pi * f x := by
    rw [integral_mul_const]
    have h_eq : (fun w : ℝ => Real.exp (-(w^2))) = (fun w : ℝ => Real.exp (-(1 : ℝ) * w^2)) := by
      funext w
      congr 1
      ring
    rw [h_eq, integral_gaussian]
    rw [show Real.pi / (1 : ℝ) = Real.pi from by norm_num]
  -- Step 2: heatSolution coincides with the rescaled form eventually on the filter.
  have h_rescale : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      heatSolution f t x =
        (1 / Real.sqrt Real.pi) *
          ∫ w : ℝ, Real.exp (-(w^2)) * f (x - 2 * Real.sqrt t * w) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ Set.Ioi 0)
    exact heatSolution_eq_rescaled f ht x
  -- Step 3: dominated convergence for the rescaled integral.
  have h_dct :
      Tendsto (fun t : ℝ => ∫ w : ℝ, Real.exp (-(w^2)) * f (x - 2 * Real.sqrt t * w))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (∫ w : ℝ, Real.exp (-(w^2)) * f x)) := by
    -- Bound: |exp(-w²) · f(x - 2√t · w)| ≤ M · exp(-w²) uniformly in t.
    -- Pointwise limit: as t → 0⁺, x - 2√t · w → x, so by continuity of f,
    --   exp(-w²) · f(x - 2√t · w) → exp(-w²) · f(x).
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun w : ℝ => M * Real.exp (-(w^2))) ?_ ?_ ?_ ?_
    · -- measurability for each t in the filter
      filter_upwards with t
      apply Continuous.aestronglyMeasurable
      exact (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))).mul
        (hf_cont.comp (continuous_const.sub ((continuous_const.mul
          (Real.continuous_sqrt.comp continuous_const)).mul continuous_id)))
    · -- |·| ≤ M · exp(-w²) eventually
      filter_upwards with t
      filter_upwards with w
      rw [Real.norm_eq_abs, abs_mul]
      have h_exp_nn : 0 ≤ Real.exp (-(w^2)) := (Real.exp_pos _).le
      rw [abs_of_nonneg h_exp_nn]
      have := hM (x - 2 * Real.sqrt t * w)
      nlinarith [h_exp_nn]
    · -- M · exp(-w²) integrable
      apply MeasureTheory.Integrable.const_mul
      rw [show (fun w : ℝ => Real.exp (-(w^2))) = (fun w => Real.exp (-(1:ℝ) * w^2)) from by
        funext w; congr 1; ring]
      exact integrable_exp_neg_mul_sq one_pos
    · -- pointwise convergence: exp(-w²) · f(x - 2√t · w) → exp(-w²) · f(x)
      filter_upwards with w
      -- x - 2√t · w → x as t → 0⁺
      have h_sqrt : Tendsto (fun t : ℝ => Real.sqrt t) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
        have := Real.continuous_sqrt.tendsto 0
        rw [Real.sqrt_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h_inner : Tendsto (fun t : ℝ => x - 2 * Real.sqrt t * w)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 x) := by
        have : Tendsto (fun t : ℝ => x - 2 * Real.sqrt t * w) (nhdsWithin 0 (Set.Ioi 0))
            (𝓝 (x - 2 * 0 * w)) := by
          apply tendsto_const_nhds.sub
          exact ((tendsto_const_nhds.mul h_sqrt).mul tendsto_const_nhds)
        simpa using this
      have h_f : Tendsto (fun t : ℝ => f (x - 2 * Real.sqrt t * w))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (f x)) :=
        (hf_cont.tendsto _).comp h_inner
      exact tendsto_const_nhds.mul h_f
  -- Step 4: combine. (1/√π) · √π · f(x) = f(x).
  have h_combine :
      Tendsto (fun t : ℝ =>
        (1 / Real.sqrt Real.pi) *
          ∫ w : ℝ, Real.exp (-(w^2)) * f (x - 2 * Real.sqrt t * w))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((1 / Real.sqrt Real.pi) * (Real.sqrt Real.pi * f x))) := by
    refine tendsto_const_nhds.mul ?_
    rw [← h_gauss_const]
    exact h_dct
  have h_target : (1 / Real.sqrt Real.pi) * (Real.sqrt Real.pi * f x) = f x := by
    rw [show (1 : ℝ) / Real.sqrt Real.pi = (Real.sqrt Real.pi)⁻¹ from by ring]
    rw [← mul_assoc, inv_mul_cancel₀ hsqrtπ_pos.ne', one_mul]
  rw [← h_target]
  exact h_combine.congr' (h_rescale.mono fun _ h => h.symm)

set_option maxHeartbeats 1600000 in
/-- **PDE part.** For each `(t, x)` with `t > 0`, the heat solution satisfies the heat
equation in the sense of the existential statement of the main theorem.

Sketch. Define the spatial first derivative as
  `ux y := ∫ ∂_z K t (y - z) · f z dz`.
By `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (differentiation
under the integral sign), `(fun y => heatSolution f t y)` has derivative `ux y` at
every `y` (using `f` bounded and Gaussian-tail domination). The same theorem applied a
second time yields `HasDerivAt ux uxx x` where `uxx := ∫ ∂_z² K t (x - z) · f z dz`.

The time derivative `HasDerivAt (fun s => heatSolution f s x) uxx t` follows likewise,
substituting the pointwise identity `∂_t K t u = ∂_u² K t u` (= `K t u · (u² - 2t) / (4 t²)`).
-/
lemma pde_solved_at (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
      (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
      HasDerivAt ux uxx x ∧
      HasDerivAt (fun s => heatSolution f s x) uxx t := by
  -- Choose ux y := ∫ z, -((y - z)/(2t)) · K t (y - z) · f z dz
  --        uxx  := ∫ z, ((x - z)^2 - 2t)/(4t^2) · K t (x - z) · f z dz
  -- These are the spatial first/second derivatives of the convolution.
  obtain ⟨M, hM⟩ := hf_bdd
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h2t_pos : (0 : ℝ) < 2 * t := by linarith
  have h4πt_pos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  refine ⟨fun y => ∫ z, -((y - z) / (2 * t)) * K t (y - z) * f z,
          ∫ z, ((x - z) ^ 2 - 2 * t) / (4 * t ^ 2) * K t (x - z) * f z,
          ?_, ?_, ?_⟩
  · -- HasDerivAt of the spatial first derivative at every y.
    -- Use hasDerivAt_integral_of_dominated_loc_of_deriv_le applied to F z w := K t (z-w) * f w.
    intro y
    -- Rewrite heatSolution as integral
    have h_rw : (fun z : ℝ => heatSolution f t z) =
                (fun z : ℝ => ∫ w : ℝ, K t (z - w) * f w) := by
      funext z
      exact heatSolution_eq_integral f ht z
    rw [h_rw]
    -- Apply diff-under-integral.
    -- F z w := K t (z - w) * f w
    -- F' z w := -((z - w) / (2t)) * K t (z - w) * f w
    -- bound w := M * (|y - w| + 1) / (2t) * (4πt)^{-1/2} * exp(1/(4t)) * exp(-(y - w)^2 / (8t))
    set Fz := fun (z : ℝ) (w : ℝ) => K t (z - w) * f w with hFz_def
    set F'z := fun (z : ℝ) (w : ℝ) =>
      -((z - w) / (2 * t)) * K t (z - w) * f w with hF'z_def
    set bound : ℝ → ℝ := fun w =>
      M * (|y - w| + 1) / (2 * t) *
        (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
        Real.exp (1 / (4 * t)) *
        Real.exp (-(y - w)^2 / (8 * t)) with hbound_def
    -- Hypothesis: HasDerivAt of the integrand at every z ∈ s, for every w.
    have h_diff : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ z ∈ Set.Ioo (y - 1) (y + 1),
          HasDerivAt (fun z => Fz z w) (F'z z w) z := by
      filter_upwards with w
      intro z _
      show HasDerivAt (fun z => K t (z - w) * f w)
        (-((z - w) / (2 * t)) * K t (z - w) * f w) z
      have h_K : HasDerivAt (fun u => K t u)
          (-((z - w) / (2 * t)) * K t (z - w)) (z - w) :=
        K_hasDerivAt_spatial ht (z - w)
      have h_shift : HasDerivAt (fun z : ℝ => K t (z - w))
          (-((z - w) / (2 * t)) * K t (z - w)) z := by
        have h_id_sub : HasDerivAt (fun z : ℝ => z - w) 1 z :=
          (hasDerivAt_id z).sub_const w
        have := h_K.comp z h_id_sub
        simpa using this
      exact h_shift.mul_const (f w)
    -- Hypothesis hs : s ∈ 𝓝 y
    have hs : Set.Ioo (y - 1) (y + 1) ∈ 𝓝 y :=
      Ioo_mem_nhds (by linarith) (by linarith)
    -- K t is continuous (smooth even) for t > 0.
    have hK_cont : Continuous (fun u => K t u) := by
      unfold K
      exact continuous_const.mul
        (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const (4 * t)))
    have hK_cont_sub : ∀ z₀ : ℝ, Continuous (fun w : ℝ => K t (z₀ - w)) := fun z₀ =>
      hK_cont.comp (continuous_const.sub continuous_id)
    -- Hypothesis hF_meas : ∀ᶠ x in 𝓝 y, AEStronglyMeasurable (Fz x) volume.
    have hF_meas : ∀ᶠ x in 𝓝 y,
        MeasureTheory.AEStronglyMeasurable (Fz x) MeasureTheory.volume := by
      filter_upwards with x
      exact ((hK_cont_sub x).mul hf_cont).aestronglyMeasurable
    -- Hypothesis hF'_meas : AEStronglyMeasurable (F'z y) volume.
    have hF'_meas : MeasureTheory.AEStronglyMeasurable (F'z y) MeasureTheory.volume := by
      have h_cont : Continuous (fun w => F'z y w) := by
        show Continuous (fun w => -((y - w) / (2 * t)) * K t (y - w) * f w)
        refine Continuous.mul (Continuous.mul ?_ (hK_cont_sub y)) hf_cont
        exact (continuous_const.sub continuous_id).div_const (2 * t) |>.neg
      exact h_cont.aestronglyMeasurable
    -- Hypothesis hF_int : Integrable (Fz y) volume.
    -- |Fz y w| = |K t (y - w) · f w| ≤ K t (y - w) · M; K t is integrable (Gaussian).
    have hK_y_int : MeasureTheory.Integrable
        (fun w => K t (y - w)) MeasureTheory.volume := by
      -- ∫ K t (y - w) dw = ∫ K t u du (by translation), = 1. Hence integrable.
      -- Use: x ↦ K t x is integrable, then x ↦ K t (y - x) is integrable (translation).
      have hK_int : MeasureTheory.Integrable (fun u => K t u) MeasureTheory.volume := by
        unfold K
        apply MeasureTheory.Integrable.const_mul
        have h_eq : (fun u : ℝ => Real.exp (-(u^2) / (4 * t))) =
            (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u^2)) := by
          funext u; congr 1; field_simp
        rw [h_eq]
        exact integrable_exp_neg_mul_sq (by positivity)
      -- Translation: ∫ K t (y - w) dw = ∫ K t u du via integral_sub_left_eq_self
      have := hK_int.comp_sub_left y
      exact this
    have hF_int : MeasureTheory.Integrable (Fz y) MeasureTheory.volume := by
      show MeasureTheory.Integrable (fun w => K t (y - w) * f w) MeasureTheory.volume
      have h_swap : (fun w : ℝ => K t (y - w) * f w) = (fun w => f w * K t (y - w)) := by
        funext w; ring
      rw [h_swap]
      refine hK_y_int.bdd_mul (c := M) hf_cont.aestronglyMeasurable ?_
      filter_upwards with w using by rw [Real.norm_eq_abs]; exact hM w
    -- Hypothesis h_bound : ∀ᵐ w, ∀ z ∈ s, ‖F'z z w‖ ≤ bound w.
    have h_bound : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ z ∈ Set.Ioo (y - 1) (y + 1), ‖F'z z w‖ ≤ bound w := by
      filter_upwards with w
      intro z hz
      simp only [hF'z_def, hbound_def, Set.mem_Ioo] at hz ⊢
      -- hz : y - 1 < z ∧ z < y + 1
      have hzy : |z - y| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      -- |z - w| ≤ |y - w| + 1
      have h_zw_yw : |z - w| ≤ |y - w| + 1 := by
        have h_eq : z - w = (y - w) + (z - y) := by ring
        rw [h_eq]
        calc |(y - w) + (z - y)| ≤ |y - w| + |z - y| := abs_add_le _ _
          _ ≤ |y - w| + 1 := by linarith [hzy.le]
      -- (z - w)² ≥ (y - w)²/2 - 1
      have h_sq_bound : (y - w)^2 / 2 - 1 ≤ (z - w)^2 := by
        have hzy' : (z - y)^2 < 1 := by
          have := abs_lt.mp hzy
          nlinarith
        have h_expand : (z - w)^2 = (y - w)^2 + 2 * (y - w) * (z - y) + (z - y)^2 := by
          ring
        nlinarith [sq_nonneg (y - w + 2 * (z - y)), hzy'.le, h_expand]
      -- K t (z - w) ≤ (4πt)^{-1/2} · exp(1/(4t)) · exp(-(y-w)²/(8t))
      have h_K_bound : K t (z - w) ≤
          (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
            Real.exp (-(y - w)^2 / (8 * t)) := by
        unfold K
        have hC_pos : (0 : ℝ) < (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) := by
          apply Real.rpow_pos_of_pos; positivity
        have h_exp_arg : -((z - w)^2) / (4 * t) ≤ -((y - w)^2 / 2 - 1) / (4 * t) := by
          rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * t)]
          linarith
        have h_exp_bound :
            Real.exp (-((z - w)^2) / (4 * t)) ≤
              Real.exp (-((y - w)^2 / 2 - 1) / (4 * t)) :=
          Real.exp_le_exp.mpr h_exp_arg
        have h_split : -((y - w)^2 / 2 - 1) / (4 * t) =
            1 / (4 * t) + (-(y - w)^2 / (8 * t)) := by
          field_simp; ring
        rw [h_split, Real.exp_add] at h_exp_bound
        calc (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(z - w)^2 / (4 * t))
            ≤ (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
                (Real.exp (1 / (4 * t)) * Real.exp (-(y - w)^2 / (8 * t))) := by
              gcongr
          _ = (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
                Real.exp (-(y - w)^2 / (8 * t)) := by ring
      -- Combine to bound F'z.
      have h_K_nn : 0 ≤ K t (z - w) := by
        unfold K
        apply mul_nonneg
        · apply Real.rpow_nonneg; positivity
        · exact (Real.exp_pos _).le
      have h_fw_le_M : |f w| ≤ M := hM w
      have h_abs_zw_div : |((z - w) / (2 * t))| = |z - w| / (2 * t) := by
        rw [abs_div, abs_of_pos h2t_pos]
      calc ‖-((z - w) / (2 * t)) * K t (z - w) * f w‖
          = |z - w| / (2 * t) * K t (z - w) * |f w| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, h_abs_zw_div,
                abs_of_nonneg h_K_nn]
        _ ≤ (|y - w| + 1) / (2 * t) * K t (z - w) * M := by
            gcongr
        _ ≤ (|y - w| + 1) / (2 * t) *
            ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
              Real.exp (-(y - w)^2 / (8 * t))) * M := by
            have h_yw_nn : 0 ≤ |y - w| + 1 := by positivity
            gcongr
        _ = M * (|y - w| + 1) / (2 * t) *
            (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
            Real.exp (1 / (4 * t)) *
            Real.exp (-(y - w)^2 / (8 * t)) := by ring
    -- Hypothesis bound_integrable : Integrable bound volume. (Polynomial × Gaussian)
    have bound_integrable : MeasureTheory.Integrable bound MeasureTheory.volume := by
      -- bound w = C · (|y - w| + 1) · exp(-(y - w)²/(8t)) where C is a positive constant.
      -- After translation u = y - w, we get C · (|u| + 1) · exp(-u²/(8t)),
      -- a sum of |u| · exp(-bu²) and exp(-bu²), each integrable.
      simp only [hbound_def]
      have h_8t_pos : (0 : ℝ) < 1 / (8 * t) := by positivity
      -- Integrable (fun u => exp(-u²/(8t))) over ℝ.
      have h_g_int : MeasureTheory.Integrable
          (fun u : ℝ => Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_eq : (fun u : ℝ => Real.exp (-u^2 / (8 * t))) =
            (fun u : ℝ => Real.exp (-(1 / (8 * t)) * u^2)) := by
          funext u; congr 1; field_simp
        rw [h_eq]
        exact integrable_exp_neg_mul_sq h_8t_pos
      -- Integrable (fun u => u · exp(-u²/(8t))) over ℝ (signed).
      have h_ug_int : MeasureTheory.Integrable
          (fun u : ℝ => u * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_eq : (fun u : ℝ => u * Real.exp (-u^2 / (8 * t))) =
            (fun u : ℝ => u^(1 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) := by
          funext u
          rw [Real.rpow_one]
          congr 2
          field_simp
        rw [h_eq]
        exact integrable_rpow_mul_exp_neg_mul_sq h_8t_pos (by norm_num : (-1 : ℝ) < 1)
      -- Integrable (fun u => |u| · exp(-u²/(8t))) via |·|.
      have h_abs_ug_int : MeasureTheory.Integrable
          (fun u : ℝ => |u| * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have := h_ug_int.norm
        simp only [Real.norm_eq_abs] at this
        have h_eq : (fun u : ℝ => |u * Real.exp (-u^2 / (8 * t))|) =
            (fun u : ℝ => |u| * Real.exp (-u^2 / (8 * t))) := by
          funext u
          rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        rw [h_eq] at this
        exact this
      -- bound w via translation y - w → u; combine.
      have h_poly_int : MeasureTheory.Integrable
          (fun w : ℝ => (|y - w| + 1) * Real.exp (-(y - w)^2 / (8 * t)))
          MeasureTheory.volume := by
        -- Translation: ∫ g (y - w) dw = ∫ g u du (via integral_sub_left_eq_self).
        have h_eq_w_u : (fun w : ℝ => (|y - w| + 1) * Real.exp (-(y - w)^2 / (8 * t))) =
            (fun w : ℝ => ((fun u : ℝ => (|u| + 1) * Real.exp (-u^2 / (8 * t))) (y - w))) := by
          funext w; rfl
        rw [h_eq_w_u]
        -- (|·|+1) · exp(-·²/(8t)) is integrable (= |·| · exp + 1 · exp, both integrable).
        have h_sum : (fun u : ℝ => (|u| + 1) * Real.exp (-u^2 / (8 * t))) =
            (fun u => |u| * Real.exp (-u^2 / (8 * t)) +
                      Real.exp (-u^2 / (8 * t))) := by
          funext u; ring
        have h_u_int : MeasureTheory.Integrable
            (fun u : ℝ => (|u| + 1) * Real.exp (-u^2 / (8 * t)))
            MeasureTheory.volume := by
          rw [h_sum]; exact h_abs_ug_int.add h_g_int
        -- Apply Integrable.comp_sub_left.
        exact h_u_int.comp_sub_left y
      -- bound w = (some positive constant) · (|y - w| + 1) · exp(-(y-w)²/(8t))
      have hC : ∀ w : ℝ,
          M * (|y - w| + 1) / (2 * t) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
            Real.exp (1 / (4 * t)) * Real.exp (-(y - w) ^ 2 / (8 * t)) =
          (M / (2 * t) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t))) *
            ((|y - w| + 1) * Real.exp (-(y - w) ^ 2 / (8 * t))) := by
        intro w; ring
      simp_rw [hC]
      exact h_poly_int.const_mul _
    -- Apply diff-under-integral:
    have h_apply := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
    exact h_apply.2
  · -- HasDerivAt of ux at x giving uxx (spatial second derivative).
    -- Same template as the first spatial derivative, but Fy is the first derivative
    -- and F'y is the second derivative.
    set Fy := fun (y : ℝ) (w : ℝ) =>
      -((y - w) / (2 * t)) * K t (y - w) * f w with hFy_def
    set F'y := fun (y : ℝ) (w : ℝ) =>
      ((y - w)^2 - 2 * t) / (4 * t^2) * K t (y - w) * f w with hF'y_def
    set bound2 : ℝ → ℝ := fun w =>
      M * ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) *
        (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
        Real.exp (1 / (4 * t)) *
        Real.exp (-(x - w)^2 / (8 * t)) with hbound2_def
    have hK_cont : Continuous (fun u => K t u) := by
      unfold K
      exact continuous_const.mul
        (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const (4 * t)))
    have hK_cont_sub : ∀ z₀ : ℝ, Continuous (fun w : ℝ => K t (z₀ - w)) := fun z₀ =>
      hK_cont.comp (continuous_const.sub continuous_id)
    -- HasDerivAt of integrand for second derivative at every y, every w.
    have h_diff : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y ∈ Set.Ioo (x - 1) (x + 1),
          HasDerivAt (fun y => Fy y w) (F'y y w) y := by
      filter_upwards with w
      intro y _
      show HasDerivAt (fun y => -((y - w) / (2 * t)) * K t (y - w) * f w)
        (((y - w)^2 - 2 * t) / (4 * t^2) * K t (y - w) * f w) y
      have h_K2 : HasDerivAt (fun u => -(u / (2 * t)) * K t u)
          (((y - w)^2 - 2 * t) / (4 * t^2) * K t (y - w)) (y - w) :=
        K_hasDerivAt_spatial_second ht (y - w)
      have h_shift : HasDerivAt (fun y : ℝ => -((y - w) / (2 * t)) * K t (y - w))
          (((y - w)^2 - 2 * t) / (4 * t^2) * K t (y - w)) y := by
        have h_id_sub : HasDerivAt (fun y : ℝ => y - w) 1 y :=
          (hasDerivAt_id y).sub_const w
        have := h_K2.comp y h_id_sub
        simpa using this
      exact h_shift.mul_const (f w)
    -- hs
    have hs : Set.Ioo (x - 1) (x + 1) ∈ 𝓝 x :=
      Ioo_mem_nhds (by linarith) (by linarith)
    -- hF_meas
    have hF_meas : ∀ᶠ y in 𝓝 x,
        MeasureTheory.AEStronglyMeasurable (Fy y) MeasureTheory.volume := by
      filter_upwards with y
      have : Continuous (fun w : ℝ => -((y - w) / (2 * t)) * K t (y - w) * f w) := by
        refine Continuous.mul (Continuous.mul ?_ (hK_cont_sub y)) hf_cont
        exact (continuous_const.sub continuous_id).div_const (2 * t) |>.neg
      exact this.aestronglyMeasurable
    -- hF'_meas
    have hF'_meas : MeasureTheory.AEStronglyMeasurable (F'y x) MeasureTheory.volume := by
      have h_cont : Continuous (fun w => F'y x w) := by
        show Continuous (fun w => ((x - w)^2 - 2 * t) / (4 * t^2) *
                                  K t (x - w) * f w)
        refine Continuous.mul (Continuous.mul ?_ (hK_cont_sub x)) hf_cont
        refine Continuous.div_const ?_ (4 * t^2)
        exact ((continuous_const.sub continuous_id).pow 2).sub continuous_const
      exact h_cont.aestronglyMeasurable
    -- hF_int : Fy x integrable.
    -- |Fy x w| = |(x-w)/(2t)| · K t (x - w) · |f w| ≤ M · |x-w| · K t (x-w) / (2t)
    -- |·| · K is integrable (polynomial × Gaussian).
    have hF_int : MeasureTheory.Integrable (Fy x) MeasureTheory.volume := by
      -- Use direct bound: |Fy x w| ≤ M * |x-w| · K t (x - w) / (2t)
      -- And K t is uniformly bounded by (4πt)^{-1/2}
      -- So |x - w| · K(t, x - w) integrable; here just bound by M and the gaussian-decay version.
      -- Simpler: show Fy x is continuous and bounded by an integrable function.
      have h_cont : Continuous (Fy x) := by
        show Continuous (fun w => -((x - w) / (2 * t)) * K t (x - w) * f w)
        refine Continuous.mul (Continuous.mul ?_ (hK_cont_sub x)) hf_cont
        exact (continuous_const.sub continuous_id).div_const (2 * t) |>.neg
      -- Bound: |Fy x w| ≤ M · |x-w|/(2t) · K t (x - w)
      -- Use that |x-w|/(2t) · K t (x-w) is integrable. We've shown this for "u · K" essentially.
      -- Construct via integrable_rpow_mul_exp_neg_mul_sq + translation.
      have h_int_aux : MeasureTheory.Integrable
          (fun w : ℝ => |x - w| / (2 * t) * K t (x - w)) MeasureTheory.volume := by
        -- Reduce to |u| · K t u integrable via translation.
        have h_inner_int : MeasureTheory.Integrable
            (fun u : ℝ => |u| / (2 * t) * K t u) MeasureTheory.volume := by
          unfold K
          have h_4t_pos : (0 : ℝ) < 1 / (4 * t) := by positivity
          -- |u|/(2t) * ((4πt)^{-1/2} * exp(-u²/(4t))) = C * |u| * exp(-u²/(4t))
          have h_rewrite : (fun u : ℝ => |u| / (2 * t) *
                ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(u^2) / (4 * t)))) =
              (fun u : ℝ => (1 / (2 * t) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) *
                (|u| * Real.exp (-(1 / (4 * t)) * u^2))) := by
            funext u
            have : -(u^2) / (4 * t) = -(1 / (4 * t)) * u^2 := by field_simp
            rw [this]
            ring
          rw [h_rewrite]
          apply MeasureTheory.Integrable.const_mul
          -- |u| · exp(-(1/(4t))·u²) integrable: use |u · exp(-bu²)|
          have h_u_int : MeasureTheory.Integrable
              (fun u : ℝ => u^(1 : ℝ) * Real.exp (-(1 / (4 * t)) * u^2)) MeasureTheory.volume :=
            integrable_rpow_mul_exp_neg_mul_sq h_4t_pos (by norm_num : (-1 : ℝ) < 1)
          have h_eq : (fun u : ℝ => u^(1 : ℝ) * Real.exp (-(1 / (4 * t)) * u^2)) =
              (fun u : ℝ => u * Real.exp (-(1 / (4 * t)) * u^2)) := by
            funext u; rw [Real.rpow_one]
          rw [h_eq] at h_u_int
          have h_abs := h_u_int.norm
          have h_abs_eq : (fun u : ℝ => ‖u * Real.exp (-(1 / (4 * t)) * u^2)‖) =
              (fun u : ℝ => |u| * Real.exp (-(1 / (4 * t)) * u^2)) := by
            funext u
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
          rw [h_abs_eq] at h_abs
          exact h_abs
        -- Translate u = x - w
        have h_eq_translation : (fun w : ℝ => |x - w| / (2 * t) * K t (x - w)) =
            ((fun u : ℝ => |u| / (2 * t) * K t u) ∘ (fun w : ℝ => x - w)) := by
          funext w; rfl
        rw [h_eq_translation]
        exact h_inner_int.comp_sub_left x
      -- Bound by M · |x-w|/(2t) · K t (x-w) which is M times h_int_aux integrand.
      have h_int_M := h_int_aux.const_mul M
      refine h_int_M.mono' h_cont.aestronglyMeasurable ?_
      filter_upwards with w
      show ‖-((x - w) / (2 * t)) * K t (x - w) * f w‖ ≤
            M * (|x - w| / (2 * t) * K t (x - w))
      have h_K_nn : 0 ≤ K t (x - w) := by
        unfold K
        apply mul_nonneg
        · apply Real.rpow_nonneg; positivity
        · exact (Real.exp_pos _).le
      have hf_le : |f w| ≤ M := hM w
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
      have h_div : |(x - w) / (2 * t)| = |x - w| / (2 * t) := by
        rw [abs_div, abs_of_pos h2t_pos]
      rw [h_div, abs_of_nonneg h_K_nn]
      have h_nn : 0 ≤ |x - w| / (2 * t) * K t (x - w) := by positivity
      calc |x - w| / (2 * t) * K t (x - w) * |f w|
          ≤ |x - w| / (2 * t) * K t (x - w) * M := by gcongr
        _ = M * (|x - w| / (2 * t) * K t (x - w)) := by ring
    -- bound_integrable: (|x-w|+1)² + 2t = (x-w)² + 2|x-w| + 1 + 2t.
    -- Each of (x-w)² · exp, |x-w| · exp, exp is integrable (via translation).
    have bound2_integrable : MeasureTheory.Integrable bound2 MeasureTheory.volume := by
      simp only [hbound2_def]
      have h_8t_pos : (0 : ℝ) < 1 / (8 * t) := by positivity
      -- Integrable: exp(-u²/(8t))
      have h_g_int : MeasureTheory.Integrable
          (fun u : ℝ => Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_eq : (fun u : ℝ => Real.exp (-u^2 / (8 * t))) =
            (fun u : ℝ => Real.exp (-(1 / (8 * t)) * u^2)) := by
          funext u; congr 1; field_simp
        rw [h_eq]
        exact integrable_exp_neg_mul_sq h_8t_pos
      -- Integrable: |u| · exp(-u²/(8t))
      have h_abs_u_int : MeasureTheory.Integrable
          (fun u : ℝ => |u| * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_u_int : MeasureTheory.Integrable
            (fun u : ℝ => u^(1 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) MeasureTheory.volume :=
          integrable_rpow_mul_exp_neg_mul_sq h_8t_pos (by norm_num : (-1 : ℝ) < 1)
        have h_eq : (fun u : ℝ => u^(1 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) =
            (fun u : ℝ => u * Real.exp (-u^2 / (8 * t))) := by
          funext u; rw [Real.rpow_one]; congr 1; field_simp
        rw [h_eq] at h_u_int
        have h_norm := h_u_int.norm
        have h_norm_eq : (fun u : ℝ => ‖u * Real.exp (-u^2 / (8 * t))‖) =
            (fun u : ℝ => |u| * Real.exp (-u^2 / (8 * t))) := by
          funext u
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        rw [h_norm_eq] at h_norm
        exact h_norm
      -- Integrable: u² · exp(-u²/(8t))
      have h_sq_int : MeasureTheory.Integrable
          (fun u : ℝ => u^2 * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_u_int : MeasureTheory.Integrable
            (fun u : ℝ => u^(2 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) MeasureTheory.volume :=
          integrable_rpow_mul_exp_neg_mul_sq h_8t_pos (by norm_num : (-1 : ℝ) < 2)
        have h_eq : (fun u : ℝ => u^(2 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) =
            (fun u : ℝ => u^2 * Real.exp (-u^2 / (8 * t))) := by
          funext u
          have h_rpow : u^(2 : ℝ) = u^2 := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
          rw [h_rpow]
          congr 1; field_simp
        rw [h_eq] at h_u_int
        exact h_u_int
      -- (|u|+1)² + 2t = u² + 2|u| + 1 + 2t
      -- Each piece times exp(-u²/(8t)) integrable. Sum integrable.
      have h_poly_int : MeasureTheory.Integrable
          (fun u : ℝ => ((|u| + 1)^2 + 2 * t) * Real.exp (-u^2 / (8 * t)))
          MeasureTheory.volume := by
        have h_expand : (fun u : ℝ => ((|u| + 1)^2 + 2 * t) * Real.exp (-u^2 / (8 * t))) =
            (fun u : ℝ => u^2 * Real.exp (-u^2 / (8 * t)) +
                          2 * |u| * Real.exp (-u^2 / (8 * t)) +
                          (1 + 2 * t) * Real.exp (-u^2 / (8 * t))) := by
          funext u
          have h_u2 : |u|^2 = u^2 := sq_abs u
          have : (|u| + 1)^2 + 2 * t = u^2 + 2 * |u| + 1 + 2 * t := by
            rw [add_sq, h_u2]; ring
          rw [this]; ring
        rw [h_expand]
        have h2 : MeasureTheory.Integrable
            (fun u : ℝ => 2 * |u| * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
          have := h_abs_u_int.const_mul 2
          convert this using 1; funext u; ring
        have h3 : MeasureTheory.Integrable
            (fun u : ℝ => (1 + 2 * t) * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
          exact h_g_int.const_mul (1 + 2 * t)
        exact (h_sq_int.add h2).add h3
      -- Translate u = x - w
      have h_poly_int_w : MeasureTheory.Integrable
          (fun w : ℝ => ((|x - w| + 1)^2 + 2 * t) * Real.exp (-(x - w)^2 / (8 * t)))
          MeasureTheory.volume := by
        have h_eq : (fun w : ℝ => ((|x - w| + 1)^2 + 2 * t) * Real.exp (-(x - w)^2 / (8 * t))) =
            ((fun u : ℝ => ((|u| + 1)^2 + 2 * t) * Real.exp (-u^2 / (8 * t))) ∘
              (fun w : ℝ => x - w)) := by
          funext w; rfl
        rw [h_eq]
        exact h_poly_int.comp_sub_left x
      -- Final: bound2 = const · h_poly_int_w
      have hC2 : ∀ w : ℝ,
          M * ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) *
            (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
            Real.exp (-(x - w)^2 / (8 * t)) =
          (M / (4 * t^2) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t))) *
            (((|x - w| + 1)^2 + 2 * t) * Real.exp (-(x - w)^2 / (8 * t))) := by
        intro w; ring
      simp_rw [hC2]
      exact h_poly_int_w.const_mul _
    -- h_bound: ‖F'y y w‖ ≤ bound2 w for y ∈ Ioo(x-1, x+1).
    have h_bound2 : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y ∈ Set.Ioo (x - 1) (x + 1), ‖F'y y w‖ ≤ bound2 w := by
      filter_upwards with w
      intro y hy
      simp only [hF'y_def, hbound2_def, Set.mem_Ioo] at hy ⊢
      have hxy : |y - x| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      have h_yw_xw : |y - w| ≤ |x - w| + 1 := by
        have h_eq : y - w = (x - w) + (y - x) := by ring
        rw [h_eq]
        calc |(x - w) + (y - x)| ≤ |x - w| + |y - x| := abs_add_le _ _
          _ ≤ |x - w| + 1 := by linarith [hxy.le]
      -- (y-w)² ≥ (x-w)²/2 - 1
      have h_sq_lb : (x - w)^2 / 2 - 1 ≤ (y - w)^2 := by
        have hxy' : (y - x)^2 < 1 := by
          have := abs_lt.mp hxy
          nlinarith
        have h_expand : (y - w)^2 = (x - w)^2 + 2 * (x - w) * (y - x) + (y - x)^2 := by ring
        nlinarith [sq_nonneg (x - w + 2 * (y - x)), hxy'.le, h_expand]
      -- (y-w)² ≤ (|x-w| + 1)²
      have h_sq_ub : (y - w)^2 ≤ (|x - w| + 1)^2 := by
        have h_abs_sq : (y - w)^2 = |y - w|^2 := (sq_abs _).symm
        rw [h_abs_sq]
        apply sq_le_sq' _ h_yw_xw
        have h_yw_nn : 0 ≤ |y - w| := abs_nonneg _
        have h_xw_nn : 0 ≤ |x - w| + 1 := by positivity
        linarith
      -- K t (y - w) ≤ (4πt)^{-1/2} · exp(1/(4t)) · exp(-(x-w)²/(8t))
      have h_K_bound : K t (y - w) ≤
          (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
            Real.exp (-(x - w)^2 / (8 * t)) := by
        unfold K
        have hC_pos : (0 : ℝ) < (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) := by
          apply Real.rpow_pos_of_pos; positivity
        have h_exp_arg : -((y - w)^2) / (4 * t) ≤ -((x - w)^2 / 2 - 1) / (4 * t) := by
          rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * t)]
          linarith
        have h_exp_bound :
            Real.exp (-((y - w)^2) / (4 * t)) ≤
              Real.exp (-((x - w)^2 / 2 - 1) / (4 * t)) :=
          Real.exp_le_exp.mpr h_exp_arg
        have h_split : -((x - w)^2 / 2 - 1) / (4 * t) =
            1 / (4 * t) + (-(x - w)^2 / (8 * t)) := by
          field_simp; ring
        rw [h_split, Real.exp_add] at h_exp_bound
        calc (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(y - w)^2 / (4 * t))
            ≤ (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
                (Real.exp (1 / (4 * t)) * Real.exp (-(x - w)^2 / (8 * t))) := by
              gcongr
          _ = (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
                Real.exp (-(x - w)^2 / (8 * t)) := by ring
      -- |((y-w)² - 2t)/(4t²)| ≤ ((|x-w|+1)² + 2t)/(4t²)
      have h_4t2_pos : (0 : ℝ) < 4 * t^2 := by positivity
      have h_poly_bound : |((y - w)^2 - 2 * t) / (4 * t^2)| ≤
          ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) := by
        rw [abs_div, abs_of_pos h_4t2_pos]
        apply div_le_div_of_nonneg_right _ h_4t2_pos.le
        calc |(y - w)^2 - 2 * t| ≤ (y - w)^2 + 2 * t := by
              rcases le_or_gt ((y - w)^2 - 2 * t) 0 with h | h
              · rw [abs_of_nonpos h]; nlinarith [sq_nonneg (y - w)]
              · rw [abs_of_pos h]; linarith [ht.le]
          _ ≤ (|x - w| + 1)^2 + 2 * t := by linarith
      -- Combine
      have h_K_nn : 0 ≤ K t (y - w) := by
        unfold K
        apply mul_nonneg
        · apply Real.rpow_nonneg; positivity
        · exact (Real.exp_pos _).le
      have h_fw_le : |f w| ≤ M := hM w
      have h_RHS_nn : 0 ≤ ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) := by positivity
      calc ‖((y - w)^2 - 2 * t) / (4 * t^2) * K t (y - w) * f w‖
          = |((y - w)^2 - 2 * t) / (4 * t^2)| * K t (y - w) * |f w| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h_K_nn]
        _ ≤ ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) * K t (y - w) * M := by
            gcongr
        _ ≤ ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) *
              ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
                Real.exp (-(x - w)^2 / (8 * t))) * M := by gcongr
        _ = M * ((|x - w| + 1)^2 + 2 * t) / (4 * t^2) *
              (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
              Real.exp (-(x - w)^2 / (8 * t)) := by ring
    -- Apply diff-under-integral.
    have h_apply2 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs hF_meas hF_int hF'_meas h_bound2 bound2_integrable h_diff
    -- Goal: HasDerivAt ux uxx x
    -- ux y = ∫ z, -((y - z)/(2t)) · K t (y - z) · f z = ∫ z, Fy y z
    -- uxx = ∫ z, ((x - z)² - 2t)/(4t²) · K t (x - z) · f z = ∫ z, F'y x z
    -- h_apply2.2 gives HasDerivAt (fun y => ∫ z, Fy y z) (∫ z, F'y x z) x — exactly what we need.
    exact h_apply2.2
  · -- HasDerivAt of t-slice at t giving uxx (heat equation: ∂_t = ∂_x²).
    -- Goal: HasDerivAt (fun s => heatSolution f s x)
    --                  (∫ z, ((x - z)^2 - 2 * t) / (4 * t^2) * K t (x - z) * f z) t
    -- Strategy: rewrite as integral and apply diff-under-integral with K_hasDerivAt_temporal.
    set Gs := fun (s : ℝ) (w : ℝ) => K s (x - w) * f w with hGs_def
    set G's := fun (s : ℝ) (w : ℝ) =>
      ((x - w)^2 - 2 * s) / (4 * s^2) * K s (x - w) * f w with hG's_def
    set bound3 : ℝ → ℝ := fun w =>
      M * ((x - w)^2 + 3 * t) / t^2 *
        (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
        Real.exp (-(x - w)^2 / (8 * t)) with hbound3_def
    have ht_half : (0 : ℝ) < t / 2 := by linarith
    -- s-neighborhood
    have hs_nbhd : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t :=
      Ioo_mem_nhds (by linarith) (by linarith)
    -- HasDerivAt of integrand at every s ∈ Ioo (t/2) (3t/2), every w.
    have h_diff : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2),
          HasDerivAt (fun s => Gs s w) (G's s w) s := by
      filter_upwards with w
      intro s hs
      have hs_pos : 0 < s := by
        simp only [Set.mem_Ioo] at hs; linarith
      show HasDerivAt (fun s => K s (x - w) * f w)
        (((x - w)^2 - 2 * s) / (4 * s^2) * K s (x - w) * f w) s
      have h_K := K_hasDerivAt_temporal hs_pos (x - w)
      exact h_K.mul_const (f w)
    -- Continuity of fun w => K s (x - w) for fixed s.
    have hK_cont_w : ∀ s₀ : ℝ, Continuous (fun w : ℝ => K s₀ (x - w)) := fun s₀ => by
      unfold K
      refine Continuous.mul continuous_const ?_
      refine Real.continuous_exp.comp ?_
      refine Continuous.div_const ?_ (4 * s₀)
      exact ((continuous_const.sub continuous_id).pow 2).neg
    -- hF_meas
    have hF_meas : ∀ᶠ s in 𝓝 t,
        MeasureTheory.AEStronglyMeasurable (Gs s) MeasureTheory.volume := by
      filter_upwards with s
      exact ((hK_cont_w s).mul hf_cont).aestronglyMeasurable
    -- hF'_meas
    have hF'_meas : MeasureTheory.AEStronglyMeasurable (G's t) MeasureTheory.volume := by
      have h_cont : Continuous (fun w => G's t w) := by
        show Continuous (fun w => ((x - w)^2 - 2 * t) / (4 * t^2) *
                                  K t (x - w) * f w)
        refine Continuous.mul (Continuous.mul ?_ (hK_cont_w t)) hf_cont
        refine Continuous.div_const ?_ (4 * t^2)
        exact ((continuous_const.sub continuous_id).pow 2).sub continuous_const
      exact h_cont.aestronglyMeasurable
    -- hF_int : Gs t = K t (x - ·) · f integrable.
    have hF_int : MeasureTheory.Integrable (Gs t) MeasureTheory.volume := by
      show MeasureTheory.Integrable (fun w => K t (x - w) * f w) MeasureTheory.volume
      have hK_int : MeasureTheory.Integrable (fun u => K t u) MeasureTheory.volume := by
        unfold K
        apply MeasureTheory.Integrable.const_mul
        have h_eq : (fun u : ℝ => Real.exp (-(u^2) / (4 * t))) =
            (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u^2)) := by
          funext u; congr 1; field_simp
        rw [h_eq]
        exact integrable_exp_neg_mul_sq (by positivity)
      have hK_x_int : MeasureTheory.Integrable
          (fun w => K t (x - w)) MeasureTheory.volume := hK_int.comp_sub_left x
      have h_swap : (fun w : ℝ => K t (x - w) * f w) = (fun w => f w * K t (x - w)) := by
        funext w; ring
      rw [h_swap]
      refine hK_x_int.bdd_mul (c := M) hf_cont.aestronglyMeasurable ?_
      filter_upwards with w using by rw [Real.norm_eq_abs]; exact hM w
    -- h_bound : ‖G's s w‖ ≤ bound3 w for s ∈ Ioo (t/2) (3t/2).
    have h_bound : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), ‖G's s w‖ ≤ bound3 w := by
      filter_upwards with w
      intro s hs
      simp only [hG's_def, hbound3_def, Set.mem_Ioo] at hs ⊢
      have hs_pos : 0 < s := by linarith
      have hs_lb : t / 2 ≤ s := hs.1.le
      have hs_ub : s ≤ 3 * t / 2 := hs.2.le
      -- K s (x - w) ≤ (2πt)^{-1/2} · exp(-(x-w)²/(8t))
      have h_4πs_pos : (0 : ℝ) < 4 * Real.pi * s := by positivity
      have h_2πt_pos : (0 : ℝ) < 2 * Real.pi * t := by positivity
      have h_4s_pos : (0 : ℝ) < 4 * s := by linarith
      have h_8t_pos : (0 : ℝ) < 8 * t := by linarith
      have h_4s_le_8t : 4 * s ≤ 8 * t := by linarith
      have h_2πt_le_4πs : 2 * Real.pi * t ≤ 4 * Real.pi * s := by
        have h_2t_le : (2 : ℝ) * t ≤ 4 * s := by linarith
        nlinarith [Real.pi_pos.le]
      have h_inv_le : (4 * Real.pi * s)⁻¹ ≤ (2 * Real.pi * t)⁻¹ := by
        rw [inv_le_inv₀ h_4πs_pos h_2πt_pos]; exact h_2πt_le_4πs
      have h_rpow_le : (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) ≤
          (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (inv_nonneg.mpr h_4πs_pos.le) h_inv_le (by norm_num)
      have h_div_le : (x - w)^2 / (8 * t) ≤ (x - w)^2 / (4 * s) :=
        div_le_div_of_nonneg_left (sq_nonneg _) h_4s_pos h_4s_le_8t
      have h_exp_arg_le : -(x - w)^2 / (4 * s) ≤ -(x - w)^2 / (8 * t) := by
        have h1 : -(x - w)^2 / (4 * s) = -((x - w)^2 / (4 * s)) := by ring
        have h2 : -(x - w)^2 / (8 * t) = -((x - w)^2 / (8 * t)) := by ring
        rw [h1, h2]; linarith
      have h_exp_le : Real.exp (-(x - w)^2 / (4 * s)) ≤
          Real.exp (-(x - w)^2 / (8 * t)) := Real.exp_le_exp.mpr h_exp_arg_le
      have h_K_bound : K s (x - w) ≤
          (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
            Real.exp (-(x - w)^2 / (8 * t)) := by
        unfold K
        have h_rpow_nn : 0 ≤ (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) :=
          Real.rpow_nonneg (inv_nonneg.mpr h_4πs_pos.le) _
        calc (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(x - w)^2 / (4 * s))
            ≤ (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
                Real.exp (-(x - w)^2 / (4 * s)) := by gcongr
          _ ≤ (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
                Real.exp (-(x - w)^2 / (8 * t)) := by gcongr
      -- |(x-w)² - 2s|/(4s²) ≤ ((x-w)² + 3t)/t²
      have h_4s2_pos : (0 : ℝ) < 4 * s^2 := by positivity
      have h_t2_pos : (0 : ℝ) < t^2 := by positivity
      have h_t2_le_4s2 : t^2 ≤ 4 * s^2 := by nlinarith [hs_lb, ht.le]
      have h_num_bound : |(x - w)^2 - 2 * s| ≤ (x - w)^2 + 3 * t := by
        rcases le_or_gt ((x - w)^2 - 2 * s) 0 with h | h
        · rw [abs_of_nonpos h]
          linarith [sq_nonneg (x - w), hs_ub]
        · rw [abs_of_pos h]; linarith
      have h_num_nn : 0 ≤ (x - w)^2 + 3 * t :=
        by linarith [sq_nonneg (x - w), ht.le]
      have h_frac_bound : |(x - w)^2 - 2 * s| / (4 * s^2) ≤
          ((x - w)^2 + 3 * t) / t^2 := by
        rw [div_le_div_iff₀ h_4s2_pos h_t2_pos]
        calc |(x - w)^2 - 2 * s| * t^2
            ≤ ((x - w)^2 + 3 * t) * t^2 :=
              mul_le_mul_of_nonneg_right h_num_bound h_t2_pos.le
          _ ≤ ((x - w)^2 + 3 * t) * (4 * s^2) :=
              mul_le_mul_of_nonneg_left h_t2_le_4s2 h_num_nn
      have h_K_nn : 0 ≤ K s (x - w) := by
        unfold K
        apply mul_nonneg
        · apply Real.rpow_nonneg; positivity
        · exact (Real.exp_pos _).le
      have h_fw_le : |f w| ≤ M := hM w
      have h_RHS_nn : 0 ≤ ((x - w)^2 + 3 * t) / t^2 :=
        div_nonneg h_num_nn h_t2_pos.le
      have h_bound_K_nn : (0 : ℝ) ≤ (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
          Real.exp (-(x - w)^2 / (8 * t)) := by positivity
      calc ‖((x - w)^2 - 2 * s) / (4 * s^2) * K s (x - w) * f w‖
          = |(x - w)^2 - 2 * s| / (4 * s^2) * K s (x - w) * |f w| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos h_4s2_pos]
            rw [abs_of_nonneg h_K_nn]
        _ ≤ ((x - w)^2 + 3 * t) / t^2 * K s (x - w) * M := by gcongr
        _ ≤ ((x - w)^2 + 3 * t) / t^2 *
              ((2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
                Real.exp (-(x - w)^2 / (8 * t))) * M := by gcongr
        _ = M * ((x - w)^2 + 3 * t) / t^2 *
              (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
              Real.exp (-(x - w)^2 / (8 * t)) := by ring
    -- bound3 integrable
    have bound3_integrable : MeasureTheory.Integrable bound3 MeasureTheory.volume := by
      simp only [hbound3_def]
      have h_8t_pos : (0 : ℝ) < 1 / (8 * t) := by positivity
      have h_g_int : MeasureTheory.Integrable
          (fun u : ℝ => Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_eq : (fun u : ℝ => Real.exp (-u^2 / (8 * t))) =
            (fun u : ℝ => Real.exp (-(1 / (8 * t)) * u^2)) := by
          funext u; congr 1; field_simp
        rw [h_eq]
        exact integrable_exp_neg_mul_sq h_8t_pos
      have h_sq_int : MeasureTheory.Integrable
          (fun u : ℝ => u^2 * Real.exp (-u^2 / (8 * t))) MeasureTheory.volume := by
        have h_u_int : MeasureTheory.Integrable
            (fun u : ℝ => u^(2 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) MeasureTheory.volume :=
          integrable_rpow_mul_exp_neg_mul_sq h_8t_pos (by norm_num : (-1 : ℝ) < 2)
        have h_eq : (fun u : ℝ => u^(2 : ℝ) * Real.exp (-(1 / (8 * t)) * u^2)) =
            (fun u : ℝ => u^2 * Real.exp (-u^2 / (8 * t))) := by
          funext u
          have h_rpow : u^(2 : ℝ) = u^2 := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
          rw [h_rpow]; congr 1; field_simp
        rw [h_eq] at h_u_int
        exact h_u_int
      have h_poly_int : MeasureTheory.Integrable
          (fun u : ℝ => (u^2 + 3 * t) * Real.exp (-u^2 / (8 * t)))
          MeasureTheory.volume := by
        have h_expand : (fun u : ℝ => (u^2 + 3 * t) * Real.exp (-u^2 / (8 * t))) =
            (fun u : ℝ => u^2 * Real.exp (-u^2 / (8 * t)) +
                          3 * t * Real.exp (-u^2 / (8 * t))) := by
          funext u; ring
        rw [h_expand]
        exact h_sq_int.add (h_g_int.const_mul (3 * t))
      have h_poly_int_w : MeasureTheory.Integrable
          (fun w : ℝ => ((x - w)^2 + 3 * t) * Real.exp (-(x - w)^2 / (8 * t)))
          MeasureTheory.volume := by
        have h_eq : (fun w : ℝ => ((x - w)^2 + 3 * t) * Real.exp (-(x - w)^2 / (8 * t))) =
            ((fun u : ℝ => (u^2 + 3 * t) * Real.exp (-u^2 / (8 * t))) ∘
              (fun w : ℝ => x - w)) := by funext w; rfl
        rw [h_eq]
        exact h_poly_int.comp_sub_left x
      have hC3 : ∀ w : ℝ,
          M * ((x - w)^2 + 3 * t) / t^2 *
            (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
            Real.exp (-(x - w)^2 / (8 * t)) =
          (M / t^2 * (2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) *
            (((x - w)^2 + 3 * t) * Real.exp (-(x - w)^2 / (8 * t))) := by
        intro w; ring
      simp_rw [hC3]
      exact h_poly_int_w.const_mul _
    -- Apply diff-under-integral.
    have h_apply3 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nbhd hF_meas hF_int hF'_meas h_bound bound3_integrable h_diff
    -- h_apply3.2 : HasDerivAt (fun s => ∫ w, Gs s w) (∫ w, G's t w) t
    -- Translate to heatSolution via heatSolution_eq_integral on s > 0.
    have h_eventually : (fun s => heatSolution f s x) =ᶠ[𝓝 t]
        (fun s => ∫ w, K s (x - w) * f w) := by
      filter_upwards [Ioi_mem_nhds ht] with s' hs'
      exact heatSolution_eq_integral f hs' x
    exact (h_apply3.2).congr_of_eventuallyEq h_eventually

/-- The main heat-equation theorem. -/
theorem heat_kernel_solves_heat_equation
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    (∀ x : ℝ,
        Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  refine ⟨?_, ?_⟩
  · intro t ht x
    exact pde_solved_at f hf_cont hf_bdd ht x
  · intro x
    exact tendsto_heatSolution_at_zero f hf_cont hf_bdd x

end Submission.Helpers
