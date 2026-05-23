/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: heat_kernel_solves_heat_equation
user: daouid
model: Antigravity (Multi-Model Ensemble: Gemini 3.1 Pro, Gemini 3 Flash, Claude 4.6 Sonnet/Opus)
submission_repo: daouid/lean-eval
submission_ref: be5ca99521362ea9131eca9a2d95d91ec6fff0f4
issue_number: 245
-/
import ChallengeDeps

open LeanEval.Analysis.ODE Real MeasureTheory Filter Topology

set_option maxHeartbeats 3200000

namespace Submission


-- ═══════════════════════════════════════════════════════════════════
-- 1. Basic helpers
-- ═══════════════════════════════════════════════════════════════════

private lemma continuous_kernel (t x : ℝ) :
    Continuous (fun y => rexp (-((x - y) ^ 2) / (4 * t))) :=
  continuous_exp.comp ((continuous_sub_left x |>.pow 2).neg.div_const _)

private lemma aestronglyMeasurable_integrand (f : ℝ → ℝ) (hf : Continuous f)
    (t x : ℝ) :
    AEStronglyMeasurable (fun y => rexp (-((x - y) ^ 2) / (4 * t)) * f y)
      volume :=
  ((continuous_kernel t x).mul hf).aestronglyMeasurable

-- ═══════════════════════════════════════════════════════════════════
-- 2. Integrability lemmas
-- ═══════════════════════════════════════════════════════════════════

private lemma integrable_integrand (f : ℝ → ℝ) (hf : Continuous f) (t x : ℝ)
    (ht : 0 < t) (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    Integrable (fun y => rexp (-((x - y) ^ 2) / (4 * t)) * f y) volume := by
  apply Integrable.mono'
    (g := fun y => M * rexp (-(4 * t)⁻¹ * (x - y) ^ 2))
  · exact ((integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*t)⁻¹)).comp_sub_left x).const_mul M
  · exact aestronglyMeasurable_integrand f hf t x
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_nonneg _)]
    calc rexp (-((x - y) ^ 2) / (4 * t)) * |f y|
        ≤ rexp (-((x - y) ^ 2) / (4 * t)) * M :=
        mul_le_mul_of_nonneg_left (hM y) (exp_nonneg _)
      _ = M * rexp (-(4 * t)⁻¹ * (x - y) ^ 2) := by ring_nf

-- ═══════════════════════════════════════════════════════════════════
-- 3. Derivative of integrand w.r.t. spatial variable
-- ═══════════════════════════════════════════════════════════════════

private lemma hasDerivAt_integrand_x (f : ℝ → ℝ) (t y z : ℝ) :
    HasDerivAt (fun x => rexp (-((x - y) ^ 2) / (4 * t)) * f y)
      (rexp (-((z - y) ^ 2) / (4 * t)) * (-(2 * (z - y)) / (4 * t)) * f y)
      z := by
  have h1 : HasDerivAt (fun x => -((x - y) ^ 2) / (4 * t))
      (-(2 * (z - y)) / (4 * t)) z := by
    apply HasDerivAt.div_const; apply HasDerivAt.neg
    have := ((hasDerivAt_id z).sub_const y).pow 2; simp at this; exact this
  exact h1.exp.mul_const _

-- ═══════════════════════════════════════════════════════════════════
-- 4. Spatial derivative via differentiation under integral
-- ═══════════════════════════════════════════════════════════════════

private lemma spatial_deriv_integral (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ)
    (ht : 0 < t) (M : ℝ) (hM : ∀ y, |f y| ≤ M) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y, rexp (-((x - y) ^ 2) / (4 * t)) * f y)
      (∫ y, rexp (-((x₀ - y) ^ 2) / (4 * t)) *
        (-(2 * (x₀ - y)) / (4 * t)) * f y) x₀ := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
  have hb : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y => rexp (-((x - y) ^ 2) / (4 * t)) * f y)
    (F' := fun x y => rexp (-((x - y) ^ 2) / (4 * t)) *
      (-(2 * (x - y)) / (4 * t)) * f y)
    (bound := fun y => M * rexp ((4 * t)⁻¹) / (2 * t) *
      (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2))
    (x₀ := x₀)
    (s := Set.Ioo (x₀ - 1) (x₀ + 1))
    (μ := volume)
    -- (1) s ∈ nhds x₀
    (Ioo_mem_nhds (by linarith) (by linarith))
    -- (2) AEStronglyMeasurable F(x) for x near x₀
    (by filter_upwards with z; exact aestronglyMeasurable_integrand f hf t z)
    -- (3) Integrable F(x₀)
    (integrable_integrand f hf t x₀ ht M hM)
    -- (4) AEStronglyMeasurable F'(x₀)
    (by -- AEStronglyMeasurable F'(x₀)
      show AEStronglyMeasurable
        (fun y => rexp (-((x₀ - y) ^ 2) / (4 * t)) *
          (-(2 * (x₀ - y)) / (4 * t)) * f y) volume
      apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · exact (continuous_kernel t x₀).aestronglyMeasurable
        · apply Continuous.aestronglyMeasurable
          apply Continuous.div_const
          apply Continuous.neg
          exact (continuous_sub_left x₀).const_mul 2
      · exact hf.aestronglyMeasurable)
    -- (5) ‖F'(x, y)‖ ≤ bound(y) for x ∈ s, a.e. y
    (by filter_upwards with y
        intro x hx
        -- where g = -(x-y)²/(4t), h = -(2(x-y))/(4t)
        rw [Real.norm_eq_abs]
        -- Step 1: Break into factors
        have hxs : |x - x₀| < 1 := by
          rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
        -- |exp * h * f(y)| = exp(...) * |-(2(x-y))/(4t)| * |f(y)|
        rw [abs_mul, abs_mul, abs_of_nonneg (exp_nonneg _)]
        -- Need: exp(-(x-y)²/(4t)) * |-(2(x-y))/(4t)| * |f(y)| ≤ bound
        -- Step 2: Bound |f(y)| ≤ M
        calc rexp (-(x - y) ^ 2 / (4 * t)) * |-(2 * (x - y)) / (4 * t)| * |f y|
            ≤ rexp (-(x - y) ^ 2 / (4 * t)) * |-(2 * (x - y)) / (4 * t)| * M := by
              apply mul_le_mul_of_nonneg_left (hM y)
              apply mul_nonneg (exp_nonneg _) (abs_nonneg _)
          -- Step 3: Bound |-(2(x-y))/(4t)| = |x-y|/(2t)
          -- and |x-y| ≤ |x₀-y| + |x-x₀| ≤ |x₀-y| + 1
          _ ≤ rexp (-(x - y) ^ 2 / (4 * t)) * ((|x₀ - y| + 1) / (2 * t)) * M := by
              apply mul_le_mul_of_nonneg_right _ hM0
              apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
              -- |-(2(x-y))/(4t)| = 2*|x-y|/(4t) = |x-y|/(2t) ≤ (|x₀-y|+1)/(2t)
              rw [abs_div, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
                abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * t)]
              rw [show (2 : ℝ) * |x - y| / (4 * t) = |x - y| / (2 * t) by ring]
              apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < 2 * t).le
              calc |x - y| = |(x₀ - y) + (x - x₀)| := by ring_nf
                _ ≤ |x₀ - y| + |x - x₀| := abs_add_le _ _
                _ ≤ |x₀ - y| + 1 := by linarith [hxs.le]
          -- Step 4: Bound exp(-(x-y)²/(4t)) ≤ exp(1/(4t)) * exp(-(x₀-y)²/(8t))
          -- This uses: (x-y)² ≥ (x₀-y)²/2 - 1
          _ ≤ rexp ((4 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) *
              ((|x₀ - y| + 1) / (2 * t)) * M := by
              apply mul_le_mul_of_nonneg_right _ hM0
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              -- exp(-(x-y)²/(4t)) ≤ exp(1/(4t)) * exp(-(x₀-y)²/(8t))
              -- ⟺ exp(-(x-y)²/(4t)) ≤ exp(1/(4t) - (x₀-y)²/(8t))
              rw [← Real.exp_add]
              apply Real.exp_le_exp_of_le
              -- Need: -(x-y)²/(4t) ≤ (4t)⁻¹ - (8t)⁻¹*(x₀-y)²
              calc -(x - y) ^ 2 / (4 * t)
                = (-(x - y) ^ 2 * 2) / (8 * t) := by ring
                _ ≤ (2 - (x₀ - y) ^ 2) / (8 * t) := by
                  apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 8 * t)
                  -- (x₀-y)² - 2(x-y)² ≤ 2
                  -- Let a = x₀-y, δ = x-x₀, so x-y = a + δ, |δ| < 1
                  -- a² - 2(a+δ)² = - (a + 2δ)² + 2δ² ≤ 2δ² ≤ 2
                  have : (x₀ - y) ^ 2 - 2 * (x - y) ^ 2 ≤ 2 := by
                    have h1 : -1 ≤ x - x₀ := by linarith [hx.1]
                    have h2 : x - x₀ ≤ 1 := by linarith [hx.2]
                    have hs : (x - x₀) ^ 2 ≤ 1 := by nlinarith [h1, h2]
                    have hs2 : 0 ≤ ((x₀ - y) + 2 * (x - x₀)) ^ 2 := sq_nonneg _
                    nlinarith
                  linarith
                _ = (4 * t)⁻¹ + -(8 * t)⁻¹ * (x₀ - y) ^ 2 := by ring
          _ = M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) *
              rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by ring)
    -- (6) Integrable bound
    (by -- bound(y) = M*exp(1/(4t))/(2t) * (|x₀-y|+1) * exp(-(8t)⁻¹*(x₀-y)²)
        -- = constant * [(|x₀-y|+1) * exp(-(8t)⁻¹*(x₀-y)²)]
        have h8 : (0:ℝ) < (8*t)⁻¹ := by positivity
        -- First show (|a|+1)*exp(-c*a²) is integrable (with translation)
        have habs : Integrable (fun y : ℝ => |x₀ - y| * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2))
            volume := by
          have h := (integrable_rpow_mul_exp_neg_mul_sq h8
            (s := 1) (by norm_num : (-1:ℝ) < 1)).norm.comp_sub_left x₀
          convert h using 1; ext y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_nonneg _)]
          simp [pow_succ, pow_zero, abs_mul]
        have hone : Integrable (fun y : ℝ => (1 : ℝ) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2))
            volume := by
          simpa using (integrable_exp_neg_mul_sq h8).comp_sub_left x₀
        have hsum : Integrable (fun y => (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2))
            volume := by
          have : (fun y => (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
              fun y => |x₀ - y| * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) +
                1 * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by ext y; ring
          rw [this]; exact habs.add hone
        -- Now the bound is C * [(|x₀-y|+1) * exp(-c*(x₀-y)²)] where C = M*exp(1/(4t))/(2t)
        -- Need to show the whole thing is integrable
        show Integrable (fun y => M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) *
          rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume
        have : (fun y => M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) *
            rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
          fun y => (M * rexp (4 * t)⁻¹ / (2 * t)) *
            ((|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) := by ext y; ring
        rw [this]
        exact hsum.const_mul _)
    -- (7) HasDerivAt for a.e. y and x ∈ s
    (by filter_upwards with y; intro x _; exact hasDerivAt_integrand_x f t y x)
  exact key.2

private lemma hasDerivAt_heatSolution_x (f : ℝ → ℝ) (hf : Continuous f)
    (t : ℝ) (ht : 0 < t) (M : ℝ) (hM : ∀ y, |f y| ≤ M) (x₀ : ℝ) :
    HasDerivAt (fun z => heatSolution f t z)
      ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
        ∫ y, rexp (-((x₀ - y) ^ 2) / (4 * t)) *
          (-(2 * (x₀ - y)) / (4 * t)) * f y) x₀ := by
  have key : (fun z => heatSolution f t z) =
      fun z => (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
        ∫ y, rexp (-((z - y) ^ 2) / (4 * t)) * f y := by
    ext z; simp [heatSolution, ht]
  rw [key]
  exact (spatial_deriv_integral f hf t ht M hM x₀).const_mul _

-- ═══════════════════════════════════════════════════════════════════
-- 5. Second spatial derivative
-- ═══════════════════════════════════════════════════════════════════

private lemma hasDerivAt_deriv_integrand_x (f : ℝ → ℝ) (t y z : ℝ)
    (ht : 0 < t) :
    HasDerivAt
      (fun x => rexp (-((x - y) ^ 2) / (4 * t)) *
        (-(2 * (x - y)) / (4 * t)) * f y)
      (rexp (-((z - y) ^ 2) / (4 * t)) *
        ((-(2 * (z - y)) / (4 * t)) ^ 2 + (-2 / (4 * t))) * f y)
      z := by
  -- This is d/dx [exp(g(x)) * h(x) * f(y)]
  -- where g(x) = -(x-y)²/(4t), h(x) = -(2(x-y))/(4t)
  -- = [exp(g) * g' * h + exp(g) * h'] * f(y)
  -- = exp(g) * (g'*h + h') * f(y)
  -- = exp(g) * (h² + (-2/(4t))) * f(y)
  have h4t : (4 : ℝ) * t ≠ 0 := by positivity
  -- g and its derivative
  have hg : HasDerivAt (fun x => -((x - y) ^ 2) / (4 * t))
      (-(2 * (z - y)) / (4 * t)) z := by
    apply HasDerivAt.div_const; apply HasDerivAt.neg
    have := ((hasDerivAt_id z).sub_const y).pow 2; simp at this; exact this
  -- exp(g) and its derivative
  have hexp := hg.exp
  -- h and its derivative: h(x) = -(2*(x-y))/(4t), h'(x) = -2/(4t)
  have hh : HasDerivAt (fun x => -(2 * (x - y)) / (4 * t))
      (-2 / (4 * t)) z := by
    apply HasDerivAt.div_const; apply HasDerivAt.neg
    have h1 : HasDerivAt (fun x => x - y) 1 z := (hasDerivAt_id z).sub_const y
    have h2 : HasDerivAt (fun x => 2 * (x - y)) (2 * 1) z :=
      h1.const_mul 2
    simpa using h2
  -- Product rule for exp(g) * h
  have hprod := hexp.mul hh
  -- hprod : HasDerivAt (fun x => exp(g(x)) * h(x))
  --   (exp(g(z)) * g'(z) * h(z) + exp(g(z)) * h'(z)) z
  -- = (exp(g(z)) * (g'(z) * h(z) + h'(z))) z
  -- Note: g'(z) = h(z), so g'(z) * h(z) = h(z)²
  -- Multiply by constant f(y)
  have hfinal := hprod.mul_const (f y)
  -- hfinal has derivative (exp(g) * g' * h + exp(g) * h') * f(y)
  -- = (exp(g) * (-(2(z-y))/(4t)) * (-(2(z-y))/(4t)) + exp(g) * (-2/(4t))) * f(y)
  -- We need: exp(g) * (h² + h') * f(y)
  convert hfinal using 1
  ring

private lemma spatial_deriv2_integral (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ)
    (ht : 0 < t) (M : ℝ) (hM : ∀ y, |f y| ≤ M) (x₀ : ℝ) :
    HasDerivAt
      (fun x => ∫ y, rexp (-((x - y) ^ 2) / (4 * t)) *
        (-(2 * (x - y)) / (4 * t)) * f y)
      (∫ y, rexp (-((x₀ - y) ^ 2) / (4 * t)) *
        ((-(2 * (x₀ - y)) / (4 * t)) ^ 2 + (-2 / (4 * t))) * f y)
      x₀ := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y => rexp (-((x - y) ^ 2) / (4 * t)) * (-(2 * (x - y)) / (4 * t)) * f y)
    (F' := fun x y => rexp (-((x - y) ^ 2) / (4 * t)) *
      ((-(2 * (x - y)) / (4 * t)) ^ 2 + (-2 / (4 * t))) * f y)
    (bound := fun y => M * rexp ((4 * t)⁻¹) * (((|x₀ - y| + 1) ^ 2 / (4 * t ^ 2)) + (2 * t)⁻¹) *
      rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2))
    (x₀ := x₀)
    (s := Set.Ioo (x₀ - 1) (x₀ + 1))
    (μ := volume)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (by -- AEStronglyMeasurable F(x)
      filter_upwards with z
      show AEStronglyMeasurable (fun y => rexp (-((z - y) ^ 2) / (4 * t)) *
        (-(2 * (z - y)) / (4 * t)) * f y) volume
      apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · exact (continuous_kernel t z).aestronglyMeasurable
        · apply Continuous.aestronglyMeasurable
          apply Continuous.div_const; apply Continuous.neg
          exact (continuous_sub_left z).const_mul 2
      · exact hf.aestronglyMeasurable)
    (by -- Integrable F(x₀)
      -- F(x₀,y) = exp(g) * h * f(y). We bound it by the same bound as in spatial_deriv_integral.
      have hM0_pos : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
      have h8 : (0:ℝ) < (8*t)⁻¹ := by positivity
      have habs : Integrable (fun y : ℝ => |x₀ - y| * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
        have h := (integrable_rpow_mul_exp_neg_mul_sq h8 (s := 1) (by norm_num : (-1:ℝ) < 1)).norm.comp_sub_left x₀
        convert h using 1; ext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_nonneg _)]
        simp [pow_succ, pow_zero, abs_mul]
      have hone : Integrable (fun y : ℝ => (1 : ℝ) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
        simpa using (integrable_exp_neg_mul_sq h8).comp_sub_left x₀
      have hsum : Integrable (fun y => (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
        have : (fun y => (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
            fun y => |x₀ - y| * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) + 1 * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by ext y; ring
        rw [this]; exact habs.add hone
      have hbound : Integrable (fun y => M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
        have : (fun y => M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
          fun y => (M * rexp (4 * t)⁻¹ / (2 * t)) * ((|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) := by ext y; ring
        rw [this]; exact hsum.const_mul _
      apply hbound.mono
      · show AEStronglyMeasurable (fun y => rexp (-((x₀ - y) ^ 2) / (4 * t)) * (-(2 * (x₀ - y)) / (4 * t)) * f y) volume
        apply AEStronglyMeasurable.mul
        · apply AEStronglyMeasurable.mul
          · exact (continuous_kernel t x₀).aestronglyMeasurable
          · apply Continuous.aestronglyMeasurable
            apply Continuous.div_const; apply Continuous.neg
            exact (continuous_sub_left x₀).const_mul 2
        · exact hf.aestronglyMeasurable
      · filter_upwards with y
        have hM0_pos : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
        have h_bound_nonneg : 0 ≤ M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by
          positivity
        rw [Real.norm_of_nonneg h_bound_nonneg]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (exp_nonneg _)]
        calc rexp (-(x₀ - y) ^ 2 / (4 * t)) * |-(2 * (x₀ - y)) / (4 * t)| * |f y|
            ≤ rexp (-(x₀ - y) ^ 2 / (4 * t)) * |-(2 * (x₀ - y)) / (4 * t)| * M := by
              apply mul_le_mul_of_nonneg_left (hM y)
              apply mul_nonneg (exp_nonneg _) (abs_nonneg _)
          _ ≤ rexp (-(x₀ - y) ^ 2 / (4 * t)) * ((|x₀ - y| + 1) / (2 * t)) * M := by
            apply mul_le_mul_of_nonneg_right _ hM0_pos
            apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
            rw [abs_div, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * t)]
            rw [show (2 : ℝ) * |x₀ - y| / (4 * t) = |x₀ - y| / (2 * t) by ring]
            apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < 2 * t).le
            linarith
          _ ≤ rexp ((4 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) * ((|x₀ - y| + 1) / (2 * t)) * M := by
            apply mul_le_mul_of_nonneg_right _ hM0_pos
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [← Real.exp_add]
            apply Real.exp_le_exp_of_le
            calc -(x₀ - y) ^ 2 / (4 * t)
              = (-(x₀ - y) ^ 2 * 2) / (8 * t) := by ring
              _ ≤ (2 - (x₀ - y) ^ 2) / (8 * t) := by
                apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 8 * t)
                linarith [sq_nonneg (x₀ - y)]
              _ = (4 * t)⁻¹ + -(8 * t)⁻¹ * (x₀ - y) ^ 2 := by ring
          _ = M * rexp (4 * t)⁻¹ / (2 * t) * (|x₀ - y| + 1) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by ring)
    (by -- AEStronglyMeasurable F'(x₀)
      show AEStronglyMeasurable (fun y => rexp (-((x₀ - y) ^ 2) / (4 * t)) *
        ((-(2 * (x₀ - y)) / (4 * t)) ^ 2 + (-2 / (4 * t))) * f y) volume
      apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · exact (continuous_kernel t x₀).aestronglyMeasurable
        · apply Continuous.aestronglyMeasurable
          apply Continuous.add
          · apply Continuous.pow
            apply Continuous.div_const; apply Continuous.neg
            exact (continuous_sub_left x₀).const_mul 2
          · exact continuous_const
      · exact hf.aestronglyMeasurable)
    (by filter_upwards with y
        intro x hx
        -- ‖F'(x,y)‖ ≤ bound(y)
        have hxs : |x - x₀| < 1 := by rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
        have h_abs1 : |(-(2 * (x - y)) / (4 * t)) ^ 2 + -2 / (4 * t)| ≤ |(-(2 * (x - y)) / (4 * t)) ^ 2| + |-2 / (4 * t)| := abs_add_le _ _
        have h_sq1 : |(-(2 * (x - y)) / (4 * t)) ^ 2| = (x - y) ^ 2 / (4 * t ^ 2) := by
          rw [abs_sq]; ring
        have h_abs2 : |-2 / (4 * t)| = (2 * t)⁻¹ := by
          rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * t)]
          ring
        have h_abs_sum : |(-(2 * (x - y)) / (4 * t)) ^ 2 + -2 / (4 * t)| ≤ (x - y) ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹ := by
          linarith [h_abs1, h_sq1, h_abs2]
        
        have h_xy_le : |x - y| ≤ |x₀ - y| + 1 := by
          calc |x - y| = |(x₀ - y) + (x - x₀)| := by ring_nf
            _ ≤ |x₀ - y| + |x - x₀| := abs_add_le _ _
            _ ≤ |x₀ - y| + 1 := by linarith [hxs.le]
        have h_xy_sq_le : (x - y) ^ 2 ≤ (|x₀ - y| + 1) ^ 2 := by
          have h1 : 0 ≤ |x - y| := abs_nonneg _
          have h2 : |x - y| ^ 2 ≤ (|x₀ - y| + 1) ^ 2 := by nlinarith [h_xy_le, h1]
          rwa [sq_abs] at h2

        have h_poly_bound : (x - y) ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹ ≤ (|x₀ - y| + 1) ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹ := by
          have h_div_le : (x - y) ^ 2 / (4 * t ^ 2) ≤ (|x₀ - y| + 1) ^ 2 / (4 * t ^ 2) := div_le_div_of_nonneg_right h_xy_sq_le (by positivity)
          linarith [h_div_le]
        
        have h_exp_bound : rexp (-(x - y) ^ 2 / (4 * t)) ≤ rexp ((4 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp_of_le
          calc -(x - y) ^ 2 / (4 * t)
            = (-(x - y) ^ 2 * 2) / (8 * t) := by ring
            _ ≤ (2 - (x₀ - y) ^ 2) / (8 * t) := by
              apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 8 * t)
              have h1 : -1 ≤ x - x₀ := by linarith [hx.1]
              have h2 : x - x₀ ≤ 1 := by linarith [hx.2]
              have hs : (x - x₀) ^ 2 ≤ 1 := by nlinarith [h1, h2]
              have hs2 : 0 ≤ ((x₀ - y) + 2 * (x - x₀)) ^ 2 := sq_nonneg _
              nlinarith
            _ = (4 * t)⁻¹ + -(8 * t)⁻¹ * (x₀ - y) ^ 2 := by ring

        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (exp_nonneg _)]
        have stp1 : rexp (-(x - y) ^ 2 / (4 * t)) * |(-(2 * (x - y)) / (4 * t)) ^ 2 + -2 / (4 * t)| * |f y| ≤
                    rexp (-(x - y) ^ 2 / (4 * t)) * |(-(2 * (x - y)) / (4 * t)) ^ 2 + -2 / (4 * t)| * M :=
          mul_le_mul_of_nonneg_left (hM y) (mul_nonneg (exp_nonneg _) (abs_nonneg _))
        
        have stp2 : rexp (-(x - y) ^ 2 / (4 * t)) * |(-(2 * (x - y)) / (4 * t)) ^ 2 + -2 / (4 * t)| * M ≤
                    rexp (-(x - y) ^ 2 / (4 * t)) * ((x - y) ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹) * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_abs_sum (exp_nonneg _)) (by linarith [hM 0, abs_nonneg (f 0)])

        have stp3 : rexp (-(x - y) ^ 2 / (4 * t)) * ((x - y) ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹) * M ≤
                    rexp (-(x - y) ^ 2 / (4 * t)) * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_poly_bound (exp_nonneg _)) (by linarith [hM 0, abs_nonneg (f 0)])

        have stp4 : rexp (-(x - y) ^ 2 / (4 * t)) * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) * M ≤
                    (rexp ((4 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) * M := by
          have h1 : rexp (-(x - y) ^ 2 / (4 * t)) * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) ≤
                    (rexp ((4 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) :=
            mul_le_mul_of_nonneg_right h_exp_bound (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (by linarith [hM 0, abs_nonneg (f 0)])
        
        have stp5 : (rexp ((4 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) * M =
                    M * rexp (4 * t)⁻¹ * (((|x₀ - y| + 1) ^ 2) / (4 * t ^ 2) + (2 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by ring
        
        linarith [stp1, stp2, stp3, stp4, stp5])
    (by -- Integrable bound
        -- bound(y) = M*exp(1/(4t)) * [ ((|x₀-y|+1)^2/(4t²) + 1/(2t)) * exp(-(8t)⁻¹*(x₀-y)²) ]
        have h8 : (0:ℝ) < (8*t)⁻¹ := by positivity
        -- First show |x₀-y|^2 * exp(...) is integrable
        have hsq : Integrable (fun y : ℝ => (|x₀ - y| ^ 2) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
          have h := (integrable_rpow_mul_exp_neg_mul_sq h8 (s := 2) (by norm_num : (-1:ℝ) < 2)).comp_sub_left x₀
          convert h using 1; ext y
          have : ((x₀ - y) ^ (2 : ℝ)) = (x₀ - y) ^ 2 := Real.rpow_natCast (x₀ - y) 2
          rw [this, ← sq_abs (x₀ - y)]
        -- Show |x₀-y| * exp(...) is integrable
        have habs : Integrable (fun y : ℝ => |x₀ - y| * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
          have h := (integrable_rpow_mul_exp_neg_mul_sq h8 (s := 1) (by norm_num : (-1:ℝ) < 1)).norm.comp_sub_left x₀
          convert h using 1; ext y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_nonneg _)]
          simp [pow_succ, pow_zero]
        have hone : Integrable (fun y : ℝ => (1 : ℝ) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
          simpa using (integrable_exp_neg_mul_sq h8).comp_sub_left x₀
        -- sum: (|x₀-y| + 1)^2 = |x₀-y|^2 + 2|x₀-y| + 1
        have hsum : Integrable (fun y => ((|x₀ - y| + 1) ^ 2) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
          have : (fun y => ((|x₀ - y| + 1) ^ 2) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
              fun y => |x₀ - y| ^ 2 * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) +
                2 * (|x₀ - y| * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) +
                1 * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2) := by ext y; ring
          rw [this]; exact (hsq.add (habs.const_mul 2)).add hone
        -- Add the constant term for 1/(2t)
        have hsum2 : Integrable (fun y => (((|x₀ - y| + 1) ^ 2 / (4 * t ^ 2)) + (2 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume := by
          have : (fun y => (((|x₀ - y| + 1) ^ 2 / (4 * t ^ 2)) + (2 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
              fun y => (4 * t ^ 2)⁻¹ * (((|x₀ - y| + 1) ^ 2) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) +
                (2 * t)⁻¹ * (1 * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) := by ext y; ring
          rw [this]; exact (hsum.const_mul _).add (hone.const_mul _)
        -- Multiply by M * exp(...)
        show Integrable (fun y => M * rexp (4 * t)⁻¹ * (((|x₀ - y| + 1) ^ 2 / (4 * t ^ 2)) + (2 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) volume
        have : (fun y => M * rexp (4 * t)⁻¹ * (((|x₀ - y| + 1) ^ 2 / (4 * t ^ 2)) + (2 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) =
          fun y => (M * rexp (4 * t)⁻¹) * ((((|x₀ - y| + 1) ^ 2 / (4 * t ^ 2)) + (2 * t)⁻¹) * rexp (-(8 * t)⁻¹ * (x₀ - y) ^ 2)) := by ext y; ring
        rw [this]; exact hsum2.const_mul _)
    (by filter_upwards with y; intro x _; exact hasDerivAt_deriv_integrand_x f t y x ht)
  exact key.2

-- ═══════════════════════════════════════════════════════════════════
-- 6. Time derivative  (key: equals second spatial derivative)
-- ═══════════════════════════════════════════════════════════════════

private lemma time_deriv_integral (f : ℝ → ℝ) (hf : Continuous f)
    (t : ℝ) (ht : 0 < t) (M : ℝ) (hM : ∀ y, |f y| ≤ M) (x : ℝ) :
    HasDerivAt (fun s => ∫ y, rexp (-(x - y)^2/(4*s)) * f y)
      (∫ y, (x - y)^2 / (4 * t^2) * rexp (-(x - y)^2/(4*t)) * f y) t := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := fun s y => rexp (-(x - y) ^ 2 / (4 * s)) * f y)
    (F' := fun s y => (x - y) ^ 2 / (4 * s ^ 2) * rexp (-(x - y) ^ 2 / (4 * s)) * f y)
    (x₀ := t)
    (bound := fun y => ((x - y) ^ 2 / t ^ 2) * rexp (-(6 * t)⁻¹ * (x - y) ^ 2) * M)
    (s := Set.Ioo (t / 2) (t * 3 / 2))
    (Ioo_mem_nhds (by linarith : t / 2 < t) (by linarith : t < t * 3 / 2))
    (by -- hF_meas
      filter_upwards with s
      apply Continuous.aestronglyMeasurable
      continuity)
    (by -- hF_int
      have h4 : 0 < (4*t)⁻¹ := by positivity
      have h_int : Integrable (fun y => rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) volume := by
        have h := (integrable_rpow_mul_exp_neg_mul_sq h4 (s := 0) (by norm_num : (-1:ℝ) < 0)).comp_sub_left x
        convert h using 1; ext y; simp [Real.rpow_zero]
      have h_int2 : Integrable (fun y => rexp (-(x - y) ^ 2 / (4 * t))) volume := by
        have h_eq : (fun y => rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) = fun y => rexp (-(x - y) ^ 2 / (4 * t)) := by ext y; ring
        rw [← h_eq]
        exact h_int
      have h_int_mul : Integrable (fun y => f y * rexp (-(x - y) ^ 2 / (4 * t))) volume :=
        Integrable.bdd_mul h_int2 hf.aestronglyMeasurable (Filter.Eventually.of_forall hM)
      convert h_int_mul using 1
      ext y
      ring)
    (by -- hF'_meas
      apply Continuous.aestronglyMeasurable
      continuity)
    (by -- h_bound
      filter_upwards with y
      intro s hs
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (exp_nonneg _)]
      have h_s_pos : 0 < s := by linarith [hs.1, ht]
      have h_div : |(x - y)^2 / (4 * s^2)| ≤ (x - y)^2 / t^2 := by
        rw [abs_div, abs_sq, abs_of_nonneg (by positivity : 0 ≤ 4 * s^2)]
        have h1 : t / 2 ≤ s := hs.1.le
        have h2 : t^2 ≤ 4 * s^2 := by nlinarith [ht, h1]
        have h3 : 1 / (4 * s^2) ≤ 1 / t^2 := one_div_le_one_div_of_le (by positivity) h2
        calc (x - y)^2 / (4 * s^2) = (x - y)^2 * (1 / (4 * s^2)) := by ring
          _ ≤ (x - y)^2 * (1 / t^2) := by apply mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
          _ = (x - y)^2 / t^2 := by ring
      have h_exp : rexp (-(x - y) ^ 2 / (4 * s)) ≤ rexp (-(6 * t)⁻¹ * (x - y) ^ 2) := by
        apply Real.exp_le_exp_of_le
        have h1 : s ≤ t * 3 / 2 := hs.2.le
        have h2 : 4 * s ≤ 6 * t := by linarith
        have h3 : (6 * t)⁻¹ ≤ (4 * s)⁻¹ := by apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr h2
        calc -(x - y)^2 / (4 * s) = -(x - y)^2 * (4 * s)⁻¹ := by ring
          _ ≤ -(x - y)^2 * (6 * t)⁻¹ := by
            apply mul_le_mul_of_nonpos_left h3
            exact neg_nonpos.mpr (sq_nonneg _)
          _ = -(6 * t)⁻¹ * (x - y)^2 := by ring
      have stp1 : |(x - y) ^ 2 / (4 * s ^ 2)| * rexp (-(x - y) ^ 2 / (4 * s)) * |f y| ≤
                  |(x - y) ^ 2 / (4 * s ^ 2)| * rexp (-(x - y) ^ 2 / (4 * s)) * M := by
        exact mul_le_mul_of_nonneg_left (hM y) (by positivity)
      have stp2 : |(x - y) ^ 2 / (4 * s ^ 2)| * rexp (-(x - y) ^ 2 / (4 * s)) * M ≤
                  (x - y) ^ 2 / t ^ 2 * rexp (-(6 * t)⁻¹ * (x - y) ^ 2) * M := by
        apply mul_le_mul_of_nonneg_right _ (by linarith [hM 0, abs_nonneg (f 0)])
        exact mul_le_mul h_div h_exp (exp_nonneg _) (by positivity)
      linarith [stp1, stp2]
    )
    (bound_integrable := by
      have h6 : (0:ℝ) < (6*t)⁻¹ := by positivity
      have hsq : Integrable (fun y : ℝ => (|x - y| ^ 2) * rexp (-(6 * t)⁻¹ * (x - y) ^ 2)) volume := by
        have h := (integrable_rpow_mul_exp_neg_mul_sq h6 (s := 2) (by norm_num : (-1:ℝ) < 2)).comp_sub_left x
        convert h using 1; ext y
        have : ((x - y) ^ (2 : ℝ)) = (x - y) ^ 2 := Real.rpow_natCast (x - y) 2
        rw [this, ← sq_abs (x - y)]
      have hsq2 : Integrable (fun y : ℝ => ((x - y) ^ 2) * rexp (-(6 * t)⁻¹ * (x - y) ^ 2)) volume := by
        convert hsq using 1; ext y; rw [sq_abs]
      have : (fun y => (x - y) ^ 2 / t ^ 2 * rexp (-(6 * t)⁻¹ * (x - y) ^ 2) * M) =
             fun y => (M / t ^ 2) * (((x - y) ^ 2) * rexp (-(6 * t)⁻¹ * (x - y) ^ 2)) := by ext y; ring
      rw [this]
      exact hsq2.const_mul _
    )
    (by -- h_deriv
      filter_upwards with y
      intro s hs
      have h_s_pos : 0 < s := by linarith [hs.1, ht]
      have h1 : HasDerivAt (fun s => -(x - y) ^ 2 / (4 * s)) ((x - y) ^ 2 / (4 * s ^ 2)) s := by
        have : (fun s => -(x - y) ^ 2 / (4 * s)) = fun s => (-(x - y) ^ 2 / 4) * s⁻¹ := by ext s'; ring
        rw [this]
        have h_inv : HasDerivAt (fun s => s⁻¹) (-s⁻¹ ^ 2) s := by
          convert hasDerivAt_inv h_s_pos.ne' using 1
          ring
        have hd := h_inv.const_mul (-(x - y) ^ 2 / 4)
        convert hd using 1
        ring
      have h2 : HasDerivAt (fun s => rexp (-(x - y) ^ 2 / (4 * s))) ((x - y) ^ 2 / (4 * s ^ 2) * rexp (-(x - y) ^ 2 / (4 * s))) s := by
        have hd := h1.exp
        convert hd using 1
        ring
      have hd3 := h2.mul_const (f y)
      convert hd3 using 1
    )
  exact key.2

-- ═══════════════════════════════════════════════════════════════════
-- 6. Time derivative  (key: equals second spatial derivative)
-- ═══════════════════════════════════════════════════════════════════

-- ∂/∂t [C(t) * ∫ K(t,x,y) f(y) dy] = C(t) * ∫ [(x-y)²/(4t²) - 1/(2t)] K f dy
-- This equals uxx = C(t) * ∫ [(2(x-y)/(4t))² - 2/(4t)] K f dy
-- since (2(x-y))²/(4t)² = 4(x-y)²/(16t²) = (x-y)²/(4t²)
-- and 2/(4t) = 1/(2t). So the PDE identity holds.

private lemma C_deriv (t : ℝ) (ht : 0 < t) :
  HasDerivAt (fun s => (4 * Real.pi * s)⁻¹ ^ ((1:ℝ)/2))
    (-(2 * t)⁻¹ * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) t := by
  have h_pi_pos : 0 < 4 * Real.pi := by positivity
  have h_s_pos : 0 < 4 * Real.pi * t := mul_pos h_pi_pos ht
  have h_s_inv_pos : 0 < (4 * Real.pi * t)⁻¹ := inv_pos.mpr h_s_pos
  have hd1 : HasDerivAt (fun s => 4 * Real.pi * s) (4 * Real.pi) t := by
    have := hasDerivAt_id t |>.const_mul (4 * Real.pi)
    convert this using 1; ring
  have hd2 : HasDerivAt (fun s => (4 * Real.pi * s)⁻¹) (-(4 * Real.pi) / (4 * Real.pi * t) ^ 2) t := hd1.inv h_s_pos.ne'
  have hd3 : HasDerivAt (fun s => (4 * Real.pi * s)⁻¹ ^ ((1:ℝ)/2))
    ((-(4 * Real.pi) / (4 * Real.pi * t) ^ 2) * (1/2 : ℝ) * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2 - 1)) t := by
    apply HasDerivAt.rpow_const hd2
    left; exact inv_ne_zero h_s_pos.ne'
  have h_rpow : (4 * Real.pi * t)⁻¹ ^ ((1:ℝ) / 2 - 1) = (4 * Real.pi * t)⁻¹ ^ ((1:ℝ) / 2) / (4 * Real.pi * t)⁻¹ := by
    rw [Real.rpow_sub h_s_inv_pos, Real.rpow_one]
  have h_div : (4 * Real.pi * t)⁻¹ ^ ((1:ℝ) / 2) / (4 * Real.pi * t)⁻¹ = (4 * Real.pi * t)⁻¹ ^ ((1:ℝ) / 2) * (4 * Real.pi * t) := by
    rw [div_inv_eq_mul]
  convert hd3 using 1
  rw [h_rpow, h_div]
  have h1 : -(2 * t)⁻¹ = -1 / (2 * t) := by rw [inv_eq_one_div]; ring
  have h2 : -1 / (2 * t) = (-1 * (8 * Real.pi ^ 2 * t)) / ((2 * t) * (8 * Real.pi ^ 2 * t)) := by
    rw [mul_div_mul_right _ _ (by positivity : 8 * Real.pi ^ 2 * t ≠ 0)]
  have h3 : (-1 * (8 * Real.pi ^ 2 * t)) / ((2 * t) * (8 * Real.pi ^ 2 * t)) = (-(4 * Real.pi) * (1 / 2) * (4 * Real.pi * t)) / (16 * Real.pi ^ 2 * t ^ 2) := by ring
  have h4 : (-(4 * Real.pi) * (1 / 2) * (4 * Real.pi * t)) / (16 * Real.pi ^ 2 * t ^ 2) * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ) / 2) = -(4 * Real.pi) / (4 * Real.pi * t) ^ 2 * (1 / 2) * ((4 * Real.pi * t)⁻¹ ^ ((1:ℝ) / 2) * (4 * Real.pi * t)) := by ring
  rw [h1, h2, h3]
  exact h4

private lemma h_int1_proof (f : ℝ → ℝ) (hf : Continuous f) (x t M : ℝ) (ht : 0 < t) (hM : ∀ y, |f y| ≤ M) :
  Integrable (fun y => rexp (-(x - y) ^ 2 / (4 * t)) * f y) volume := by
  have hint : Integrable (fun y => rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) volume :=
    (integrable_exp_neg_mul_sq (by positivity)).comp_sub_left x
  have heq : (fun y => rexp (-((x - y) ^ 2) / (4 * t)) * f y) = fun y => f y * rexp (-(4 * t)⁻¹ * (x - y) ^ 2) := by
    ext y
    have : -((x - y) ^ 2) / (4 * t) = -(4 * t)⁻¹ * (x - y) ^ 2 := by ring
    rw [this, mul_comm]
  rw [heq]
  apply Integrable.bdd_mul hint hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => hM y)

private lemma h_int2_proof (f : ℝ → ℝ) (hf : Continuous f) (x t M : ℝ) (ht : 0 < t) (hM : ∀ y, |f y| ≤ M) :
  Integrable (fun y => (x - y) ^ 2 / (4 * t ^ 2) * rexp (-(x - y) ^ 2 / (4 * t)) * f y) volume := by
  have h8 : (0:ℝ) < (4 * t)⁻¹ := by positivity
  have hsq : Integrable (fun y : ℝ => (|x - y| ^ 2) * rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) volume := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq h8 (s := 2) (by norm_num : (-1:ℝ) < 2)).comp_sub_left x
    convert h using 1; ext y
    have : ((x - y) ^ (2 : ℝ)) = (x - y) ^ 2 := Real.rpow_natCast (x - y) 2
    rw [this, ← sq_abs (x - y)]
  have hsq_noabs : Integrable (fun y : ℝ => (x - y) ^ 2 * rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) volume := by
    convert hsq using 1; ext y
    have : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs (x - y)
    rw [this]
  have hsq2 : Integrable (fun y : ℝ => (4 * t ^ 2)⁻¹ * ((x - y) ^ 2 * rexp (-(4 * t)⁻¹ * (x - y) ^ 2))) volume :=
    hsq_noabs.const_mul _
  have hint : Integrable (fun y : ℝ => (x - y) ^ 2 / (4 * t ^ 2) * rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) volume := by
    convert hsq2 using 1; ext y
    ring
  have heq : (fun y => (x - y) ^ 2 / (4 * t ^ 2) * rexp (-(x - y) ^ 2 / (4 * t)) * f y) =
    fun y => f y * ((x - y) ^ 2 / (4 * t ^ 2) * rexp (-(4 * t)⁻¹ * (x - y) ^ 2)) := by
    ext y
    have : -(x - y) ^ 2 / (4 * t) = -(4 * t)⁻¹ * (x - y) ^ 2 := by ring
    rw [this]
    ring
  rw [heq]
  apply Integrable.bdd_mul hint hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => hM y)

-- ═══════════════════════════════════════════════════════════════════
-- 7. Initial condition
-- ═══════════════════════════════════════════════════════════════════

lemma integral_cov (g : ℝ → ℝ) (x c : ℝ) (hc : 0 < c) :
  ∫ y, g y = c * ∫ w, g (w * c + x) := by
  have h1 : ∫ w, g (w * c + x) = ∫ y, (fun w => g (w + x)) (y * c) := by rfl
  rw [h1]
  have h2 := MeasureTheory.Measure.integral_comp_mul_right (fun w => g (w + x)) c
  rw [h2]
  have hc_abs : |c⁻¹| = c⁻¹ := by rw [abs_inv, abs_of_pos hc]
  have h3 : ∫ (y : ℝ), g (y + x) = ∫ y, g y := by
    exact (MeasureTheory.integral_add_right_eq_self (μ := volume) g x)
  rw [h3]
  have h4 : |c⁻¹| • ∫ (y : ℝ), g y = c⁻¹ * ∫ y, g y := by
    rw [hc_abs, smul_eq_mul]
  rw [h4, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]

lemma heatSolution_eq_cov (f : ℝ → ℝ) (x t : ℝ) (ht : 0 < t) :
  (4 * π * t)⁻¹ ^ ((1 : ℝ) / 2) * ∫ y, rexp (-((x - y) ^ 2) / (4 * t)) * f y =
  π⁻¹ ^ ((1 : ℝ) / 2) * ∫ w, rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2)) := by
  have hc_pos : 0 < (4 * t) ^ ((1 : ℝ) / 2) := by positivity
  have hcov := integral_cov (fun y => rexp (-((x - y) ^ 2) / (4 * t)) * f y) x ((4 * t) ^ ((1 : ℝ) / 2)) hc_pos
  have h_int_eq : (∫ w, (fun y => rexp (-((x - y) ^ 2) / (4 * t)) * f y) (w * (4 * t) ^ ((1 : ℝ) / 2) + x)) =
    ∫ w, rexp (-w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2)) := by
    congr 1
    ext w
    dsimp
    have h1_sub : x - (w * (4 * t) ^ ((1 : ℝ) / 2) + x) = - (w * (4 * t) ^ ((1 : ℝ) / 2)) := by ring
    have h1_sq : (- (w * (4 * t) ^ ((1 : ℝ) / 2))) ^ 2 = w ^ 2 * ((4 * t) ^ ((1 : ℝ) / 2)) ^ 2 := by
      calc (- (w * (4 * t) ^ ((1 : ℝ) / 2))) ^ 2 = (w * (4 * t) ^ ((1 : ℝ) / 2)) ^ 2 := neg_sq _
        _ = w ^ 2 * ((4 * t) ^ ((1 : ℝ) / 2)) ^ 2 := mul_pow w _ 2
    have h1_rpow2 : ((4 * t) ^ ((1 : ℝ) / 2)) ^ 2 = 4 * t := by
      rw [← rpow_natCast, ← rpow_mul (by positivity : 0 ≤ 4 * t)]
      norm_num
    have h1 : -((x - (w * (4 * t) ^ ((1 : ℝ) / 2) + x)) ^ 2) / (4 * t) = - w ^ 2 := by
      calc -((x - (w * (4 * t) ^ ((1 : ℝ) / 2) + x)) ^ 2) / (4 * t)
        _ = -((- (w * (4 * t) ^ ((1 : ℝ) / 2))) ^ 2) / (4 * t) := by rw [h1_sub]
        _ = -(w ^ 2 * ((4 * t) ^ ((1 : ℝ) / 2)) ^ 2) / (4 * t) := by rw [h1_sq]
        _ = -(w ^ 2 * (4 * t)) / (4 * t) := by rw [h1_rpow2]
        _ = -((w ^ 2 * (4 * t)) / (4 * t)) := by ring
        _ = -w ^ 2 := by rw [mul_div_cancel_right₀ (w ^ 2) (ne_of_gt (by positivity : 0 < 4 * t))]
    have h2 : w * (4 * t) ^ ((1 : ℝ) / 2) + x = x + w * (4 * t) ^ ((1 : ℝ) / 2) := by ring
    rw [h1, h2]
  rw [hcov, h_int_eq]
  have h_mul : (4 * π * t)⁻¹ ^ ((1 : ℝ) / 2) * (4 * t) ^ ((1 : ℝ) / 2) = π⁻¹ ^ ((1 : ℝ) / 2) := by
    have h_pos_4t : 0 ≤ 4 * t := by positivity
    have h_pos_pi : 0 ≤ π⁻¹ := by positivity
    have h_pos_4t_inv : 0 ≤ (4 * t)⁻¹ := by positivity
    have heq1 : (4 * π * t)⁻¹ = π⁻¹ * (4 * t)⁻¹ := by
      have : 4 * π * t = π * (4 * t) := by ring
      rw [this, mul_inv]
    rw [heq1]
    rw [mul_rpow h_pos_pi h_pos_4t_inv]
    rw [mul_assoc]
    have heq2 : (4 * t)⁻¹ ^ ((1 : ℝ) / 2) * (4 * t) ^ ((1 : ℝ) / 2) = 1 := by
      rw [← mul_rpow h_pos_4t_inv h_pos_4t]
      have : (4 * t)⁻¹ * (4 * t) = 1 := inv_mul_cancel₀ (ne_of_gt (by positivity : 0 < 4 * t))
      rw [this, one_rpow]
    rw [heq2, mul_one]
  rw [← mul_assoc, h_mul]

lemma rpow_tendsto_zero :
  Tendsto (fun t : ℝ => (4 * t) ^ ((1 : ℝ) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have : (fun t : ℝ => (4 * t) ^ ((1 : ℝ) / 2)) = (fun t => t ^ ((1 : ℝ) / 2)) ∘ (fun t => 4 * t) := by
    ext t; rfl
  rw [this]
  have h1 : Tendsto (fun t : ℝ => 4 * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_cont : Tendsto (fun t : ℝ => 4 * t) (nhds 0) (nhds (4 * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    have : (4 * 0 : ℝ) = 0 := by ring
    rw [this] at h_cont
    exact h_cont.mono_left nhdsWithin_le_nhds
  have h2 : Continuous (fun x : ℝ => x ^ ((1 : ℝ) / 2)) := Real.continuous_rpow_const (by norm_num)
  have h3 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 2)) (nhds 0) (nhds 0) := by
    have h_cont := h2.tendsto 0
    have : (0 : ℝ) ^ ((1 : ℝ) / 2) = 0 := Real.zero_rpow (by norm_num)
    rwa [this] at h_cont
  exact h3.comp h1

lemma pointwise_limit (f : ℝ → ℝ) (hf : Continuous f) (x w : ℝ) :
  Tendsto (fun (t : ℝ) => rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2)))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (rexp (- w ^ 2) * f x)) := by
  have h_add : Tendsto (fun t : ℝ => x + w * (4 * t) ^ ((1 : ℝ) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (x + w * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul rpow_tendsto_zero)
  have h_add_simp : Tendsto (fun t : ℝ => x + w * (4 * t) ^ ((1 : ℝ) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
    have : x + w * 0 = x := by ring
    rwa [this] at h_add
  have h_f : Tendsto (fun t : ℝ => f (x + w * (4 * t) ^ ((1 : ℝ) / 2))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) :=
    (hf.tendsto x).comp h_add_simp
  exact tendsto_const_nhds.mul h_f

lemma DCT_apply (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ y, |f y| ≤ M) (x : ℝ) :
  Tendsto (fun (t : ℝ) => ∫ w, rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2)))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ w, rexp (- w ^ 2) * f x)) := by
  let bound := fun w : ℝ => M * rexp (- w ^ 2)
  have h_bound : ∀ᶠ (t : ℝ) in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ (w : ℝ), |rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2))| ≤ bound w := by
    apply Eventually.of_forall
    intro t
    apply Eventually.of_forall
    intro w
    rw [abs_mul, abs_of_pos (exp_pos _)]
    have : |f (x + w * (4 * t) ^ ((1 : ℝ) / 2))| ≤ M := hM _
    have h_le : rexp (- w ^ 2) * |f (x + w * (4 * t) ^ ((1 : ℝ) / 2))| ≤ rexp (- w ^ 2) * M :=
      mul_le_mul_of_nonneg_left this (exp_pos _).le
    have h_eq : rexp (- w ^ 2) * M = M * rexp (- w ^ 2) := mul_comm _ _
    rwa [h_eq] at h_le
  have h_int : Integrable bound := by
    have : bound = (fun w : ℝ => M * rexp (- (1:ℝ) * w ^ 2)) := by
      ext w; dsimp [bound]; ring_nf
    rw [this]
    have hint := integrable_exp_neg_mul_sq (by norm_num : 0 < (1:ℝ))
    exact hint.const_mul M
  have h_ae_limit : ∀ᵐ (w : ℝ), Tendsto (fun t : ℝ => rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2)))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (rexp (- w ^ 2) * f x)) := by
    apply Eventually.of_forall
    intro w
    exact pointwise_limit f hf x w
  have h_ae_meas : ∀ᶠ (t : ℝ) in nhdsWithin 0 (Set.Ioi 0), AEStronglyMeasurable (fun w => rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2))) volume := by
    apply Eventually.of_forall
    intro t
    apply Continuous.aestronglyMeasurable
    have h1 : Continuous (fun w => rexp (- w ^ 2)) := by continuity
    have h2 : Continuous (fun w => f (x + w * (4 * t) ^ ((1 : ℝ) / 2))) := by
      have : Continuous (fun w => x + w * (4 * t) ^ ((1 : ℝ) / 2)) := by continuity
      exact hf.comp this
    exact h1.mul h2
  exact tendsto_integral_filter_of_dominated_convergence bound h_ae_meas h_bound h_int h_ae_limit

lemma initial_condition (f : ℝ → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : ∀ y, |f y| ≤ M) (x : ℝ) :
    Tendsto (fun t : ℝ => heatSolution f t x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  have hdct := DCT_apply f hf M hM x
  have h_tendsto : Tendsto (fun t : ℝ => π⁻¹ ^ ((1 : ℝ) / 2) * ∫ w, rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2)))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π⁻¹ ^ ((1 : ℝ) / 2) * ∫ w, rexp (- w ^ 2) * f x)) :=
    tendsto_const_nhds.mul hdct
  have heq : (fun t : ℝ => heatSolution f t x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] 
    (fun t : ℝ => π⁻¹ ^ ((1 : ℝ) / 2) * ∫ w, rexp (- w ^ 2) * f (x + w * (4 * t) ^ ((1 : ℝ) / 2))) := by
    filter_upwards [self_mem_nhdsWithin]
    intro t ht
    have ht_pos : 0 < t := ht
    dsimp [heatSolution]
    rw [if_pos ht_pos]
    exact heatSolution_eq_cov f x t ht_pos
  have h_tendsto_heat : Tendsto (fun t : ℝ => heatSolution f t x)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π⁻¹ ^ ((1 : ℝ) / 2) * ∫ w, rexp (- w ^ 2) * f x)) :=
    Tendsto.congr' heq.symm h_tendsto
  have h_int_eval : ∫ w, rexp (- w ^ 2) * f x = f x * ∫ w, rexp (- w ^ 2) := by
    have : (fun w => rexp (- w ^ 2) * f x) = fun w => f x • rexp (- w ^ 2) := by ext w; exact mul_comm _ _
    rw [this]
    exact integral_smul (f x) _
  have h_gauss : ∫ w, rexp (- w ^ 2) = π ^ ((1 : ℝ) / 2) := by
    have : (fun w : ℝ => rexp (- w ^ 2)) = (fun w : ℝ => rexp (- 1 * w ^ 2)) := by ext w; ring_nf
    rw [this, integral_gaussian (1 : ℝ)]
    rw [div_one, sqrt_eq_rpow]
  rw [h_int_eval, h_gauss] at h_tendsto_heat
  have h_mul_cancel : π⁻¹ ^ ((1 : ℝ) / 2) * (f x * π ^ ((1 : ℝ) / 2)) = f x := by
    have : π⁻¹ ^ ((1 : ℝ) / 2) * (f x * π ^ ((1 : ℝ) / 2)) = f x * (π⁻¹ ^ ((1 : ℝ) / 2) * π ^ ((1 : ℝ) / 2)) := by ring
    rw [this]
    have h_inv : π⁻¹ ^ ((1 : ℝ) / 2) = (π ^ ((1 : ℝ) / 2))⁻¹ := by
      exact Real.inv_rpow (by positivity : 0 ≤ π) _
    rw [h_inv, inv_mul_cancel₀ (ne_of_gt (by positivity : 0 < π ^ ((1:ℝ)/2))), mul_one]
  rwa [h_mul_cancel] at h_tendsto_heat

-- ═══════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════════

theorem heat_kernel_solves_heat_equation
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    (∀ x : ℝ,
        Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  obtain ⟨M, hM⟩ := hf_bdd
  refine ⟨fun t ht x => ?_, fun x => initial_condition f hf_cont M hM x⟩
  -- PDE part: provide explicit ux and uxx
  refine ⟨fun y => (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) *
      ∫ w, rexp (-((y - w) ^ 2) / (4 * t)) *
        (-(2 * (y - w)) / (4 * t)) * f w,
    (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) *
      ∫ w, rexp (-((x - w) ^ 2) / (4 * t)) *
        ((-(2 * (x - w)) / (4 * t)) ^ 2 + (-2 / (4 * t))) * f w,
    ?_, ?_, ?_⟩
  · -- ∀ y, HasDerivAt (fun z => heatSolution f t z) (ux y) y
    intro y
    exact hasDerivAt_heatSolution_x f hf_cont t ht M hM y
  · -- HasDerivAt ux uxx x (second spatial derivative)
    exact (spatial_deriv2_integral f hf_cont t ht M hM x).const_mul _
  · -- HasDerivAt (fun s => heatSolution f s x) uxx t (time derivative = uxx)
    have hC := C_deriv t ht
    have hI := time_deriv_integral f hf_cont t ht M hM x
    have h_prod := hC.mul hI
    have heq : ∀ᶠ s in nhds t, heatSolution f s x =
      (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) * ∫ y, rexp (-((x - y) ^ 2) / (4 * s)) * f y := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      dsimp [heatSolution]
      have hs_pos : 0 < s := hs
      rw [if_pos hs_pos]
    have h_deriv_eq : HasDerivAt (fun s => heatSolution f s x)
      ((-(2 * t)⁻¹ * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) * (∫ y, rexp (-((x - y) ^ 2) / (4 * t)) * f y) +
      (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * (∫ y, (x - y) ^ 2 / (4 * t ^ 2) * rexp (-(x - y) ^ 2 / (4 * t)) * f y)) t := by
      exact HasDerivAt.congr_of_eventuallyEq h_prod heq
    convert h_deriv_eq using 1
    have h_int1 := h_int1_proof f hf_cont x t M ht hM
    have h_int2 := h_int2_proof f hf_cont x t M ht hM
    have hc1 : (-(2 * t)⁻¹ * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) * (∫ y, rexp (-((x - y) ^ 2) / (4 * t)) * f y) =
      ∫ y, (-(2 * t)⁻¹ * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) * (rexp (-((x - y) ^ 2) / (4 * t)) * f y) := by
      exact (integral_smul (𝕜 := ℝ) (G := ℝ) (-(2 * t)⁻¹ * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) _).symm
    rw [hc1]
    have hc2 : (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * (∫ y, (x - y) ^ 2 / (4 * t ^ 2) * rexp (-(x - y) ^ 2 / (4 * t)) * f y) =
      ∫ y, (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * ((x - y) ^ 2 / (4 * t ^ 2) * rexp (-(x - y) ^ 2 / (4 * t)) * f y) := by
      exact (integral_smul (𝕜 := ℝ) (G := ℝ) ((4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) _).symm
    rw [hc2]
    rw [← integral_add (Integrable.const_mul h_int1 _) (Integrable.const_mul h_int2 _)]
    have h_eq : (fun y => (-(2 * t)⁻¹ * (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) * (rexp (-((x - y) ^ 2) / (4 * t)) * f y) +
        (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * ((x - y) ^ 2 / (4 * t ^ 2) * rexp (-(x - y) ^ 2 / (4 * t)) * f y)) =
        fun w => (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * (rexp (-((x - w) ^ 2) / (4 * t)) * ((-(2 * (x - w)) / (4 * t)) ^ 2 + -2 / (4 * t)) * f w) := by
      ext y
      have : -(2 * t)⁻¹ = -2 / (4 * t) := by ring
      rw [this]
      ring
    rw [h_eq]
    have hc3 : (∫ w, (4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * (rexp (-((x - w) ^ 2) / (4 * t)) * ((-(2 * (x - w)) / (4 * t)) ^ 2 + -2 / (4 * t)) * f w)) =
      ∫ w, ((4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) • (rexp (-((x - w) ^ 2) / (4 * t)) * ((-(2 * (x - w)) / (4 * t)) ^ 2 + -2 / (4 * t)) * f w) := rfl
    rw [hc3]
    have hc4 : ((4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2) * ∫ w, rexp (-((x - w) ^ 2) / (4 * t)) * ((-(2 * (x - w)) / (4 * t)) ^ 2 + -2 / (4 * t)) * f w) =
      ((4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) • ∫ w, (rexp (-((x - w) ^ 2) / (4 * t)) * ((-(2 * (x - w)) / (4 * t)) ^ 2 + -2 / (4 * t)) * f w) := rfl
    rw [hc4]
    exact (integral_smul (𝕜 := ℝ) (G := ℝ) ((4 * Real.pi * t)⁻¹ ^ ((1:ℝ)/2)) _).symm


end Submission