import Mathlib

namespace Submission

namespace LeanEval
namespace Analysis
namespace ODE

/-!
The Gaussian heat kernel solves the 1D heat equation.

Define
  `u(t, x) = (4 π t)^(-1/2) · ∫_ℝ exp(-(x - y)² / (4 t)) · f(y) dy`
for `t > 0`, and extend by `u(t, x) := f x` for `t ≤ 0`. Then on `(0, ∞) × ℝ` we have
  `∂_t u = ∂_x² u`,
and `u(t, x) → f x` as `t ↓ 0` for every `x`.

This is a substantial benchmark because it exercises differentiation under the integral
sign, the explicit Gaussian integral evaluation, approximate-identity arguments for the
initial trace, and the heat-PDE identity satisfied by the kernel itself.

The PDE statement asserts the existence of the spatial first and second derivatives at
each `(t, x)` with `t > 0`, and equates the time derivative of `u` to the spatial second
derivative. Stating things via `HasDerivAt` (rather than relying on `deriv` returning `0`
silently when the derivative does not exist) ensures the Lean statement matches the
intended PDE.
-/

open Real MeasureTheory

/-- The 1D Gaussian heat kernel. Extended by `f x` for `t ≤ 0` so that it is a global
function `ℝ × ℝ → ℝ`; the PDE statement only constrains its behaviour on `t > 0`. -/
noncomputable def heatSolution (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
      ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y
  else
    f x



end ODE
end Analysis
end LeanEval

open LeanEval.Analysis.ODE
open Real MeasureTheory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open Filter Set MeasureTheory

/-- An elementary integrable majorant (constant, linear and quadratic moments of a Gaussian). -/
lemma hk_integrable_poly (b : ℝ) (hb : 0 < b) :
    Integrable (fun r : ℝ => (|r| + 1)^2 * Real.exp (- b * r^2)) := by
  have h0 : Integrable (fun r : ℝ => Real.exp (-b * r^2)) :=
    integrable_exp_neg_mul_sq hb
  have h1s : Integrable (fun r : ℝ => r * Real.exp (-b * r^2)) :=
    integrable_mul_exp_neg_mul_sq hb
  have h1 : Integrable (fun r : ℝ => |r| * Real.exp (-b * r^2)) := by
    have hn := h1s.norm
    -- taking the norm just inserts an absolute value, since the exponential is positive
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le] using hn
  have h2 : Integrable (fun r : ℝ => r^2 * Real.exp (-b * r^2)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < (2:ℝ)))
    simpa [Real.rpow_two] using h
  have h2' : Integrable (fun r : ℝ => |r|^2 * Real.exp (-b * r^2)) := by
    simpa [sq_abs] using h2
  have hs := (h2'.add (h1.const_mul 2)).add h0
  -- expand the square
  have heq : (fun r : ℝ => (|r| + 1)^2 * Real.exp (- b * r^2)) =
      (fun r : ℝ => |r|^2 * Real.exp (- b * r^2) +
        2 * (|r| * Real.exp (- b * r^2)) + Real.exp (- b * r^2)) := by
    funext r
    ring
  rw [heq]
  exact hs

/-- the same majorant after a translation of Lebesgue measure -/
lemma hk_integrable_poly_shift (b : ℝ) (hb : 0 < b) (x : ℝ) :
    Integrable (fun y : ℝ => (|y - x| + 1)^2 * Real.exp (- b * (y-x)^2)) := by
  have h := (hk_integrable_poly b hb).comp_add_right (-x)
  simpa [sub_eq_add_neg] using h

lemma hk_abs_le (x₀ x y : ℝ) (hx : |x-x₀| ≤ 1) :
    |x-y| ≤ |y-x₀| + 1 := by
  calc
    |x-y| = |(x-x₀) + (x₀-y)| := by ring_nf
    _ ≤ |x-x₀| + |x₀-y| := abs_add_le _ _
    _ ≤ |y-x₀| + 1 := by rw [abs_sub_comm x₀ y]; linarith

lemma hk_sq_le (x₀ x y : ℝ) (hx : |x-x₀| ≤ 1) :
    (y-x₀)^2 ≤ 2*(x-y)^2 + 2 := by
  have hx2 : (x-x₀)^2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (x-x₀)) (by norm_num : (0:ℝ) ≤ 1)).2 hx
    nlinarith [sq_abs (x-x₀)]
  nlinarith [sq_nonneg ((y-x) - (x-x₀))]

/-- uniform estimate for translating and slightly widening a Gaussian -/
lemma hk_gaussian_le (T t x₀ x y : ℝ) (hT : 0 < T)
    (ht : 0 < t) (htT : t ≤ T) (hx : |x-x₀| ≤ 1) :
    Real.exp (-(x-y)^2 / (4*t)) ≤
      Real.exp (1/(4*T)) * Real.exp (-(1/(8*T)) * (y-x₀)^2) := by
  have hq : 0 ≤ (x-y)^2 := sq_nonneg _
  have ht4 : 0 < 4*t := by positivity
  have hT4 : 0 < 4*T := by positivity
  have hdiv : (x-y)^2 / (4*T) ≤ (x-y)^2 / (4*t) := by
    exact div_le_div_of_nonneg_left hq ht4 (by linarith)
  have hs := hk_sq_le x₀ x y hx
  have hsecond : -(x-y)^2/(4*T) ≤ -(1/(8*T))*(y-x₀)^2 + 1/(4*T) := by
    calc
      -(x-y)^2/(4*T) = (-2*(x-y)^2)/(8*T) := by ring
      _ ≤ (-(y-x₀)^2 + 2)/(8*T) := by
        apply div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = -(1/(8*T))*(y-x₀)^2 + 1/(4*T) := by ring
  have hexp : -(x-y)^2/(4*t) ≤
        1/(4*T) + (-(1/(8*T))*(y-x₀)^2) := by
    have hfirst : -(x-y)^2/(4*t) ≤ -(x-y)^2/(4*T) := by
      have := neg_le_neg hdiv
      simpa [neg_div] using (neg_le_neg hdiv)
    linarith
  calc
    Real.exp (-(x-y)^2/(4*t)) ≤
        Real.exp (1/(4*T) + (-(1/(8*T))*(y-x₀)^2)) :=
          Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add]

noncomputable def hkK (t x y : ℝ) := Real.exp (-(x-y)^2/(4*t))
noncomputable def hkX (t x y : ℝ) := (-(x-y)/(2*t)) * hkK t x y
noncomputable def hkXX (t x y : ℝ) := (((x-y)^2/(4*t^2)) - 1/(2*t)) * hkK t x y
noncomputable def hkT (t x y : ℝ) := ((x-y)^2/(4*t^2)) * hkK t x y
noncomputable def hkC (t : ℝ) := (4*Real.pi*t)⁻¹ ^ ((1:ℝ)/2)

lemma hkK_x (t x y : ℝ) (ht : t ≠ 0) : HasDerivAt (fun q => hkK t q y) (hkX t x y) x := by
  simp only [hkK, hkX]
  convert HasDerivAt.exp
    (((((hasDerivAt_id x).sub_const y).pow 2).neg.div_const (4*t))) using 1 <;>
    (try simp [hkK, hkX, hkXX, hkT, hkC]) <;> (try field_simp) <;> (try ring)

lemma hkX_x (t x y : ℝ) (ht : t ≠ 0) : HasDerivAt (fun q => hkX t q y) (hkXX t x y) x := by
  simp only [hkX, hkXX, hkK]
  convert
    (((((hasDerivAt_id x).sub_const y).neg.div_const (2*t)).mul
      (HasDerivAt.exp (((((hasDerivAt_id x).sub_const y).pow 2).neg.div_const (4*t)))))) using 1 <;> try rfl
  simp
  field_simp
  ring

lemma hkK_t (t x y : ℝ) (ht : t ≠ 0) : HasDerivAt (fun q => hkK q x y) (hkT t x y) t := by
  simp only [hkK, hkT]
  -- use the quotient rule
  convert HasDerivAt.exp
    (((hasDerivAt_const t ( -((x-y)^2))).div
      ((hasDerivAt_id t).const_mul 4) (by positivity : (4:ℝ)*t ≠ 0))) using 1 <;>
    (try simp [hkK, hkX, hkXX, hkT, hkC]) <;> (try field_simp) <;> (try ring)

lemma hkC_pos {t : ℝ} (ht : 0 < t) : 0 < hkC t := by
  unfold hkC
  exact Real.rpow_pos_of_pos (by positivity) _

lemma hkC_t (t : ℝ) (ht : 0 < t) :
    HasDerivAt hkC (-(hkC t)/(2*t)) t := by
  unfold hkC
  -- differentiate rpow after the reciprocal
  have hbase : HasDerivAt (fun q : ℝ => (4*Real.pi*q)⁻¹)
      (- (4*Real.pi*t)^(-2:ℤ) * (4*Real.pi)) t := by
    convert ((hasDerivAt_const t (1:ℝ)).div
      (((hasDerivAt_id t).const_mul (4*Real.pi))) (by positivity : (4*Real.pi)*t ≠ 0)) using 1 <;> try rfl
    · funext q; simp
    · simp
      field_simp
  have hpow := Real.hasDerivAt_rpow_const
     (x := (4*Real.pi*t)⁻¹) (p := ((1:ℝ)/2)) (Or.inl (by positivity))
  convert hpow.comp t hbase using 1 <;> try rfl
  rw [Real.rpow_sub_one (by positivity)]
  norm_num [zpow_negSucc]
  field_simp


lemma hk_M_nonneg {f : ℝ → ℝ} {M : ℝ} (h : ∀ y, |f y| ≤ M) : 0 ≤ M :=
  le_trans (abs_nonneg _) (h 0)

lemma hk_big_nonneg (a : ℝ) (ha : 0 < a) : 0 ≤ 1 + a⁻¹ + a⁻¹^2 := by positivity

lemma hk_coeffX_le (a t x₀ x y : ℝ) (ha : 0 < a) (hat : a ≤ t)
    (hx : |x-x₀| ≤ 1) :
    |-(x-y)/(2*t)| ≤ (1 + a⁻¹ + a⁻¹^2) * (|y-x₀|+1)^2 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hr := hk_abs_le x₀ x y hx
  have hr0 : 0 ≤ |y-x₀|+1 := by positivity
  have hm : |x-y|/(2*t) ≤ (|y-x₀|+1)/(2*a) :=
    calc
      _ ≤ (|y-x₀|+1)/(2*t) := div_le_div_of_nonneg_right hr (by positivity)
      _ ≤ (|y-x₀|+1)/(2*a) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
  have ha' : 0 ≤ a⁻¹ := by positivity
  have ha2 : 0 ≤ a⁻¹^2 := by positivity
  have key : (|y-x₀|+1)/(2*a) ≤ (1+a⁻¹+a⁻¹^2) * (|y-x₀|+1)^2 := by
    rw [div_eq_mul_inv]
    have : (2*a)⁻¹ = a⁻¹/2 := by field_simp
    rw [this]
    have hr1 : 1 ≤ |y-x₀|+1 := by linarith [abs_nonneg (y-x₀)]
    nlinarith [sq_nonneg (|y-x₀|)]
  calc
    |-(x-y)/(2*t)| = |x-y|/(2*t) := by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos ht]
      norm_num
    _ ≤ (|y-x₀|+1)/(2*a) := hm
    _ ≤ _ := key

lemma hk_coeffT_le (a t x₀ x y : ℝ) (ha : 0 < a) (hat : a ≤ t)
    (hx : |x-x₀| ≤ 1) :
    |(x-y)^2/(4*t^2)| ≤ (1+a⁻¹+a⁻¹^2) * (|y-x₀|+1)^2 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hr := hk_abs_le x₀ x y hx
  have hr0 : 0 ≤ |y-x₀|+1 := by positivity
  have hr2 : (x-y)^2 ≤ (|y-x₀|+1)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (x-y)) hr0).2 hr
    simpa [sq_abs] using hh
  have hm1 : (x-y)^2/(4*t^2) ≤ (x-y)^2/(4*a^2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith
  have hm2 : (x-y)^2/(4*a^2) ≤ (|y-x₀|+1)^2/(4*a^2) :=
    div_le_div_of_nonneg_right hr2 (by positivity)
  have ha1 : 0 ≤ a⁻¹ := by positivity
  have ha2 : 0 ≤ a⁻¹^2 := by positivity
  have key : (|y-x₀|+1)^2/(4*a^2) ≤ (1+a⁻¹+a⁻¹^2) * (|y-x₀|+1)^2 := by
    have hinv : (4*a^2)⁻¹ = a⁻¹^2/4 := by field_simp
    rw [div_eq_mul_inv, hinv]
    have hn : 0 ≤ (|y-x₀|+1)^2 := sq_nonneg _
    nlinarith
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  exact hm1.trans (hm2.trans key)

lemma hk_coeffXX_le (a t x₀ x y : ℝ) (ha : 0 < a) (hat : a ≤ t)
    (hx : |x-x₀| ≤ 1) :
    |(x-y)^2/(4*t^2) - 1/(2*t)| ≤
       (1+a⁻¹+a⁻¹^2) * (|y-x₀|+1)^2 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hr := hk_abs_le x₀ x y hx
  have hr0 : 0 ≤ |y-x₀|+1 := by positivity
  have hr2 : (x-y)^2 ≤ (|y-x₀|+1)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (x-y)) hr0).2 hr
    simpa [sq_abs] using hh
  have hquad : (x-y)^2/(4*t^2) ≤ (|y-x₀|+1)^2 * (a⁻¹^2/4) := by
    calc
      _ ≤ (x-y)^2/(4*a^2) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        nlinarith
      _ ≤ (|y-x₀|+1)^2/(4*a^2) := div_le_div_of_nonneg_right hr2 (by positivity)
      _ = _ := by field_simp
  have hone : 1/(2*t) ≤ a⁻¹/2 := by
    have : t⁻¹ ≤ a⁻¹ := by simpa [one_div] using (one_div_le_one_div_of_le ha hat)
    simpa [div_eq_mul_inv] using (show t⁻¹/2 ≤ a⁻¹/2 from (div_le_div_of_nonneg_right this (by positivity)))
  calc
    |(x-y)^2/(4*t^2) - 1/(2*t)| ≤ (x-y)^2/(4*t^2) + 1/(2*t) := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [div_nonneg (sq_nonneg (x-y)) (by positivity : (0:ℝ) ≤ 4*t^2), (show 0 < 1/(2*t) by positivity)]
    _ ≤ (|y-x₀|+1)^2 * (a⁻¹^2/4) + a⁻¹/2 := by linarith
    _ ≤ (1+a⁻¹+a⁻¹^2) * (|y-x₀|+1)^2 := by
      have ha1 : 0 ≤ a⁻¹ := by positivity
      have ha2 : 0 ≤ a⁻¹^2 := by positivity
      have hr1 : 1 ≤ |y-x₀|+1 := by linarith [abs_nonneg (y-x₀)]
      nlinarith [sq_nonneg (|y-x₀|)]

noncomputable def hkBound (M a T x : ℝ) (y : ℝ) :=
  (M * (1+a⁻¹+a⁻¹^2) * Real.exp (1/(4*T))) *
     ((|y-x|+1)^2 * Real.exp (-(1/(8*T))*(y-x)^2))

lemma hkBound_int (M a T x : ℝ) (hT : 0 < T) :
    Integrable (hkBound M a T x) := by
  have h := (hk_integrable_poly_shift (1/(8*T)) (by positivity) x).const_mul
       (M * (1+a⁻¹+a⁻¹^2) * Real.exp (1/(4*T)))
  convert h using 1
  rfl

lemma hk_boundK (f : ℝ → ℝ) {M a T x₀ t x y : ℝ}
    (hf : ∀ y, |f y| ≤ M) (ha : 0 < a) (hat : a ≤ t)
    (hT : 0 < T) (htT : t ≤ T) (hx : |x-x₀| ≤ 1) :
    ‖hkK t x y * f y‖ ≤ hkBound M a T x₀ y := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hM := hk_M_nonneg hf
  have hg := hk_gaussian_le T t x₀ x y hT ht htT hx
  have hc : 1 ≤ (1+a⁻¹+a⁻¹^2)*(|y-x₀|+1)^2 := by
    have hR : 1 ≤ |y-x₀|+1 := by linarith [abs_nonneg (y-x₀)]
    have ha1 : 0 ≤ a⁻¹ := by positivity
    have ha2 : 0 ≤ a⁻¹^2 := by positivity
    nlinarith [sq_nonneg (|y-x₀|)]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hkK, abs_of_pos (Real.exp_pos _)]
  unfold hkBound
  calc
    Real.exp (-(x-y)^2/(4*t)) * |f y|
        ≤ (Real.exp (1/(4*T))*Real.exp (-(1/(8*T))*(y-x₀)^2)) * M :=
          mul_le_mul hg (hf y) (abs_nonneg _) (by positivity)
    _ ≤ (M * (1+a⁻¹+a⁻¹^2) * Real.exp (1/(4*T))) *
          ((|y-x₀|+1)^2 * Real.exp (-(1/(8*T))*(y-x₀)^2)) := by
          have ep : 0 ≤ Real.exp (1/(4*T)) * Real.exp (-(1/(8*T))*(y-x₀)^2) := by positivity
          calc
            _ ≤ M * ((1+a⁻¹+a⁻¹^2)*(|y-x₀|+1)^2) *
                 (Real.exp (1/(4*T)) * Real.exp (-(1/(8*T))*(y-x₀)^2)) := by
                    calc
                      _ = M * 1 * (Real.exp (1/(4*T)) * Real.exp (-(1/(8*T))*(y-x₀)^2)) := by ring
                      _ ≤ _ := by gcongr
            _ = _ := by ring

lemma hk_boundX (f : ℝ → ℝ) {M a T x₀ t x y : ℝ}
    (hf : ∀ y, |f y| ≤ M) (ha : 0 < a) (hat : a ≤ t)
    (hT : 0 < T) (htT : t ≤ T) (hx : |x-x₀| ≤ 1) :
    ‖hkX t x y * f y‖ ≤ hkBound M a T x₀ y := by
  have ht := lt_of_lt_of_le ha hat
  have hM := hk_M_nonneg hf
  have hg := hk_gaussian_le T t x₀ x y hT ht htT hx
  have hc := hk_coeffX_le a t x₀ x y ha hat hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hkX, abs_mul, hkK, abs_of_pos (Real.exp_pos _)]
  unfold hkBound
  have ep : 0 ≤ Real.exp (1/(4*T)) := (Real.exp_pos _).le
  have ep2 : 0 ≤ Real.exp (-(1/(8*T))*(y-x₀)^2) := (Real.exp_pos _).le
  calc
    (|-(x-y)/(2*t)| * Real.exp (-(x-y)^2/(4*t))) * |f y|
       ≤ (((1+a⁻¹+a⁻¹^2)*(|y-x₀|+1)^2) *
           (Real.exp (1/(4*T))* Real.exp (-(1/(8*T))*(y-x₀)^2))) * M := by
         gcongr
         exact hf y
    _ = _ := by ring

lemma hk_boundT (f : ℝ → ℝ) {M a T x₀ t x y : ℝ}
    (hf : ∀ y, |f y| ≤ M) (ha : 0 < a) (hat : a ≤ t)
    (hT : 0 < T) (htT : t ≤ T) (hx : |x-x₀| ≤ 1) :
    ‖hkT t x y * f y‖ ≤ hkBound M a T x₀ y := by
  have ht := lt_of_lt_of_le ha hat
  have hM := hk_M_nonneg hf
  have hg := hk_gaussian_le T t x₀ x y hT ht htT hx
  have hc := hk_coeffT_le a t x₀ x y ha hat hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hkT, abs_mul, hkK, abs_of_pos (Real.exp_pos _)]
  unfold hkBound
  calc
    (|(x-y)^2/(4*t^2)| * Real.exp (-(x-y)^2/(4*t))) * |f y|
       ≤ (((1+a⁻¹+a⁻¹^2)*(|y-x₀|+1)^2) *
           (Real.exp (1/(4*T))* Real.exp (-(1/(8*T))*(y-x₀)^2))) * M := by
         gcongr
         exact hf y
    _ = _ := by ring

lemma hk_boundXX (f : ℝ → ℝ) {M a T x₀ t x y : ℝ}
    (hf : ∀ y, |f y| ≤ M) (ha : 0 < a) (hat : a ≤ t)
    (hT : 0 < T) (htT : t ≤ T) (hx : |x-x₀| ≤ 1) :
    ‖hkXX t x y * f y‖ ≤ hkBound M a T x₀ y := by
  have ht := lt_of_lt_of_le ha hat
  have hM := hk_M_nonneg hf
  have hg := hk_gaussian_le T t x₀ x y hT ht htT hx
  have hc := hk_coeffXX_le a t x₀ x y ha hat hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hkXX, abs_mul, hkK, abs_of_pos (Real.exp_pos _)]
  unfold hkBound
  calc
    (|(x-y)^2/(4*t^2)-1/(2*t)| * Real.exp (-(x-y)^2/(4*t))) * |f y|
       ≤ (((1+a⁻¹+a⁻¹^2)*(|y-x₀|+1)^2) *
           (Real.exp (1/(4*T))* Real.exp (-(1/(8*T))*(y-x₀)^2))) * M := by
         gcongr
         exact hf y
    _ = _ := by ring

lemma hk_meas (f : ℝ → ℝ) (hf : Continuous f) (t x : ℝ) :
  AEStronglyMeasurable (fun y => hkK t x y * f y) := by
   unfold hkK
   fun_prop
lemma hk_measX (f : ℝ → ℝ) (hf : Continuous f) (t x : ℝ) :
  AEStronglyMeasurable (fun y => hkX t x y * f y) := by
   unfold hkX hkK; fun_prop
lemma hk_measXX (f : ℝ → ℝ) (hf : Continuous f) (t x : ℝ) :
  AEStronglyMeasurable (fun y => hkXX t x y * f y) := by
   unfold hkXX hkK; fun_prop
lemma hk_measT (f : ℝ → ℝ) (hf : Continuous f) (t x : ℝ) :
  AEStronglyMeasurable (fun y => hkT t x y * f y) := by
   unfold hkT hkK; fun_prop

noncomputable def hkI (f : ℝ → ℝ) (t x : ℝ) := ∫ y : ℝ, hkK t x y * f y
noncomputable def hkIx (f : ℝ → ℝ) (t x : ℝ) := ∫ y : ℝ, hkX t x y * f y
noncomputable def hkIxx (f : ℝ → ℝ) (t x : ℝ) := ∫ y : ℝ, hkXX t x y * f y
noncomputable def hkIt (f : ℝ → ℝ) (t x : ℝ) := ∫ y : ℝ, hkT t x y * f y

lemma hkI_x (f) (hc : Continuous f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
  {t x : ℝ} (ht : 0 < t) : HasDerivAt (hkI f t) (hkIx f t x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (bound := hkBound M t t x)
    (F := fun q y => hkK t q y * f y)
    (F' := fun q y => hkX t q y * f y)
    (s := Set.Icc (x-1) (x+1))
    (x₀ := x)
    (by exact Icc_mem_nhds (by linarith) (by linarith))
    (by filter_upwards [] with q; exact hk_meas f hc t q)
    (by
      apply Integrable.mono' (hkBound_int M t t x ht) (hk_meas f hc t x)
      exact Filter.Eventually.of_forall (fun y => hk_boundK f hb ht (le_rfl) ht (le_rfl) (by simp)))
    (hk_measX f hc t x)
    (by
      exact Filter.Eventually.of_forall (fun y q hq =>
        hk_boundX f hb ht (le_rfl) ht (le_rfl)
          (by rw [abs_le]; constructor <;> linarith [hq.1, hq.2])))
    (hkBound_int M t t x ht)
    (by
      exact Filter.Eventually.of_forall (fun y q hq =>
        (hkK_x t q y (ne_of_gt ht)).mul_const (f y)))
  exact h.2

lemma hkIx_x (f) (hc : Continuous f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
  {t x : ℝ} (ht : 0 < t) : HasDerivAt (hkIx f t) (hkIxx f t x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := hkBound M t t x)
    (F := fun q y => hkX t q y * f y)
    (F' := fun q y => hkXX t q y * f y)
    (s := Set.Icc (x-1) (x+1)) (x₀ := x)
    (by exact Icc_mem_nhds (by linarith) (by linarith))
    (by filter_upwards [] with q; exact hk_measX f hc t q)
    (by
      apply Integrable.mono' (hkBound_int M t t x ht) (hk_measX f hc t x)
      exact Filter.Eventually.of_forall (fun y => hk_boundX f hb ht (le_rfl) ht (le_rfl) (by simp)))
    (hk_measXX f hc t x)
    (by
      exact Filter.Eventually.of_forall (fun y q hq =>
        hk_boundXX f hb ht (le_rfl) ht (le_rfl)
          (by rw [abs_le]; constructor <;> linarith [hq.1, hq.2])))
    (hkBound_int M t t x ht)
    (by exact Filter.Eventually.of_forall (fun y q hq => (hkX_x t q y (ne_of_gt ht)).mul_const (f y)))
  exact h.2

lemma hkI_t (f) (hc : Continuous f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
  {t x : ℝ} (ht : 0 < t) : HasDerivAt (fun q => hkI f q x) (hkIt f t x) t := by
  let a := t/2
  let T := t + 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hT : 0 < T := by dsimp [T]; linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := hkBound M a T x)
    (F := fun q y => hkK q x y * f y)
    (F' := fun q y => hkT q x y * f y)
    (s := Set.Ioo a T) (x₀ := t)
    (by apply IsOpen.mem_nhds isOpen_Ioo; dsimp [a,T]; constructor <;> linarith)
    (by filter_upwards [] with q; exact hk_meas f hc q x)
    (by apply Integrable.mono' (hkBound_int M a T x hT) (hk_meas f hc t x)
        exact Filter.Eventually.of_forall (fun y => hk_boundK f hb ha (by dsimp [a]; linarith)
          hT (by dsimp [T]; linarith) (by simp)))
    (hk_measT f hc t x)
    (by
      exact Filter.Eventually.of_forall (fun y q hq =>
        hk_boundT f hb ha (le_of_lt hq.1) hT (le_of_lt hq.2) (by simp)))
    (hkBound_int M a T x hT)
    (by exact Filter.Eventually.of_forall (fun y q hq =>
      (hkK_t q x y (ne_of_gt (lt_of_lt_of_le ha (le_of_lt hq.1)))).mul_const (f y)))
  exact h.2

lemma hkIxx_eq (f) (hc : Continuous f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
 (t x : ℝ) (ht : 0 < t) :
 hkIxx f t x = hkIt f t x - (1/(2*t))* hkI f t x := by
  have hK : Integrable (fun y => hkK t x y * f y) := by
    apply Integrable.mono' (hkBound_int M t t x ht) (hk_meas f hc t x)
    exact Filter.Eventually.of_forall (fun y => hk_boundK f hb ht le_rfl ht le_rfl (by simp))
  have hT : Integrable (fun y => hkT t x y * f y) := by
    apply Integrable.mono' (hkBound_int M t t x ht) (hk_measT f hc t x)
    exact Filter.Eventually.of_forall (fun y => hk_boundT f hb ht le_rfl ht le_rfl (by simp))
  have heq : (fun y => hkXX t x y * f y) =
      (fun y => (hkT t x y * f y) - (1/(2*t)) * (hkK t x y * f y)) := by
    funext y
    dsimp [hkXX, hkT, hkK]
    ring
  simp only [hkIxx, hkIt, hkI, heq]
  rw [integral_sub hT (hK.const_mul _), integral_const_mul]

lemma heat_eq {f} {t x : ℝ} (ht : 0 < t) :
  heatSolution f t x = hkC t * hkI f t x := by simp [heatSolution, ht, hkC, hkI, hkK]

lemma heat_scaled {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ) :
  heatSolution f t x = (Real.pi ^ ((1:ℝ)/2))⁻¹ *
      ∫ z : ℝ, Real.exp (-(z^2)) * f (x + (2*Real.sqrt t)*z) := by
  let b : ℝ := 2 * Real.sqrt t
  have hb : 0 < b := by dsimp [b]; positivity
  let g : ℝ → ℝ := fun y => Real.exp (-(x-y)^2/(4*t)) * f y
  have trans : (∫ u : ℝ, g (u + x)) = ∫ y : ℝ, g y := integral_add_right_eq_self g x
  have scale := Measure.integral_comp_mul_left (fun u : ℝ => g (u + x)) b
  have eq : (∫ y : ℝ, g y) = b * ∫ z : ℝ, Real.exp (-(z^2)) * f (x + b*z) := by
    have ker : (fun z : ℝ => g (b*z+x)) =
          (fun z : ℝ => Real.exp (-(z^2)) * f (x+b*z)) := by
      funext z
      dsimp [g]
      have hs : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt ht)
      have harg : -(x-(b*z+x))^2/(4*t) = -(z^2) := by
        dsimp [b]
        field_simp
        nlinarith
      rw [harg]
      congr 1 <;> ring
    have hsc : (∫ z : ℝ, g (b*z + x)) = b⁻¹ * (∫ y : ℝ, g y) := by
      simpa [abs_of_pos hb, trans] using scale
    rw [ker] at hsc
    calc
      ∫ y : ℝ, g y = b * (b⁻¹ * ∫ y : ℝ, g y) := by field_simp
      _ = _ := by rw [← hsc]
  rw [heat_eq ht]
  change hkC t * (∫ y : ℝ, g y) = _
  rw [eq]
  dsimp [hkC, b]
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hcalc : (4*Real.pi*t)⁻¹ ^ ((1:ℝ)/2) * (2*Real.sqrt t) =
       (Real.pi ^ ((1:ℝ)/2))⁻¹ := by
    rw [Real.inv_rpow (by positivity)];
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi) (le_of_lt ht)]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (le_of_lt hp)]
    rw [show (4:ℝ) ^ ((1:ℝ)/2) = 2 by norm_num]
    rw [← Real.sqrt_eq_rpow t]
    rw [← Real.sqrt_eq_rpow π]
    field_simp
  rw [← mul_assoc, hcalc]


/-- The normalized, translated Gaussian tends to the original value on the positive
side of zero.  This is the (pointwise) approximate identity fact needed at `t=0`. -/
lemma hk_trace (f : ℝ → ℝ) (hf : Continuous f) {M : ℝ}
    (hM : ∀ y : ℝ, |f y| ≤ M) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => heatSolution f t x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hpos : ∀ᶠ t : ℝ in l, 0 < t := by
    change {t : ℝ | 0 < t} ∈ l
    exact self_mem_nhdsWithin
  -- On making the change of variables in `heat_scaled`, the gaussian has no
  -- remaining dependence on `t`.  It is therefore a very simple dominated
  -- convergence application.
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t) l (nhds (0 : ℝ)) := by
    have h := (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto
    have h' := h.mono_left (show l ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
    simpa using h'
  let F : ℝ → ℝ → ℝ := fun t z =>
    Real.exp (-(z^2)) * f (x + (2 * Real.sqrt t) * z)
  let Flim : ℝ → ℝ := fun z => Real.exp (-(z^2)) * f x
  let B : ℝ → ℝ := fun z => M * Real.exp (-(z^2))
  have hB : Integrable B := by
    have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul M
    simpa [B] using h
  have hmeas : ∀ᶠ t : ℝ in l, AEStronglyMeasurable (F t) := by
    filter_upwards [] with t
    have hcont : Continuous (fun z : ℝ =>
        Real.exp (-(z^2)) * f (x + (2 * Real.sqrt t) * z)) := by
      fun_prop
    simpa [F] using hcont.aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in l, ∀ᵐ z : ℝ, ‖F t z‖ ≤ B z := by
    filter_upwards [] with t
    exact Filter.Eventually.of_forall (fun z => by
      dsimp [F, B]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-(z^2)) * |f (x + (2 * Real.sqrt t) * z)|
            ≤ Real.exp (-(z^2)) * M :=
              mul_le_mul_of_nonneg_left (hM _) (by positivity)
        _ = M * Real.exp (-(z^2)) := by ring)
  have hlim : ∀ᵐ z : ℝ, Tendsto (fun t : ℝ => F t z) l (nhds (Flim z)) := by
    refine MeasureTheory.ae_of_all _ ?_
    intro z
    have harg : Tendsto (fun t : ℝ => x + (2 * Real.sqrt t) * z) l (nhds x) := by
      have h2 := Filter.Tendsto.const_mul (2 : ℝ) hsqrt
      have h3 := Filter.Tendsto.mul_const z h2
      have h4 := Filter.Tendsto.const_add x h3
      simpa using h4
    have hfarg : Tendsto (fun t : ℝ => f (x + (2 * Real.sqrt t) * z)) l
        (nhds (f x)) := by
      have := (hf.continuousAt (x := x)).tendsto.comp harg
      simpa [Function.comp_def] using this
    have hh := Filter.Tendsto.const_mul (Real.exp (-(z^2))) hfarg
    simpa [F, Flim] using hh
  have hInt : Tendsto (fun t : ℝ => ∫ z : ℝ, F t z) l
      (nhds (∫ z : ℝ, Flim z)) := by
    exact tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB hlim
  have hmass : (∫ z : ℝ, Real.exp (-(z^2))) =
      Real.pi ^ ((1 : ℝ) / 2) := by
    simpa [Real.sqrt_eq_rpow] using (integral_gaussian (1 : ℝ))
  have hpow : Real.pi ^ ((1 : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hval : (Real.pi ^ ((1 : ℝ) / 2))⁻¹ * (∫ z : ℝ, Flim z) = f x := by
    dsimp [Flim]
    rw [integral_mul_const, hmass]
    exact inv_mul_cancel_left₀ hpow (f x)
  have hmul : Tendsto
       (fun t : ℝ => (Real.pi ^ ((1 : ℝ) / 2))⁻¹ * (∫ z : ℝ, F t z)) l
       (nhds ((Real.pi ^ ((1 : ℝ) / 2))⁻¹ * (∫ z : ℝ, Flim z))) := by
     exact Filter.Tendsto.const_mul _ hInt
  have heq :
       (fun t : ℝ => (Real.pi ^ ((1 : ℝ) / 2))⁻¹ * (∫ z : ℝ, F t z))
        =ᶠ[l] (fun t : ℝ => heatSolution f t x) := by
    filter_upwards [hpos] with t ht
    -- the equality `heat_scaled` is valid in the open half line
    symm
    simpa [F] using (heat_scaled (f := f) ht x)
  have hfin : Tendsto (fun t : ℝ => heatSolution f t x) l
      (nhds ((Real.pi ^ ((1 : ℝ) / 2))⁻¹ * (∫ z : ℝ, Flim z))) :=
    hmul.congr' heq
  change Tendsto (fun t : ℝ => heatSolution f t x) l (nhds (f x))
  rw [hval] at hfin
  exact hfin
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem heat_kernel_solves_heat_equation (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    -- The PDE on (0, ∞) × ℝ.
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    -- Initial condition recovered as a one-sided limit at t = 0.
    (∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) :=
/-ResultProofBegin-/ by
  obtain ⟨M,hM⟩ := hf_bdd
  constructor
  · intro t ht x
    refine ⟨(fun y => hkC t * hkIx f t y), hkC t * hkIxx f t x, ?_, ?_, ?_⟩
    · intro y
      have h := (hkI_x f hf_cont hM ht : HasDerivAt (hkI f t) (hkIx f t y) y)
      have hh := (HasDerivAt.const_mul (hkC t) h)
      simpa [heat_eq ht] using hh
    · exact HasDerivAt.const_mul (hkC t) (hkIx_x f hf_cont hM ht)
    ·
      -- For positive time the cut-off definition is just the product of its
      -- normalization factor and the (unnormalized) integral.
      have hprod' : HasDerivAt
          (fun s : ℝ => hkC s * hkI f s x)
          ((-(hkC t)/(2*t)) * hkI f t x + hkC t * hkIt f t x) t := by
        exact (hkC_t t ht).mul (hkI_t f hf_cont hM (x := x) ht)
      have heq : (fun s : ℝ => heatSolution f s x) =ᶠ[nhds t]
          (fun s : ℝ => hkC s * hkI f s x) := by
        have hp : Set.Ioi (0 : ℝ) ∈ nhds t := Ioi_mem_nhds ht
        filter_upwards [hp] with s hs
        exact heat_eq hs
      have hder : HasDerivAt (fun s : ℝ => heatSolution f s x)
          ((-(hkC t)/(2*t)) * hkI f t x + hkC t * hkIt f t x) t :=
        hprod'.congr_of_eventuallyEq heq
      have hxx := hkIxx_eq f hf_cont hM t x ht
      convert hder using 1
      -- This is exactly the adjustment of the derivative of the normalizing
      -- constant.
      rw [hxx]
      ring
  · intro x
    exact hk_trace f hf_cont hM x
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
