import Submission.PrimeSeries
import Mathlib.NumberTheory.LSeries.Positivity

open Complex Filter Topology
open scoped ComplexOrder LSeries.notation

namespace Submission.Landau

private lemma iterate_logMul_apply (a : ℕ → ℝ) (m n : ℕ) :
    (LSeries.logMul^[m] (fun k => (a k : ℂ))) n =
      ((Real.log n) ^ m * a n : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih]
      rw [← natCast_log]
      push_cast
      ring

private noncomputable def taylorAtom (a : ℕ → ℝ) (c x : ℝ) (m n : ℕ) : ℝ :=
  (m.factorial : ℝ)⁻¹ * (c - x) ^ m *
    (LSeries.term (LSeries.logMul^[m] (fun k => (a k : ℂ))) c n).re

private lemma iterate_logMul_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (m n : ℕ) :
    0 ≤ (LSeries.logMul^[m] (fun k => (a k : ℂ))) n := by
  rw [iterate_logMul_apply]
  exact_mod_cast mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) m) (ha n)

private lemma taylorAtom_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {c x : ℝ} (hxc : x ≤ c) (m n : ℕ) :
    0 ≤ taylorAtom a c x m n := by
  unfold taylorAtom
  have hterm := LSeries.term_nonneg (iterate_logMul_nonneg ha m n) c
  have htermRe : 0 ≤ (LSeries.term
      (LSeries.logMul^[m] (fun k => (a k : ℂ))) c n).re :=
    (Complex.le_def.mp hterm).1
  positivity

private lemma tsum_taylorAtom_eq
    {a : ℕ → ℝ} {f : ℂ → ℂ} {c x : ℝ}
    (hc : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < c)
    (hderiv : ∀ m, iteratedDeriv m f c =
      iteratedDeriv m (LSeries fun n => (a n : ℂ)) c) (m : ℕ) :
    ∑' n, taylorAtom a c x m n =
      (((m.factorial : ℂ)⁻¹ * (x - c) ^ m * iteratedDeriv m f c)).re := by
  rw [hderiv, LSeries_iteratedDeriv m hc]
  have hsum : LSeriesSummable
      (LSeries.logMul^[m] (fun n => (a n : ℂ))) c :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simpa using hc
  have hscalar :
      (m.factorial : ℂ)⁻¹ * (x - c : ℂ) ^ m * (-1 : ℂ) ^ m =
        (((m.factorial : ℝ)⁻¹ * (c - x) ^ m : ℝ) : ℂ) := by
    calc
      _ = (m.factorial : ℂ)⁻¹ * (((x - c : ℂ) * -1) ^ m) := by
        rw [mul_assoc, ← mul_pow]
      _ = (m.factorial : ℂ)⁻¹ * (c - x : ℂ) ^ m := by
        congr 2
        ring
      _ = _ := by
        push_cast
        rfl
  rw [← mul_assoc, hscalar, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [LSeries, re_tsum hsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold taylorAtom
  rfl

private lemma tsum_taylorAtom_col_eq
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {c x : ℝ} (n : ℕ) :
    ∑' m, taylorAtom a c x m n =
      ‖LSeries.term (fun k => (a k : ℂ)) x n‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [taylorAtom]
  have hn0 : n ≠ 0 := hn.ne'
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hterm (m : ℕ) :
      (LSeries.term (LSeries.logMul^[m] (fun k => (a k : ℂ))) c n).re =
        (Real.log n) ^ m * a n / (n : ℝ) ^ c := by
    rw [LSeries.term_of_ne_zero hn0, iterate_logMul_apply]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hnR.le]
    norm_cast
  simp_rw [taylorAtom, hterm]
  have hexp := (NormedSpace.expSeries_div_hasSum_exp
    ((c - x) * Real.log n : ℝ)).tsum_eq
  rw [show (∑' m : ℕ, (m.factorial : ℝ)⁻¹ * (c - x) ^ m *
      ((Real.log n) ^ m * a n / (n : ℝ) ^ c)) =
      a n / (n : ℝ) ^ c *
        ∑' m : ℕ, (((c - x) * Real.log n) ^ m / m.factorial) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [mul_pow]
    field_simp]
  rw [hexp]
  rw [← Real.exp_eq_exp_ℝ, mul_comm (c - x), ← Real.rpow_def_of_pos hnR]
  rw [LSeries.norm_term_eq, if_neg hn0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (ha n), Complex.ofReal_re]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hnR.le,
    ← Real.rpow_neg hnR.le, mul_assoc, ← Real.rpow_add hnR]
  congr 1
  congr 1
  ring

theorem LSeriesSummable_of_taylor_extension
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {f : ℂ → ℂ} {c x r : ℝ}
    (hc : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < c)
    (hxc : x < c) (hxr : c - x < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hderiv : ∀ m, iteratedDeriv m f c =
      iteratedDeriv m (LSeries fun n => (a n : ℂ)) c) :
    LSeriesSummable (fun n => (a n : ℂ)) x := by
  have hxball : (x : ℂ) ∈ Metric.ball (c : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hxc.le), neg_sub]
    exact hxr
  have htaylor := Complex.hasSum_taylorSeries_on_ball hf hxball
  have houter : Summable (fun m => ∑' n, taylorAtom a c x m n) := by
    refine (hasSum_re htaylor).summable.congr (fun m => ?_)
    rw [tsum_taylorAtom_eq hc hderiv]
    simp only [smul_eq_mul]
    rw [mul_assoc]
  have hrow (m : ℕ) : Summable (fun n => taylorAtom a c x m n) := by
    have hs : LSeriesSummable
        (LSeries.logMul^[m] (fun n => (a n : ℂ))) c :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simpa using hc
    exact ((hasSum_re hs.hasSum).summable.mul_left
      ((m.factorial : ℝ)⁻¹ * (c - x) ^ m)).congr fun n => by
      simp only [taylorAtom]
  have hprod : Summable (fun mn : ℕ × ℕ => taylorAtom a c x mn.1 mn.2) :=
    (summable_prod_of_nonneg (fun mn => taylorAtom_nonneg ha hxc.le mn.1 mn.2)).2
      ⟨hrow, houter⟩
  have hcols : Summable (fun n => ∑' m, taylorAtom a c x m n) :=
    (summable_prod_of_nonneg
      (fun nm => taylorAtom_nonneg ha hxc.le nm.2 nm.1)).1 hprod.prod_symm |>.2
  rw [LSeriesSummable, ← summable_norm_iff]
  exact hcols.congr fun n => tsum_taylorAtom_col_eq ha n

theorem no_analyticContinuationAt_abscissa
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {f : ℂ → ℂ} {beta r : ℝ}
    (hbeta : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) = beta)
    (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball beta r))
    (heq : Set.EqOn f (LSeries fun n => (a n : ℂ))
      (Metric.ball beta r ∩ {s : ℂ | beta < s.re})) :
    False := by
  let d := r / 8
  let c := beta + d
  let x := beta - d
  have hd : 0 < d := div_pos hr (by norm_num)
  have hcBeta : beta < c := by dsimp [c]; linarith
  have hxBeta : x < beta := by dsimp [x]; linarith
  have hxc : x < c := hxBeta.trans hcBeta
  have hcBall : (c : ℂ) ∈ Metric.ball (beta : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    dsimp [c, d]
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hUOpen : IsOpen (Metric.ball (beta : ℂ) r ∩ {s : ℂ | beta < s.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hcU : (c : ℂ) ∈ Metric.ball (beta : ℂ) r ∩ {s : ℂ | beta < s.re} :=
    ⟨hcBall, hcBeta⟩
  have hevent : f =ᶠ[𝓝 (c : ℂ)] LSeries (fun n => (a n : ℂ)) :=
    eventually_of_mem (hUOpen.mem_nhds hcU) heq
  have hderiv (m : ℕ) : iteratedDeriv m f c =
      iteratedDeriv m (LSeries fun n => (a n : ℂ)) c :=
    hevent.iteratedDeriv_eq m
  have hlocal : DifferentiableOn ℂ f (Metric.ball (c : ℂ) (r / 2)) := by
    apply hf.mono
    apply Metric.ball_subset_ball'
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    dsimp [c, d]
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hc : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < c := by
    rw [hbeta]
    exact_mod_cast hcBeta
  have hxr : c - x < r / 2 := by
    dsimp [c, x, d]
    linarith
  have hsum := LSeriesSummable_of_taylor_extension ha hc hxc hxr hlocal hderiv
  have hab := hsum.abscissaOfAbsConv_le
  rw [hbeta] at hab
  have : beta ≤ x := by exact_mod_cast hab
  linarith

end Submission.Landau
