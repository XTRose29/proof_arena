import Submission.CenteredLinearControl
import Mathlib.Analysis.ODE.DiscreteGronwall

namespace Submission.Helpers

open Filter MeasureTheory

noncomputable def prefixProduct (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, a i

@[simp]
lemma prefixProduct_zero (a : ℕ → ℝ) : prefixProduct a 0 = 1 := by
  simp [prefixProduct]

lemma prefixProduct_succ (a : ℕ → ℝ) (n : ℕ) :
    prefixProduct a (n + 1) = prefixProduct a n * a n := by
  simp [prefixProduct, Finset.prod_range_succ]

lemma prefixProduct_pos {a : ℕ → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) :
    0 < prefixProduct a n := by
  exact Finset.prod_pos fun i _hi => ha i

lemma nonlinear_recurrence_normalized_gronwall
    {a d : ℕ → ℝ} {B c : ℝ}
    (hd : ∀ n, 0 ≤ d n) (hB : 0 ≤ B) (hc : 0 < c)
    (ha : ∀ n, c ≤ a n)
    (hstep : ∀ n, d (n + 1) ≤ a n * d n + B * d n ^ 2)
    (n : ℕ) :
    d n / prefixProduct a n ≤
      d 0 * Real.exp
        (∑ i ∈ Finset.range n, (B / a i) * d i) := by
  have ha_pos : ∀ i, 0 < a i := fun i => hc.trans_le (ha i)
  let u : ℕ → ℝ := fun i => d i / prefixProduct a i
  let e : ℕ → ℝ := fun i => (B / a i) * d i
  have hu_nonneg : 0 ≤ u 0 := by
    simp [u, hd]
  have he_nonneg : ∀ i, 0 ≤ e i := by
    intro i
    exact mul_nonneg (div_nonneg hB (ha_pos i).le) (hd i)
  have hu_step : ∀ i, u (i + 1) ≤ (1 + e i) * u i + 0 := by
    intro i
    have hp_pos := prefixProduct_pos ha_pos i
    have hai_pos := ha_pos i
    dsimp [u, e]
    rw [prefixProduct_succ]
    apply (div_le_iff₀ (mul_pos hp_pos hai_pos)).2
    calc
      d (i + 1) ≤ a i * d i + B * d i ^ 2 := hstep i
      _ = (1 + B / a i * d i) *
          (d i / prefixProduct a i) *
            (prefixProduct a i * a i) := by
        field_simp [hp_pos.ne', hai_pos.ne']
      _ = ((1 + B / a i * d i) *
          (d i / prefixProduct a i) + 0) *
            (prefixProduct a i * a i) := by ring
  have hgronwall := discrete_gronwall
    (u := u) (b := fun _ => 0) (c := e) hu_nonneg
      (fun i _hi => hu_step i) (fun i _hi => he_nonneg i)
      (fun _i _hi => le_rfl) (Nat.zero_le n)
  simpa [u, e] using hgronwall

lemma nonlinear_recurrence_le_two_prefixProduct
    {a d : ℕ → ℝ} {B c M b : ℝ} {Q : ℕ}
    (hd : ∀ n, 0 ≤ d n) (hB : 0 ≤ B) (hc : 0 < c)
    (ha : ∀ n, c ≤ a n)
    (hstep : ∀ n, d (n + 1) ≤ a n * d n + B * d n ^ 2)
    (hM : 0 ≤ M) (hb : 1 ≤ b)
    (hprod : ∀ n, n ≤ Q → prefixProduct a n ≤ M * b ^ n)
    (hsmall : (Q : ℝ) * (2 * (B / c) * M * b ^ Q * d 0) ≤ Real.log 2) :
    ∀ n, n ≤ Q → d n ≤ 2 * prefixProduct a n * d 0 := by
  have ha_pos : ∀ i, 0 < a i := fun i => hc.trans_le (ha i)
  have hBc : 0 ≤ B / c := div_nonneg hB hc.le
  have hd0 : 0 ≤ d 0 := hd 0
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hnorm := nonlinear_recurrence_normalized_gronwall
        hd hB hc ha hstep n
      have hterm : ∀ i ∈ Finset.range n,
          (B / a i) * d i ≤ 2 * (B / c) * M * b ^ Q * d 0 := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hiQ : i ≤ Q := (Nat.le_of_lt hi_lt).trans hn
        have hdi := ih i hi_lt hiQ
        have hprod_i := hprod i hiQ
        have hpow : b ^ i ≤ b ^ Q := pow_le_pow_right₀ hb hiQ
        have hdiv : B / a i ≤ B / c := by
          exact div_le_div_of_nonneg_left hB hc (ha i)
        calc
          (B / a i) * d i ≤ (B / c) * d i :=
            mul_le_mul_of_nonneg_right hdiv (hd i)
          _ ≤ (B / c) * (2 * prefixProduct a i * d 0) :=
            mul_le_mul_of_nonneg_left hdi hBc
          _ ≤ (B / c) * (2 * (M * b ^ i) * d 0) := by
            gcongr
          _ ≤ (B / c) * (2 * (M * b ^ Q) * d 0) := by
            gcongr
          _ = 2 * (B / c) * M * b ^ Q * d 0 := by ring
      have hsum :
          (∑ i ∈ Finset.range n, (B / a i) * d i) ≤ Real.log 2 := by
        have hconst_nonneg :
            0 ≤ 2 * (B / c) * M * b ^ Q * d 0 := by positivity
        calc
          (∑ i ∈ Finset.range n, (B / a i) * d i) ≤
              ∑ _i ∈ Finset.range n,
                (2 * (B / c) * M * b ^ Q * d 0) :=
            Finset.sum_le_sum hterm
          _ = (n : ℝ) * (2 * (B / c) * M * b ^ Q * d 0) := by
            simp [mul_comm]
          _ ≤ (Q : ℝ) * (2 * (B / c) * M * b ^ Q * d 0) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hconst_nonneg
          _ ≤ Real.log 2 := hsmall
      have hexp : Real.exp
          (∑ i ∈ Finset.range n, (B / a i) * d i) ≤ 2 := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact Real.exp_le_exp.mpr hsum
      have hp_nonneg : 0 ≤ prefixProduct a n :=
        (prefixProduct_pos ha_pos n).le
      have hnormalized : d n / prefixProduct a n ≤ 2 * d 0 := by
        calc
          d n / prefixProduct a n ≤ d 0 * Real.exp
              (∑ i ∈ Finset.range n, (B / a i) * d i) := hnorm
          _ ≤ d 0 * 2 := mul_le_mul_of_nonneg_left hexp hd0
          _ = 2 * d 0 := by ring
      calc
        d n = prefixProduct a n * (d n / prefixProduct a n) := by
          field_simp [(prefixProduct_pos ha_pos n).ne']
        _ ≤ prefixProduct a n * (2 * d 0) :=
          mul_le_mul_of_nonneg_left hnormalized hp_nonneg
        _ = 2 * prefixProduct a n * d 0 := by ring

end Submission.Helpers
