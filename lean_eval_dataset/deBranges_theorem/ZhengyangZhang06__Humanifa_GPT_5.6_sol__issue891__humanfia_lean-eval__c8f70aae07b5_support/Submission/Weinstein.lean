import Submission.StrongGrunsky
import Submission.RobertsonRoot

open Metric

namespace Submission

lemma exteriorFactorPowerSeries_pow_coeff_recurrence
    {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (exteriorFactorPowerSeries L ^ n) +
        ∑ k : Fin n,
          PowerSeries.coeff (n - k) (exteriorFactorPowerSeries L ^ n) *
            ((k : ℕ) * taylorCoeff L k) =
      -((n : ℕ) * taylorCoeff L n) := by
  let q : ℂ → ℂ := fun z => exteriorAnalyticFactor L z ^ n
  let B : ℂ → ℂ := fun z => -(n : ℂ) * L z
  have hq : DifferentiableOn ℂ q (ball 0 R) :=
    (exteriorAnalyticFactor_differentiableOn hL).pow n
  have hB : DifferentiableOn ℂ B (ball 0 R) := by
    exact (differentiableOn_const (c := -(n : ℂ))).mul hL
  have hderiv : Set.EqOn (deriv q) (q * deriv B) (ball 0 R) := by
    intro z hz
    have hEAt : DifferentiableAt ℂ (exteriorAnalyticFactor L) z :=
      (exteriorAnalyticFactor_differentiableOn hL).differentiableAt
        (isOpen_ball.mem_nhds hz)
    have hLAt : DifferentiableAt ℂ L z :=
      hL.differentiableAt (isOpen_ball.mem_nhds hz)
    have hpow := (hEAt.hasDerivAt.pow n).deriv
    have hconst := (hLAt.hasDerivAt.const_mul (-(n : ℂ))).deriv
    change deriv (exteriorAnalyticFactor L ^ n) z =
      exteriorAnalyticFactor L z ^ n * deriv B z
    rw [hpow, deriv_exteriorAnalyticFactor_eq hL hz,
      show deriv B z = -(n : ℂ) * deriv L z by exact hconst]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one, pow_succ]
    ring
  have hrec := taylorCoeff_log_recurrence hR hq hB hderiv (n - 1)
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hnsub] at hrec
  have hqcoeff (j : ℕ) :
      taylorCoeff q j =
        PowerSeries.coeff j (exteriorFactorPowerSeries L ^ n) := by
    exact (coeff_exteriorFactorPowerSeries_pow hR hL n j).symm
  have hBcoeff (j : ℕ) :
      taylorCoeff B j = -(n : ℂ) * taylorCoeff L j := by
    exact taylorCoeff_const_mul_function (-(n : ℂ)) L j
  simp_rw [hqcoeff, hBcoeff] at hrec
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcancel :
      PowerSeries.coeff n (exteriorFactorPowerSeries L ^ n) =
        -∑ i ∈ Finset.range n,
          PowerSeries.coeff i (exteriorFactorPowerSeries L ^ n) *
            ((n - i : ℕ) * taylorCoeff L (n - i)) := by
    apply mul_left_cancel₀ hn0
    calc
      (n : ℂ) * PowerSeries.coeff n (exteriorFactorPowerSeries L ^ n) =
          ∑ i ∈ Finset.range n,
            PowerSeries.coeff i (exteriorFactorPowerSeries L ^ n) *
              ((n - 1 - i + 1 : ℕ) *
                (-(n : ℂ) * taylorCoeff L (n - 1 - i + 1))) := hrec
      _ = (n : ℂ) *
          (-∑ i ∈ Finset.range n,
            PowerSeries.coeff i (exteriorFactorPowerSeries L ^ n) *
              ((n - i : ℕ) * taylorCoeff L (n - i))) := by
        rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        rw [show n - 1 - i + 1 = n - i by omega]
        ring
  rw [hcancel]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => PowerSeries.coeff (n - k) (exteriorFactorPowerSeries L ^ n) *
      ((k : ℕ) * taylorCoeff L k)) n]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hreflect := Finset.sum_range_reflect
    (fun i => PowerSeries.coeff i (exteriorFactorPowerSeries L ^ (m + 1)) *
      (((m + 1 - i : ℕ) : ℂ) * taylorCoeff L (m + 1 - i))) (m + 1)
  have hzeroCoeff :
      PowerSeries.coeff 0 (exteriorFactorPowerSeries L ^ (m + 1)) = 1 :=
    coeff_powerSeries_pow_zero (exteriorFactorPowerSeries_constantCoeff hL0) (m + 1)
  have hconv :
      (∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i (exteriorFactorPowerSeries L ^ (m + 1)) *
            (((m + 1 - i : ℕ) : ℂ) * taylorCoeff L (m + 1 - i))) =
        (∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff (m + 1 - k) (exteriorFactorPowerSeries L ^ (m + 1)) *
            ((k : ℂ) * taylorCoeff L k)) +
          ((m + 1 : ℕ) : ℂ) * taylorCoeff L (m + 1) := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1),
          PowerSeries.coeff (m - j) (exteriorFactorPowerSeries L ^ (m + 1)) *
            (((m + 1 - (m - j) : ℕ) : ℂ) *
              taylorCoeff L (m + 1 - (m - j))) := by
          simpa only [Nat.add_one_sub_one] using hreflect.symm
      _ = (∑ j ∈ Finset.range m,
          PowerSeries.coeff (m - j) (exteriorFactorPowerSeries L ^ (m + 1)) *
            ((((j + 1 : ℕ) : ℂ)) * taylorCoeff L (j + 1))) +
          ((m + 1 : ℕ) : ℂ) * taylorCoeff L (m + 1) := by
        rw [Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          have hjm : j < m := Finset.mem_range.mp hj
          rw [show m + 1 - (m - j) = j + 1 by omega]
        · rw [Nat.sub_self, Nat.sub_zero, hzeroCoeff, one_mul]
      _ = _ := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [show m + 1 - (j + 1) = m - j by omega]
  rw [hconv]
  ring

lemma faberPolynomial_eval_zero_exteriorFactor
    {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    {n : ℕ} (hn : 0 < n) :
    (faberPolynomial (exteriorFactorPowerSeries L) n).eval 0 =
      (n : ℂ) * taylorCoeff L n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [faberPolynomial, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, zero_pow hn.ne', Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, zero_sub]
      have hlower :
          (∑ k : Fin n,
              PowerSeries.coeff (n - k) (exteriorFactorPowerSeries L ^ n) *
                (faberPolynomial (exteriorFactorPowerSeries L) k).eval 0) =
            PowerSeries.coeff n (exteriorFactorPowerSeries L ^ n) +
              ∑ k : Fin n,
                PowerSeries.coeff (n - k) (exteriorFactorPowerSeries L ^ n) *
                  ((k : ℕ) * taylorCoeff L k) := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add]
        have hPzero :
            (faberPolynomial (exteriorFactorPowerSeries L) 0).eval 0 = 1 := by
          rw [faberPolynomial]
          simp
        rw [hPzero, mul_one, Nat.sub_zero]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih (k.succ : ℕ) k.succ.isLt (Nat.succ_pos k)]
      rw [hlower,
        exteriorFactorPowerSeries_pow_coeff_recurrence hR hL hL0 hn]
      simp

lemma faberPolynomial_eval_zero_oddRoot
    {L : ℂ → ℂ} {R S : ℝ} (hS : 0 < S)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hSR : S ^ 2 < R) {n : ℕ} (hn : 0 < n) :
    (faberPolynomial
        (exteriorFactorPowerSeries (rootTransformLog L 2)) (2 * n)).eval 0 =
      ((2 * n : ℕ) : ℂ) * logarithmicCoeff L n := by
  rw [faberPolynomial_eval_zero_exteriorFactor hS
      (rootTransformLog_differentiableOn (by norm_num) hL hSR)
      (rootTransformLog_zero (by norm_num) hL0)
      (Nat.mul_pos (by norm_num) hn),
    taylorCoeff_rootTransformLog_mul hS (by norm_num) hL hSR,
    logarithmicCoeff]
  push_cast
  ring

noncomputable def positiveIndexEnergy (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ‖a (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ)

noncomputable def grunskyBilinearPolynomial
    (L : ℂ → ℂ) (a b : ℕ → ℂ) (N M : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N, ∑ m ∈ Finset.range M,
    Polynomial.monomial (k + m + 2)
      (a (k + 1) * b (m + 1) * grunskyCoeff L (k + 1) (m + 1))

lemma coeff_grunskyBilinearPolynomial
    (L : ℂ → ℂ) (a b : ℕ → ℂ) (N M d : ℕ) :
    (grunskyBilinearPolynomial L a b N M).coeff d =
      ∑ k ∈ Finset.range N, ∑ m ∈ Finset.range M,
        if k + m + 2 = d then
          a (k + 1) * b (m + 1) * grunskyCoeff L (k + 1) (m + 1)
        else 0 := by
  rw [grunskyBilinearPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.coeff_monomial]

lemma finiteGrunskyCombination_phase_div
    (L : ℂ → ℂ) (a : ℕ → ℂ) (N m : ℕ) {z : ℂ} :
    finiteGrunskyCombination L
        (fun n => a n * z ^ n / (n : ℂ)) N m =
      ∑ k ∈ Finset.range N,
        a (k + 1) * z ^ (k + 1) * grunskyCoeff L (k + 1) m := by
  unfold finiteGrunskyCombination
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk0]

lemma eval_grunskyBilinearPolynomial
    (L : ℂ → ℂ) (a b : ℕ → ℂ) (N M : ℕ) (z : ℂ) :
    (grunskyBilinearPolynomial L a b N M).eval z =
      ∑ m ∈ Finset.range M,
        b (m + 1) * z ^ (m + 1) *
          finiteGrunskyCombination L
            (fun n => a n * z ^ n / (n : ℂ)) N (m + 1) := by
  rw [grunskyBilinearPolynomial, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [finiteGrunskyCombination_phase_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show k + m + 2 = (m + 1) + (k + 1) by omega, pow_add]
  ring

lemma positiveIndexEnergy_phase_div
    (a : ℕ → ℂ) (N : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ k ∈ Finset.range N,
        ((k + 1 : ℕ) : ℝ) *
          ‖a (k + 1) * z ^ (k + 1) / ((k + 1 : ℕ) : ℂ)‖ ^ 2) =
      positiveIndexEnergy a N := by
  rw [positiveIndexEnergy]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_div, norm_mul, norm_pow, hz, one_pow, Complex.norm_natCast]
  have hk0 : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hk0]

lemma norm_eval_grunskyBilinearPolynomial_sq_le
    {f L : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (a b : ℕ → ℂ) (N M : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(grunskyBilinearPolynomial L a b N M).eval z‖ ^ 2 ≤
      positiveIndexEnergy a N * positiveIndexEnergy b M := by
  rw [eval_grunskyBilinearPolynomial]
  have hnorm :
      ‖∑ m ∈ Finset.range M,
          b (m + 1) * z ^ (m + 1) *
            finiteGrunskyCombination L
              (fun n => a n * z ^ n / (n : ℂ)) N (m + 1)‖ ≤
        ∑ m ∈ Finset.range M,
          ‖b (m + 1)‖ *
            ‖finiteGrunskyCombination L
              (fun n => a n * z ^ n / (n : ℂ)) N (m + 1)‖ := by
    calc
      _ ≤ ∑ m ∈ Finset.range M,
          ‖b (m + 1) * z ^ (m + 1) *
            finiteGrunskyCombination L
              (fun n => a n * z ^ n / (n : ℂ)) N (m + 1)‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [norm_mul, norm_mul, norm_pow, hz, one_pow, mul_one]
  calc
    ‖∑ m ∈ Finset.range M,
        b (m + 1) * z ^ (m + 1) *
          finiteGrunskyCombination L
            (fun n => a n * z ^ n / (n : ℂ)) N (m + 1)‖ ^ 2 ≤
        (∑ m ∈ Finset.range M,
          ‖b (m + 1)‖ *
            ‖finiteGrunskyCombination L
              (fun n => a n * z ^ n / (n : ℂ)) N (m + 1)‖) ^ 2 := by
      gcongr
    _ ≤ (∑ m ∈ Finset.range M,
          ((m + 1 : ℕ) : ℝ) *
            ‖finiteGrunskyCombination L
              (fun n => a n * z ^ n / (n : ℂ)) N (m + 1)‖ ^ 2) *
        positiveIndexEnergy b M := by
      rw [positiveIndexEnergy]
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro m hm
        positivity
      · intro m hm
        positivity
      · intro m hm
        have hm0 : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp [hm0]
        exact le_rfl
    _ ≤ positiveIndexEnergy a N * positiveIndexEnergy b M := by
      apply mul_le_mul_of_nonneg_right _ (by
        rw [positiveIndexEnergy]
        positivity)
      have hstrong := finiteGrunskyCombination_norm_sq_le hR1 hf hL hL0 hexp
        (fun n => a n * z ^ n / (n : ℂ)) N (M + 1)
      rw [Finset.sum_range_succ'] at hstrong
      simp only [Nat.cast_zero, zero_mul, add_zero] at hstrong
      rw [positiveIndexEnergy_phase_div a N hz] at hstrong
      exact hstrong

lemma grunskyBilinearPolynomial_sum_sq_le
    {f L : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (a b : ℕ → ℂ) (N M : ℕ) :
    (∑ d ∈ (grunskyBilinearPolynomial L a b N M).support,
        ‖(grunskyBilinearPolynomial L a b N M).coeff d‖ ^ 2) ≤
      positiveIndexEnergy a N * positiveIndexEnergy b M := by
  rw [Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (by fun_prop : Continuous
      (fun z => ‖(grunskyBilinearPolynomial L a b N M).eval z‖ ^ 2)).continuousOn
        |>.circleIntegrable zero_le_one
  · intro z hz
    have hnorm : ‖z‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hz
    exact norm_eval_grunskyBilinearPolynomial_sq_le hR1 hf hL hL0 hexp
      a b N M hnorm

end Submission
