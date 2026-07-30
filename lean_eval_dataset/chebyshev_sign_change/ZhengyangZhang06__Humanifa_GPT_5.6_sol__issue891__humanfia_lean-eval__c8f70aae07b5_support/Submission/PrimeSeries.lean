import Submission.Analytic
import Mathlib.NumberTheory.LSeries.SumCoeff

open LeanEval.NumberTheory.ChebyshevSignChangeProblem
open scoped ArithmeticFunction.vonMangoldt LSeries.notation Chebyshev Topology

namespace Submission.PrimeSeries

open Submission.Helpers Submission.Analytic
open Filter

/-- The exponent in the canonical prime-power presentation of `n`. -/
def primePowerExponent (n : ℕ) : ℕ :=
  n.factorization n.minFac

/-- The contribution from prime squares to the non-prime part of `χ₄ Λ`. -/
noncomputable def squarePrimePowerCoeff (n : ℕ) : ℂ :=
  if IsPrimePow n ∧ primePowerExponent n = 2 then higherPrimePowerCoeff n else 0

/-- The contribution from prime powers of exponent at least three to `χ₄ Λ`. -/
noncomputable def higherExponentPrimePowerCoeff (n : ℕ) : ℂ :=
  if IsPrimePow n ∧ 3 ≤ primePowerExponent n then higherPrimePowerCoeff n else 0

lemma primePowerExponent_pos {n : ℕ} (hn : IsPrimePow n) :
    0 < primePowerExponent n := by
  exact Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero hn.one_lt)

lemma primePowerExponent_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    primePowerExponent (p ^ k) = k := by
  rw [primePowerExponent, hp.pow_minFac hk, hp.factorization_pow,
    Finsupp.single_eq_same]

lemma prime_of_isPrimePow_primePowerExponent_eq_one {n : ℕ}
    (hn : IsPrimePow n) (hexp : primePowerExponent n = 1) : n.Prime := by
  have hpow := hn.minFac_pow_factorization_eq
  rw [show n.factorization n.minFac = primePowerExponent n by rfl, hexp, pow_one] at hpow
  have hpmin : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  exact hpow ▸ hpmin

lemma higherPrimePowerCoeff_eq_zero_of_not_isPrimePow {n : ℕ}
    (hn : ¬IsPrimePow n) : higherPrimePowerCoeff n = 0 := by
  by_cases hp : n.Prime
  · simp [higherPrimePowerCoeff, hp]
  · rw [higherPrimePowerCoeff, if_neg hp, twistedVonMangoldtCoeff,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, Complex.ofReal_zero, mul_zero]

lemma higherPrimePowerCoeff_eq_square_add_higherExponent (n : ℕ) :
    higherPrimePowerCoeff n =
      squarePrimePowerCoeff n + higherExponentPrimePowerCoeff n := by
  by_cases hn : IsPrimePow n
  · have hpos := primePowerExponent_pos hn
    by_cases htwo : primePowerExponent n = 2
    · simp [squarePrimePowerCoeff, higherExponentPrimePowerCoeff, hn, htwo]
    · by_cases hone : primePowerExponent n = 1
      · have hp := prime_of_isPrimePow_primePowerExponent_eq_one hn hone
        simp [squarePrimePowerCoeff, higherExponentPrimePowerCoeff, hn, hone,
          higherPrimePowerCoeff, hp]
      · have hthree : 3 ≤ primePowerExponent n := by omega
        simp [squarePrimePowerCoeff, higherExponentPrimePowerCoeff, hn, htwo, hthree]
  · rw [higherPrimePowerCoeff_eq_zero_of_not_isPrimePow hn]
    simp [squarePrimePowerCoeff, higherExponentPrimePowerCoeff, hn]

lemma twistedVonMangoldtCoeff_eq_prime_add_error (n : ℕ) :
    twistedVonMangoldtCoeff n =
      twistedPrimeLogCoeff n + higherPrimePowerCoeff n := by
  by_cases hn : n.Prime
  · simp [twistedPrimeLogCoeff, higherPrimePowerCoeff, twistedVonMangoldtCoeff, hn,
      ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [twistedPrimeLogCoeff, higherPrimePowerCoeff, hn]

lemma twistedVonMangoldtCoeff_eq_prime_add_square_add_higherExponent (n : ℕ) :
    twistedVonMangoldtCoeff n =
      twistedPrimeLogCoeff n + squarePrimePowerCoeff n +
        higherExponentPrimePowerCoeff n := by
  rw [twistedVonMangoldtCoeff_eq_prime_add_error,
    higherPrimePowerCoeff_eq_square_add_higherExponent]
  ring

lemma norm_higherExponentPrimePowerCoeff_prime_pow_le {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    ‖higherExponentPrimePowerCoeff (p ^ k)‖ ≤
      if 3 ≤ k then Real.log p else 0 := by
  by_cases hthree : 3 ≤ k
  · have hcond : IsPrimePow (p ^ k) ∧ 3 ≤ primePowerExponent (p ^ k) := by
      exact ⟨hp.isPrimePow.pow hk, by rwa [primePowerExponent_prime_pow hp hk]⟩
    rw [if_pos hthree, higherExponentPrimePowerCoeff, if_pos hcond,
      higherPrimePowerCoeff_eq_real, Complex.norm_real, Real.norm_eq_abs]
    exact abs_realHigherPrimePowerCoeff_prime_pow_le_log hp (by omega)
  · rw [if_neg hthree, higherExponentPrimePowerCoeff,
      if_neg (not_and_or.mpr <| Or.inr <| by
        rw [primePowerExponent_prime_pow hp hk]
        exact hthree), norm_zero]

lemma higherExponent_norm_sum_eq_sum_exponents (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, ‖higherExponentPrimePowerCoeff m‖ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log n / Real.log 2⌋₊,
        ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          ‖higherExponentPrimePowerCoeff (p ^ k)‖ := by
  classical
  rw [show Finset.Icc 1 n = Finset.Ioc 0 n by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega]
  calc
    ∑ m ∈ Finset.Ioc 0 n, ‖higherExponentPrimePowerCoeff m‖ =
        ∑ m ∈ Finset.Ioc 0 n with IsPrimePow m,
          ‖higherExponentPrimePowerCoeff m‖ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hpow : IsPrimePow m
      · simp [hpow]
      · simp [hpow, higherExponentPrimePowerCoeff]
    _ = _ := by
      simpa using Chebyshev.sum_PrimePow_eq_sum_sum
        (fun m => ‖higherExponentPrimePowerCoeff m‖) (x := (n : ℝ)) (by positivity)

lemma higherExponent_norm_sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n, ‖higherExponentPrimePowerCoeff m‖ ≤
      (Real.log n / Real.log 2) *
        (Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  rw [higherExponent_norm_sum_eq_sum_exponents]
  let N := ⌊Real.log n / Real.log 2⌋₊
  let B := Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ)
  have hB : 0 ≤ B :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg (by positivity) _)
  have hquot : 0 ≤ Real.log n / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Real.log_nonneg (by norm_num))
  calc
    (∑ k ∈ Finset.Icc 1 N,
        ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          ‖higherExponentPrimePowerCoeff (p ^ k)‖) ≤
        ∑ _k ∈ Finset.Icc 1 N, B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : k ≠ 0 := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      by_cases hthree : 3 ≤ k
      · calc
          (∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
              ‖higherExponentPrimePowerCoeff (p ^ k)‖) ≤
              ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
                Real.log p := by
            apply Finset.sum_le_sum
            intro p hpMem
            simpa [hthree] using
              norm_higherExponentPrimePowerCoeff_prime_pow_le
                (Finset.mem_filter.mp hpMem).2 hkpos
          _ = Chebyshev.theta ((n : ℝ) ^ ((1 : ℝ) / k)) := rfl
          _ ≤ Real.log 4 * ((n : ℝ) ^ ((1 : ℝ) / k)) :=
            Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg (by positivity) _)
          _ ≤ B := by
            dsimp [B]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le
                (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
                (one_div_nat_le_one_third hthree))
              (Real.log_nonneg (by norm_num))
      · have hzero :
            (∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
              ‖higherExponentPrimePowerCoeff (p ^ k)‖) = 0 := by
          apply Finset.sum_eq_zero
          intro p hpMem
          have hp := (Finset.mem_filter.mp hpMem).2
          have hnorm := norm_higherExponentPrimePowerCoeff_prime_pow_le hp hkpos
          rw [if_neg hthree] at hnorm
          exact le_antisymm hnorm (norm_nonneg _)
        rw [hzero]
        exact hB
    _ = ((Finset.Icc 1 N).card : ℝ) * B := by simp
    _ ≤ (N : ℝ) * B := by
      gcongr
      simp
    _ ≤ (Real.log n / Real.log 2) * B := by
      gcongr
      exact Nat.floor_le hquot

lemma explicit_higherExponent_bound_isLittleO_two_fifths_real :
    (fun x : ℝ => (Real.log x / Real.log 2) *
      (Real.log 4 * x ^ (1 / 3 : ℝ))) =o[Filter.atTop]
        fun x : ℝ => x ^ (2 / 5 : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 15)).mul_isBigO
    (Asymptotics.isBigO_refl (fun x : ℝ => x ^ (1 / 3 : ℝ)) Filter.atTop)
  refine (h.const_mul_left (Real.log 4 / Real.log 2)).congr' ?_ ?_
  · filter_upwards with x
    ring
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx]
    norm_num

lemma explicit_higherExponent_bound_isLittleO_two_fifths_nat :
    (fun n : ℕ => (Real.log n / Real.log 2) *
      (Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ))) =o[Filter.atTop]
        fun n : ℕ => (n : ℝ) ^ (2 / 5 : ℝ) := by
  simpa [Function.comp_def] using
    explicit_higherExponent_bound_isLittleO_two_fifths_real.comp_tendsto
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)

lemma higherExponent_norm_sum_isBigO_two_fifths :
    (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n,
      ‖higherExponentPrimePowerCoeff m‖) =O[Filter.atTop]
        fun n : ℕ => (n : ℝ) ^ (2 / 5 : ℝ) := by
  have hO : (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n,
      ‖higherExponentPrimePowerCoeff m‖) =O[Filter.atTop]
      fun n : ℕ => (Real.log n / Real.log 2) *
        (Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact higherExponent_norm_sum_le n hn
  exact hO.trans explicit_higherExponent_bound_isLittleO_two_fifths_nat.isBigO

lemma higherExponentPrimePowerCoeff_LSeriesSummable {s : ℂ}
    (hs : (2 / 5 : ℝ) < s.re) :
    LSeriesSummable higherExponentPrimePowerCoeff s :=
  LSeriesSummable_of_sum_norm_bigO higherExponent_norm_sum_isBigO_two_fifths
    (by norm_num) hs

lemma higherExponentPrimePowerCoeff_abscissaOfAbsConv_le :
    LSeries.abscissaOfAbsConv higherExponentPrimePowerCoeff ≤ (2 / 5 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact higherExponentPrimePowerCoeff_LSeriesSummable (by simpa using hy)

lemma higherExponentPrimePowerCoeff_LSeries_analyticOnNhd :
    AnalyticOnNhd ℂ (L higherExponentPrimePowerCoeff)
      {s : ℂ | (2 / 5 : ℝ) < s.re} := by
  apply (LSeries_analyticOnNhd higherExponentPrimePowerCoeff).mono
  intro s hs
  change (2 / 5 : ℝ) < s.re at hs
  exact higherExponentPrimePowerCoeff_abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hs)

private lemma LSeriesSummable_of_norm_le_vonMangoldt {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n) (hs : 1 < s.re) :
    LSeriesSummable f s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable, ← summable_norm_iff] at hΛ ⊢
  exact hΛ.of_nonneg_of_le (fun _ => norm_nonneg _) fun n =>
    LSeries.norm_term_le s (by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hf n)

lemma norm_twistedPrimeLogCoeff_le_vonMangoldt (n : ℕ) :
    ‖twistedPrimeLogCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n.Prime
  · rw [twistedPrimeLogCoeff, if_pos hn, norm_mul,
      ArithmeticFunction.vonMangoldt_apply_prime hn, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hn.one_le))]
    exact mul_le_of_le_one_left (Real.log_nonneg (Nat.one_le_cast.mpr hn.one_le))
      (chiFour.norm_le_one n)
  · rw [twistedPrimeLogCoeff, if_neg hn, norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg

lemma norm_squarePrimePowerCoeff_le_vonMangoldt (n : ℕ) :
    ‖squarePrimePowerCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rw [squarePrimePowerCoeff]
  split_ifs
  · exact (norm_higherPrimePowerCoeff_le n).trans (by
      split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl)
  · simpa only [norm_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))

lemma norm_higherExponentPrimePowerCoeff_le_vonMangoldt (n : ℕ) :
    ‖higherExponentPrimePowerCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rw [higherExponentPrimePowerCoeff]
  split_ifs
  · exact (norm_higherPrimePowerCoeff_le n).trans (by
      split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl)
  · simpa only [norm_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))

lemma twistedPrimeLogCoeff_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable twistedPrimeLogCoeff s :=
  LSeriesSummable_of_norm_le_vonMangoldt norm_twistedPrimeLogCoeff_le_vonMangoldt hs

lemma squarePrimePowerCoeff_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable squarePrimePowerCoeff s :=
  LSeriesSummable_of_norm_le_vonMangoldt norm_squarePrimePowerCoeff_le_vonMangoldt hs

lemma twistedVonMangoldt_LSeries_eq_prime_add_square_add_higherExponent
    {s : ℂ} (hs : 1 < s.re) :
    L twistedVonMangoldtCoeff s =
      L twistedPrimeLogCoeff s + L squarePrimePowerCoeff s +
        L higherExponentPrimePowerCoeff s := by
  have hprime := twistedPrimeLogCoeff_LSeriesSummable hs
  have hsquare := squarePrimePowerCoeff_LSeriesSummable hs
  have hhigher := higherExponentPrimePowerCoeff_LSeriesSummable (s := s) (by linarith)
  have hcoeff : twistedVonMangoldtCoeff =
      twistedPrimeLogCoeff + squarePrimePowerCoeff + higherExponentPrimePowerCoeff := by
    funext n
    exact twistedVonMangoldtCoeff_eq_prime_add_square_add_higherExponent n
  rw [hcoeff, LSeries_add (hprime.add hsquare) hhigher, LSeries_add hprime hsquare]

lemma twistedPrimeLog_LSeries_eq_negLogDerivative_sub_square_sub_higherExponent
    {s : ℂ} (hs : 1 < s.re) :
    L twistedPrimeLogCoeff s =
      chiFourNegLogDerivative s - L squarePrimePowerCoeff s -
        L higherExponentPrimePowerCoeff s := by
  have h := twistedVonMangoldt_LSeries_eq_prime_add_square_add_higherExponent hs
  rw [twistedVonMangoldt_LSeries_eq_continued hs] at h
  rw [h]
  ring

/-- The ordinary prime-log coefficient, used to identify the square-prime singularity. -/
noncomputable def primeLogCoeff (n : ℕ) : ℂ :=
  if n.Prime then (Real.log n : ℂ) else 0

/-- The non-prime contribution to the ordinary von Mangoldt coefficient. -/
noncomputable def nonPrimeVonMangoldtCoeff (n : ℕ) : ℂ :=
  if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℂ)

lemma vonMangoldt_coeff_eq_prime_add_nonPrime (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℂ) =
      primeLogCoeff n + nonPrimeVonMangoldtCoeff n := by
  by_cases hn : n.Prime
  · simp [primeLogCoeff, nonPrimeVonMangoldtCoeff, hn,
      ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [primeLogCoeff, nonPrimeVonMangoldtCoeff, hn]

lemma nonPrimeVonMangoldt_norm_sum_eq_psi_sub_theta (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, ‖nonPrimeVonMangoldtCoeff m‖ =
      Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast]
  rw [show Finset.Icc 1 n = Finset.Ioc 0 n by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hp : m.Prime
  · simp [hp, nonPrimeVonMangoldtCoeff]
  · simp [hp, nonPrimeVonMangoldtCoeff, ArithmeticFunction.vonMangoldt_nonneg]

lemma nonPrimeVonMangoldt_norm_sum_isBigO_sqrt :
    (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, ‖nonPrimeVonMangoldtCoeff m‖) =O[Filter.atTop]
      fun n : ℕ => √(n : ℝ) := by
  have h := Chebyshev.isBigO_psi_sub_theta_sqrt.comp_tendsto
    (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards with n
  simpa [Function.comp_def, Pi.sub_apply] using
    (nonPrimeVonMangoldt_norm_sum_eq_psi_sub_theta n).symm

lemma nonPrimeVonMangoldt_norm_sum_isBigO_one_half :
    (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, ‖nonPrimeVonMangoldtCoeff m‖) =O[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) := by
  simpa only [Real.sqrt_eq_rpow] using nonPrimeVonMangoldt_norm_sum_isBigO_sqrt

lemma nonPrimeVonMangoldtCoeff_LSeriesSummable {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) :
    LSeriesSummable nonPrimeVonMangoldtCoeff s :=
  LSeriesSummable_of_sum_norm_bigO nonPrimeVonMangoldt_norm_sum_isBigO_one_half
    (by norm_num) hs

lemma nonPrimeVonMangoldtCoeff_abscissaOfAbsConv_le :
    LSeries.abscissaOfAbsConv nonPrimeVonMangoldtCoeff ≤ (1 / 2 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact nonPrimeVonMangoldtCoeff_LSeriesSummable (by simpa using hy)

lemma nonPrimeVonMangoldtCoeff_LSeries_analyticOnNhd :
    AnalyticOnNhd ℂ (L nonPrimeVonMangoldtCoeff)
      {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  apply (LSeries_analyticOnNhd nonPrimeVonMangoldtCoeff).mono
  intro s hs
  change (1 / 2 : ℝ) < s.re at hs
  exact nonPrimeVonMangoldtCoeff_abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hs)

lemma norm_primeLogCoeff_le_vonMangoldt (n : ℕ) :
    ‖primeLogCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n.Prime
  · rw [primeLogCoeff, if_pos hn, ArithmeticFunction.vonMangoldt_apply_prime hn,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hn.one_le))]
  · simp [primeLogCoeff, hn, ArithmeticFunction.vonMangoldt_nonneg]

lemma primeLogCoeff_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable primeLogCoeff s :=
  LSeriesSummable_of_norm_le_vonMangoldt norm_primeLogCoeff_le_vonMangoldt hs

lemma vonMangoldt_LSeries_eq_prime_add_nonPrime {s : ℂ} (hs : 1 < s.re) :
    L (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      L primeLogCoeff s + L nonPrimeVonMangoldtCoeff s := by
  have hprime := primeLogCoeff_LSeriesSummable hs
  have hnonprime := nonPrimeVonMangoldtCoeff_LSeriesSummable (s := s) (by linarith)
  have hcoeff : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) =
      primeLogCoeff + nonPrimeVonMangoldtCoeff := by
    funext n
    exact vonMangoldt_coeff_eq_prime_add_nonPrime n
  rw [hcoeff, LSeries_add hprime hnonprime]

lemma primeLog_LSeries_eq_zetaNegLogDerivative_sub_nonPrime {s : ℂ} (hs : 1 < s.re) :
    L primeLogCoeff s =
      -deriv riemannZeta s / riemannZeta s - L nonPrimeVonMangoldtCoeff s := by
  have h := vonMangoldt_LSeries_eq_prime_add_nonPrime hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at h
  rw [h]
  ring

/-- The analytic factor obtained by removing the simple pole of `ζ` at `1`. -/
noncomputable def riemannZetaPoleFactor (s : ℂ) : ℂ :=
  Function.update (fun z => (z - 1) * riemannZeta z) 1 1 s

@[simp]
lemma riemannZetaPoleFactor_one : riemannZetaPoleFactor 1 = 1 := by
  simp [riemannZetaPoleFactor]

lemma riemannZetaPoleFactor_apply_of_ne {s : ℂ} (hs : s ≠ 1) :
    riemannZetaPoleFactor s = (s - 1) * riemannZeta s := by
  simp [riemannZetaPoleFactor, hs]

lemma riemannZetaPoleFactor_analyticAt_one :
    AnalyticAt ℂ riemannZetaPoleFactor 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := by simpa using hs
    have hdiff : DifferentiableAt ℂ (fun z => (z - 1) * riemannZeta z) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)
    have heq : riemannZetaPoleFactor =ᶠ[𝓝 s]
        fun z => (z - 1) * riemannZeta z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
      have hz1 : z ≠ 1 := by simpa using hz
      simp [riemannZetaPoleFactor, hz1]
    exact heq.differentiableAt_iff.mpr hdiff
  · change ContinuousAt
      (Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1) 1
    rw [continuousAt_update_same]
    exact riemannZeta_residue_one

lemma tendsto_zeta_negLogDerivative_residue_one :
    Filter.Tendsto
      (fun s : ℂ => (s - 1) * (-deriv riemannZeta s / riemannZeta s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  let g := riemannZetaPoleFactor
  have hg : AnalyticAt ℂ g 1 := riemannZetaPoleFactor_analyticAt_one
  have hg1 : g 1 ≠ 0 := by simp [g]
  have hg_ne : ∀ᶠ z in 𝓝 (1 : ℂ), g z ≠ 0 :=
    hg.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr hg1)
  have hlogg : Filter.Tendsto (logDeriv g) (𝓝 (1 : ℂ)) (𝓝 (logDeriv g 1)) := by
    have hcont : ContinuousAt (logDeriv g) 1 := by
      change ContinuousAt (deriv g / g) 1
      exact hg.deriv.continuousAt.div hg.continuousAt hg1
    exact hcont
  have hsub : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - 1) 1 := by fun_prop
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have hprod : Filter.Tendsto (fun s : ℂ => (s - 1) * logDeriv g s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using hsub.mul (hlogg.mono_left nhdsWithin_le_nhds)
  have hevent : (fun s : ℂ => (s - 1) * (-deriv riemannZeta s / riemannZeta s))
      =ᶠ[𝓝[≠] (1 : ℂ)] (fun s => (1 : ℂ) - (s - 1) * logDeriv g s) := by
    filter_upwards [hg_ne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hgs hs
    have hs1 : s ≠ 1 := by simpa using hs
    have hlocal : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
      have hz1 : z ≠ 1 := by simpa using hz
      simp [g, riemannZetaPoleFactor, hz1]
    have hvalue := hlocal.eq_of_nhds
    have hzeta : riemannZeta s ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hvalue
      exact hgs hvalue
    have hlog : logDeriv g s =
        logDeriv (fun z : ℂ => z - 1) s + logDeriv riemannZeta s := by
      rw [logDeriv_apply, hlocal.deriv_eq, hvalue]
      exact logDeriv_mul s (sub_ne_zero.mpr hs1) hzeta
        (by fun_prop) (differentiableAt_riemannZeta hs1)
    rw [hlog, logDeriv_apply, deriv_sub_const, deriv_id'', one_div,
      logDeriv_apply]
    field_simp
    ring
  have hone : Filter.Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    tendsto_const_nhds
  simpa using (hone.sub hprod).congr' hevent.symm

/-- Meromorphic continuation of the ordinary prime-log L-series near `re s = 1`. -/
noncomputable def primeLogContinuation (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s - L nonPrimeVonMangoldtCoeff s

lemma primeLogContinuation_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    primeLogContinuation s = L primeLogCoeff s := by
  rw [primeLogContinuation, primeLog_LSeries_eq_zetaNegLogDerivative_sub_nonPrime hs]

lemma tendsto_primeLogContinuation_residue_one :
    Filter.Tendsto (fun s : ℂ => (s - 1) * primeLogContinuation s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have htailAnalytic : AnalyticAt ℂ (L nonPrimeVonMangoldtCoeff) 1 :=
    nonPrimeVonMangoldtCoeff_LSeries_analyticOnNhd (1 : ℂ) (by norm_num)
  have htail : Filter.Tendsto (L nonPrimeVonMangoldtCoeff) (𝓝[≠] (1 : ℂ))
      (𝓝 (L nonPrimeVonMangoldtCoeff 1)) :=
    htailAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - 1) 1 := by fun_prop
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have htailProd : Filter.Tendsto
      (fun s : ℂ => (s - 1) * L nonPrimeVonMangoldtCoeff s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using hsub.mul htail
  have h := tendsto_zeta_negLogDerivative_residue_one.sub htailProd
  have hevent :
      (fun s : ℂ => (s - 1) * (-deriv riemannZeta s / riemannZeta s) -
        (s - 1) * L nonPrimeVonMangoldtCoeff s) =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s => (s - 1) * primeLogContinuation s := by
    filter_upwards with s
    simp only [primeLogContinuation]
    ring
  simpa using h.congr' hevent

/-- The ordinary prime-log coefficient with the prime `2` removed. -/
noncomputable def oddPrimeLogCoeff (n : ℕ) : ℂ :=
  if n = 2 then 0 else primeLogCoeff n

lemma oddPrimeLogCoeff_apply_prime {p : ℕ} (hp : p.Prime) :
    oddPrimeLogCoeff p = if p = 2 then 0 else (Real.log p : ℂ) := by
  by_cases hp2 : p = 2 <;> simp [oddPrimeLogCoeff, primeLogCoeff, hp, hp2]

lemma squarePrimePowerCoeff_prime_sq {p : ℕ} (hp : p.Prime) :
    squarePrimePowerCoeff (p ^ 2) =
      if p = 2 then 0 else (Real.log p : ℂ) := by
  rw [squarePrimePowerCoeff, if_pos ⟨hp.isPrimePow.pow (by norm_num),
    primePowerExponent_prime_pow hp (by norm_num)⟩,
    higherPrimePowerCoeff_eq_real, realHigherPrimePowerCoeff_sq hp]
  split_ifs <;> simp

lemma squarePrimePowerCoeff_prime_pow_succ {p k : ℕ} (hp : p.Prime) :
    squarePrimePowerCoeff (p ^ (k + 1)) =
      if k = 1 then oddPrimeLogCoeff p else 0 := by
  by_cases hk : k = 1
  · subst k
    simp only [if_true, one_add_one_eq_two]
    rw [squarePrimePowerCoeff_prime_sq hp, oddPrimeLogCoeff_apply_prime hp]
  · rw [if_neg hk, squarePrimePowerCoeff,
      if_neg (not_and_or.mpr <| Or.inr <| by
        rw [primePowerExponent_prime_pow hp (Nat.succ_ne_zero k)]
        omega)]

lemma norm_squarePrimePowerCoeff_le_nonPrimeVonMangoldtCoeff (n : ℕ) :
    ‖squarePrimePowerCoeff n‖ ≤ ‖nonPrimeVonMangoldtCoeff n‖ := by
  rw [squarePrimePowerCoeff]
  split_ifs with h
  · have hnotPrime : ¬n.Prime := by
      intro hp
      have hexp : primePowerExponent n = 1 := by
        simpa using primePowerExponent_prime_pow hp (k := 1) (by norm_num)
      omega
    rw [nonPrimeVonMangoldtCoeff, if_neg hnotPrime, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (norm_higherPrimePowerCoeff_le n).trans (by simp [hnotPrime])
  · simpa only [norm_zero] using norm_nonneg (nonPrimeVonMangoldtCoeff n)

lemma squarePrimePowerCoeff_LSeriesSummable_halfPlane {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) :
    LSeriesSummable squarePrimePowerCoeff s := by
  have hnonprime := nonPrimeVonMangoldtCoeff_LSeriesSummable hs
  rw [LSeriesSummable, ← summable_norm_iff] at hnonprime ⊢
  exact hnonprime.of_nonneg_of_le (fun _ => norm_nonneg _) fun n =>
    LSeries.norm_term_le s (norm_squarePrimePowerCoeff_le_nonPrimeVonMangoldtCoeff n)

lemma squarePrimePowerCoeff_term_prime_pow_succ
    (p : Nat.Primes) (k : ℕ) (s : ℂ) :
    LSeries.term squarePrimePowerCoeff s ((p : ℕ) ^ (k + 1)) =
      if k = 1 then LSeries.term oddPrimeLogCoeff (2 * s) (p : ℕ) else 0 := by
  rcases p with ⟨p, hp⟩
  change LSeries.term squarePrimePowerCoeff s (p ^ (k + 1)) =
    if k = 1 then LSeries.term oddPrimeLogCoeff (2 * s) p else 0
  by_cases hk : k = 1
  · subst k
    rw [if_pos rfl, one_add_one_eq_two,
      LSeries.term_of_ne_zero (pow_ne_zero 2 hp.ne_zero),
      LSeries.term_of_ne_zero hp.ne_zero,
      squarePrimePowerCoeff_prime_sq hp,
      oddPrimeLogCoeff_apply_prime hp]
    congr 1
    simp only [Nat.cast_pow]
    rw [← Complex.natCast_cpow_natCast_mul]
    norm_num
  · rw [if_neg hk, LSeries.term_def,
      squarePrimePowerCoeff_prime_pow_succ hp, if_neg hk]
    simp

lemma squarePrimePowerCoeff_LSeries_eq_oddPrimeLogCoeff
    {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    L squarePrimePowerCoeff s = L oddPrimeLogCoeff (2 * s) := by
  let fsquare : ℕ → ℂ := LSeries.term squarePrimePowerCoeff s
  let fodd : ℕ → ℂ := LSeries.term oddPrimeLogCoeff (2 * s)
  have hsquare := squarePrimePowerCoeff_LSeriesSummable_halfPlane hs
  change Summable fsquare at hsquare
  have hsquare_zero {n : ℕ} (hn : ¬IsPrimePow n) : fsquare n = 0 := by
    simp [fsquare, LSeries.term_def, squarePrimePowerCoeff, hn]
  have hsub : Summable (fun n : {n : ℕ // IsPrimePow n} => fsquare n) :=
    hsquare.subtype IsPrimePow
  have hpair : Summable (fun pk : Nat.Primes × ℕ =>
      fsquare ((Nat.Primes.prodNatEquiv pk : {n : ℕ // IsPrimePow n}) : ℕ)) := by
    simpa [Function.comp_def] using
      (Nat.Primes.prodNatEquiv.summable_iff).2 hsub
  change (∑' n : ℕ, fsquare n) = ∑' n : ℕ, fodd n
  calc
    (∑' n : ℕ, fsquare n) =
        ∑' n : {n : ℕ // IsPrimePow n}, fsquare n := by
      calc
        (∑' n : ℕ, fsquare n) =
            ∑' n : ℕ, Set.indicator {n : ℕ | IsPrimePow n} fsquare n := by
          apply tsum_congr
          intro n
          by_cases hn : IsPrimePow n
          · exact (Set.indicator_of_mem (s := {n : ℕ | IsPrimePow n}) hn fsquare).symm
          · rw [Set.indicator_of_notMem (s := {n : ℕ | IsPrimePow n}) hn fsquare,
              hsquare_zero hn]
        _ = ∑' n : {n : ℕ // IsPrimePow n}, fsquare n :=
          (tsum_subtype {n : ℕ | IsPrimePow n} fsquare).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        fsquare ((Nat.Primes.prodNatEquiv pk : {n : ℕ // IsPrimePow n}) : ℕ) := by
      simpa [Function.comp_def] using
        (Nat.Primes.prodNatEquiv.tsum_eq
          (fun n : {n : ℕ // IsPrimePow n} => fsquare n)).symm
    _ = ∑' p : Nat.Primes, ∑' k : ℕ, fsquare ((p : ℕ) ^ (k + 1)) := by
      simpa using hpair.tsum_prod
    _ = ∑' p : Nat.Primes, fodd (p : ℕ) := by
      apply tsum_congr
      intro p
      have hfun : (fun k : ℕ => fsquare ((p : ℕ) ^ (k + 1))) =
          fun k => if k = 1 then fodd (p : ℕ) else 0 := by
        funext k
        exact squarePrimePowerCoeff_term_prime_pow_succ p k s
      rw [hfun, tsum_ite_eq]
    _ = ∑' n : ℕ, fodd n := by
      change (∑' p : {p : ℕ // p.Prime}, fodd p) = ∑' n : ℕ, fodd n
      calc
        (∑' p : {p : ℕ // p.Prime}, fodd p) =
            ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime} fodd n :=
          tsum_subtype {n : ℕ | n.Prime} fodd
        _ = ∑' n : ℕ, fodd n := by
          apply tsum_congr
          intro n
          by_cases hp : n.Prime
          · exact Set.indicator_of_mem (s := {n : ℕ | n.Prime}) hp fodd
          · rw [Set.indicator_of_notMem (s := {n : ℕ | n.Prime}) hp fodd]
            simp [fodd, LSeries.term_def, oddPrimeLogCoeff, primeLogCoeff, hp]

noncomputable def twoPrimeLogCoeff (n : ℕ) : ℂ :=
  if n = 2 then (Real.log 2 : ℂ) else 0

lemma primeLogCoeff_eq_odd_add_two (n : ℕ) :
    primeLogCoeff n = oddPrimeLogCoeff n + twoPrimeLogCoeff n := by
  by_cases hn2 : n = 2
  · subst n
    norm_num [primeLogCoeff, oddPrimeLogCoeff, twoPrimeLogCoeff,
      ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [oddPrimeLogCoeff, twoPrimeLogCoeff, hn2]

lemma norm_oddPrimeLogCoeff_le_vonMangoldt (n : ℕ) :
    ‖oddPrimeLogCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rw [oddPrimeLogCoeff]
  split_ifs
  · simpa only [norm_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · exact norm_primeLogCoeff_le_vonMangoldt n

lemma norm_twoPrimeLogCoeff_le_vonMangoldt (n : ℕ) :
    ‖twoPrimeLogCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn2 : n = 2
  · subst n
    rw [twoPrimeLogCoeff, if_pos rfl,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
    norm_num
  · simp [twoPrimeLogCoeff, hn2, ArithmeticFunction.vonMangoldt_nonneg]

lemma oddPrimeLogCoeff_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable oddPrimeLogCoeff s :=
  LSeriesSummable_of_norm_le_vonMangoldt norm_oddPrimeLogCoeff_le_vonMangoldt hs

lemma twoPrimeLogCoeff_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable twoPrimeLogCoeff s :=
  LSeriesSummable_of_norm_le_vonMangoldt norm_twoPrimeLogCoeff_le_vonMangoldt hs

lemma twoPrimeLogCoeff_LSeries (s : ℂ) :
    L twoPrimeLogCoeff s = (Real.log 2 : ℂ) / (2 : ℂ) ^ s := by
  rw [LSeries, tsum_eq_single 2]
  · rw [LSeries.term_of_ne_zero (by norm_num)]
    simp [twoPrimeLogCoeff]
  · intro n hn
    simp [LSeries.term_def, twoPrimeLogCoeff, hn]

lemma primeLog_LSeries_eq_odd_add_two {s : ℂ} (hs : 1 < s.re) :
    L primeLogCoeff s = L oddPrimeLogCoeff s + L twoPrimeLogCoeff s := by
  have hodd := oddPrimeLogCoeff_LSeriesSummable hs
  have htwo := twoPrimeLogCoeff_LSeriesSummable hs
  have hcoeff : primeLogCoeff = oddPrimeLogCoeff + twoPrimeLogCoeff := by
    funext n
    exact primeLogCoeff_eq_odd_add_two n
  rw [hcoeff, LSeries_add hodd htwo]

noncomputable def oddPrimeLogContinuation (s : ℂ) : ℂ :=
  primeLogContinuation s - (Real.log 2 : ℂ) / (2 : ℂ) ^ s

lemma oddPrimeLogContinuation_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    oddPrimeLogContinuation s = L oddPrimeLogCoeff s := by
  rw [oddPrimeLogContinuation, primeLogContinuation_eq_LSeries hs,
    primeLog_LSeries_eq_odd_add_two hs, twoPrimeLogCoeff_LSeries]
  ring

lemma tendsto_oddPrimeLogContinuation_residue_one :
    Filter.Tendsto (fun s : ℂ => (s - 1) * oddPrimeLogContinuation s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have hcorrection : Filter.Tendsto
      (fun s : ℂ => (Real.log 2 : ℂ) / (2 : ℂ) ^ s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 ((Real.log 2 : ℂ) / (2 : ℂ) ^ (1 : ℂ))) := by
    have hpow : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ s) 1 :=
      continuousAt_const_cpow (by norm_num)
    have hcont : ContinuousAt
        (fun s : ℂ => (Real.log 2 : ℂ) / (2 : ℂ) ^ s) 1 :=
      continuousAt_const.div hpow (Complex.cpow_ne_zero_iff.mpr <| Or.inl <| by norm_num)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - 1) 1 := by fun_prop
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have hproduct : Filter.Tendsto
      (fun s : ℂ => (s - 1) * ((Real.log 2 : ℂ) / (2 : ℂ) ^ s))
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using hsub.mul hcorrection
  have h := tendsto_primeLogContinuation_residue_one.sub hproduct
  have hevent :
      (fun s : ℂ => (s - 1) * primeLogContinuation s -
        (s - 1) * ((Real.log 2 : ℂ) / (2 : ℂ) ^ s)) =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s => (s - 1) * oddPrimeLogContinuation s := by
    filter_upwards with s
    simp only [oddPrimeLogContinuation]
    ring
  simpa using h.congr' hevent

noncomputable def squarePrimePowerContinuation (s : ℂ) : ℂ :=
  oddPrimeLogContinuation (2 * s)

lemma squarePrimePowerContinuation_eq_LSeries {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) :
    squarePrimePowerContinuation s = L squarePrimePowerCoeff s := by
  have htwo : 1 < (2 * s).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  rw [squarePrimePowerContinuation, oddPrimeLogContinuation_eq_LSeries htwo,
    squarePrimePowerCoeff_LSeries_eq_oddPrimeLogCoeff hs]

private lemma tendsto_two_mul_nhdsNE_half_nhdsNE_one :
    Filter.Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont := (by fun_prop : ContinuousAt (fun s : ℂ => 2 * s) (1 / 2)).tendsto
    simpa using hcont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hsHalf : s ≠ 1 / 2 := by simpa using hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro htwo
    apply hsHalf
    calc
      s = (2 : ℂ)⁻¹ * (2 * s) := by field_simp
      _ = (2 : ℂ)⁻¹ * 1 := by rw [htwo]
      _ = 1 / 2 := by norm_num

lemma tendsto_squarePrimePowerContinuation_residue_half :
    Filter.Tendsto
      (fun s : ℂ => (s - 1 / 2) * squarePrimePowerContinuation s)
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
  have hres := tendsto_oddPrimeLogContinuation_residue_one.comp
    tendsto_two_mul_nhdsNE_half_nhdsNE_one
  have hhalf : Filter.Tendsto (fun _ : ℂ => (1 / 2 : ℂ))
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 / 2 : ℂ)) := tendsto_const_nhds
  have hscaled := hhalf.mul hres
  have hevent :
      (fun s : ℂ => (1 / 2 : ℂ) *
        ((2 * s - 1) * oddPrimeLogContinuation (2 * s))) =ᶠ[𝓝[≠] (1 / 2 : ℂ)]
      fun s => (s - 1 / 2) * squarePrimePowerContinuation s := by
    filter_upwards with s
    simp only [squarePrimePowerContinuation]
    ring
  simpa using hscaled.congr' hevent

lemma primeLogContinuation_analyticAt {s : ℂ}
    (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ primeLogContinuation s := by
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs1)
  have hmain : AnalyticAt ℂ (fun z => -deriv riemannZeta z / riemannZeta z) s :=
    hzetaAnalytic.deriv.neg.div hzetaAnalytic hzeta
  have htail : AnalyticAt ℂ (L nonPrimeVonMangoldtCoeff) s :=
    nonPrimeVonMangoldtCoeff_LSeries_analyticOnNhd s hs
  exact hmain.sub htail

lemma oddPrimeLogContinuation_analyticAt {s : ℂ}
    (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ oddPrimeLogContinuation s := by
  have hprime := primeLogContinuation_analyticAt hs1 hzeta hs
  have hpow : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) s :=
    (differentiable_const_cpow_of_neZero (2 : ℂ)).analyticAt s
  have hpow_ne : (2 : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hcorrection : AnalyticAt ℂ
      (fun z : ℂ => (Real.log 2 : ℂ) / (2 : ℂ) ^ z) s :=
    analyticAt_const.div hpow hpow_ne
  exact hprime.sub hcorrection

lemma squarePrimePowerContinuation_analyticAt_of_half_le_re_of_im_ne_zero
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) (hsim : s.im ≠ 0) :
    AnalyticAt ℂ squarePrimePowerContinuation s := by
  have htwoRe : 1 ≤ (2 * s).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  have htwoIm : (2 * s).im ≠ 0 := by
    rw [Complex.mul_im]
    norm_num
    exact hsim
  have htwoOne : 2 * s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hsim this
  have htwoHalf : (1 / 2 : ℝ) < (2 * s).re := lt_of_lt_of_le (by norm_num) htwoRe
  have hodd := oddPrimeLogContinuation_analyticAt htwoOne
    (riemannZeta_ne_zero_of_one_le_re htwoRe) htwoHalf
  have hlinear : AnalyticAt ℂ (fun z : ℂ => 2 * z) s := by fun_prop
  change AnalyticAt ℂ (fun z => oddPrimeLogContinuation (2 * z)) s
  exact hodd.comp hlinear

noncomputable def twistedPrimeLogContinuation (s : ℂ) : ℂ :=
  chiFourNegLogDerivative s - squarePrimePowerContinuation s -
    L higherExponentPrimePowerCoeff s

lemma twistedPrimeLogContinuation_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    twistedPrimeLogContinuation s = L twistedPrimeLogCoeff s := by
  have hsHalf : (1 / 2 : ℝ) < s.re := by linarith
  rw [twistedPrimeLogContinuation,
    squarePrimePowerContinuation_eq_LSeries hsHalf,
    twistedPrimeLog_LSeries_eq_negLogDerivative_sub_square_sub_higherExponent hs]

noncomputable def chiFourCentralMultiplicity : ℕ :=
  if DirichletCharacter.LFunction chiFour (1 / 2 : ℂ) = 0 then
    chiFourZeroMultiplicity (1 / 2 : ℂ) else 0

lemma tendsto_chiFourNegLogDerivative_central :
    Filter.Tendsto
      (fun s : ℂ => (s - 1 / 2) * chiFourNegLogDerivative s)
      (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 (-(chiFourCentralMultiplicity : ℂ))) := by
  by_cases hzero : DirichletCharacter.LFunction chiFour (1 / 2 : ℂ) = 0
  · have hmult : (chiFourCentralMultiplicity : ℂ) =
        (chiFourZeroMultiplicity (1 / 2 : ℂ) : ℂ) := by
      have hzero' : DirichletCharacter.LFunction chiFour (2⁻¹ : ℂ) = 0 := by
        simpa only [one_div] using hzero
      simp only [chiFourCentralMultiplicity, one_div, hzero', if_true]
    rw [hmult]
    exact (chiFourNegLogDerivative_residueAt_zero hzero).2
  · have hL : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) (1 / 2 : ℂ) :=
      differentiable_chiFour_LFunction.analyticAt _
    have hlog : AnalyticAt ℂ chiFourNegLogDerivative (1 / 2 : ℂ) := by
      change AnalyticAt ℂ
        (fun s => -(deriv (DirichletCharacter.LFunction chiFour) s /
          DirichletCharacter.LFunction chiFour s)) (1 / 2 : ℂ)
      exact (hL.deriv.div hL hzero).neg
    have hsub : Filter.Tendsto (fun s : ℂ => s - 1 / 2)
        (𝓝[≠] (1 / 2 : ℂ)) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℂ => s - 1 / 2) (1 / 2 : ℂ) := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hprod := hsub.mul (hlog.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hmult : (chiFourCentralMultiplicity : ℂ) = 0 := by
      have hzero' : DirichletCharacter.LFunction chiFour (2⁻¹ : ℂ) ≠ 0 := by
        simpa only [one_div] using hzero
      simp only [chiFourCentralMultiplicity, one_div, hzero', if_false, Nat.cast_zero]
    rw [hmult]
    simpa using hprod

lemma tendsto_twistedPrimeLogContinuation_central :
    Filter.Tendsto
      (fun s : ℂ => (s - 1 / 2) * twistedPrimeLogContinuation s)
      (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 (-((chiFourCentralMultiplicity : ℂ) + 1 / 2))) := by
  have hhigherAnalytic : AnalyticAt ℂ (L higherExponentPrimePowerCoeff) (1 / 2 : ℂ) :=
    higherExponentPrimePowerCoeff_LSeries_analyticOnNhd (1 / 2 : ℂ) (by norm_num)
  have hsub : Filter.Tendsto (fun s : ℂ => s - 1 / 2)
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - 1 / 2) (1 / 2 : ℂ) := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hhigher : Filter.Tendsto
      (fun s : ℂ => (s - 1 / 2) * L higherExponentPrimePowerCoeff s)
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 0) := by
    simpa using hsub.mul
      (hhigherAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h := tendsto_chiFourNegLogDerivative_central.sub
    tendsto_squarePrimePowerContinuation_residue_half |>.sub hhigher
  have hevent :
      (fun s : ℂ => (s - 1 / 2) * chiFourNegLogDerivative s -
          (s - 1 / 2) * squarePrimePowerContinuation s -
          (s - 1 / 2) * L higherExponentPrimePowerCoeff s) =ᶠ[𝓝[≠] (1 / 2 : ℂ)]
        fun s => (s - 1 / 2) * twistedPrimeLogContinuation s := by
    filter_upwards with s
    simp only [twistedPrimeLogContinuation]
    ring
  simpa [sub_eq_add_neg, add_comm] using h.congr' hevent

lemma tendsto_twistedPrimeLogContinuation_nonreal_zero
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chiFour rho = 0)
    (hre : (1 / 2 : ℝ) ≤ rho.re) (him : rho.im ≠ 0) :
    Filter.Tendsto
      (fun s : ℂ => (s - rho) * twistedPrimeLogContinuation s)
      (𝓝[≠] rho) (𝓝 (-(chiFourZeroMultiplicity rho : ℂ))) := by
  have hsquareAnalytic :=
    squarePrimePowerContinuation_analyticAt_of_half_le_re_of_im_ne_zero hre him
  have hrhoHigher : (2 / 5 : ℝ) < rho.re := by linarith
  have hhigherAnalytic : AnalyticAt ℂ (L higherExponentPrimePowerCoeff) rho :=
    higherExponentPrimePowerCoeff_LSeries_analyticOnNhd rho hrhoHigher
  have hsub : Filter.Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - rho) rho := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsquare : Filter.Tendsto
      (fun s : ℂ => (s - rho) * squarePrimePowerContinuation s)
      (𝓝[≠] rho) (𝓝 0) := by
    simpa using hsub.mul
      (hsquareAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hhigher : Filter.Tendsto
      (fun s : ℂ => (s - rho) * L higherExponentPrimePowerCoeff s)
      (𝓝[≠] rho) (𝓝 0) := by
    simpa using hsub.mul
      (hhigherAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h := (chiFourNegLogDerivative_residueAt_zero hrho).2.sub hsquare |>.sub hhigher
  have hevent :
      (fun s : ℂ => (s - rho) * chiFourNegLogDerivative s -
          (s - rho) * squarePrimePowerContinuation s -
          (s - rho) * L higherExponentPrimePowerCoeff s) =ᶠ[𝓝[≠] rho]
        fun s => (s - rho) * twistedPrimeLogContinuation s := by
    filter_upwards with s
    simp only [twistedPrimeLogContinuation]
    ring
  simpa using h.congr' hevent

end Submission.PrimeSeries
