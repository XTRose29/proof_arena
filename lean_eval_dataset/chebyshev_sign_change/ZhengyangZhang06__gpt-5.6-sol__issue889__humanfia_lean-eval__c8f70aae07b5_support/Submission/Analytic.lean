import Submission.Helpers

open LeanEval.NumberTheory.ChebyshevSignChangeProblem
open scoped ArithmeticFunction.vonMangoldt LSeries.notation Chebyshev Topology

namespace Submission.Analytic

open Submission.Helpers
open Filter

lemma chiFour_apply_nat (n : ℕ) : chiFour n = ((ZMod.χ₄ n : ℤ) : ℂ) := by
  rfl

noncomputable def twistedVonMangoldtCoeff (n : ℕ) : ℂ :=
  chiFour n * (ArithmeticFunction.vonMangoldt n : ℂ)

noncomputable def twistedChebyshevSum (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), twistedVonMangoldtCoeff k

noncomputable def realTwistedVonMangoldtCoeff (n : ℕ) : ℝ :=
  (ZMod.χ₄ n : ℤ) * ArithmeticFunction.vonMangoldt n

noncomputable def realTwistedChebyshevSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), realTwistedVonMangoldtCoeff k

noncomputable def primeCharacterCoeff (n : ℕ) : ℂ :=
  if n.Prime then chiFour n else 0

noncomputable def complexCharacterPrimeSum (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.range (n + 1), primeCharacterCoeff p

def realCharacterPrimeSum (n : ℕ) : ℝ :=
  characterPrimeSum n

noncomputable def twistedPrimeLogCoeff (n : ℕ) : ℂ :=
  if n.Prime then chiFour n * (Real.log n : ℂ) else 0

noncomputable def twistedPrimeLogSum (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.range (n + 1), twistedPrimeLogCoeff p

noncomputable def realTwistedPrimeLogCoeff (n : ℕ) : ℝ :=
  if n.Prime then (ZMod.χ₄ n : ℤ) * Real.log n else 0

noncomputable def realTwistedPrimeLogSum (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n + 1), realTwistedPrimeLogCoeff p

noncomputable def higherPrimePowerCoeff (n : ℕ) : ℂ :=
  if n.Prime then 0 else twistedVonMangoldtCoeff n

noncomputable def higherPrimePowerError (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), higherPrimePowerCoeff k

noncomputable def realHigherPrimePowerCoeff (n : ℕ) : ℝ :=
  if n.Prime then 0 else realTwistedVonMangoldtCoeff n

noncomputable def realHigherPrimePowerError (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), realHigherPrimePowerCoeff k

lemma higherPrimePowerCoeff_support {n : ℕ} (hn : higherPrimePowerCoeff n ≠ 0) :
    IsPrimePow n ∧ ¬n.Prime := by
  by_cases hp : n.Prime
  · simp [higherPrimePowerCoeff, hp] at hn
  · refine ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp ?_, hp⟩
    intro hzero
    apply hn
    simp [higherPrimePowerCoeff, twistedVonMangoldtCoeff, hp, hzero]

lemma complexCharacterPrimeSum_eq (n : ℕ) :
    complexCharacterPrimeSum n = (characterPrimeSum n : ℂ) := by
  classical
  unfold complexCharacterPrimeSum characterPrimeSum primeCharacterCoeff
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hp : p.Prime
  · simp [hp, chiFour_apply_nat, ZMod.χ₄]
  · simp [hp]

lemma complexCharacterPrimeSum_eq_real (n : ℕ) :
    complexCharacterPrimeSum n = (realCharacterPrimeSum n : ℂ) := by
  rw [complexCharacterPrimeSum_eq, realCharacterPrimeSum]
  norm_cast

lemma twistedVonMangoldtCoeff_eq (n : ℕ) :
    twistedVonMangoldtCoeff n =
      ((ZMod.χ₄ n : ℤ) : ℂ) * ArithmeticFunction.vonMangoldt n := by
  rfl

lemma twistedVonMangoldtCoeff_eq_real (n : ℕ) :
    twistedVonMangoldtCoeff n = (realTwistedVonMangoldtCoeff n : ℂ) := by
  rw [twistedVonMangoldtCoeff_eq]
  norm_cast

lemma twistedChebyshevSum_eq_real (n : ℕ) :
    twistedChebyshevSum n = (realTwistedChebyshevSum n : ℂ) := by
  classical
  rw [twistedChebyshevSum, realTwistedChebyshevSum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _hk => twistedVonMangoldtCoeff_eq_real k

lemma twistedPrimeLogCoeff_eq_real (n : ℕ) :
    twistedPrimeLogCoeff n = (realTwistedPrimeLogCoeff n : ℂ) := by
  by_cases hn : n.Prime
  · simp [twistedPrimeLogCoeff, realTwistedPrimeLogCoeff, hn, chiFour_apply_nat]
  · simp [twistedPrimeLogCoeff, realTwistedPrimeLogCoeff, hn]

lemma twistedPrimeLogSum_eq_real (n : ℕ) :
    twistedPrimeLogSum n = (realTwistedPrimeLogSum n : ℂ) := by
  classical
  rw [twistedPrimeLogSum, realTwistedPrimeLogSum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun p _hp => twistedPrimeLogCoeff_eq_real p

lemma higherPrimePowerCoeff_eq_real (n : ℕ) :
    higherPrimePowerCoeff n = (realHigherPrimePowerCoeff n : ℂ) := by
  by_cases hn : n.Prime
  · simp [higherPrimePowerCoeff, realHigherPrimePowerCoeff, hn]
  · simp [higherPrimePowerCoeff, realHigherPrimePowerCoeff, hn,
      twistedVonMangoldtCoeff_eq_real]

lemma higherPrimePowerError_eq_real (n : ℕ) :
    higherPrimePowerError n = (realHigherPrimePowerError n : ℂ) := by
  classical
  rw [higherPrimePowerError, realHigherPrimePowerError, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _hk => higherPrimePowerCoeff_eq_real k

lemma realHigherPrimePowerError_eq_sum_exponents (n : ℕ) :
    realHigherPrimePowerError n =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log n / Real.log 2⌋₊,
        ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          realHigherPrimePowerCoeff (p ^ k) := by
  classical
  rw [realHigherPrimePowerError]
  calc
    ∑ k ∈ Finset.range (n + 1), realHigherPrimePowerCoeff k =
        ∑ k ∈ Finset.Ioc 0 n, realHigherPrimePowerCoeff k := by
      rw [show Finset.range (n + 1) = Finset.Icc 0 n by ext k; simp,
        Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
      simp [realHigherPrimePowerCoeff, realTwistedVonMangoldtCoeff]
    _ = ∑ k ∈ Finset.Ioc 0 n with IsPrimePow k,
          realHigherPrimePowerCoeff k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hpow : IsPrimePow k
      · simp [hpow]
      · have hΛ : ArithmeticFunction.vonMangoldt k = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
        simp [hpow, realHigherPrimePowerCoeff, realTwistedVonMangoldtCoeff, hΛ]
    _ = _ := by
      simpa using Chebyshev.sum_PrimePow_eq_sum_sum
        realHigherPrimePowerCoeff (x := (n : ℝ)) (by positivity)

lemma chiFour_square_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (ZMod.χ₄ ((p ^ 2 : ℕ) : ZMod 4) : ℤ) = 1 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hmod4lt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
  have hmod4odd : p % 4 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4), hodd]
  have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hsquaremod : p ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod4 with h | h
    · norm_num [h]
    · norm_num [h]
  have hsquareodd : p ^ 2 % 2 = 1 := by
    rw [Nat.pow_mod, hodd]
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  norm_num [hsquaremod, hsquareodd]

lemma realHigherPrimePowerCoeff_sq {p : ℕ} (hp : p.Prime) :
    realHigherPrimePowerCoeff (p ^ 2) = if p = 2 then 0 else Real.log p := by
  by_cases hp2 : p = 2
  · subst p
    norm_num [realHigherPrimePowerCoeff, realTwistedVonMangoldtCoeff, ZMod.χ₄]
  · rw [if_neg hp2]
    simp only [realHigherPrimePowerCoeff, Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 2),
      ↓reduceIte, realTwistedVonMangoldtCoeff,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    rw [chiFour_square_of_prime_ne_two hp hp2]
    norm_num

noncomputable def realPrimePowerExponentTerm (n k : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
    realHigherPrimePowerCoeff (p ^ k)

noncomputable def realPrimeSquareTerm (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊√(n : ℝ)⌋₊ with p.Prime,
    if p = 2 then 0 else Real.log p

noncomputable def realHigherExponentRemainder (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 3 ⌊Real.log n / Real.log 2⌋₊,
    realPrimePowerExponentTerm n k

lemma realPrimePowerExponentTerm_one (n : ℕ) :
    realPrimePowerExponentTerm n 1 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter] at hp
  simp [realHigherPrimePowerCoeff, hp.2]

lemma realPrimePowerExponentTerm_two (n : ℕ) :
    realPrimePowerExponentTerm n 2 = realPrimeSquareTerm n := by
  classical
  unfold realPrimePowerExponentTerm realPrimeSquareTerm
  rw [show ((1 : ℝ) / (2 : ℕ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  apply Finset.sum_congr rfl
  intro p hp
  exact realHigherPrimePowerCoeff_sq (Finset.mem_filter.mp hp).2

lemma two_le_log_floor {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ ⌊Real.log n / Real.log 2⌋₊ := by
  rw [Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0),
    le_div_iff₀ (Real.log_pos (by norm_num))]
  rw [← Real.log_pow]
  gcongr
  exact_mod_cast hn

lemma realHigherPrimePowerError_eq_square_add_remainder (n : ℕ) (hn : 4 ≤ n) :
    realHigherPrimePowerError n =
      realPrimeSquareTerm n + realHigherExponentRemainder n := by
  rw [realHigherPrimePowerError_eq_sum_exponents]
  change (∑ k ∈ Finset.Icc 1 ⌊Real.log n / Real.log 2⌋₊,
      realPrimePowerExponentTerm n k) = _
  let N := ⌊Real.log n / Real.log 2⌋₊
  have hN : 2 ≤ N := two_le_log_floor hn
  have hsplit1 : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp
    omega
  have hsplit2 : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext k
    simp
    omega
  rw [show ⌊Real.log n / Real.log 2⌋₊ = N by rfl, hsplit1,
    Finset.sum_insert (by simp), hsplit2, Finset.sum_insert (by simp),
    realPrimePowerExponentTerm_one, zero_add, realPrimePowerExponentTerm_two]
  rfl

lemma realPrimeSquareTerm_eq_theta (n : ℕ) (hn : 4 ≤ n) :
    realPrimeSquareTerm n = Chebyshev.theta √(n : ℝ) - Real.log 2 := by
  classical
  have h2sqrt : 2 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
  let s := (Finset.Ioc 0 ⌊√(n : ℝ)⌋₊).filter Nat.Prime
  have h2mem : 2 ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨by simp [h2sqrt], Nat.prime_two⟩
  change (∑ p ∈ s, if p = 2 then 0 else Real.log p) =
    (∑ p ∈ s, Real.log p) - Real.log 2
  calc
    (∑ p ∈ s, if p = 2 then 0 else Real.log p) =
        ∑ p ∈ s, (Real.log p - if p = 2 then Real.log p else 0) := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hp2 : p = 2 <;> simp [hp2]
    _ = (∑ p ∈ s, Real.log p) -
        ∑ p ∈ s, if p = 2 then Real.log p else 0 :=
      Finset.sum_sub_distrib _ _
    _ = (∑ p ∈ s, Real.log p) - Real.log 2 := by
      rw [Finset.sum_ite_eq' s 2]
      simp [h2mem]

lemma abs_theta_sqrt_sub_log_two_le (n : ℕ) (hn : 1 ≤ n) :
    |Chebyshev.theta √(n : ℝ) - Real.log 2| ≤
      (Real.log 4 + Real.log 2) * √(n : ℝ) := by
  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_one : 1 ≤ √(n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have htheta_nonneg : 0 ≤ Chebyshev.theta √(n : ℝ) := Chebyshev.theta_nonneg _
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    |Chebyshev.theta √(n : ℝ) - Real.log 2| ≤
        Chebyshev.theta √(n : ℝ) + Real.log 2 :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ ≤ Real.log 4 * √(n : ℝ) + Real.log 2 * √(n : ℝ) := by
      gcongr
      · exact Chebyshev.theta_le_log4_mul_x hsqrt_nonneg
      · simpa using mul_le_mul_of_nonneg_left hsqrt_one hlog2_nonneg
    _ = (Real.log 4 + Real.log 2) * √(n : ℝ) := by ring

lemma abs_realPrimeSquareTerm_le_sqrt (n : ℕ) (hn : 4 ≤ n) :
    |realPrimeSquareTerm n| ≤
      (Real.log 4 + Real.log 2) * √(n : ℝ) := by
  rw [realPrimeSquareTerm_eq_theta n hn]
  exact abs_theta_sqrt_sub_log_two_le n (by omega)

lemma norm_twistedVonMangoldtCoeff_le (n : ℕ) :
    ‖twistedVonMangoldtCoeff n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rw [twistedVonMangoldtCoeff, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (chiFour.norm_le_one n)

lemma norm_higherPrimePowerCoeff_le (n : ℕ) :
    ‖higherPrimePowerCoeff n‖ ≤
      if n.Prime then 0 else ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n.Prime
  · simp [higherPrimePowerCoeff, hn]
  · simpa [higherPrimePowerCoeff, hn] using norm_twistedVonMangoldtCoeff_le n

lemma abs_realHigherPrimePowerCoeff_prime_pow_le_log {p k : ℕ}
    (hp : p.Prime) (hk : 2 ≤ k) :
    |realHigherPrimePowerCoeff (p ^ k)| ≤ Real.log p := by
  have h := norm_higherPrimePowerCoeff_le (p ^ k)
  rw [higherPrimePowerCoeff_eq_real, Complex.norm_real, Real.norm_eq_abs,
    if_neg (Nat.Prime.not_prime_pow hk),
    ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp] at h
  exact h

lemma abs_realPrimePowerExponentTerm_le_theta (n k : ℕ) (hk : 2 ≤ k) :
    |realPrimePowerExponentTerm n k| ≤
      Chebyshev.theta ((n : ℝ) ^ ((1 : ℝ) / k)) := by
  classical
  unfold realPrimePowerExponentTerm Chebyshev.theta
  calc
    |∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        realHigherPrimePowerCoeff (p ^ k)| ≤
        ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          |realHigherPrimePowerCoeff (p ^ k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Ioc 0 ⌊(n : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        Real.log p := by
      apply Finset.sum_le_sum
      intro p hp_mem
      exact abs_realHigherPrimePowerCoeff_prime_pow_le_log
        (Finset.mem_filter.mp hp_mem).2 hk

lemma one_div_nat_le_one_third {k : ℕ} (hk : 3 ≤ k) :
    (1 : ℝ) / k ≤ 1 / 3 := by
  exact (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1)
    (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) hk))
    (by norm_num : (0 : ℝ) < 3)).2 (by exact_mod_cast hk)

lemma abs_realPrimePowerExponentTerm_le_cuberoot (n k : ℕ)
    (hn : 1 ≤ n) (hk : 3 ≤ k) :
    |realPrimePowerExponentTerm n k| ≤
      Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  refine (abs_realPrimePowerExponentTerm_le_theta n k (by omega)).trans ?_
  refine (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg (by positivity) _)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
      (one_div_nat_le_one_third hk))
    (Real.log_nonneg (by norm_num))

lemma abs_realHigherExponentRemainder_le (n : ℕ) (hn : 4 ≤ n) :
    |realHigherExponentRemainder n| ≤
      (Real.log n / Real.log 2) *
        (Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  unfold realHigherExponentRemainder
  let N := ⌊Real.log n / Real.log 2⌋₊
  let B := Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ)
  have hB : 0 ≤ B :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg (by positivity) _)
  have hquot : 0 ≤ Real.log n / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
      (Real.log_nonneg (by norm_num))
  calc
    |∑ k ∈ Finset.Icc 3 N, realPrimePowerExponentTerm n k| ≤
        ∑ k ∈ Finset.Icc 3 N, |realPrimePowerExponentTerm n k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 3 N, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_realPrimePowerExponentTerm_le_cuberoot n k (by omega)
        (Finset.mem_Icc.mp hk).1
    _ = ((Finset.Icc 3 N).card : ℝ) * B := by simp
    _ ≤ (N : ℝ) * B := by
      gcongr
      simp
    _ ≤ (Real.log n / Real.log 2) * B := by
      gcongr
      exact Nat.floor_le hquot

lemma explicit_remainder_bound_isLittleO_sqrt_real :
    (fun x : ℝ => (Real.log x / Real.log 2) *
      (Real.log 4 * x ^ (1 / 3 : ℝ))) =o[Filter.atTop] Real.sqrt := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).mul_isBigO
    (Asymptotics.isBigO_refl (fun x : ℝ => x ^ (1 / 3 : ℝ)) Filter.atTop)
  refine (h.const_mul_left (Real.log 4 / Real.log 2)).congr' ?_ ?_
  · filter_upwards with x
    ring
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num

lemma explicit_remainder_bound_isLittleO_sqrt_nat :
    (fun n : ℕ => (Real.log n / Real.log 2) *
      (Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ))) =o[Filter.atTop]
      fun n : ℕ => √(n : ℝ) := by
  simpa [Function.comp_def] using
    explicit_remainder_bound_isLittleO_sqrt_real.comp_tendsto
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)

lemma realHigherExponentRemainder_isLittleO_sqrt :
    realHigherExponentRemainder =o[Filter.atTop] fun n : ℕ => √(n : ℝ) := by
  have hO : realHigherExponentRemainder =O[Filter.atTop]
      fun n : ℕ => (Real.log n / Real.log 2) *
        (Real.log 4 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    simpa only [Real.norm_eq_abs] using abs_realHigherExponentRemainder_le n hn
  exact hO.trans_isLittleO explicit_remainder_bound_isLittleO_sqrt_nat

lemma realHigherPrimePowerError_bound_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      |realHigherPrimePowerError n| ≤
        (Real.log 4 + Real.log 2 + ε) * √(n : ℝ) := by
  have hrem := realHigherExponentRemainder_isLittleO_sqrt.bound hε
  filter_upwards [Filter.eventually_ge_atTop 4, hrem] with n hn hremn
  rw [realHigherPrimePowerError_eq_square_add_remainder n hn]
  have hremn' : |realHigherExponentRemainder n| ≤ ε * √(n : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hremn
  calc
    |realPrimeSquareTerm n + realHigherExponentRemainder n| ≤
        |realPrimeSquareTerm n| + |realHigherExponentRemainder n| := abs_add_le _ _
    _ ≤ (Real.log 4 + Real.log 2) * √(n : ℝ) + ε * √(n : ℝ) :=
      add_le_add (abs_realPrimeSquareTerm_le_sqrt n hn) hremn'
    _ = (Real.log 4 + Real.log 2 + ε) * √(n : ℝ) := by ring

lemma realTwistedVonMangoldtCoeff_eq_prime_add_error (n : ℕ) :
    realTwistedVonMangoldtCoeff n =
      realTwistedPrimeLogCoeff n + realHigherPrimePowerCoeff n := by
  by_cases hn : n.Prime
  · simp [realTwistedPrimeLogCoeff, realHigherPrimePowerCoeff,
      realTwistedVonMangoldtCoeff, hn, ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [realTwistedPrimeLogCoeff, realHigherPrimePowerCoeff, hn]

lemma realTwistedChebyshevSum_eq_prime_add_error (n : ℕ) :
    realTwistedChebyshevSum n =
      realTwistedPrimeLogSum n + realHigherPrimePowerError n := by
  classical
  rw [realTwistedChebyshevSum, realTwistedPrimeLogSum, realHigherPrimePowerError,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _hk => realTwistedVonMangoldtCoeff_eq_prime_add_error k

lemma realTwistedChebyshevSum_eq_prime_add_square_add_remainder
    (n : ℕ) (hn : 4 ≤ n) :
    realTwistedChebyshevSum n =
      realTwistedPrimeLogSum n + (Chebyshev.theta √(n : ℝ) - Real.log 2) +
        realHigherExponentRemainder n := by
  rw [realTwistedChebyshevSum_eq_prime_add_error,
    realHigherPrimePowerError_eq_square_add_remainder n hn,
    realPrimeSquareTerm_eq_theta n hn]
  ring

lemma twistedVonMangoldt_LSeries_eq {s : ℂ} (hs : 1 < s.re) :
    L twistedVonMangoldtCoeff s =
      -deriv (L ↗chiFour) s / L ↗chiFour s := by
  change L (↗chiFour * ↗ArithmeticFunction.vonMangoldt) s = _
  exact chiFour_LSeries_twist_vonMangoldt_eq hs

private lemma chiFour_LSeries_conj (s : ℂ) :
    (starRingEnd ℂ) (L (chiFour ·) ((starRingEnd ℂ) s)) = L (chiFour ·) s := by
  rw [LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀]
    have harg : ((n : ℂ).arg) ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    rw [← Complex.conj_cpow (n : ℂ) s harg]
    simp [chiFour_apply_nat]

lemma chiFour_LFunction_conj (s : ℂ) :
    DirichletCharacter.LFunction chiFour ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction chiFour s) := by
  let f := DirichletCharacter.LFunction chiFour
  let g := (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)
  have hf : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 differentiable_chiFour_LFunction
  have hg_diff : Differentiable ℂ g := by
    intro z
    change DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) z
    rw [differentiableAt_conj_conj_iff]
    exact differentiable_chiFour_LFunction ((starRingEnd ℂ) z)
  have hg : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 hg_diff
  have heq : f = g := by
    apply hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ))
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (by norm_num : 1 < (2 : ℂ).re)] with z hz
    change DirichletCharacter.LFunction chiFour z =
      (starRingEnd ℂ) (DirichletCharacter.LFunction chiFour ((starRingEnd ℂ) z))
    rw [DirichletCharacter.LFunction_eq_LSeries chiFour hz]
    rw [DirichletCharacter.LFunction_eq_LSeries chiFour (by simpa using hz)]
    exact (chiFour_LSeries_conj z).symm
  have hs := congrFun heq ((starRingEnd ℂ) s)
  simpa [f, g, Function.comp_def] using hs

noncomputable def chiFourNegLogDerivative (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction chiFour) s

lemma twistedVonMangoldt_LSeries_eq_continued {s : ℂ} (hs : 1 < s.re) :
    L twistedVonMangoldtCoeff s = chiFourNegLogDerivative s := by
  rw [twistedVonMangoldt_LSeries_eq hs, chiFourNegLogDerivative, logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chiFour hs,
    DirichletCharacter.LFunction_eq_LSeries chiFour hs]
  rw [neg_div]

lemma chiFourNegLogDerivative_meromorphic : Meromorphic chiFourNegLogDerivative := by
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chiFour) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 differentiable_chiFour_LFunction
  have hm : Meromorphic (DirichletCharacter.LFunction chiFour) := by
    simpa [Meromorphic] using hA.meromorphicOn
  change Meromorphic (fun s => -logDeriv (DirichletCharacter.LFunction chiFour) s)
  exact hm.logDeriv.neg

lemma chiFourNegLogDerivative_continuousOn :
    ContinuousOn chiFourNegLogDerivative
      {s | DirichletCharacter.LFunction chiFour s ≠ 0} := by
  change ContinuousOn
    (fun s => -(deriv (DirichletCharacter.LFunction chiFour) s /
      DirichletCharacter.LFunction chiFour s)) _
  simpa only [neg_div] using
    DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv chiFour_ne_one

def chiFourZeroSet : Set ℂ :=
  {s | DirichletCharacter.LFunction chiFour s = 0}

lemma chiFourZeroSet_isDiscrete : IsDiscrete chiFourZeroSet := by
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chiFour) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 differentiable_chiFour_LFunction
  have hnot : ¬Set.EqOn (DirichletCharacter.LFunction chiFour) 0 Set.univ := by
    intro h
    have hzero := h (Set.mem_univ (1 : ℂ))
    exact chiFour_LFunction_ne_zero_of_one_le_re (s := (1 : ℂ)) (by simp) (by simpa using hzero)
  have hne :=
    (hA.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left hnot
  have hmem : {s | DirichletCharacter.LFunction chiFour s ≠ 0} ∈ Filter.codiscrete ℂ := by
    rw [Filter.codiscrete]
    change ∀ᶠ s in Filter.codiscreteWithin Set.univ,
      DirichletCharacter.LFunction chiFour s ≠ 0
    exact hne
  have hd := (mem_codiscrete'.mp hmem).2
  change IsDiscrete chiFourZeroSet
  convert hd using 1
  ext s
  simp [chiFourZeroSet]

lemma chiFourZeroSet_inter_compact_finite {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ chiFourZeroSet).Finite := by
  have hclosed : IsClosed chiFourZeroSet := by
    rw [chiFourZeroSet]
    exact isClosed_eq differentiable_chiFour_LFunction.continuous continuous_const
  have hcompact : IsCompact (K ∩ chiFourZeroSet) := hK.inter_right hclosed
  exact hcompact.finite (chiFourZeroSet_isDiscrete.mono Set.inter_subset_right)

lemma chiFour_LFunction_analyticOrderAt_ne_top (s : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction chiFour) s ≠ ⊤ := by
  intro htop
  have hzero : DirichletCharacter.LFunction chiFour = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
      (fun z => differentiable_chiFour_LFunction.analyticAt z)).mp htop
  have h1 : DirichletCharacter.LFunction chiFour (1 : ℂ) = 0 := by
    rw [hzero]
    rfl
  exact chiFour_LFunction_ne_zero_of_one_le_re (s := (1 : ℂ)) (by simp) h1

lemma chiFour_invGammaFactor_analyticAt (s : ℂ) :
    AnalyticAt ℂ (fun z => (DirichletCharacter.gammaFactor chiFour z)⁻¹) s := by
  have h : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ (z + 1))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (by fun_prop)
  simpa only [chiFour_odd.gammaFactor_def] using h.analyticAt s

lemma chiFour_invGammaFactor_ne_zero {s : ℂ} (hs : -1 < s.re) :
    (DirichletCharacter.gammaFactor chiFour s)⁻¹ ≠ 0 := by
  apply inv_ne_zero
  rw [chiFour_odd.gammaFactor_def]
  exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

lemma chiFour_LFunction_eq_completed_mul_invGammaFactor :
    DirichletCharacter.LFunction chiFour =
      DirichletCharacter.completedLFunction chiFour *
        fun z => (DirichletCharacter.gammaFactor chiFour z)⁻¹ := by
  funext z
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chiFour z
    (Or.inr (by norm_num : (4 : ℕ) ≠ 1))]
  rfl

lemma chiFour_LFunction_analyticOrderAt_eq_completed {s : ℂ}
    (hs : -1 < s.re) :
    analyticOrderAt (DirichletCharacter.LFunction chiFour) s =
      analyticOrderAt (DirichletCharacter.completedLFunction chiFour) s := by
  have hcompleted :
      AnalyticAt ℂ (DirichletCharacter.completedLFunction chiFour) s :=
    (DirichletCharacter.differentiable_completedLFunction chiFour_ne_one).analyticAt s
  have hinv := chiFour_invGammaFactor_analyticAt s
  have hinvOrder :
      analyticOrderAt (fun z => (DirichletCharacter.gammaFactor chiFour z)⁻¹) s = 0 :=
    hinv.analyticOrderAt_eq_zero.mpr (chiFour_invGammaFactor_ne_zero hs)
  rw [chiFour_LFunction_eq_completed_mul_invGammaFactor,
    analyticOrderAt_mul hcompleted hinv, hinvOrder, add_zero]

noncomputable def chiFourZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction chiFour) s

lemma chiFourZeroMultiplicity_eq_completed {s : ℂ} (hs : -1 < s.re) :
    chiFourZeroMultiplicity s =
      analyticOrderNatAt (DirichletCharacter.completedLFunction chiFour) s := by
  unfold chiFourZeroMultiplicity analyticOrderNatAt
  rw [chiFour_LFunction_analyticOrderAt_eq_completed hs]

lemma chiFourZeroMultiplicity_pos {s : ℂ}
    (hs : DirichletCharacter.LFunction chiFour s = 0) :
    0 < chiFourZeroMultiplicity s := by
  have hf : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) s :=
    differentiable_chiFour_LFunction.analyticAt s
  have horder : analyticOrderAt (DirichletCharacter.LFunction chiFour) s ≠ 0 :=
    hf.analyticOrderAt_ne_zero.mpr hs
  apply Nat.pos_of_ne_zero
  intro hm
  apply horder
  rw [← Nat.cast_analyticOrderNatAt (chiFour_LFunction_analyticOrderAt_ne_top s)]
  simp [chiFourZeroMultiplicity] at hm
  rw [hm]
  rfl

lemma tendsto_sub_mul_logDeriv_analyticOrderNatAt {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfinite : analyticOrderAt f x ≠ ⊤) :
    Filter.Tendsto (fun w => (w - x) * logDeriv f w) (𝓝[≠] x)
      (𝓝 (analyticOrderNatAt f x : ℂ)) := by
  let m := analyticOrderNatAt f x
  obtain ⟨g, hg, hg0, hfg⟩ :=
    (hf.analyticOrderNatAt_eq_iff hfinite (n := m)).mp rfl
  have hfg' : f =ᶠ[𝓝 x] fun z => (z - x) ^ m * g z := by
    filter_upwards [hfg] with z hz
    simpa [smul_eq_mul] using hz
  have hderiv := hfg'.deriv
  have hg_ne : ∀ᶠ z in 𝓝 x, g z ≠ 0 :=
    hg.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr hg0)
  have hg_analytic : ∀ᶠ z in 𝓝 x, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have heq :
      (fun w => (w - x) * logDeriv f w) =ᶠ[𝓝[≠] x]
        fun w => (m : ℂ) + (w - x) * logDeriv g w := by
    filter_upwards [hfg'.filter_mono nhdsWithin_le_nhds,
      hderiv.filter_mono nhdsWithin_le_nhds,
      hg_ne.filter_mono nhdsWithin_le_nhds,
      hg_analytic.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hfw hdfw hgw hgaw hw
    have hwx : w - x ≠ 0 := sub_ne_zero.mpr hw
    rw [logDeriv_apply, hdfw, hfw]
    change (w - x) * logDeriv (fun z => (z - x) ^ m * g z) w = _
    rw [logDeriv_mul (f := fun z => (z - x) ^ m) (g := g) w
      (pow_ne_zero _ hwx) hgw (by fun_prop) hgaw.differentiableAt]
    rw [logDeriv_fun_pow (by fun_prop) m]
    simp only [logDeriv_apply, deriv_sub_const]
    rw [deriv_id'']
    field_simp
  have hlogg : Filter.Tendsto (logDeriv g) (𝓝 x) (𝓝 (logDeriv g x)) := by
    have hcont : ContinuousAt (logDeriv g) x := by
      change ContinuousAt (deriv g / g) x
      exact hg.deriv.continuousAt.div hg.continuousAt hg0
    exact hcont
  have hsub : Filter.Tendsto (fun w : ℂ => w - x) (𝓝[≠] x) (𝓝 0) := by
    have hcont : ContinuousAt (fun w : ℂ => w - x) x := by fun_prop
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have hprod : Filter.Tendsto (fun w => (w - x) * logDeriv g w)
      (𝓝[≠] x) (𝓝 0) := by
    simpa using hsub.mul (hlogg.mono_left nhdsWithin_le_nhds)
  refine (tendsto_congr' heq).2 ?_
  simpa [m] using tendsto_const_nhds.add hprod

lemma chiFourNegLogDerivative_residueAt_zero {s : ℂ}
    (hs : DirichletCharacter.LFunction chiFour s = 0) :
    0 < chiFourZeroMultiplicity s ∧
      Filter.Tendsto (fun w => (w - s) * chiFourNegLogDerivative w) (𝓝[≠] s)
        (𝓝 (-(chiFourZeroMultiplicity s : ℂ))) := by
  refine ⟨chiFourZeroMultiplicity_pos hs, ?_⟩
  have h := tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (differentiable_chiFour_LFunction.analyticAt s)
    (chiFour_LFunction_analyticOrderAt_ne_top s)
  simpa [chiFourNegLogDerivative, chiFourZeroMultiplicity] using h.neg

lemma chiFour_completedLFunction_zero_one_sub_iff (s : ℂ) :
    DirichletCharacter.completedLFunction chiFour (1 - s) = 0 ↔
      DirichletCharacter.completedLFunction chiFour s = 0 := by
  constructor
  · intro h
    have h' := chiFour_completedLFunction_one_sub (1 - s)
    rw [h, mul_zero] at h'
    simpa only [sub_sub_cancel] using h'
  · intro h
    rw [chiFour_completedLFunction_one_sub, h, mul_zero]

lemma chiFourNegLogDerivative_orderAt_zero {s : ℂ}
    (hs : DirichletCharacter.LFunction chiFour s = 0) :
    meromorphicOrderAt chiFourNegLogDerivative s = -1 := by
  let f := DirichletCharacter.LFunction chiFour
  have hf_diff : Differentiable ℂ f := differentiable_chiFour_LFunction
  have hf : AnalyticAt ℂ f s := hf_diff.analyticAt s
  have hnotTop : analyticOrderAt f s ≠ ⊤ := chiFour_LFunction_analyticOrderAt_ne_top s
  let m := analyticOrderNatAt f s
  have horder : analyticOrderAt f s = m := (Nat.cast_analyticOrderNatAt hnotTop).symm
  have hm : m ≠ 0 := by
    intro hm0
    apply hf.analyticOrderAt_ne_zero.mpr hs
    rw [horder, hm0]
    rfl
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have horder' : analyticOrderAt f s = (n + 1 : ℕ) := by
    rw [horder, hn]
  have hderivOrder : analyticOrderAt (deriv f) s = n :=
    analyticOrderAt_deriv_of_pos hf horder'
  have hlog : meromorphicOrderAt (logDeriv f) s = -1 := by
    rw [show logDeriv f = deriv f / f by rfl,
      meromorphicOrderAt_div hf.deriv.meromorphicAt hf.meromorphicAt,
      hf.deriv.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq,
      hderivOrder, horder']
    change (((n : ℤ) - ((n : ℤ) + 1) : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ)
    norm_num
  change meromorphicOrderAt (-(logDeriv f)) s = -1
  rw [← meromorphicOrderAt_neg]
  exact hlog

lemma chiFour_LFunction_zero_iff_completed {s : ℂ} (hs : -1 < s.re) :
    DirichletCharacter.LFunction chiFour s = 0 ↔
      DirichletCharacter.completedLFunction chiFour s = 0 := by
  have hgamma : DirichletCharacter.gammaFactor chiFour s ≠ 0 := by
    rw [chiFour_odd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chiFour s
    (Or.inr (by norm_num : (4 : ℕ) ≠ 1))]
  simp [hgamma]

lemma chiFour_completedLFunction_ne_zero_two :
    DirichletCharacter.completedLFunction chiFour (2 : ℂ) ≠ 0 := by
  intro h
  have hL : DirichletCharacter.LFunction chiFour (2 : ℂ) = 0 :=
    (chiFour_LFunction_zero_iff_completed (s := (2 : ℂ)) (by norm_num)).2 h
  exact chiFour_LFunction_ne_zero_of_one_le_re (s := (2 : ℂ)) (by norm_num) hL

lemma chiFour_completedLFunction_analyticOrderAt_ne_top (s : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction chiFour) s ≠ ⊤ := by
  intro htop
  have hglobal :
      AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction chiFour) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2
      (DirichletCharacter.differentiable_completedLFunction chiFour_ne_one)
  have hzero : DirichletCharacter.completedLFunction chiFour = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
      (fun z => hglobal z (Set.mem_univ z))).mp htop
  exact chiFour_completedLFunction_ne_zero_two (congrFun hzero (2 : ℂ))

lemma chiFour_LFunction_zero_one_sub_iff {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DirichletCharacter.LFunction chiFour (1 - s) = 0 ↔
      DirichletCharacter.LFunction chiFour s = 0 := by
  have hs : -1 < s.re := by linarith
  have h1s : -1 < (1 - s).re := by simp; linarith
  rw [chiFour_LFunction_zero_iff_completed h1s,
    chiFour_LFunction_zero_iff_completed hs,
    chiFour_completedLFunction_zero_one_sub_iff]

lemma chiFour_LFunction_ne_zero_of_neg_one_lt_re_of_re_le_zero {s : ℂ}
    (hsneg : -1 < s.re) (hs0 : s.re ≤ 0) :
    DirichletCharacter.LFunction chiFour s ≠ 0 := by
  intro hs
  have hcs : DirichletCharacter.completedLFunction chiFour s = 0 :=
    (chiFour_LFunction_zero_iff_completed hsneg).mp hs
  have hc1s : DirichletCharacter.completedLFunction chiFour (1 - s) = 0 :=
    (chiFour_completedLFunction_zero_one_sub_iff s).mpr hcs
  have h1sneg : -1 < (1 - s).re := by simp; linarith
  have hL1s : DirichletCharacter.LFunction chiFour (1 - s) = 0 :=
    (chiFour_LFunction_zero_iff_completed h1sneg).mpr hc1s
  exact chiFour_LFunction_ne_zero_of_one_le_re (s := 1 - s) (by simp; linarith) hL1s

def chiFourNontrivialZeroSet : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1 ∧ DirichletCharacter.LFunction chiFour s = 0}

lemma chiFourNontrivialZeroSet_subset : chiFourNontrivialZeroSet ⊆ chiFourZeroSet := by
  rintro s ⟨_hs0, _hs1, hsz⟩
  exact hsz

lemma chiFour_completed_divisor_eq_zeroMultiplicity
    {U : Set ℂ} {s : ℂ} (hs : s ∈ chiFourNontrivialZeroSet) (hU : s ∈ U) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction chiFour) U s =
      (chiFourZeroMultiplicity s : ℤ) := by
  have hglobal :
      AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction chiFour) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2
      (DirichletCharacter.differentiable_completedLFunction chiFour_ne_one)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (hglobal.mono (Set.subset_univ U)) hU]
  rw [← Nat.cast_analyticOrderNatAt
    (chiFour_completedLFunction_analyticOrderAt_ne_top s)]
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  exact_mod_cast (chiFourZeroMultiplicity_eq_completed (by linarith [hs.1])).symm

lemma chiFourNontrivialZeroSet_conj {s : ℂ} (hs : s ∈ chiFourNontrivialZeroSet) :
    (starRingEnd ℂ) s ∈ chiFourNontrivialZeroSet := by
  rcases hs with ⟨hs0, hs1, hsz⟩
  refine ⟨by simpa using hs0, by simpa using hs1, ?_⟩
  rw [chiFour_LFunction_conj, hsz, map_zero]

lemma chiFourNontrivialZeroSet_one_sub {s : ℂ} (hs : s ∈ chiFourNontrivialZeroSet) :
    1 - s ∈ chiFourNontrivialZeroSet := by
  rcases hs with ⟨hs0, hs1, hsz⟩
  refine ⟨by simp; linarith, by simp; linarith, ?_⟩
  exact (chiFour_LFunction_zero_one_sub_iff hs0 hs1).2 hsz

def chiFourNontrivialZeroRectangle (T : ℝ) : Set ℂ :=
  {s | s ∈ chiFourNontrivialZeroSet ∧ |s.im| ≤ T}

lemma chiFourNontrivialZeroRectangle_finite (T : ℝ) :
    (chiFourNontrivialZeroRectangle T).Finite := by
  apply (chiFourZeroSet_inter_compact_finite
    (isCompact_closedBall (0 : ℂ) (1 + T))).subset
  rintro s ⟨⟨hs0, hs1, hsz⟩, hsim⟩
  refine ⟨?_, hsz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ 1 + T := by
      gcongr
      rw [abs_of_nonneg hs0.le]
      exact hs1.le

noncomputable def chiFourNontrivialZerosInRectangle (T : ℝ) : Finset ℂ :=
  (chiFourNontrivialZeroRectangle_finite T).toFinset

lemma mem_chiFourNontrivialZerosInRectangle {T : ℝ} {s : ℂ} :
    s ∈ chiFourNontrivialZerosInRectangle T ↔
      s ∈ chiFourNontrivialZeroSet ∧ |s.im| ≤ T := by
  simp [chiFourNontrivialZerosInRectangle, chiFourNontrivialZeroRectangle]

noncomputable def chiFourNontrivialZeroMultisetInRectangle (T : ℝ) : Multiset ℂ :=
  (chiFourNontrivialZerosInRectangle T).val.bind fun s =>
    Multiset.replicate (chiFourZeroMultiplicity s) s

lemma count_chiFourNontrivialZeroMultisetInRectangle {T : ℝ} {s : ℂ} :
    (chiFourNontrivialZeroMultisetInRectangle T).count s =
      if s ∈ chiFourNontrivialZerosInRectangle T then chiFourZeroMultiplicity s else 0 := by
  classical
  simp [chiFourNontrivialZeroMultisetInRectangle, Multiset.count_bind,
    Multiset.count_replicate]

lemma card_chiFourNontrivialZeroMultisetInRectangle (T : ℝ) :
    (chiFourNontrivialZeroMultisetInRectangle T).card =
      ∑ s ∈ chiFourNontrivialZerosInRectangle T, chiFourZeroMultiplicity s := by
  classical
  simp [chiFourNontrivialZeroMultisetInRectangle, Multiset.card_bind]

lemma exists_grid_point_away_from_finset (F : Finset ℝ) (H : ℝ) :
    ∃ T ∈ Set.Ioo H (H + 1),
      ∀ y ∈ F, (3 * ((F.card : ℝ) + 2))⁻¹ ≤ |y - T| := by
  classical
  let M : ℝ := (F.card : ℝ) + 2
  let delta : ℝ := (3 * M)⁻¹
  let grid : Fin (F.card + 1) → ℝ := fun i =>
    H + ((i.val + 1 : ℕ) : ℝ) / M
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hgrid_mem (i : Fin (F.card + 1)) : grid i ∈ Set.Ioo H (H + 1) := by
    have hi : i.val + 1 < F.card + 2 := by omega
    have hi' : (((i.val + 1 : ℕ) : ℝ)) < M := by
      dsimp [M]
      exact_mod_cast hi
    have hfrac_pos : 0 < (((i.val + 1 : ℕ) : ℝ)) / M := div_pos (by positivity) hM
    have hfrac_lt : (((i.val + 1 : ℕ) : ℝ)) / M < 1 := (div_lt_one hM).2 hi'
    dsimp [grid]
    constructor <;> linarith
  have hgrid_sep {i j : Fin (F.card + 1)} (hij : i ≠ j) :
      1 / M ≤ |grid i - grid j| := by
    have hijv : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    rcases lt_or_gt_of_ne hijv with hijlt | hjilt
    · have hnat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hijlt
      have hreal' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
        exact_mod_cast hnat
      have hreal : (1 : ℝ) ≤ (j.val : ℝ) - (i.val : ℝ) := by
        linarith
      have hdiff : grid j - grid i = ((j.val : ℝ) - (i.val : ℝ)) / M := by
        dsimp [grid]
        push_cast
        ring
      have hdiff_nonneg : 0 ≤ grid j - grid i := by
        rw [hdiff]
        positivity
      calc
        1 / M ≤ ((j.val : ℝ) - (i.val : ℝ)) / M :=
          (div_le_div_iff_of_pos_right hM).2 hreal
        _ = grid j - grid i := hdiff.symm
        _ = |grid j - grid i| := (abs_of_nonneg hdiff_nonneg).symm
        _ = |grid i - grid j| := abs_sub_comm _ _
    · have hnat : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hjilt
      have hreal' : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
        exact_mod_cast hnat
      have hreal : (1 : ℝ) ≤ (i.val : ℝ) - (j.val : ℝ) := by
        linarith
      have hdiff : grid i - grid j = ((i.val : ℝ) - (j.val : ℝ)) / M := by
        dsimp [grid]
        push_cast
        ring
      have hdiff_nonneg : 0 ≤ grid i - grid j := by
        rw [hdiff]
        positivity
      calc
        1 / M ≤ ((i.val : ℝ) - (j.val : ℝ)) / M :=
          (div_le_div_iff_of_pos_right hM).2 hreal
        _ = grid i - grid j := hdiff.symm
        _ = |grid i - grid j| := (abs_of_nonneg hdiff_nonneg).symm
  have hdelta_lt : 2 * delta < 1 / M := by
    calc
      2 * delta = (2 / 3 : ℝ) * (1 / M) := by
        dsimp [delta]
        field_simp [hM.ne']
      _ < 1 * (1 / M) :=
        mul_lt_mul_of_pos_right (by norm_num) (one_div_pos.mpr hM)
      _ = 1 / M := one_mul _
  by_contra! h
  have hbad (i : Fin (F.card + 1)) :
      ∃ y ∈ F, |y - grid i| < delta := by
    simpa [delta, M] using h (grid i) (hgrid_mem i)
  let pick : Fin (F.card + 1) → {y // y ∈ F} := fun i =>
    ⟨Classical.choose (hbad i), (Classical.choose_spec (hbad i)).1⟩
  have hpick_close (i : Fin (F.card + 1)) :
      |(pick i : ℝ) - grid i| < delta :=
    (Classical.choose_spec (hbad i)).2
  have hpick_injective : Function.Injective pick := by
    intro i j hij
    by_contra hij'
    have hsep := hgrid_sep hij'
    have hpick_eq : (pick i : ℝ) = (pick j : ℝ) := congrArg Subtype.val hij
    have hclose : |grid i - grid j| < 2 * delta := by
      calc
        |grid i - grid j| =
            |(grid i - (pick i : ℝ)) + ((pick j : ℝ) - grid j)| := by
              rw [hpick_eq]
              congr 1
              ring
        _ ≤ |grid i - (pick i : ℝ)| + |(pick j : ℝ) - grid j| := abs_add_le _ _
        _ < delta + delta := by
          exact add_lt_add (by simpa [abs_sub_comm] using hpick_close i) (hpick_close j)
        _ = 2 * delta := by ring
    exact (not_lt_of_ge hsep) (hclose.trans hdelta_lt)
  have hcard := Fintype.card_le_of_injective pick hpick_injective
  have : F.card + 1 ≤ F.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  omega

noncomputable def chiFourForbiddenZeroHeights (H : ℝ) : Finset ℝ :=
  (chiFourNontrivialZerosInRectangle (H + 2)).image fun s => |s.im|

lemma exists_chiFour_quantitative_zero_avoiding_height (H : ℝ) (hH : 0 ≤ H) :
    ∃ T ∈ Set.Ioo H (H + 1),
      0 < (3 * ((chiFourNontrivialZerosInRectangle (H + 2)).card : ℝ) + 6)⁻¹ ∧
      ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet →
        (3 * ((chiFourNontrivialZerosInRectangle (H + 2)).card : ℝ) + 6)⁻¹ ≤
            |s.im - T| ∧
          (3 * ((chiFourNontrivialZerosInRectangle (H + 2)).card : ℝ) + 6)⁻¹ ≤
            |s.im + T| := by
  classical
  let Z := chiFourNontrivialZerosInRectangle (H + 2)
  let F := chiFourForbiddenZeroHeights H
  obtain ⟨T, hT, hsep⟩ := exists_grid_point_away_from_finset F H
  have hTnonneg : 0 ≤ T := hH.trans hT.1.le
  have hmargin_pos : 0 < (3 * (Z.card : ℝ) + 6)⁻¹ := by
    positivity
  have hmargin_le_one : (3 * (Z.card : ℝ) + 6)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have hcard : 0 ≤ (Z.card : ℝ) := Nat.cast_nonneg Z.card
    nlinarith
  have hcard : F.card ≤ Z.card := by
    simpa [F, Z, chiFourForbiddenZeroHeights] using
      (Finset.card_image_le :
        ((Z.image fun s : ℂ => |s.im|).card ≤ Z.card))
  have hcard' : (F.card : ℝ) ≤ (Z.card : ℝ) := by
    exact_mod_cast hcard
  have hmargin_le_grid :
      (3 * (Z.card : ℝ) + 6)⁻¹ ≤ (3 * (F.card : ℝ) + 6)⁻¹ := by
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  refine ⟨T, hT, by simpa [Z] using hmargin_pos, ?_⟩
  intro s hs
  have hsep' : (3 * (Z.card : ℝ) + 6)⁻¹ ≤ |(|s.im| - T)| := by
    by_cases hsim : |s.im| ≤ H + 2
    · have hmem : |s.im| ∈ F := by
        apply Finset.mem_image.mpr
        refine ⟨s, ?_, rfl⟩
        exact mem_chiFourNontrivialZerosInRectangle.mpr ⟨hs, hsim⟩
      apply hmargin_le_grid.trans
      rw [show 3 * (F.card : ℝ) + 6 = 3 * ((F.card : ℝ) + 2) by ring]
      exact hsep |s.im| hmem
    · have him : H + 2 < |s.im| := lt_of_not_ge hsim
      have hone : 1 < |s.im| - T := by linarith [hT.2]
      have habs : |s.im| - T ≤ |(|s.im| - T)| := le_abs_self _
      exact hmargin_le_one.trans (hone.le.trans habs)
  change
    (3 * (Z.card : ℝ) + 6)⁻¹ ≤ |s.im - T| ∧
      (3 * (Z.card : ℝ) + 6)⁻¹ ≤ |s.im + T|
  constructor
  · apply hsep'.trans
    simpa [abs_of_nonneg hTnonneg] using abs_abs_sub_abs_le_abs_sub s.im T
  · apply hsep'.trans
    simpa [abs_of_nonneg hTnonneg] using abs_abs_sub_abs_le_abs_sub s.im (-T)

lemma chiFourForbiddenZeroHeights_card_le (H : ℝ) :
    (chiFourForbiddenZeroHeights H).card ≤
      (chiFourNontrivialZerosInRectangle (H + 2)).card := by
  exact Finset.card_image_le

noncomputable def chiFourQuantitativeZeroAvoidingHeight (n : ℕ) : ℝ :=
  Classical.choose
    (exists_chiFour_quantitative_zero_avoiding_height (n : ℝ) (Nat.cast_nonneg n))

noncomputable def chiFourQuantitativeZeroAvoidingMargin (n : ℕ) : ℝ :=
  (3 * ((chiFourNontrivialZerosInRectangle ((n : ℝ) + 2)).card : ℝ) + 6)⁻¹

lemma chiFourQuantitativeZeroAvoidingHeight_mem_Ioo (n : ℕ) :
    chiFourQuantitativeZeroAvoidingHeight n ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
  exact (Classical.choose_spec
    (exists_chiFour_quantitative_zero_avoiding_height
      (n : ℝ) (Nat.cast_nonneg n))).1

lemma chiFourQuantitativeZeroAvoidingMargin_pos (n : ℕ) :
    0 < chiFourQuantitativeZeroAvoidingMargin n := by
  exact (Classical.choose_spec
    (exists_chiFour_quantitative_zero_avoiding_height
      (n : ℝ) (Nat.cast_nonneg n))).2.1

lemma chiFourQuantitativeZeroAvoidingMargin_le (n : ℕ) {s : ℂ}
    (hs : s ∈ chiFourNontrivialZeroSet) :
    chiFourQuantitativeZeroAvoidingMargin n ≤
        |s.im - chiFourQuantitativeZeroAvoidingHeight n| ∧
      chiFourQuantitativeZeroAvoidingMargin n ≤
        |s.im + chiFourQuantitativeZeroAvoidingHeight n| := by
  exact (Classical.choose_spec
    (exists_chiFour_quantitative_zero_avoiding_height
      (n : ℝ) (Nat.cast_nonneg n))).2.2 s hs

lemma tendsto_chiFourQuantitativeZeroAvoidingHeight :
    Filter.Tendsto chiFourQuantitativeZeroAvoidingHeight Filter.atTop Filter.atTop := by
  exact tendsto_atTop_mono
    (fun n => (chiFourQuantitativeZeroAvoidingHeight_mem_Ioo n).1.le)
    (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)

lemma chiFourNontrivialZeroMultisetInRectangle_card_le_jensen
    (H M : ℝ) (hH : 0 ≤ H) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (2 * (H + 2)),
      ‖DirichletCharacter.completedLFunction chiFour z‖ ≤ M) :
    ((chiFourNontrivialZeroMultisetInRectangle H).card : ℝ) ≤
      Real.log
          (M / ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
        Real.log 2 := by
  classical
  let f := DirichletCharacter.completedLFunction chiFour
  let Z := chiFourNontrivialZerosInRectangle H
  let B := Metric.closedBall (2 : ℂ) (H + 2)
  have hdiff : Differentiable ℂ f :=
    DirichletCharacter.differentiable_completedLFunction chiFour_ne_one
  have hglobal : AnalyticOnNhd ℂ f Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hdiff
  have hball : AnalyticOnNhd ℂ f B := hglobal.mono (Set.subset_univ B)
  have hf2 : f (2 : ℂ) ≠ 0 := by
    simpa [f] using chiFour_completedLFunction_ne_zero_two
  have hZball {s : ℂ} (hs : s ∈ Z) : s ∈ B := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have hs' := mem_chiFourNontrivialZerosInRectangle.mp hs
    have hre : s.re - 2 ≤ 0 := by linarith [hs'.1.2]
    calc
      ‖s - 2‖ ≤ |(s - 2).re| + |(s - 2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = 2 - s.re + |s.im| := by simp [abs_of_nonpos hre]
      _ ≤ H + 2 := by linarith [hs'.1.1, hs'.2]
  let multiplicityIndicator : ℂ → ℤ := fun s =>
    if s ∈ Z then chiFourZeroMultiplicity s else 0
  have hindicator_finite : Function.HasFiniteSupport multiplicityIndicator := by
    apply Z.finite_toSet.subset
    intro s hs
    by_contra hsz
    have hsz' : s ∉ Z := by simpa using hsz
    exact hs (by simp [multiplicityIndicator, hsz'])
  have hdivisor_finite :
      Function.HasFiniteSupport (MeromorphicOn.divisor f B) :=
    (MeromorphicOn.divisor f B).finiteSupport (isCompact_closedBall (2 : ℂ) (H + 2))
  have hindicator_le : multiplicityIndicator ≤ MeromorphicOn.divisor f B := by
    intro s
    by_cases hs : s ∈ Z
    · have hdivisor : MeromorphicOn.divisor f B s = (chiFourZeroMultiplicity s : ℤ) := by
        simpa [f] using chiFour_completed_divisor_eq_zeroMultiplicity
          (mem_chiFourNontrivialZerosInRectangle.mp hs).1 (hZball hs)
      simp [multiplicityIndicator, hs, hdivisor]
    · simpa [multiplicityIndicator, hs] using
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hball s)
  have hcard_le_divisor_int :
      ((chiFourNontrivialZeroMultisetInRectangle H).card : ℤ) ≤
        ∑ᶠ s : ℂ, MeromorphicOn.divisor f B s := by
    have hsum := finsum_le_finsum' hindicator_finite hdivisor_finite hindicator_le
    have hindicator_sum :
        ∑ᶠ s : ℂ, multiplicityIndicator s =
          ((chiFourNontrivialZeroMultisetInRectangle H).card : ℤ) := by
      have hsupp : Function.support multiplicityIndicator ⊆ (Z : Set ℂ) := by
        intro s hs
        by_contra hsz
        have hsz' : s ∉ Z := by simpa using hsz
        exact hs (by simp [multiplicityIndicator, hsz'])
      rw [finsum_eq_sum_of_support_subset multiplicityIndicator (s := Z) hsupp]
      rw [card_chiFourNontrivialZeroMultisetInRectangle]
      simp [multiplicityIndicator, Z]
    rwa [hindicator_sum] at hsum
  have hcard_le_divisor :
      ((chiFourNontrivialZeroMultisetInRectangle H).card : ℝ) ≤
        (∑ᶠ s : ℂ, MeromorphicOn.divisor f B s : ℤ) := by
    exact_mod_cast hcard_le_divisor_int
  have hrpos : 0 < H + 2 := by linarith
  have hRpos : 0 < 2 * (H + 2) := by positivity
  have hr_lt_R : |H + 2| < |2 * (H + 2)| := by
    rw [abs_of_pos hrpos, abs_of_pos hRpos]
    linarith
  have hratio : 2 * (H + 2) / (H + 2) = 2 := by
    field_simp [hrpos.ne']
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (f := f) (c := (2 : ℂ)) (r := H + 2) (R := 2 * (H + 2)) (M := M)
    (by simpa [abs_of_pos hrpos] using hrpos)
    hr_lt_R
    hM
    (by simpa [abs_of_pos hRpos, B] using
      hglobal.mono (Set.subset_univ (Metric.closedBall (2 : ℂ) (2 * (H + 2)))))
    hf2
    (by simpa [abs_of_pos hRpos] using hbound)
  have hball_eq : Metric.closedBall (2 : ℂ) |H + 2| = B := by
    simp [B, abs_of_pos hrpos]
  rw [hball_eq] at hjensen
  apply hcard_le_divisor.trans
  simpa [f, hratio] using hjensen

lemma chiFourNontrivialZerosInRectangle_card_le_multiset_card (T : ℝ) :
    (chiFourNontrivialZerosInRectangle T).card ≤
      (chiFourNontrivialZeroMultisetInRectangle T).card := by
  rw [card_chiFourNontrivialZeroMultisetInRectangle]
  calc
    (chiFourNontrivialZerosInRectangle T).card =
        ∑ _s ∈ chiFourNontrivialZerosInRectangle T, 1 := by simp
    _ ≤ ∑ s ∈ chiFourNontrivialZerosInRectangle T, chiFourZeroMultiplicity s := by
      apply Finset.sum_le_sum
      intro s hs
      exact chiFourZeroMultiplicity_pos
        (mem_chiFourNontrivialZerosInRectangle.mp hs).1.2.2

lemma chiFourNontrivialZerosInRectangle_card_le_jensen
    (H M : ℝ) (hH : 0 ≤ H) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (2 * (H + 2)),
      ‖DirichletCharacter.completedLFunction chiFour z‖ ≤ M) :
    ((chiFourNontrivialZerosInRectangle H).card : ℝ) ≤
      Real.log
          (M / ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
        Real.log 2 := by
  have hcard :
      ((chiFourNontrivialZerosInRectangle H).card : ℝ) ≤
        ((chiFourNontrivialZeroMultisetInRectangle H).card : ℝ) := by
    exact_mod_cast chiFourNontrivialZerosInRectangle_card_le_multiset_card H
  exact hcard.trans
    (chiFourNontrivialZeroMultisetInRectangle_card_le_jensen H M hH hM hbound)

lemma exists_chiFour_jensen_zero_avoiding_height
    (H M : ℝ) (hH : 0 ≤ H) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (2 * (H + 4)),
      ‖DirichletCharacter.completedLFunction chiFour z‖ ≤ M) :
    ∃ T ∈ Set.Ioo H (H + 1),
      0 <
        (3 *
            (Real.log
                (M / ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
              Real.log 2) +
          6)⁻¹ ∧
      ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet →
        (3 *
              (Real.log
                  (M / ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
                Real.log 2) +
            6)⁻¹ ≤ |s.im - T| ∧
          (3 *
                (Real.log
                    (M / ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
                  Real.log 2) +
              6)⁻¹ ≤ |s.im + T| := by
  let J :=
    Real.log (M / ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
      Real.log 2
  let Z := chiFourNontrivialZerosInRectangle (H + 2)
  have hcount : (Z.card : ℝ) ≤ J := by
    apply chiFourNontrivialZerosInRectangle_card_le_jensen (H + 2) M (by linarith) hM
    simpa [show H + 2 + 2 = H + 4 by ring] using hbound
  have hJnonneg : 0 ≤ J := (Nat.cast_nonneg Z.card).trans hcount
  have hmargin_pos : 0 < (3 * J + 6)⁻¹ := by positivity
  have hmargin_le : (3 * J + 6)⁻¹ ≤ (3 * (Z.card : ℝ) + 6)⁻¹ := by
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  obtain ⟨T, hT, _hmargin, hsep⟩ :=
    exists_chiFour_quantitative_zero_avoiding_height H hH
  refine ⟨T, hT, by simpa [J] using hmargin_pos, ?_⟩
  intro s hs
  have hsep' := hsep s hs
  change
    (3 * J + 6)⁻¹ ≤ |s.im - T| ∧
      (3 * J + 6)⁻¹ ≤ |s.im + T|
  exact ⟨hmargin_le.trans hsep'.1, hmargin_le.trans hsep'.2⟩

lemma exists_chiFour_zero_free_height (H : ℝ) (hH : 0 ≤ H) :
    ∃ T ∈ Set.Ioo H (H + 1),
      ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet → s.im ≠ T := by
  classical
  let heights := (chiFourNontrivialZerosInRectangle (H + 1)).image Complex.im
  obtain ⟨T, hT, hTnot⟩ :=
    (Set.Ioo_infinite (by linarith : H < H + 1)).exists_notMem_finset heights
  refine ⟨T, hT, ?_⟩
  intro s hs hsim
  apply hTnot
  apply Finset.mem_image.mpr
  refine ⟨s, ?_, hsim⟩
  rw [mem_chiFourNontrivialZerosInRectangle]
  refine ⟨hs, ?_⟩
  rw [hsim, abs_of_pos (hH.trans_lt hT.1)]
  exact hT.2.le

lemma exists_chiFour_zero_avoiding_margin (T : ℝ) (hT : 0 ≤ T)
    (havoid : ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet → s.im ≠ T) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet → delta ≤ |s.im - T| := by
  classical
  let distances : Finset ℝ := insert 1
    ((chiFourNontrivialZerosInRectangle (T + 1)).image fun s => |s.im - T|)
  have hdistances : distances.Nonempty := by
    refine ⟨1, ?_⟩
    simp [distances]
  let delta := distances.min' hdistances
  have hdelta_pos : 0 < delta := by
    have hall : ∀ y ∈ distances, 0 < y := by
      intro y hy
      simp only [distances, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · norm_num
      · rcases Finset.mem_image.mp hy with ⟨s, hs, rfl⟩
        rw [abs_pos]
        apply sub_ne_zero.mpr
        exact havoid s (mem_chiFourNontrivialZerosInRectangle.mp hs).1
    exact hall delta (distances.min'_mem hdistances)
  refine ⟨delta, hdelta_pos, ?_⟩
  intro s hs
  by_cases hsim : |s.im| ≤ T + 1
  · apply distances.min'_le
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨s, mem_chiFourNontrivialZerosInRectangle.mpr ⟨hs, hsim⟩, rfl⟩
  · have hdelta_one : delta ≤ 1 := by
      apply distances.min'_le
      simp [distances]
    have him : T + 1 < |s.im| := lt_of_not_ge hsim
    have hreverse : |s.im| - |T| ≤ |s.im - T| := abs_sub_abs_le_abs_sub _ _
    rw [abs_of_nonneg hT] at hreverse
    linarith

noncomputable def chiFourZeroAvoidingHeight (n : ℕ) : ℝ :=
  Classical.choose (exists_chiFour_zero_free_height (n : ℝ) (Nat.cast_nonneg n))

lemma chiFourZeroAvoidingHeight_mem_Ioo (n : ℕ) :
    chiFourZeroAvoidingHeight n ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) :=
  (Classical.choose_spec
    (exists_chiFour_zero_free_height (n : ℝ) (Nat.cast_nonneg n))).1

lemma chiFourZeroAvoidingHeight_avoids (n : ℕ) :
    ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet → s.im ≠ chiFourZeroAvoidingHeight n :=
  (Classical.choose_spec
    (exists_chiFour_zero_free_height (n : ℝ) (Nat.cast_nonneg n))).2

private lemma exists_chiFourZeroAvoidingMargin (n : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℂ, s ∈ chiFourNontrivialZeroSet →
        delta ≤ |s.im - chiFourZeroAvoidingHeight n| := by
  apply exists_chiFour_zero_avoiding_margin
  · exact (Nat.cast_nonneg n).trans (chiFourZeroAvoidingHeight_mem_Ioo n).1.le
  · exact chiFourZeroAvoidingHeight_avoids n

noncomputable def chiFourZeroAvoidingMargin (n : ℕ) : ℝ :=
  Classical.choose (exists_chiFourZeroAvoidingMargin n)

lemma chiFourZeroAvoidingMargin_pos (n : ℕ) : 0 < chiFourZeroAvoidingMargin n :=
  (Classical.choose_spec (exists_chiFourZeroAvoidingMargin n)).1

lemma chiFourZeroAvoidingMargin_le (n : ℕ) {s : ℂ}
    (hs : s ∈ chiFourNontrivialZeroSet) :
    chiFourZeroAvoidingMargin n ≤ |s.im - chiFourZeroAvoidingHeight n| :=
  (Classical.choose_spec (exists_chiFourZeroAvoidingMargin n)).2 s hs

lemma tendsto_chiFourZeroAvoidingHeight :
    Filter.Tendsto chiFourZeroAvoidingHeight Filter.atTop Filter.atTop := by
  exact tendsto_atTop_mono
    (fun n => (chiFourZeroAvoidingHeight_mem_Ioo n).1.le)
    (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)

def chiFourTrivialZero (n : ℕ) : ℂ :=
  -(2 * (n : ℂ)) - 1

lemma chiFourTrivialZero_injective : Function.Injective chiFourTrivialZero := by
  intro m n h
  have hr := congrArg Complex.re h
  simp [chiFourTrivialZero] at hr
  exact hr

lemma chiFour_LFunction_trivialZero (n : ℕ) :
    DirichletCharacter.LFunction chiFour (chiFourTrivialZero n) = 0 := by
  exact chiFour_odd.LFunction_neg_two_mul_nat_sub_one n

lemma chiFour_trivialZeros_infinite :
    (Set.range chiFourTrivialZero).Infinite :=
  Set.infinite_range_of_injective chiFourTrivialZero_injective

lemma chiFourZeroSet_infinite : chiFourZeroSet.Infinite := by
  apply chiFour_trivialZeros_infinite.mono
  rintro s ⟨n, rfl⟩
  exact chiFour_LFunction_trivialZero n

lemma chiFourNegLogDerivative_orderAt_trivialZero (n : ℕ) :
    meromorphicOrderAt chiFourNegLogDerivative (chiFourTrivialZero n) = -1 :=
  chiFourNegLogDerivative_orderAt_zero (chiFour_LFunction_trivialZero n)

lemma twistedVonMangoldtCoeff_eq_prime_add_error (n : ℕ) :
    twistedVonMangoldtCoeff n = twistedPrimeLogCoeff n + higherPrimePowerCoeff n := by
  by_cases hn : n.Prime
  · simp [twistedPrimeLogCoeff, higherPrimePowerCoeff, twistedVonMangoldtCoeff, hn,
      ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [twistedPrimeLogCoeff, higherPrimePowerCoeff, hn]

lemma twistedChebyshevSum_eq_prime_add_error (n : ℕ) :
    twistedChebyshevSum n = twistedPrimeLogSum n + higherPrimePowerError n := by
  classical
  rw [twistedChebyshevSum, twistedPrimeLogSum, higherPrimePowerError,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _hk => twistedVonMangoldtCoeff_eq_prime_add_error k

lemma norm_higherPrimePowerError_le_psi_sub_theta (n : ℕ) :
    ‖higherPrimePowerError n‖ ≤ Chebyshev.psi n - Chebyshev.theta n := by
  classical
  calc
    ‖higherPrimePowerError n‖ ≤
        ∑ k ∈ Finset.range (n + 1), ‖higherPrimePowerCoeff k‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      exact Finset.sum_le_sum fun k _hk => norm_higherPrimePowerCoeff_le k
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      simp only [Nat.floor_natCast, Finset.sum_filter]
      rw [show Finset.range (n + 1) = Finset.Icc 0 n by ext k; simp]
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
      simp

lemma norm_higherPrimePowerError_le (n : ℕ) (hn : 1 ≤ n) :
    ‖higherPrimePowerError n‖ ≤ 2 * √(n : ℝ) * Real.log n :=
  (norm_higherPrimePowerError_le_psi_sub_theta n).trans
    (Chebyshev.psi_sub_theta_le (mod_cast hn))

lemma exists_norm_higherPrimePowerError_le_sqrt :
    ∃ C : ℝ, ∀ n : ℕ, ‖higherPrimePowerError n‖ ≤ C * √(n : ℝ) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  exact ⟨C, fun n => (norm_higherPrimePowerError_le_psi_sub_theta n).trans (hC n)⟩

lemma twistedPrimeLogCoeff_eq_log_mul (n : ℕ) :
    twistedPrimeLogCoeff n = (Real.log n : ℂ) * primeCharacterCoeff n := by
  by_cases hn : n.Prime <;>
    simp [twistedPrimeLogCoeff, primeCharacterCoeff, hn, mul_comm]

lemma twistedPrimeLogSum_partial_summation (n : ℕ) :
    twistedPrimeLogSum n =
      (Real.log n : ℂ) * complexCharacterPrimeSum n -
        ∑ i ∈ Finset.range n,
          ((Real.log (i + 1) : ℂ) - Real.log i) * complexCharacterPrimeSum i := by
  classical
  rw [twistedPrimeLogSum]
  simp_rw [twistedPrimeLogCoeff_eq_log_mul, ← smul_eq_mul]
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel, complexCharacterPrimeSum, smul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma invLog_mul_twistedPrimeLogCoeff (n : ℕ) :
    (Real.log n : ℂ)⁻¹ * twistedPrimeLogCoeff n = primeCharacterCoeff n := by
  by_cases hn : n.Prime
  · have hlog : (Real.log n : ℂ) ≠ 0 := by
      have hlogR : Real.log (n : ℝ) ≠ 0 := by
        exact (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
      exact_mod_cast hlogR
    simp only [twistedPrimeLogCoeff, primeCharacterCoeff, hn, if_true]
    field_simp
  · simp [twistedPrimeLogCoeff, primeCharacterCoeff, hn]

lemma complexCharacterPrimeSum_partial_summation (n : ℕ) :
    complexCharacterPrimeSum n =
      (Real.log n : ℂ)⁻¹ * twistedPrimeLogSum n -
        ∑ i ∈ Finset.range n,
          ((Real.log (i + 1) : ℂ)⁻¹ - (Real.log i : ℂ)⁻¹) * twistedPrimeLogSum i := by
  classical
  rw [complexCharacterPrimeSum]
  conv_lhs =>
    enter [2, i]
    rw [← invLog_mul_twistedPrimeLogCoeff]
  simp_rw [← smul_eq_mul]
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel, twistedPrimeLogSum, smul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma realTwistedPrimeLogSum_partial_summation (n : ℕ) :
    realTwistedPrimeLogSum n =
      Real.log n * realCharacterPrimeSum n -
        ∑ i ∈ Finset.range n,
          (Real.log (i + 1) - Real.log i) * realCharacterPrimeSum i := by
  apply Complex.ofReal_injective
  rw [← twistedPrimeLogSum_eq_real, twistedPrimeLogSum_partial_summation]
  simp_rw [complexCharacterPrimeSum_eq_real]
  push_cast
  rfl

lemma realCharacterPrimeSum_partial_summation (n : ℕ) :
    realCharacterPrimeSum n =
      (Real.log n)⁻¹ * realTwistedPrimeLogSum n -
        ∑ i ∈ Finset.range n,
          ((Real.log (i + 1))⁻¹ - (Real.log i)⁻¹) * realTwistedPrimeLogSum i := by
  apply Complex.ofReal_injective
  rw [← complexCharacterPrimeSum_eq_real, complexCharacterPrimeSum_partial_summation]
  simp_rw [twistedPrimeLogSum_eq_real]
  push_cast
  rfl

lemma realCharacterPrimeSum_partial_summation_positive (n : ℕ) :
    realCharacterPrimeSum n =
      (Real.log n)⁻¹ * realTwistedPrimeLogSum n +
        ∑ i ∈ Finset.range n,
          ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) * realTwistedPrimeLogSum i := by
  rw [realCharacterPrimeSum_partial_summation]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

lemma inv_log_succ_le_inv_log {i : ℕ} (hi : 2 ≤ i) :
    (Real.log (i + 1))⁻¹ ≤ (Real.log i)⁻¹ := by
  apply inv_anti₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < i)))
  exact Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
    (by exact_mod_cast (by omega : i ≤ i + 1))

lemma inv_log_sub_inv_log_succ_nonneg {i : ℕ} (hi : 2 ≤ i) :
    0 ≤ (Real.log i)⁻¹ - (Real.log (i + 1))⁻¹ :=
  sub_nonneg.mpr (inv_log_succ_le_inv_log hi)

lemma realTwistedPrimeLogSum_zero : realTwistedPrimeLogSum 0 = 0 := by
  norm_num [realTwistedPrimeLogSum, realTwistedPrimeLogCoeff]

lemma realTwistedPrimeLogSum_one : realTwistedPrimeLogSum 1 = 0 := by
  norm_num [realTwistedPrimeLogSum, realTwistedPrimeLogCoeff, Finset.sum_range_succ,
    Nat.prime_def]

noncomputable def realCharacterPrimeHistory (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 2 n,
    ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) * realTwistedPrimeLogSum i

noncomputable def realCharacterPrimeHistoryBound (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 2 n,
    ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) * |realTwistedPrimeLogSum i|

lemma realCharacterPrimeSum_eq_lead_add_history (n : ℕ) (hn : 2 ≤ n) :
    realCharacterPrimeSum n =
      (Real.log n)⁻¹ * realTwistedPrimeLogSum n + realCharacterPrimeHistory n := by
  rw [realCharacterPrimeSum_partial_summation_positive, realCharacterPrimeHistory,
    Finset.sum_Ico_eq_sub _ hn]
  simp [realTwistedPrimeLogSum_zero, realTwistedPrimeLogSum_one,
    Finset.sum_range_succ]

lemma sum_inv_log_sub_inv_log_succ_Ico (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ico 2 n, ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) =
      (Real.log 2)⁻¹ - (Real.log n)⁻¹ := by
  have htel (m : ℕ) :
      ∑ i ∈ Finset.range m, ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) =
        (Real.log 0)⁻¹ - (Real.log m)⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      (Finset.sum_range_sub' (fun i : ℕ => (Real.log i)⁻¹) m)
  rw [Finset.sum_Ico_eq_sub _ hn, htel n, htel 2]
  ring_nf

lemma abs_realCharacterPrimeHistory_le (n : ℕ) :
    |realCharacterPrimeHistory n| ≤ realCharacterPrimeHistoryBound n := by
  rw [realCharacterPrimeHistory, realCharacterPrimeHistoryBound]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  rw [abs_mul, abs_of_nonneg]
  exact inv_log_sub_inv_log_succ_nonneg (Finset.mem_Ico.mp hi).1

lemma realCharacterPrimeHistoryBound_le_of_prefix_bound {n : ℕ} (hn : 2 ≤ n)
    {M : ℝ}
    (hprefix : ∀ i : ℕ, 2 ≤ i → i < n → |realTwistedPrimeLogSum i| ≤ M) :
    realCharacterPrimeHistoryBound n ≤
      ((Real.log 2)⁻¹ - (Real.log n)⁻¹) * M := by
  rw [realCharacterPrimeHistoryBound, ← sum_inv_log_sub_inv_log_succ_Ico n hn,
    Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (hprefix i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2)
    (inv_log_sub_inv_log_succ_nonneg (Finset.mem_Ico.mp hi).1)

lemma realCharacterPrimeSum_pos_of_weighted_gt_history {n : ℕ} (hn : 2 ≤ n)
    (hdom : realCharacterPrimeHistoryBound n <
      (Real.log n)⁻¹ * realTwistedPrimeLogSum n) :
    0 < realCharacterPrimeSum n := by
  rw [realCharacterPrimeSum_eq_lead_add_history n hn]
  have habs := abs_realCharacterPrimeHistory_le n
  have hlower : -realCharacterPrimeHistoryBound n ≤ realCharacterPrimeHistory n :=
    (neg_le_neg habs).trans (neg_abs_le _)
  linarith

lemma realCharacterPrimeSum_neg_of_weighted_lt_neg_history {n : ℕ} (hn : 2 ≤ n)
    (hdom : realCharacterPrimeHistoryBound n <
      -((Real.log n)⁻¹ * realTwistedPrimeLogSum n)) :
    realCharacterPrimeSum n < 0 := by
  rw [realCharacterPrimeSum_eq_lead_add_history n hn]
  have habs := abs_realCharacterPrimeHistory_le n
  have hupper : realCharacterPrimeHistory n ≤ realCharacterPrimeHistoryBound n :=
    (le_abs_self _).trans habs
  linarith

lemma realCharacterPrimeSum_pos_of_weighted_dominates_prefix {n : ℕ} (hn : 2 ≤ n)
    {M : ℝ}
    (hprefix : ∀ i : ℕ, 2 ≤ i → i < n → |realTwistedPrimeLogSum i| ≤ M)
    (hdom : ((Real.log 2)⁻¹ - (Real.log n)⁻¹) * M <
      (Real.log n)⁻¹ * realTwistedPrimeLogSum n) :
    0 < realCharacterPrimeSum n := by
  apply realCharacterPrimeSum_pos_of_weighted_gt_history hn
  exact (realCharacterPrimeHistoryBound_le_of_prefix_bound hn hprefix).trans_lt hdom

lemma realCharacterPrimeSum_neg_of_weighted_dominates_prefix {n : ℕ} (hn : 2 ≤ n)
    {M : ℝ}
    (hprefix : ∀ i : ℕ, 2 ≤ i → i < n → |realTwistedPrimeLogSum i| ≤ M)
    (hdom : ((Real.log 2)⁻¹ - (Real.log n)⁻¹) * M <
      -((Real.log n)⁻¹ * realTwistedPrimeLogSum n)) :
    realCharacterPrimeSum n < 0 := by
  apply realCharacterPrimeSum_neg_of_weighted_lt_neg_history hn
  exact (realCharacterPrimeHistoryBound_le_of_prefix_bound hn hprefix).trans_lt hdom

lemma characterPrimeSum_pos_of_weighted_gt_history {n : ℕ} (hn : 2 ≤ n)
    (hdom : realCharacterPrimeHistoryBound n <
      (Real.log n)⁻¹ * realTwistedPrimeLogSum n) :
    0 < characterPrimeSum n := by
  have h := realCharacterPrimeSum_pos_of_weighted_gt_history hn hdom
  change (0 : ℝ) < (characterPrimeSum n : ℝ) at h
  exact_mod_cast h

lemma characterPrimeSum_neg_of_weighted_lt_neg_history {n : ℕ} (hn : 2 ≤ n)
    (hdom : realCharacterPrimeHistoryBound n <
      -((Real.log n)⁻¹ * realTwistedPrimeLogSum n)) :
    characterPrimeSum n < 0 := by
  have h := realCharacterPrimeSum_neg_of_weighted_lt_neg_history hn hdom
  change (characterPrimeSum n : ℝ) < 0 at h
  exact_mod_cast h

lemma characterPrimeSum_oscillates_of_weighted_history_excursions
    (h :
      (∀ N : ℕ, ∃ n > N, 2 ≤ n ∧
        realCharacterPrimeHistoryBound n <
          -((Real.log n)⁻¹ * realTwistedPrimeLogSum n)) ∧
      (∀ N : ℕ, ∃ n > N, 2 ≤ n ∧
        realCharacterPrimeHistoryBound n <
          (Real.log n)⁻¹ * realTwistedPrimeLogSum n)) :
    (∀ N : ℕ, ∃ n > N, characterPrimeSum n < 0) ∧
      (∀ N : ℕ, ∃ n > N, 0 < characterPrimeSum n) := by
  constructor
  · intro N
    obtain ⟨n, hnN, hn, hdom⟩ := h.1 N
    exact ⟨n, hnN, characterPrimeSum_neg_of_weighted_lt_neg_history hn hdom⟩
  · intro N
    obtain ⟨n, hnN, hn, hdom⟩ := h.2 N
    exact ⟨n, hnN, characterPrimeSum_pos_of_weighted_gt_history hn hdom⟩

lemma realCharacterPrimeSum_pos_of_weighted_nonneg {n : ℕ} (hn : 2 ≤ n)
    (hall : ∀ i : ℕ, 2 ≤ i → i < n → 0 ≤ realTwistedPrimeLogSum i)
    (hpos : 0 < realTwistedPrimeLogSum n) :
    0 < realCharacterPrimeSum n := by
  rw [realCharacterPrimeSum_partial_summation_positive]
  have hlead : 0 < (Real.log n)⁻¹ * realTwistedPrimeLogSum n :=
    mul_pos (inv_pos.mpr (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))) hpos
  have hsum : 0 ≤ ∑ i ∈ Finset.range n,
      ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) * realTwistedPrimeLogSum i := by
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases hi2 : 2 ≤ i
    · exact mul_nonneg (inv_log_sub_inv_log_succ_nonneg hi2) (hall i hi2 hi)
    · interval_cases i <;>
        simp [realTwistedPrimeLogSum_zero, realTwistedPrimeLogSum_one]
  linarith

lemma realCharacterPrimeSum_neg_of_weighted_nonpos {n : ℕ} (hn : 2 ≤ n)
    (hall : ∀ i : ℕ, 2 ≤ i → i < n → realTwistedPrimeLogSum i ≤ 0)
    (hneg : realTwistedPrimeLogSum n < 0) :
    realCharacterPrimeSum n < 0 := by
  rw [realCharacterPrimeSum_partial_summation_positive]
  have hlead : (Real.log n)⁻¹ * realTwistedPrimeLogSum n < 0 :=
    mul_neg_of_pos_of_neg
      (inv_pos.mpr (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))) hneg
  have hsum : ∑ i ∈ Finset.range n,
      ((Real.log i)⁻¹ - (Real.log (i + 1))⁻¹) * realTwistedPrimeLogSum i ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases hi2 : 2 ≤ i
    · exact mul_nonpos_of_nonneg_of_nonpos (inv_log_sub_inv_log_succ_nonneg hi2)
        (hall i hi2 hi)
    · interval_cases i <;>
        simp [realTwistedPrimeLogSum_zero, realTwistedPrimeLogSum_one]
  linarith

lemma race_oscillates_of_characterPrimeSum_oscillates
    (h : (∀ N : ℕ, ∃ n > N, characterPrimeSum n < 0) ∧
      (∀ N : ℕ, ∃ n > N, 0 < characterPrimeSum n)) :
    (∀ N : ℕ, ∃ n > N, 0 < primeRace n) ∧
      (∀ N : ℕ, ∃ n > N, primeRace n < 0) := by
  constructor
  · intro N
    obtain ⟨n, hN, hn⟩ := h.1 N
    refine ⟨n, hN, ?_⟩
    rw [primeRace_eq_neg_characterPrimeSum]
    omega
  · intro N
    obtain ⟨n, hN, hn⟩ := h.2 N
    refine ⟨n, hN, ?_⟩
    rw [primeRace_eq_neg_characterPrimeSum]
    omega

lemma chebyshev_sign_change_of_characterPrimeSum_oscillation
    (h : (∀ N : ℕ, ∃ n > N, characterPrimeSum n < 0) ∧
      (∀ N : ℕ, ∃ n > N, 0 < characterPrimeSum n)) :
    chebyshevLead.Infinite ∧
      {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}.Infinite := by
  obtain ⟨hpos, hneg⟩ := race_oscillates_of_characterPrimeSum_oscillates h
  exact chebyshev_sign_change_of_race_oscillation hpos hneg

end Submission.Analytic
