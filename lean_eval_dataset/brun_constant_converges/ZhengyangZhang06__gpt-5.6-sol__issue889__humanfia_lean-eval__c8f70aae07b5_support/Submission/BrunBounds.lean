import ChallengeDeps
import Submission.BrunSieve
import Submission.Estimates

open scoped ArithmeticFunction.omega BigOperators
open ArithmeticFunction Finset Nat Real

noncomputable section

namespace Submission.BrunSieve

def twinNu : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p =>
    if p = 2 then (1 : ℝ) / 2 else 2 / (p : ℝ)

theorem twinNu_prime {p : ℕ} (hp : p.Prime) :
    twinNu p = if p = 2 then (1 : ℝ) / 2 else 2 / (p : ℝ) := by
  rw [twinNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  have hpf : p.primeFactors = {p} := by
    ext q
    rw [Nat.mem_primeFactors, mem_singleton]
    exact ⟨fun h => (Nat.prime_dvd_prime_iff_eq h.1 hp).mp h.2.1,
      fun h => by subst q; exact ⟨hp, dvd_rfl, hp.ne_zero⟩⟩
  rw [hpf, prod_singleton]

theorem twinNu_squarefree {d : ℕ} (hd : Squarefree d) :
    twinNu d =
      (Nat.card {x : ZMod d // Submission.BrunSieve.IsTwinRoot d x} : ℝ) / (d : ℝ) := by
  rw [twinNu, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Submission.BrunSieve.card_twinRoots_squarefree hd]
  push_cast
  have hdcast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    calc
      (d : ℝ) = ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) :=
        congrArg Nat.cast (Nat.prod_primeFactors_of_squarefree hd).symm
      _ = ∏ p ∈ d.primeFactors, (p : ℝ) := by push_cast; rfl
  rw [hdcast, ← Finset.prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    simp
  · simp [hp2]

theorem primorial_squarefree (M : ℕ) : Squarefree (primorial M) := by
  rw [primorial_eq_prod_primesLE]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).2 hpq
  · intro p hp
    exact (prime_of_mem_primesLE hp).squarefree

theorem twinPolynomial_strictMono : StrictMono Submission.BrunSieve.twinPolynomial := by
  intro a b hab
  simp only [Submission.BrunSieve.twinPolynomial]
  nlinarith

def blockBase : ℕ := 2 ^ 20

def sieveWidth (q : ℕ) : ℕ := 2 ^ q

def sieveBound (q : ℕ) : ℕ := blockBase ^ (q + 1)

def twinSieve (q : ℕ) : SelbergSieve where
  support := (range (sieveBound q)).image Submission.BrunSieve.twinPolynomial
  prodPrimes := primorial ((sieveWidth q) ^ 2)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := by intro; norm_num
  totalMass := sieveBound q
  nu := twinNu
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := by
    intro p hp hpd
    rw [twinNu_prime hp]
    split_ifs with hp2
    · norm_num
    · exact div_pos (by norm_num) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp hpd
    rw [twinNu_prime hp]
    split_ifs with hp2
    · norm_num
    · apply (div_lt_one (by exact_mod_cast hp.pos)).2
      exact_mod_cast lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  level := (sieveWidth q : ℝ) ^ 4
  one_le_level := by
    apply one_le_pow₀
    exact_mod_cast Nat.one_le_pow q 2 (by norm_num : 0 < 2)

def residueCount (X d : ℕ) (r : ZMod d) : ℕ :=
  ((range X).filter fun n : ℕ => (n : ZMod d) = r).card

theorem residueCount_le (X d : ℕ) [NeZero d] (r : ZMod d) :
    residueCount X d r ≤ X / d + 1 := by
  classical
  rw [residueCount, ← card_range (X / d + 1)]
  apply Finset.card_le_card_of_injOn (fun n => n / d)
  · intro n hn
    rw [Finset.mem_coe, mem_range]
    have hn' : n ∈ (range X).filter fun n : ℕ => (n : ZMod d) = r := Finset.mem_coe.mp hn
    exact Nat.lt_succ_of_le <| Nat.div_le_div_right <|
      le_of_lt (mem_range.mp (mem_filter.mp hn').1)
  · intro a ha b hb hab
    apply (Nat.modEq_iff_eq_of_div_eq hab).mp
    apply (ZMod.natCast_eq_natCast_iff a b d).mp
    exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm

theorem le_residueCount (X d : ℕ) [NeZero d] (r : ZMod d) :
    X / d ≤ residueCount X d r := by
  classical
  let f : ℕ → ℕ := fun k => k * d + r.val
  rw [residueCount, ← card_range (X / d)]
  apply Finset.card_le_card_of_injOn f
  · intro k hk
    apply mem_filter.mpr
    constructor
    · rw [mem_range]
      have hk1 : k + 1 ≤ X / d := Nat.succ_le_iff.mpr (mem_range.mp hk)
      calc
        k * d + r.val < k * d + d := Nat.add_lt_add_left r.val_lt _
        _ = (k + 1) * d := by ring
        _ ≤ (X / d) * d := Nat.mul_le_mul_right d hk1
        _ ≤ X := Nat.div_mul_le_self X d
    · change ((k * d + r.val : ℕ) : ZMod d) = r
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
        ZMod.natCast_zmod_val]
  · intro a ha b hb hab
    apply Nat.mul_right_cancel (NeZero.pos d)
    exact Nat.add_right_cancel hab

theorem abs_residueCount_sub (X d : ℕ) [NeZero d] (r : ZMod d) :
    |(residueCount X d r : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  have hlowCount := le_residueCount X d r
  have hhighCount := residueCount_le X d r
  have hlowCount' : ((X / d : ℕ) : ℝ) ≤ (residueCount X d r : ℝ) := by
    exact_mod_cast hlowCount
  have hhighCount' : (residueCount X d r : ℝ) ≤ ((X / d : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhighCount
  have hlowDiv : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hhighDiv : (X : ℝ) / (d : ℝ) < (X / d : ℕ) + 1 := by
    have hmod : X % d < d := Nat.mod_lt X (NeZero.pos d)
    have hmod' : ((X % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
    rw [show (X : ℝ) = (d : ℝ) * (X / d : ℕ) + (X % d : ℕ) by
      exact_mod_cast (Nat.div_add_mod X d).symm]
    field_simp
    nlinarith [hmod']
  rw [abs_le]
  constructor
  · linarith
  · linarith

def polynomialCount (X d : ℕ) : ℕ :=
  ((range X).filter fun n => d ∣ Submission.BrunSieve.twinPolynomial n).card

theorem dvd_twinPolynomial_iff_root (d n : ℕ) :
    d ∣ Submission.BrunSieve.twinPolynomial n ↔
      Submission.BrunSieve.IsTwinRoot d (n : ZMod d) := by
  rw [Submission.BrunSieve.IsTwinRoot, Submission.BrunSieve.twinPolynomial]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
    (ZMod.natCast_eq_zero_iff (n * (n + 2)) d).symm

theorem multSum_twinSieve (q d : ℕ) :
    (twinSieve q).toBoundingSieve.multSum d = polynomialCount (sieveBound q) d := by
  classical
  rw [BoundingSieve.multSum]
  simp only [twinSieve, polynomialCount]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  have hfilter :
      ((range (sieveBound q)).image Submission.BrunSieve.twinPolynomial).filter (d ∣ ·) =
        ((range (sieveBound q)).filter fun n =>
          d ∣ Submission.BrunSieve.twinPolynomial n).image
            Submission.BrunSieve.twinPolynomial := by
    ext n
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hd⟩
      exact ⟨a, ⟨ha, hd⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hd⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hd⟩
  rw [hfilter, card_image_iff.mpr twinPolynomial_strictMono.injective.injOn]

noncomputable def twinRoots (d : ℕ) [NeZero d] : Finset (ZMod d) := by
  classical
  exact Finset.univ.filter fun r => Submission.BrunSieve.IsTwinRoot d r

theorem mem_twinRoots (d : ℕ) [NeZero d] (r : ZMod d) :
    r ∈ twinRoots d ↔ Submission.BrunSieve.IsTwinRoot d r := by
  classical
  simp [twinRoots]

theorem polynomialCount_eq_sum_residueCount (X d : ℕ) [NeZero d] :
    polynomialCount X d =
      ∑ r ∈ twinRoots d, residueCount X d r := by
  classical
  rw [polynomialCount]
  symm
  simpa only [residueCount, mem_twinRoots, dvd_twinPolynomial_iff_root] using
    Finset.sum_card_fiberwise_eq_card_filter (range X)
      (twinRoots d)
      (fun n : ℕ => (n : ZMod d))

theorem card_twinRoot_filter (d : ℕ) [NeZero d] :
    #(twinRoots d) =
      Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} := by
  classical
  calc
    #(twinRoots d) = Nat.card ↥(twinRoots d) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} :=
      Nat.card_congr <| (Equiv.refl (ZMod d)).subtypeEquiv fun r => mem_twinRoots d r

theorem abs_polynomialCount_sub (X d : ℕ) [NeZero d] :
    |(polynomialCount X d : ℝ) -
        (Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} : ℝ) *
          ((X : ℝ) / (d : ℝ))| ≤
      Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} := by
  classical
  let roots := twinRoots d
  rw [polynomialCount_eq_sum_residueCount]
  have hcard : #roots = Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} :=
    card_twinRoot_filter d
  calc
    |(↑(∑ r ∈ roots, residueCount X d r) : ℝ) -
        (Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} : ℝ) *
          ((X : ℝ) / (d : ℝ))| =
        |∑ r ∈ roots, ((residueCount X d r : ℝ) - (X : ℝ) / (d : ℝ))| := by
      push_cast
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
    _ ≤ ∑ r ∈ roots, |(residueCount X d r : ℝ) - (X : ℝ) / (d : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ roots, (1 : ℝ) := by
      gcongr with r hr
      exact abs_residueCount_sub X d r
    _ = Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} := by
      simp [hcard]

theorem abs_rem_twinSieve_le (q : ℕ) {d : ℕ}
    (hdP : d ∣ (twinSieve q).prodPrimes) :
    |(twinSieve q).toBoundingSieve.rem d| ≤
      Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} := by
  letI : NeZero d := ⟨ne_zero_of_dvd_ne_zero
    (twinSieve q).toBoundingSieve.prodPrimes_ne_zero hdP⟩
  rw [BoundingSieve.rem, multSum_twinSieve]
  have hdSq := (twinSieve q).toBoundingSieve.squarefree_of_dvd_prodPrimes hdP
  rw [show (twinSieve q).nu d =
      (Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} : ℝ) / (d : ℝ) by
    exact twinNu_squarefree hdSq]
  change |(polynomialCount (sieveBound q) d : ℝ) -
      ((Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} : ℝ) / (d : ℝ)) *
        (sieveBound q : ℝ)| ≤ _
  have hmain :
      ((Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} : ℝ) / (d : ℝ)) *
          (sieveBound q : ℝ) =
        (Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} : ℝ) *
          ((sieveBound q : ℝ) / (d : ℝ)) := by ring
  rw [hmain]
  exact abs_polynomialCount_sub (sieveBound q) d

theorem omega_eq_card_primeFactors (d : ℕ) : ω d = #d.primeFactors := by
  rw [cardDistinctFactors_apply]
  have hset : d.primeFactorsList.dedup.toFinset = d.primeFactorsList.toFinset := by
    ext p
    simp
  rw [← Nat.toFinset_factors, ← hset]
  exact (List.toFinset_card_of_nodup (List.nodup_dedup d.primeFactorsList)).symm

theorem card_twinRoots_le_two_pow {d : ℕ} (hd : Squarefree d) :
    Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} ≤ 2 ^ ω d := by
  rw [Submission.BrunSieve.card_twinRoots_squarefree hd,
    omega_eq_card_primeFactors, ← prod_const]
  gcongr with p hp
  split_ifs <;> omega

theorem two_pow_omega_le {d : ℕ} (hd : d ≠ 0) : 2 ^ ω d ≤ d := by
  rw [omega_eq_card_primeFactors, ← prod_const]
  calc
    ∏ _p ∈ d.primeFactors, 2 ≤ ∏ p ∈ d.primeFactors, p := by
      gcongr with p hp
      exact (prime_of_mem_primeFactors hp).two_le
    _ ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d)

theorem six_pow_omega_le_cube {d : ℕ} (hd : d ≠ 0) : 6 ^ ω d ≤ d ^ 3 := by
  calc
    6 ^ ω d ≤ 8 ^ ω d := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ ω d) ^ 3 := by
      calc
        8 ^ ω d = (2 ^ 3) ^ ω d := by norm_num
        _ = 2 ^ (3 * ω d) := by rw [pow_mul]
        _ = 2 ^ (ω d * 3) := by rw [Nat.mul_comm]
        _ = (2 ^ ω d) ^ 3 := by rw [pow_mul]
    _ ≤ d ^ 3 := Nat.pow_le_pow_left (two_pow_omega_le hd) _

theorem card_divisors_squarefree {d : ℕ} (hd : Squarefree d) :
    #d.divisors = 2 ^ ω d := by
  rw [Nat.card_divisors hd.ne_zero, omega_eq_card_primeFactors, ← prod_const]
  apply prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hd (prime_of_mem_primeFactors hp)
    (dvd_of_mem_primeFactors hp)]

theorem selbergTerms_ge_two_pow_div (q : ℕ) {l : ℕ}
    (hlP : l ∣ (twinSieve q).prodPrimes) :
    (2 ^ ω l : ℝ) / (l : ℝ) ≤
      (twinSieve q).toBoundingSieve.selbergTerms l := by
  have hlSq := (twinSieve q).toBoundingSieve.squarefree_of_dvd_prodPrimes hlP
  rw [BoundingSieve.selbergTerms_apply,
    ← (twinSieve q).toBoundingSieve.prod_primeFactors_nu hlP,
    ← Finset.prod_mul_distrib]
  calc
    (2 ^ ω l : ℝ) / (l : ℝ) =
        ∏ p ∈ l.primeFactors, (2 : ℝ) / p := by
      rw [omega_eq_card_primeFactors, ← prod_const, Finset.prod_div_distrib]
      have hlcast : (l : ℝ) = ∏ p ∈ l.primeFactors, (p : ℝ) := by
        calc
          (l : ℝ) = ((∏ p ∈ l.primeFactors, p : ℕ) : ℝ) :=
            congrArg Nat.cast (Nat.prod_primeFactors_of_squarefree hlSq).symm
          _ = ∏ p ∈ l.primeFactors, (p : ℝ) := by push_cast; rfl
      rw [hlcast]
    _ ≤ ∏ p ∈ l.primeFactors,
        (twinSieve q).nu p * (1 - (twinSieve q).nu p)⁻¹ := by
      apply prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := prime_of_mem_primeFactors hp
        have hpDvd : p ∣ (twinSieve q).prodPrimes :=
          (dvd_of_mem_primeFactors hp).trans hlP
        change (2 : ℝ) / p ≤ twinNu p * (1 - twinNu p)⁻¹
        rw [twinNu_prime hpPrime]
        by_cases hp2 : p = 2
        · subst p
          norm_num
        · rw [if_neg hp2]
          have hpgt : (2 : ℝ) < p := by
            exact_mod_cast lt_of_le_of_ne hpPrime.two_le (Ne.symm hp2)
          have hp0 : (0 : ℝ) < p := lt_trans (by norm_num) hpgt
          have hpm2 : (0 : ℝ) < p - 2 := by linarith
          field_simp
          nlinarith
    _ = _ := rfl

theorem squarefreePairs_product_mapsTo (M q : ℕ) (hqM : M = sieveWidth q) :
    Set.MapsTo (fun p : ℕ × ℕ => p.1 * p.2)
      (↑(squarefreeCoprimePairs M) : Set (ℕ × ℕ))
      (↑((divisors (twinSieve q).prodPrimes).filter fun l : ℕ =>
        (l : ℝ) ^ 2 ≤ (twinSieve q).level) : Set ℕ) := by
  intro p hp
  have hp' := mem_filter.mp (Finset.mem_coe.mp hp)
  have hp'' := mem_filter.mp hp'.1
  rcases mem_product.mp hp''.1 with ⟨ha, hb⟩
  simp only [posInterval, mem_Icc] at ha hb
  have hlSq : Squarefree (p.1 * p.2) := (Nat.squarefree_mul hp''.2).2 hp'.2
  have hlLe : p.1 * p.2 ≤ M ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul ha.2 hb.2
  have hlP : p.1 * p.2 ∣ (twinSieve q).prodPrimes := by
    change p.1 * p.2 ∣ primorial ((sieveWidth q) ^ 2)
    rw [← hqM]
    exact hlSq.dvd_primorial.trans (primorial_dvd_primorial hlLe)
  apply Finset.mem_coe.mpr
  apply mem_filter.mpr
  constructor
  · exact mem_divisors.mpr ⟨hlP, (twinSieve q).toBoundingSieve.prodPrimes_ne_zero⟩
  · change (((p.1 * p.2 : ℕ) : ℝ) ^ 2) ≤ (sieveWidth q : ℝ) ^ 4
    rw [← hqM]
    exact_mod_cast (calc
      (p.1 * p.2) ^ 2 ≤ (M ^ 2) ^ 2 := Nat.pow_le_pow_left hlLe 2
      _ = M ^ 4 := by ring)

def productFiber (M l : ℕ) : Finset (ℕ × ℕ) :=
  (squarefreeCoprimePairs M).filter fun p => p.1 * p.2 = l

theorem card_productFiber_le_divisors (M l : ℕ) :
    #(productFiber M l) ≤ #l.divisors := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    have hp' := mem_filter.mp (Finset.mem_coe.mp hp)
    have hsource := mem_filter.mp hp'.1
    have hpair := mem_filter.mp hsource.1
    have hpMem := mem_product.mp hpair.1
    have ha := hpMem.1
    have hb := hpMem.2
    simp only [posInterval, mem_Icc] at ha hb
    apply Finset.mem_coe.mpr
    apply mem_divisors.mpr
    exact ⟨⟨p.2, hp'.2.symm⟩, by
      rw [← hp'.2]
      exact mul_ne_zero (Nat.ne_of_gt ha.1) (Nat.ne_of_gt hb.1)⟩
  · intro p hp r hr hpr
    have hp' := mem_filter.mp (Finset.mem_coe.mp hp)
    have hr' := mem_filter.mp (Finset.mem_coe.mp hr)
    have hsource := mem_filter.mp hp'.1
    have hpair := mem_filter.mp hsource.1
    have ha := (mem_product.mp hpair.1).1
    simp only [posInterval, mem_Icc] at ha
    apply Prod.ext
    · exact hpr
    · apply Nat.mul_left_cancel ha.1
      change p.1 = r.1 at hpr
      calc
        p.1 * p.2 = l := hp'.2
        _ = r.1 * r.2 := hr'.2.symm
        _ = p.1 * r.2 := by rw [hpr]

theorem squarefreeCoprimePairSum_le_boundingSum (q : ℕ) :
    squarefreeCoprimePairSum (sieveWidth q) ≤
      Submission.Selberg.boundingSum (twinSieve q) := by
  classical
  let active := (divisors (twinSieve q).prodPrimes).filter fun l : ℕ =>
    (l : ℝ) ^ 2 ≤ (twinSieve q).level
  calc
    squarefreeCoprimePairSum (sieveWidth q) =
        ∑ l ∈ active, ∑ p ∈ productFiber (sieveWidth q) l,
          (((p.1 * p.2 : ℕ) : ℝ))⁻¹ := by
      rw [squarefreeCoprimePairSum]
      symm
      simpa only [active, productFiber] using
        Finset.sum_fiberwise_of_maps_to
          (squarefreePairs_product_mapsTo (sieveWidth q) q rfl)
          (fun p : ℕ × ℕ => (((p.1 * p.2 : ℕ) : ℝ))⁻¹)
    _ ≤ ∑ l ∈ active, (twinSieve q).toBoundingSieve.selbergTerms l := by
      gcongr with l hl
      have hl' := mem_filter.mp hl
      have hlSq := (twinSieve q).toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hl'.1
      calc
        ∑ p ∈ productFiber (sieveWidth q) l, (((p.1 * p.2 : ℕ) : ℝ))⁻¹ =
            (#(productFiber (sieveWidth q) l) : ℝ) * (l : ℝ)⁻¹ := by
          rw [← nsmul_eq_mul, ← sum_const]
          apply sum_congr rfl
          intro p hp
          rw [(mem_filter.mp hp).2]
        _ ≤ (2 ^ ω l : ℝ) / (l : ℝ) := by
          rw [div_eq_mul_inv]
          gcongr
          exact_mod_cast (card_productFiber_le_divisors (sieveWidth q) l).trans_eq
            (card_divisors_squarefree hlSq)
        _ ≤ (twinSieve q).toBoundingSieve.selbergTerms l :=
          selbergTerms_ge_two_pow_div q (dvd_of_mem_divisors hl'.1)
    _ = Submission.Selberg.boundingSum (twinSieve q) := by
      rw [Submission.Selberg.boundingSum, ← sum_filter]

def sieveLevelNat (q : ℕ) : ℕ := (sieveWidth q) ^ 4

theorem sieveError_le (q : ℕ) :
    (∑ d ∈ divisors (twinSieve q).prodPrimes,
      if (d : ℝ) ≤ (twinSieve q).level then
        (3 : ℝ) ^ ω d * |(twinSieve q).toBoundingSieve.rem d|
      else 0) ≤ ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 := by
  calc
    (∑ d ∈ divisors (twinSieve q).prodPrimes,
      if (d : ℝ) ≤ (twinSieve q).level then
        (3 : ℝ) ^ ω d * |(twinSieve q).toBoundingSieve.rem d|
      else 0) ≤
        ∑ d ∈ divisors (twinSieve q).prodPrimes,
          if d ≤ sieveLevelNat q then (d : ℝ) ^ 3 else 0 := by
      gcongr with d hd
      have hdP := dvd_of_mem_divisors hd
      have hd0 := ne_zero_of_dvd_ne_zero
        (twinSieve q).toBoundingSieve.prodPrimes_ne_zero hdP
      have hdSq := (twinSieve q).toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hd
      change (if (d : ℝ) ≤ (sieveWidth q : ℝ) ^ 4 then _ else _) ≤ _
      have hlevel : (d : ℝ) ≤ (sieveWidth q : ℝ) ^ 4 ↔ d ≤ sieveLevelNat q := by
        simp only [sieveLevelNat]
        norm_cast
      simp only [hlevel]
      split_ifs with hdLe
      swap
      · rfl
      calc
        (3 : ℝ) ^ ω d * |(twinSieve q).toBoundingSieve.rem d| ≤
            (3 : ℝ) ^ ω d *
              Nat.card {r : ZMod d // Submission.BrunSieve.IsTwinRoot d r} := by
          gcongr
          exact abs_rem_twinSieve_le q hdP
        _ ≤ (3 : ℝ) ^ ω d * (2 ^ ω d : ℕ) := by
          gcongr
          exact_mod_cast card_twinRoots_le_two_pow hdSq
        _ = (6 ^ ω d : ℕ) := by
          push_cast
          rw [← mul_pow]
          norm_num
        _ ≤ (d ^ 3 : ℕ) := by exact_mod_cast six_pow_omega_le_cube hd0
        _ = (d : ℝ) ^ 3 := by norm_num
    _ = ∑ d ∈ (divisors (twinSieve q).prodPrimes).filter (· ≤ sieveLevelNat q),
        (d : ℝ) ^ 3 := by
      rw [← sum_filter]
    _ ≤ ∑ d ∈ range (sieveLevelNat q + 1), (d : ℝ) ^ 3 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [mem_range]
        exact Nat.lt_succ_of_le (mem_filter.mp hd).2
      · intro d hd hnot
        positivity
    _ ≤ ∑ _d ∈ range (sieveLevelNat q + 1),
        ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 3 := by
      gcongr with d hd
      exact_mod_cast Nat.le_of_lt (mem_range.mp hd)
    _ = ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 := by
      simp [pow_succ]
      ring

def brunBlock (q : ℕ) : Finset ℕ :=
  Ico (blockBase ^ q) (blockBase ^ (q + 1))

noncomputable def twinStartsInBlock (q : ℕ) : Finset ℕ := by
  classical
  exact (brunBlock q).filter LeanEval.NumberTheory.BrunConstant.IsTwinPrimeStart

theorem mem_twinStartsInBlock (q n : ℕ) :
    n ∈ twinStartsInBlock q ↔
      n ∈ brunBlock q ∧ LeanEval.NumberTheory.BrunConstant.IsTwinPrimeStart n := by
  classical
  simp [twinStartsInBlock]

theorem sieveWidth_sq_lt_of_mem_twinStarts (q n : ℕ) (hn : n ∈ twinStartsInBlock q) :
    sieveWidth q ^ 2 < n := by
  have hn' := (mem_twinStartsInBlock q n).mp hn
  have hnBlock := mem_Ico.mp hn'.1
  rcases hn'.2 with ⟨hnPrime, hnPrime2⟩
  by_cases hq : q = 0
  · subst q
    simp only [sieveWidth, pow_zero, pow_two, one_mul]
    exact hnPrime.one_lt
  · apply lt_of_lt_of_le ?_ hnBlock.1
    change (2 ^ q) ^ 2 < (2 ^ 20) ^ q
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    apply Nat.pow_lt_pow_right (by norm_num)
    omega

theorem twinPolynomial_coprime_primorial_of_mem (q n : ℕ)
    (hn : n ∈ twinStartsInBlock q) :
    (primorial (sieveWidth q ^ 2)).Coprime
      (Submission.BrunSieve.twinPolynomial n) := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with ⟨p, hp, hpP, hpPoly⟩
  have hpLe : p ≤ sieveWidth q ^ 2 := (hp.dvd_primorial_iff).mp hpP
  have hn' := (mem_twinStartsInBlock q n).mp hn |>.2
  rw [Submission.BrunSieve.twinPolynomial] at hpPoly
  rcases hp.dvd_mul.mp hpPoly with hpn | hpn2
  · have hpeq : p = n := (Nat.prime_dvd_prime_iff_eq hp hn'.1).mp hpn
    rw [hpeq] at hpLe
    exact (not_le_of_gt (sieveWidth_sq_lt_of_mem_twinStarts q n hn)) hpLe
  · have hpeq : p = n + 2 := (Nat.prime_dvd_prime_iff_eq hp hn'.2).mp hpn2
    rw [hpeq] at hpLe
    exact (not_le_of_gt <| (sieveWidth_sq_lt_of_mem_twinStarts q n hn).trans
      (Nat.lt_add_of_pos_right (by norm_num))) hpLe

theorem twinStartCount_le_siftedSum (q : ℕ) :
    (#(twinStartsInBlock q) : ℝ) ≤ (twinSieve q).toBoundingSieve.siftedSum := by
  classical
  let sifted := ((range (sieveBound q)).image Submission.BrunSieve.twinPolynomial).filter
    fun n => (twinSieve q).prodPrimes.Coprime n
  have hcard : #(twinStartsInBlock q) ≤ #sifted := by
    apply Finset.card_le_card_of_injOn Submission.BrunSieve.twinPolynomial
    · intro n hn
      apply Finset.mem_coe.mpr
      apply mem_filter.mpr
      constructor
      · apply mem_image.mpr
        refine ⟨n, ?_, rfl⟩
        rw [mem_range]
        have hnUpper := (mem_Ico.mp ((mem_twinStartsInBlock q n).mp
          (Finset.mem_coe.mp hn)).1).2
        exact hnUpper
      · change (primorial (sieveWidth q ^ 2)).Coprime
          (Submission.BrunSieve.twinPolynomial n)
        exact twinPolynomial_coprime_primorial_of_mem q n (Finset.mem_coe.mp hn)
    · exact twinPolynomial_strictMono.injective.injOn
  calc
    (#(twinStartsInBlock q) : ℝ) ≤ (#sifted : ℝ) := by exact_mod_cast hcard
    _ = (twinSieve q).toBoundingSieve.siftedSum := by
      rw [BoundingSieve.siftedSum]
      change (#(((range (sieveBound q)).image Submission.BrunSieve.twinPolynomial).filter
        fun n => (twinSieve q).prodPrimes.Coprime n) : ℝ) =
        ∑ d ∈ (range (sieveBound q)).image Submission.BrunSieve.twinPolynomial,
          if (twinSieve q).prodPrimes.Coprime d then 1 else 0
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]

end Submission.BrunSieve
