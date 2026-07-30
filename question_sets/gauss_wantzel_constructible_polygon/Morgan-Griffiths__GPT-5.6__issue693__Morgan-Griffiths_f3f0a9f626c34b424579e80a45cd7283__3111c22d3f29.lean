import ChallengeDeps
import Submission.Helpers

namespace Submission

namespace SourceDefinitions
namespace LeanEval.NumberTheory.GaussWantzel

/-!
# Gauss-Wantzel constructible polygon theorem

`gauss_wantzel_constructible_polygon`: a regular `n`-gon is
straightedge-and-compass constructible exactly when `n` is a Gauss-Wantzel
integer. Constructibility is encoded by `IsConstructible`, the smallest
subfield of `ℝ` closed under square roots, applied to `cos (2π/n)`; the
arithmetic side `GaussWantzelNumber` requires every odd prime factor to be a
distinct Fermat prime. Mathlib has the algebraic ingredients but no
constructibility theory and no Gauss-Wantzel theorem. Category-(b) candidate
from §174 of the Knill survey.
-/

/-- The real values constructible from rational data by straightedge and
compass: the smallest subfield of `ℝ` closed under square roots. -/
inductive IsConstructible : ℝ → Prop
  | base (q : ℚ) : IsConstructible (q : ℝ)
  | add {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x + y)
  | neg {x : ℝ} : IsConstructible x → IsConstructible (-x)
  | mul {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x * y)
  | inv {x : ℝ} : IsConstructible x → IsConstructible x⁻¹
  | sqrt {x : ℝ} : IsConstructible x → IsConstructible (Real.sqrt x)

/-- Fermat primes, in the form appearing in the Gauss-Wantzel criterion. -/
def FermatPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1

/-- The number-theoretic side of the Gauss-Wantzel regular-polygon theorem:
only a power of two may occur with repeated exponent; every odd prime factor
must be a distinct Fermat prime. -/
def GaussWantzelNumber (n : ℕ) : Prop :=
  0 < n ∧
    ∀ p : ℕ, p.Prime → p ∣ n →
      (p = 2 ∨ FermatPrime p) ∧ (p ≠ 2 → ¬ p ^ 2 ∣ n)



end LeanEval.NumberTheory.GaussWantzel
end SourceDefinitions

open LeanEval.NumberTheory.GaussWantzel
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open scoped BigOperators

private lemma constructible_isAlgebraic {x : ℝ}
    (h : IsConstructible x) : IsAlgebraic ℚ x := by
  induction h with
  | base q =>
      simpa using (isAlgebraic_algebraMap (A := ℝ) q)
  | add hx hy ihx ihy => exact ihx.add ihy
  | neg hx ih => exact ih.neg
  | mul hx hy ihx ihy => exact ihx.mul ihy
  | inv hx ih => exact ih.inv
  | @sqrt x hx ih =>
      by_cases hnon : 0 ≤ x
      · have hxint : IsIntegral ℚ x := ih.isIntegral
        have hsqp : IsIntegral ℚ ((Real.sqrt x) ^ (2:ℕ)) := by
          rw [Real.sq_sqrt hnon]
          exact hxint
        exact (IsIntegral.of_pow (by decide : 0 < (2:ℕ)) hsqp).isAlgebraic
      · have hle : x ≤ 0 := le_of_lt (lt_of_not_ge hnon)
        have hz : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hle
        rw [hz]
        simpa using (isAlgebraic_algebraMap (A:=ℝ) (0 : ℚ))

/-- Once an angle in `[-π,π]` has constructible cosine, its half does too.
This is the elementary half-angle part of the converse. -/
private lemma constructible_cos_half {x : ℝ}
    (hx : IsConstructible (Real.cos x))
    (hl : -Real.pi ≤ x) (hr : x ≤ Real.pi) :
    IsConstructible (Real.cos (x / 2)) := by
  have h1 : IsConstructible (1 : ℝ) := by
    simpa using (IsConstructible.base (1 : ℚ))
  have h2 : IsConstructible (2 : ℝ) := by
    simpa using (IsConstructible.base (2 : ℚ))
  have h12 : IsConstructible ((1 + Real.cos x) / 2) := by
    have ha : IsConstructible ((1:ℝ) + Real.cos x) :=
      IsConstructible.add h1 hx
    have hi : IsConstructible ((2:ℝ)⁻¹) := IsConstructible.inv h2
    simpa [div_eq_mul_inv] using (IsConstructible.mul ha hi)
  rw [Real.cos_half hl hr]
  exact IsConstructible.sqrt h12

/-- The iterated bisections starting with the straight angle.  This tiny part
of the construction accounts for the arbitrary power of `2` in the
criterion; it uses no cyclotomic theory. -/
private lemma constructible_cos_pi_over_two_pow (r : ℕ) :
    IsConstructible (Real.cos (Real.pi / (2:ℝ) ^ r)) := by
  induction r with
  | zero =>
      have hm : IsConstructible (- (1:ℝ)) :=
        IsConstructible.neg (by simpa using (IsConstructible.base (1 : ℚ)))
      simpa using hm
  | succ r ih =>
      let y : ℝ := Real.pi / (2:ℝ) ^ r
      have hpospow : 0 < (2:ℝ) ^ r := by positivity
      have hy_nonneg : 0 ≤ y := by
        dsimp [y]
        exact div_nonneg Real.pi_nonneg (le_of_lt hpospow)
      have hleft : -Real.pi ≤ y := by
        have h : -Real.pi ≤ 0 := by linarith [Real.pi_pos]
        exact h.trans hy_nonneg
      have hp_ge_one : (1:ℝ) ≤ (2:ℝ) ^ r :=
        one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
      have hright : y ≤ Real.pi := by
        dsimp [y]
        exact div_le_self Real.pi_nonneg hp_ge_one
      have hhalf := constructible_cos_half ih hleft hright
      have heq : Real.pi / (2:ℝ) ^ (r+1) = y / 2 := by
        dsimp [y]
        rw [pow_succ, div_mul_eq_div_div]
      rw [heq]
      simpa [y] using hhalf

private lemma constructible_cos_two_pi_over_two_pow
    {r : ℕ} (hr : 1 ≤ r) :
    IsConstructible (Real.cos ((2:ℝ) * Real.pi / (2 ^ r : ℕ))) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have h := constructible_cos_pi_over_two_pow s
  have heq : (2:ℝ) * Real.pi / (↑(2 ^ (s+1) : ℕ) : ℝ)
          = Real.pi / (2:ℝ) ^ s := by
    -- cancelling the extra factor of two
    push_cast
    rw [pow_succ]
    -- the denominator is `2^s * 2`
    field_simp
  rw [heq]
  exact h

/-- Iterating the half-angle construction from any angle between `0` and
`π`.  No primitive root facts enter into the factor `2`. -/
private lemma constructible_cos_bisect {x : ℝ}
    (h0 : 0 ≤ x) (hpi : x ≤ Real.pi)
    (hx : IsConstructible (Real.cos x)) (r : ℕ) :
    IsConstructible (Real.cos (x / (2:ℝ)^r)) := by
  induction r with
  | zero => simpa using hx
  | succ r ih =>
      let y : ℝ := x / (2:ℝ)^r
      have hy0 : 0 ≤ y := by
        dsimp [y]
        exact div_nonneg h0 (by positivity)
      have hyleft : -Real.pi ≤ y := by
        have : -Real.pi ≤ 0 := by linarith [Real.pi_pos]
        exact this.trans hy0
      have hright : y ≤ Real.pi := by
        have hp : (1:ℝ) ≤ (2:ℝ)^r :=
          one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
        dsimp [y]
        exact (div_le_self h0 hp).trans hpi
      have hh := constructible_cos_half ih hyleft hright
      have heq : x / (2:ℝ)^(r+1) = y / 2 := by
        dsimp [y]
        rw [pow_succ, div_mul_eq_div_div]
      rw [heq]
      simpa [y] using hh

private lemma constructible_cos_double {x : ℝ}
    (hx : IsConstructible (Real.cos x)) :
    IsConstructible (Real.cos (2*x)) := by
  rw [Real.cos_two_mul]
  have h2 : IsConstructible (2:ℝ) := by
    simpa using (IsConstructible.base (2:ℚ))
  have h1 : IsConstructible (1:ℝ) := by
    simpa using (IsConstructible.base (1:ℚ))
  have hsq : IsConstructible ((Real.cos x)^2) := by
    simpa [pow_two] using (IsConstructible.mul hx hx)
  have hmul : IsConstructible ((2:ℝ) * (Real.cos x)^2) :=
    IsConstructible.mul h2 hsq
  exact IsConstructible.add hmul (IsConstructible.neg h1)

private lemma constructible_cos_double_iter {x : ℝ}
    (hx : IsConstructible (Real.cos x)) (r : ℕ) :
    IsConstructible (Real.cos ((2:ℝ)^r * x)) := by
  induction r with
  | zero => simpa using hx
  | succ r ih =>
      have hh := constructible_cos_double ih
      rw [pow_succ]
      -- `cos_two_mul` is stated with the two on the left
      convert hh using 2 <;> ring

/-- Removing or adding a factor `2` to the denominator does not change the
geometric difficulty.  Both implications are elementary: half-angle in one
direction and the double-angle polynomial in the other. -/
private lemma constructible_mul_two_pow_equiv (m r : ℕ) (hm : 2 ≤ m) :
    IsConstructible (Real.cos ((2:ℝ) * Real.pi / (m * 2^r : ℕ))) ↔
    IsConstructible (Real.cos ((2:ℝ) * Real.pi / (m : ℕ))) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have heq : (2:ℝ) * Real.pi / (↑(m * 2^r : ℕ) : ℝ)
        = ((2:ℝ) * Real.pi / (m:ℝ)) / (2:ℝ)^r := by
    push_cast
    rw [div_mul_eq_div_div]
  constructor
  · intro hsmall
    have hlarge := constructible_cos_double_iter hsmall r
    have heq' : (2:ℝ)^r * ((2:ℝ) * Real.pi /
           (↑(m * 2^r : ℕ) : ℝ))
           = (2:ℝ) * Real.pi / (m:ℝ) := by
      rw [heq]
      have hp : (2:ℝ)^r ≠ 0 := by positivity
      exact mul_div_cancel₀ _ hp
    rw [← heq']
    exact hlarge
  · intro hlarge
    have h0 : 0 ≤ (2:ℝ) * Real.pi / (m:ℝ) := by positivity
    have hmcast : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hpi : (2:ℝ) * Real.pi / (m:ℝ) ≤ Real.pi := by
      have hp := Real.pi_pos
      have hmpos : (0:ℝ) < m := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hmcast
      apply (div_le_iff₀ hmpos).2
      nlinarith [Real.pi_pos]
    have hsmall := constructible_cos_bisect h0 hpi hlarge r
    rw [heq]
    exact hsmall

private lemma totient_mul_two_pow_power_iff (m r : ℕ) (hmodd : Odd m)
    ( _hmpos : 0 < m) :
    (∃ k : ℕ, (m * 2^r).totient = 2^k) ↔
      (∃ k : ℕ, m.totient = 2^k) := by
  cases r with
  | zero => simp
  | succ r =>
      have hcop2 : Nat.Coprime m 2 := Odd.coprime_two_right hmodd
      have hcop : Nat.Coprime m (2^(r+1)) :=
        Nat.Coprime.pow_right (r+1) hcop2
      have hformula : (m * 2^(r+1)).totient = m.totient * 2^r := by
        rw [Nat.totient_mul hcop,
          Nat.totient_prime_pow Nat.prime_two (by omega : 0 < r+1)]
        simp
      constructor
      · rintro ⟨k, hk⟩
        have hdiv : m.totient ∣ 2^k := by
          have : m.totient * 2^r = 2^k := by simpa [hformula] using hk
          exact this ▸ (dvd_mul_right _ _)
        obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
        exact ⟨j, hjeq⟩
      · rintro ⟨k, hk⟩
        refine ⟨k+r, ?_⟩
        rw [hformula, hk, pow_add]

private lemma constructible_cos_two_pi_over_three_bisect (r : ℕ) :
    IsConstructible
      (Real.cos (((2:ℝ) * Real.pi / 3) / (2:ℝ)^r)) := by
  have hb0 : 0 ≤ (2:ℝ) * Real.pi / 3 := by positivity
  have hble : (2:ℝ) * Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  induction r with
  | zero =>
      have heq : (2:ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      have hv : Real.cos ((2:ℝ) * Real.pi / 3) = -(1/2:ℝ) := by
        rw [heq, Real.cos_pi_sub, Real.cos_pi_div_three]
      have hc : IsConstructible (-(1/2:ℝ)) := by
        -- all rational numbers, in particular the starting vertex
        simpa using (IsConstructible.base (-(1/2 : ℚ)))
      simpa [hv] using hc
  | succ r ih =>
      let x : ℝ := ((2:ℝ) * Real.pi / 3) / (2:ℝ)^r
      have hx0 : 0 ≤ x := by
        dsimp [x]
        exact div_nonneg hb0 (by positivity)
      have hxl : -Real.pi ≤ x := by
        have : -Real.pi ≤ 0 := by linarith [Real.pi_pos]
        exact this.trans hx0
      have hxle : x ≤ Real.pi := by
        have hpow : (1:ℝ) ≤ (2:ℝ)^r :=
          one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
        dsimp [x]
        exact (div_le_self hb0 hpow).trans hble
      have hh := constructible_cos_half ih hxl hxle
      have heq : ((2:ℝ) * Real.pi / 3) / (2:ℝ)^(r+1) = x / 2 := by
        dsimp [x]
        rw [pow_succ, div_mul_eq_div_div]
      rw [heq]
      simpa [x] using hh

private lemma constructible_cos_two_pi_over_three_mul_two_pow (r : ℕ) :
    IsConstructible
      (Real.cos ((2:ℝ) * Real.pi / (3 * 2^r : ℕ))) := by
  have h := constructible_cos_two_pi_over_three_bisect r
  have heq : (2:ℝ) * Real.pi / (↑(3 * 2^r : ℕ) : ℝ)
      = ((2:ℝ) * Real.pi / 3) / (2:ℝ)^r := by
    push_cast
    rw [mul_comm (3:ℝ), div_mul_eq_div_div]
    -- put the harmless factor `3` in the expected place
    ring
  rw [heq]
  exact h

private lemma constructible_sin_of_cos {x : ℝ}
    (hc : IsConstructible (Real.cos x))
    (h0 : 0 ≤ x) (hpi : x ≤ Real.pi) :
    IsConstructible (Real.sin x) := by
  rw [Real.sin_eq_sqrt_one_sub_cos_sq h0 hpi]
  have h1 : IsConstructible (1:ℝ) := by
    simpa using (IsConstructible.base (1:ℚ))
  have hsq : IsConstructible ((Real.cos x)^2) := by
    simpa [pow_two] using (IsConstructible.mul hc hc)
  have hdiff : IsConstructible ((1:ℝ) - (Real.cos x)^2) := by
    exact IsConstructible.add h1 (IsConstructible.neg hsq)
  exact IsConstructible.sqrt hdiff

private lemma constructible_cos_pi_div_five' :
    IsConstructible (Real.cos (Real.pi / 5)) := by
  rw [Real.cos_pi_div_five]
  have h5 : IsConstructible (5:ℝ) := by
    simpa using (IsConstructible.base (5:ℚ))
  have hs : IsConstructible (Real.sqrt (5:ℝ)) := IsConstructible.sqrt h5
  have h1 : IsConstructible (1:ℝ) := by
    simpa using (IsConstructible.base (1:ℚ))
  have h4 : IsConstructible (4:ℝ) := by
    simpa using (IsConstructible.base (4:ℚ))
  have ha := IsConstructible.add h1 hs
  simpa [div_eq_mul_inv] using
    (IsConstructible.mul ha (IsConstructible.inv h4))

private lemma constructible_cos_two_pi_over_five :
    IsConstructible (Real.cos ((2:ℝ)*Real.pi / 5)) := by
  have h5 : IsConstructible (5:ℝ) := by
    simpa using (IsConstructible.base (5:ℚ))
  have hs : IsConstructible (Real.sqrt (5:ℝ)) := IsConstructible.sqrt h5
  have h1 : IsConstructible (1:ℝ) := by
    simpa using (IsConstructible.base (1:ℚ))
  have h4 : IsConstructible (4:ℝ) := by
    simpa using (IsConstructible.base (4:ℚ))
  have hval : IsConstructible (((1:ℝ) + Real.sqrt 5) / 4) := by
    have ha := IsConstructible.add h1 hs
    simpa [div_eq_mul_inv] using
      (IsConstructible.mul ha (IsConstructible.inv h4))
  have hcpi : IsConstructible (Real.cos (Real.pi / 5)) := by
    rw [Real.cos_pi_div_five]
    exact hval
  have hc := constructible_cos_double hcpi
  have heq : (2:ℝ) * Real.pi / 5 = (2:ℝ) * (Real.pi / 5) := by ring
  rw [heq]
  exact hc

private lemma constructible_cos_two_pi_over_fifteen :
    IsConstructible (Real.cos ((2:ℝ)*Real.pi / 15)) := by
  have hca : IsConstructible (Real.cos (Real.pi / 3)) := by
    rw [Real.cos_pi_div_three]
    simpa using (IsConstructible.base (1/2 : ℚ))
  have hcb : IsConstructible (Real.cos (Real.pi / 5)) :=
    constructible_cos_pi_div_five'
  have hsa := constructible_sin_of_cos hca
      (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 3)
      (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi)
  have hsb := constructible_sin_of_cos hcb
      (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 5)
      (by linarith [Real.pi_pos] : Real.pi / 5 ≤ Real.pi)
  have h1 := IsConstructible.mul hca hcb
  have h2 := IsConstructible.mul hsa hsb
  have hh := IsConstructible.add h1 h2
  have hform : (2:ℝ)*Real.pi / 15 = Real.pi / 3 - Real.pi / 5 := by ring
  rw [hform, Real.cos_sub]
  exact hh

private lemma totient_three_mul_two_pow_is_two_power (r : ℕ) :
    ∃ k : ℕ, (3 * 2^r).totient = 2 ^ k := by
  cases r with
  | zero =>
      refine ⟨1, ?_⟩
      norm_num [Nat.totient_prime Nat.prime_three]
  | succ r =>
      have hc32 : Nat.Coprime 3 2 :=
        (Nat.coprime_primes Nat.prime_three Nat.prime_two).2 (by decide)
      have hc : Nat.Coprime 3 (2 ^ (r+1)) :=
        Nat.Coprime.pow_right (r+1) hc32
      refine ⟨r+1, ?_⟩
      rw [Nat.totient_mul hc]
      rw [Nat.totient_prime Nat.prime_three,
        Nat.totient_prime_pow Nat.prime_two (by omega : 0 < r+1)]
      simp [pow_succ, Nat.mul_comm]

private lemma prod_powers_two
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (h : ∀ a ∈ s, ∃ k : ℕ, f a = 2 ^ k) :
    ∃ k : ℕ, (∏ a ∈ s, f a) = 2 ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨k, hk⟩ := h a (by simp)
    obtain ⟨l, hl⟩ := ih (by
      intro b hb
      exact h b (by simp [hb]))
    refine ⟨k + l, ?_⟩
    simp [ha, hk, hl, pow_add]

private lemma gaussWantzel_iff_totient_two_power
    (n : ℕ) (hn : 0 < n) :
    GaussWantzelNumber n ↔ ∃ k : ℕ, n.totient = 2 ^ k := by
  classical
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  constructor
  · rintro ⟨_, hG⟩
    rw [Nat.totient_eq_prod_factorization hn0]
    have heach : ∀ p ∈ n.factorization.support,
        ∃ k : ℕ, p ^ (n.factorization p - 1) * (p - 1) = 2 ^ k := by
      intro p hp
      have hpprime : Nat.Prime p := by
        -- the support of the factorization is the set of prime factors
        exact Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨htype, hsq⟩ := hG p hpprime hpdvd
      rcases htype with htwo | hfermat
      · subst p
        refine ⟨n.factorization 2 - 1, ?_⟩
        simp
      · have hp2 : p ≠ 2 := by
          intro h
          have hf := hfermat.2
          obtain ⟨m, hm⟩ := hf
          -- a Fermat number is at least three
          have hbig : 2 < 2 ^ (2 ^ m) + 1 := by
            have : 0 < 2 ^ (2 ^ m) := pow_pos (by decide : 0 < (2:ℕ)) _
            -- in fact the power is at least two
            have hb : 2 ≤ 2 ^ (2 ^ m) := by
              have hh : 0 < 2 ^ m := pow_pos (by decide : 0 < (2:ℕ)) _
              calc
                2 = 2 ^ (1:ℕ) := by norm_num
                _ ≤ 2 ^ (2 ^ m) := (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hh)
            omega
          omega
        have hnodiv : ¬ p ^ 2 ∣ n := hsq hp2
        have hkpos : 0 < n.factorization p :=
          hpprime.factorization_pos_of_dvd hn0 hpdvd
        have hklt : n.factorization p < 2 := by
          by_contra hnot
          have hk : 2 ≤ n.factorization p := (Nat.not_lt).1 hnot
          apply hnodiv
          apply (Nat.factorization_le_iff_dvd (by
            have := hpprime.ne_zero
            exact pow_ne_zero _ this) hn0).1
          rw [hpprime.factorization_pow]
          exact Finsupp.single_le_iff.2 hk
        have hkone : n.factorization p = 1 := by omega
        obtain ⟨m, hm⟩ := hfermat.2
        have hpminus : p - 1 = 2 ^ (2 ^ m) := by simp [hm]
        refine ⟨2 ^ m, ?_⟩
        simp [hkone, hpminus]
    have hprod := prod_powers_two n.factorization.support
      (fun p => p ^ (n.factorization p - 1) * (p - 1)) heach
    simpa [Finsupp.prod] using hprod
  · rintro ⟨K, hK⟩
    refine ⟨hn, ?_⟩
    intro p hp hpn
    -- The contribution of the prime `p` to Euler's product divides the
    -- whole product, and hence is itself a divisor of a power of two.
    have hp_mem : p ∈ n.factorization.support := by
      exact (Nat.mem_primeFactors).2 ⟨hp, hpn, hn0⟩
    let term : ℕ → ℕ := fun q =>
      q ^ (n.factorization q - 1) * (q - 1)
    have hK' : n.factorization.prod (fun q e =>
        q ^ (e - 1) * (q - 1)) = 2 ^ K := by
      calc
        n.factorization.prod (fun q e => q ^ (e - 1) * (q-1))
            = n.totient := (Nat.totient_eq_prod_factorization hn0).symm
        _ = 2 ^ K := hK
    have htermprod : term p ∣ ∏ q ∈ n.factorization.support, term q :=
      Finset.dvd_prod_of_mem term hp_mem
    have hterm : term p ∣ 2 ^ K := by
      have : (∏ q ∈ n.factorization.support, term q) = 2 ^ K := by
        simpa [Finsupp.prod, term] using hK'
      exact this ▸ htermprod
    have hminus : p - 1 ∣ 2 ^ K := by
      apply dvd_trans ?_ hterm
      change p - 1 ∣ p ^ (n.factorization p - 1) * (p - 1)
      exact dvd_mul_left _ _
    obtain ⟨t, ht_le, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hminus
    have hp_one : 1 ≤ p := (Nat.le_of_lt hp.one_lt)
    have hp_as : p = 2 ^ t + 1 := by
      have hback : p - 1 + 1 = p := Nat.sub_add_cancel hp_one
      omega
    have hclassification : p = 2 ∨ FermatPrime p := by
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · right
        refine ⟨hp, ?_⟩
        have ht0 : t ≠ 0 := by
          intro hz
          have htone : p - 1 = 1 := by
            calc
              p - 1 = 2 ^ t := ht
              _ = 1 := by rw [hz]; norm_num
          have : p = 2 := by omega
          exact hp2 this
        have hprime' : Nat.Prime (2 ^ t + 1) := by
          simpa [← hp_as] using hp
        obtain ⟨m, hm⟩ :=
          Nat.pow_of_pow_add_prime (a := 2) (n := t)
            (by decide : 1 < (2:ℕ)) ht0 hprime'
        refine ⟨m, ?_⟩
        simpa [hm] using hp_as
    refine ⟨hclassification, ?_⟩
    intro hp2 hp2n
    have hfac_le : (p ^ 2).factorization ≤ n.factorization :=
      (Nat.factorization_le_iff_dvd
        (by exact pow_ne_zero _ hp.ne_zero) hn0).2 hp2n
    have hfac_ge : 2 ≤ n.factorization p := by
      have hval := (Finsupp.le_def.mp hfac_le) p
      simpa [hp.factorization_pow] using hval
    have hposminus : n.factorization p - 1 ≠ 0 := by omega
    have hpdivpow : p ∣ p ^ (n.factorization p - 1) :=
      dvd_pow_self _ hposminus
    have hpdivterm : p ∣ term p := by
      apply dvd_trans hpdivpow ?_ -- the first factor divides the product
      exact dvd_mul_right _ _
    have hpdivtwoPow : p ∣ 2 ^ K := dvd_trans hpdivterm hterm
    have hpdivtwo : p ∣ 2 := hp.dvd_of_dvd_pow hpdivtwoPow
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpdivtwo)


/-- A convenient way of keeping track of one radical step.  The carrier
of `nextF E a` is definitionally `E⟮a⟯`, but it is regarded as a
`ℚ`-intermediate field.  This allows the tower formula for finranks. -/
private noncomputable def nextF (E : IntermediateField ℚ ℝ) (a : ℝ) : IntermediateField ℚ ℝ :=
  (IntermediateField.adjoin E {a}).restrictScalars ℚ

private lemma le_next (E : IntermediateField ℚ ℝ) (a : ℝ) : E ≤ nextF E a := by
  intro z hz
  change z ∈ IntermediateField.adjoin E ({a}:Set ℝ)
  have h := (IntermediateField.adjoin E ({a}:Set ℝ)).algebraMap_mem (⟨z,hz⟩ : E)
  exact h

private lemma mem_next (E : IntermediateField ℚ ℝ) (a : ℝ) : a ∈ nextF E a := by
  -- using subset_adjoin and mem_restrict
  change a ∈ IntermediateField.adjoin E ({a}:Set ℝ)
  exact (IntermediateField.subset_adjoin E {a}) (by simp)

private lemma integral_of_sq_mem (E : IntermediateField ℚ ℝ) (a:ℝ)
    (ha : a^2 ∈ E) : IsIntegral E a := by
  let z : E := ⟨a^2, ha⟩
  refine ⟨Polynomial.X^2 - Polynomial.C z,
    Polynomial.monic_X_pow_sub_C z (by norm_num : (2:ℕ) ≠ 0), ?_⟩
  -- goal eval₂
  rw [← Polynomial.aeval_def]
  simp [z]

private lemma relfinrank_next_le_two (E : IntermediateField ℚ ℝ) (a:ℝ)
    (ha : a^2 ∈ E) :
    Module.finrank E (IntermediateField.adjoin E ({a}:Set ℝ)) ≤ 2 := by
  have hint : IsIntegral E a := integral_of_sq_mem E a ha
  letI : FiniteDimensional E (IntermediateField.adjoin E ({a}:Set ℝ)) :=
    IntermediateField.adjoin.finiteDimensional hint
  -- minpoly bound
  let z : E := ⟨a^2, ha⟩
  have hpmonic : (Polynomial.X^2 - Polynomial.C z).Monic :=
    Polynomial.monic_X_pow_sub_C z (by norm_num : (2:ℕ) ≠ 0)
  have hpeval : Polynomial.aeval a (Polynomial.X^2 - Polynomial.C z) = 0 := by
    simp [z]
  have hd := minpoly.min E a hpmonic hpeval
  have hd' : (minpoly E a).degree ≤ (2 : WithBot ℕ) := by
    simpa [Polynomial.degree_X_pow_sub_C (by norm_num : 0 < (2:ℕ))] using hd
  have hnat : (minpoly E a).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_iff_degree_le).2 hd'
  simpa [IntermediateField.adjoin.finrank hint] -- maybe rw
    using hnat

private lemma step (E : IntermediateField ℚ ℝ) (a : ℝ) (ha : a^2 ∈ E)
    [FiniteDimensional ℚ E]
    (hpow : ∃ k:ℕ, Module.finrank ℚ E = 2^k) :
    ∃ k:ℕ, Module.finrank ℚ (nextF E a) = 2^k := by
  have hint : IsIntegral E a := integral_of_sq_mem E a ha
  letI : FiniteDimensional E (IntermediateField.adjoin E ({a}:Set ℝ)) :=
    IntermediateField.adjoin.finiteDimensional hint
  letI : FiniteDimensional ℚ (IntermediateField.adjoin E ({a}:Set ℝ)) :=
    FiniteDimensional.trans ℚ E _
  -- want instances for next maybe:
  -- ensure change target finrank of adjoin? scalar algebra
  change ∃ k:ℕ, Module.finrank ℚ (IntermediateField.adjoin E ({a}:Set ℝ)) = 2^k
  have hle := relfinrank_next_le_two E a ha
  have hpos : 0 < Module.finrank E (IntermediateField.adjoin E ({a}:Set ℝ)) :=
    Module.finrank_pos
  have hfac : Module.finrank E (IntermediateField.adjoin E ({a}:Set ℝ)) = 1 ∨
      Module.finrank E (IntermediateField.adjoin E ({a}:Set ℝ)) = 2 := by
    omega
  obtain ⟨k,hk⟩ := hpow
  have hmul := Module.finrank_mul_finrank ℚ E (IntermediateField.adjoin E ({a}:Set ℝ))
  rcases hfac with h1 | h2
  · refine ⟨k, ?_⟩
    calc
      Module.finrank ℚ (IntermediateField.adjoin E ({a}:Set ℝ)) =
        Module.finrank ℚ E * Module.finrank E (IntermediateField.adjoin E ({a}:Set ℝ)) := hmul.symm
      _ = 2^k := by simp [hk, h1] -- scratch
  · refine ⟨k+1, ?_⟩
    calc
      Module.finrank ℚ (IntermediateField.adjoin E ({a}:Set ℝ)) =
        Module.finrank ℚ E * Module.finrank E (IntermediateField.adjoin E ({a}:Set ℝ)) := hmul.symm
      _ = (2^k) * 2 := by rw [hk, h2]
      _ = 2^(k+1) := by rw [pow_succ]

private lemma sq_sqrt_mem (E : IntermediateField ℚ ℝ) {x:ℝ} (hx:x∈E) :
    (Real.sqrt x)^2 ∈ E := by
  by_cases h:0 ≤ x
  · rw [Real.sq_sqrt h]
    exact hx
  · have hz : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)
    rw [hz]
    simp

private lemma constructible_exists_field {x:ℝ} (h : IsConstructible x) :
    ∀ (F : IntermediateField ℚ ℝ),
      [FiniteDimensional ℚ F] →
      (∃ k:ℕ, Module.finrank ℚ F = 2^k) →
      ∃ E : IntermediateField ℚ ℝ, F ≤ E ∧
        FiniteDimensional ℚ E ∧ x ∈ E ∧
        ∃ k:ℕ, Module.finrank ℚ E = 2^k := by
  induction h with
  | base q =>
      intro F hfin hpow
      letI : FiniteDimensional ℚ F := hfin
      refine ⟨F, le_rfl, inferInstance, ?_, hpow⟩
      exact F.algebraMap_mem q
  | add hx hy ihx ihy =>
      intro F hfin hpow
      letI : FiniteDimensional ℚ F := hfin
      obtain ⟨E, hFE, hEfin, hxE, hpE⟩ := ihx F hpow
      letI : FiniteDimensional ℚ E := hEfin
      obtain ⟨G, hEG, hGfin, hyG, hpG⟩ := ihy E hpE
      refine ⟨G, hFE.trans hEG, hGfin, ?_, hpG⟩
      exact G.add_mem (hEG hxE) hyG
  | neg hx ih =>
      intro F hfin hpow
      letI : FiniteDimensional ℚ F := hfin
      obtain ⟨E,hFE,hEfin,hxE,hpE⟩ := ih F hpow
      exact ⟨E,hFE,hEfin,E.neg_mem hxE,hpE⟩
  | mul hx hy ihx ihy =>
      intro F hfin hpow
      letI : FiniteDimensional ℚ F := hfin
      obtain ⟨E,hFE,hEfin,hxE,hpE⟩ := ihx F hpow
      letI : FiniteDimensional ℚ E := hEfin
      obtain ⟨G,hEG,hGfin,hyG,hpG⟩ := ihy E hpE
      exact ⟨G,hFE.trans hEG,hGfin,G.mul_mem (hEG hxE) hyG,hpG⟩
  | inv hx ih =>
      intro F hfin hpow
      letI : FiniteDimensional ℚ F := hfin
      obtain ⟨E,hFE,hEfin,hxE,hpE⟩ := ih F hpow
      exact ⟨E,hFE,hEfin,E.inv_mem hxE,hpE⟩
  | @sqrt x hx ih =>
      intro F hfin hpow
      letI : FiniteDimensional ℚ F := hfin
      obtain ⟨E,hFE,hEfin,hxE,hpE⟩ := ih F hpow
      letI : FiniteDimensional ℚ E := hEfin
      let a : ℝ := Real.sqrt x
      have ha_sq : a^2 ∈ E := sq_sqrt_mem E hxE
      -- use step and construct top
      have hint : IsIntegral E a := integral_of_sq_mem E a ha_sq
      letI : FiniteDimensional E (IntermediateField.adjoin E ({a}:Set ℝ)) :=
        IntermediateField.adjoin.finiteDimensional hint
      letI : FiniteDimensional ℚ (IntermediateField.adjoin E ({a}:Set ℝ)) :=
        FiniteDimensional.trans ℚ E _
      -- next equal type works
      have hpnext : ∃ k:ℕ, Module.finrank ℚ (nextF E a) = 2^k :=
        step E a ha_sq hpE
      -- need finite instance next; definitional
      have hfnext : FiniteDimensional ℚ (nextF E a) := by
        -- defs reduce
        change FiniteDimensional ℚ (IntermediateField.adjoin E ({a}:Set ℝ))
        infer_instance
      refine ⟨nextF E a, hFE.trans (le_next E a), hfnext, ?_, hpnext⟩
      change Real.sqrt x ∈ nextF E (Real.sqrt x)
      exact mem_next E _


private lemma constructible_minpoly_degree_power {x:ℝ} (h:IsConstructible x) :
    ∃ k:ℕ, (minpoly ℚ x).natDegree = 2^k := by
  let F : IntermediateField ℚ ℝ := ⊥
  haveI : FiniteDimensional ℚ F := by dsimp [F]; infer_instance
  have hp : ∃ k:ℕ, Module.finrank ℚ F = 2^k := by
    refine ⟨0, ?_⟩
    simp [F, IntermediateField.finrank_bot]
  obtain ⟨E, hFE, hEfin, hxE, hpE⟩ := constructible_exists_field h F hp
  letI : FiniteDimensional ℚ E := hEfin
  have hxint : IsIntegral ℚ x := by
    have hi : IsIntegral ℚ (⟨x,hxE⟩ : E) := IsIntegral.of_finite ℚ _
    exact (IntermediateField.isIntegral_iff (K:=ℚ) (L:=ℝ) (S:=E)).1 hi
  have hle : IntermediateField.adjoin ℚ ({x}:Set ℝ) ≤ E :=
    (IntermediateField.adjoin_simple_le_iff).2 hxE
  have hdvd : Module.finrank ℚ (IntermediateField.adjoin ℚ ({x}:Set ℝ)) ∣
        Module.finrank ℚ E :=
    IntermediateField.finrank_dvd_of_le_right hle
  obtain ⟨k,hk⟩ := hpE
  have hdvd' : (minpoly ℚ x).natDegree ∣ 2^k := by
    rw [← hk]
    simpa [IntermediateField.adjoin.finrank hxint] using hdvd
  obtain ⟨j,hj,hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
  exact ⟨j,hjeq⟩



/- For the necessary half of Wantzel it is enough to avoid the real
cyclotomic subfield.  In `ℂ`, put `z = exp(2πi/n)`.  The following degree
calculation uses just
`(z+z⁻¹)/2 = cos(2π/n)` and the ordinary cyclotomic polynomial. -/
open scoped ComplexConjugate
private noncomputable def zz (n:ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi:ℂ) * Complex.I / (n:ℂ))
private noncomputable def tt (n:ℕ) : ℝ := (2:ℝ) * Real.pi / n
private lemma zz_eq (n:ℕ) : zz n = Complex.exp ((tt n : ℂ) * Complex.I) := by
  dsimp [zz,tt]
  congr 1
  push_cast
  ring
private lemma zz_add_inv (n:ℕ) :
    (zz n + (zz n)⁻¹) / 2 = (tt n).cos := by
  rw [zz_eq]
  have hinv : (Complex.exp ((tt n : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((-(tt n) : ℝ) * Complex.I) := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hinv]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring
private lemma relquad (K : IntermediateField ℚ ℂ) (z : ℂ)
    (a b : K) (hz : z^2 = (a:ℂ)*z + (b:ℂ)) :
    IsIntegral K z ∧ Module.finrank K (IntermediateField.adjoin K ({z}:Set ℂ)) ≤ 2 := by
  let p : Polynomial K := Polynomial.X^2 - Polynomial.C a * Polynomial.X - Polynomial.C b
  have hpmon : p.Monic := by
    dsimp [p]
    monicity <;> norm_num
  have hlin : (Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial K).degree < (2:WithBot ℕ) := by
    have hax : (Polynomial.C a * Polynomial.X : Polynomial K).degree ≤ (1:WithBot ℕ) := by
      calc
        (Polynomial.C a * Polynomial.X : Polynomial K).degree
          ≤ (Polynomial.C a : Polynomial K).degree + (Polynomial.X : Polynomial K).degree := Polynomial.degree_mul_le _ _
        _ ≤ (0:WithBot ℕ) + (1:WithBot ℕ) :=
          add_le_add Polynomial.degree_C_le (le_of_eq Polynomial.degree_X)
        _ = 1 := by norm_num
    have hb : (Polynomial.C b : Polynomial K).degree ≤ (1:WithBot ℕ) :=
      Polynomial.degree_C_le.trans (by norm_num)
    have had : (Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial K).degree ≤ (1:WithBot ℕ) :=
      (Polynomial.degree_add_le _ _).trans (max_le hax hb)
    exact lt_of_le_of_lt had (by norm_num)
  have hpdeg : p.degree = (2:WithBot ℕ) := by
    change (Polynomial.X^2 - Polynomial.C a * Polynomial.X - Polynomial.C b : Polynomial K).degree = _
    rw [show (Polynomial.X^2 - Polynomial.C a * Polynomial.X - Polynomial.C b : Polynomial K) =
          Polynomial.X^2 - (Polynomial.C a * Polynomial.X + Polynomial.C b) by ring]
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow 2
    · simpa [Polynomial.degree_X_pow] using hlin
  have hpeval : Polynomial.aeval z p = 0 := by
    dsimp [p]
    simp [hz]
  have hi : IsIntegral K z := by
    refine ⟨p, hpmon, ?_⟩
    rwa [← Polynomial.aeval_def]
  refine ⟨hi, ?_⟩
  have hd := minpoly.min K z hpmon hpeval
  have hd' : (minpoly K z).degree ≤ (2:WithBot ℕ) := hpdeg ▸ hd
  have hnat : (minpoly K z).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_iff_degree_le).2 hd'
  simpa [IntermediateField.adjoin.finrank hi] using hnat
private lemma tot_rel (n:ℕ) (hn : 0 < n) :
    ∃ d:ℕ, (minpoly ℚ ((tt n).cos)).natDegree = d ∧
      (n.totient = d ∨ n.totient = d*2) := by
  let z : ℂ := zz n
  let c : ℝ := (tt n).cos
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({(c:ℂ)}:Set ℂ)
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({z}:Set ℂ)
  have hzmem : z ∈ L := (IntermediateField.subset_adjoin ℚ ({z}:Set ℂ)) (by simp)
  have htwo : (2:ℂ) ∈ L := by
    convert L.algebraMap_mem (2:ℚ) using 1 <;> norm_num
  have hcmem : (c:ℂ) ∈ L := by
    change ((tt n).cos:ℂ) ∈ L
    rw [← zz_add_inv n]
    change (z + z⁻¹) / (2:ℂ) ∈ L
    exact L.div_mem (L.add_mem hzmem (L.inv_mem hzmem)) htwo
  have hKL : K ≤ L := (IntermediateField.adjoin_simple_le_iff).2 hcmem
  have hcnat : (minpoly ℚ (c:ℂ)).natDegree = (minpoly ℚ c).natDegree := by
    -- alg hom ofReal
    let f : ℝ →ₐ[ℚ] ℂ := Complex.ofRealHom.toRatAlgHom
    have hf : Function.Injective f := Complex.ofReal_injective
    exact congrArg Polynomial.natDegree (minpoly.algHom_eq f hf c)
  have hcint : IsIntegral ℚ (c:ℂ) := by
    -- real algebraic cos already by Lindemann? but cos rational angle algebraic
    -- use z relation? cannot assume. Show c integrality follows from primitive z finite field contains c.
    have hzprim : IsPrimitiveRoot z n := by
      simpa [z, zz] using Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    have hzint : IsIntegral ℚ z := by
      refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic.monic n ℚ, ?_⟩
      rw [← Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.map_cyclotomic]
      exact (Polynomial.isRoot_cyclotomic_iff.mpr hzprim : _)
    letI : FiniteDimensional ℚ L := by
      dsimp [L]
      exact IntermediateField.adjoin.finiteDimensional hzint
    have hiL : IsIntegral ℚ (⟨(c:ℂ), hcmem⟩ : L) := IsIntegral.of_finite ℚ _
    exact (IntermediateField.isIntegral_iff (K:=ℚ) (L:=ℂ) (S:=L)).1 hiL

  refine ⟨(minpoly ℚ c).natDegree, rfl, ?_⟩
  -- now compute tower
  have hzprim : IsPrimitiveRoot z n := by
    simpa [z, zz] using Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hzint : IsIntegral ℚ z := by
    refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic.monic n ℚ, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr hzprim : _)
  letI : FiniteDimensional ℚ L := by
    dsimp [L]
    exact IntermediateField.adjoin.finiteDimensional hzint
  letI : FiniteDimensional ℚ K := by
    dsimp [K]
    exact IntermediateField.adjoin.finiteDimensional hcint
  -- relative field L/K is the simple extension by z
  have hext : IntermediateField.extendScalars hKL = IntermediateField.adjoin K ({z}:Set ℂ) :=
    IntermediateField.extendScalars_adjoin hKL
  -- quadratic equation z² = (2c) z -1
  let aa : K := ⟨(2:ℂ)*(c:ℂ), K.mul_mem
        (by exact K.algebraMap_mem (2:ℚ))
        (by exact (IntermediateField.subset_adjoin ℚ ({(c:ℂ)}:Set ℂ)) (by simp [K]))⟩
  let bb : K := ⟨(-1:ℂ), by
        convert K.algebraMap_mem (-1:ℚ) using 1 <;> norm_num⟩
  have hquad : z^2 = (aa:ℂ)*z + (bb:ℂ) := by
    have hz := zz_add_inv n
    -- use relation c = (z + z^-1)/2
    change (z + z⁻¹) / (2:ℂ) = (c:ℂ) at hz
    have hzne : z ≠ 0 := by
      dsimp [z, zz]
      exact Complex.exp_ne_zero _
    dsimp [aa,bb]
    field_simp at hz ⊢
    -- hz : (z+z^-1)*? ; use inverse
    linear_combination hz
  have hq := relquad K z aa bb hquad
  have hzK : IsIntegral K z := hq.1
  letI : FiniteDimensional K (IntermediateField.adjoin K ({z}:Set ℂ)) :=
    IntermediateField.adjoin.finiteDimensional hzK
  have hrelle : Module.finrank K (IntermediateField.adjoin K ({z}:Set ℂ)) ≤ 2 := hq.2
  have hrelpos : 0 < Module.finrank K (IntermediateField.adjoin K ({z}:Set ℂ)) :=
    Module.finrank_pos
  have hrel : Module.finrank K (IntermediateField.adjoin K ({z}:Set ℂ)) = 1 ∨
      Module.finrank K (IntermediateField.adjoin K ({z}:Set ℂ)) = 2 := by omega
  -- tower formula with L's underlying type via extendScalars
  letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  have htow : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  letI : IsScalarTower ℚ K L := htow
  have hmul := Module.finrank_mul_finrank ℚ K L
  have hKdeg : Module.finrank ℚ K = (minpoly ℚ c).natDegree := by
    dsimp [K]
    rw [IntermediateField.adjoin.finrank hcint]
    exact hcnat
  have hLdeg : Module.finrank ℚ L = n.totient := by
    dsimp [L]
    rw [IntermediateField.adjoin.finrank hzint]
    rw [← Polynomial.natDegree_cyclotomic n ℚ,
        Polynomial.cyclotomic_eq_minpoly_rat hzprim hn]
  have hrel' : Module.finrank K L = Module.finrank K (IntermediateField.adjoin K ({z}:Set ℂ)) := by
    -- definitional identify extendScalars hKL with L as type
    -- L carrier; hext
    -- after hext change
    -- use congrArg finrank along set equality is hard; extendScalars is defeq L
    change Module.finrank K (IntermediateField.extendScalars hKL) = _
    rw [hext]
  rcases hrel with h1 | h2
  · left
    rw [← hLdeg, ← hKdeg]
    nlinarith [hmul, hrel'.trans h1]
  · right
    rw [← hLdeg, ← hKdeg]
    nlinarith [hmul, hrel'.trans h2]


/-- The inductive predicate really is a field.  In particular, after one
has constructed a set of periods, any element of the field they generate
can be used without repeating its expression. -/
private def constructibleField : IntermediateField ℚ ℝ where
  carrier := {x | IsConstructible x}
  add_mem' := fun hx hy => IsConstructible.add hx hy
  mul_mem' := fun hx hy => IsConstructible.mul hx hy
  one_mem' := by simpa using (IsConstructible.base (1:ℚ))
  zero_mem' := by simpa using (IsConstructible.base (0:ℚ))
  algebraMap_mem' := fun q => IsConstructible.base q
  inv_mem' := fun _ hx => IsConstructible.inv hx

private lemma constructible_adjoin {S : Set ℝ}
    (hS : ∀ x ∈ S, IsConstructible x) {y : ℝ}
    (hy : y ∈ IntermediateField.adjoin ℚ S) : IsConstructible y := by
  change y ∈ constructibleField
  exact (IntermediateField.adjoin_le_iff.2 (by
    intro z hz
    change IsConstructible z
    exact hS z hz)) hy

/-- Passing from a constructed intermediate field to it with one square
root adjoined is again valid.  This is the local algebra step needed for a
quadratic intermediate-field tower; the missing global step is to produce
that tower of periods. -/
private lemma constructible_one_sqrt_extension
    (E : IntermediateField ℚ ℝ)
    (hE : ∀ z : ℝ, z ∈ E → IsConstructible z)
    (x : ℝ) (hx : x ∈ E) :
    ∀ z : ℝ, z ∈ nextF E (Real.sqrt x) → IsConstructible z := by
  have hEle : E ≤ constructibleField := by
    intro z hz
    exact hE z hz
  have ha : Real.sqrt x ∈ constructibleField :=
    IsConstructible.sqrt (hE x hx)
  -- regard the next field as the old field together with this element
  have hsup : E ⊔ IntermediateField.adjoin ℚ ({Real.sqrt x}:Set ℝ)
        ≤ constructibleField := by
    refine sup_le hEle ?_
    exact (IntermediateField.adjoin_simple_le_iff).2 ha
  intro z hz
  change z ∈ constructibleField
  apply hsup
  -- the carrier of `nextF` is `adjoin E {√x}`.  On restricting scalars
  -- this is exactly the indicated supremum.
  have heq := IntermediateField.restrictScalars_adjoin_eq_sup
       ℚ E ({Real.sqrt x}:Set ℝ)
  have hz' : z ∈ (IntermediateField.adjoin E ({Real.sqrt x}:Set ℝ)).restrictScalars ℚ := by
    exact hz
  exact (le_of_eq heq) hz'


open Polynomial
private lemma gw_quad_expr {E:Type*} [CommRing E]
 (p:Polynomial E) (hp:p.Monic) (hd:p.natDegree=2) :
 p = X^2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  by_cases h0 : n = 0
  · subst n; simp
  by_cases h1 : n = 1
  · subst n; simp
  by_cases h2 : n = 2
  · subst n
    have hc : p.coeff 2 = 1 := by simpa [hd] using hp.coeff_natDegree
    simpa [hc]
  have hgt : p.natDegree < n := by omega
  have hz : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
  have hn0 : 0 ≠ n := Ne.symm h0
  have hn1 : 1 ≠ n := Ne.symm h1
  simp [hz, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_X, Polynomial.coeff_C, h0, h1, h2, hn0, hn1]

private lemma root_small_constructible (E : IntermediateField ℚ ℝ)
    (hE : ∀ y:ℝ, y ∈ E → IsConstructible y)
    (x:ℝ) (hx : IsIntegral E x) (hdeg : (minpoly E x).natDegree ≤ 2) :
    IsConstructible x := by
  have hpos : 0 < (minpoly E x).natDegree := minpoly.natDegree_pos hx
  have cases : (minpoly E x).natDegree = 1 ∨ (minpoly E x).natDegree = 2 := by omega
  rcases cases with h1 | h2
  · have hrange : x ∈ (algebraMap E ℝ).range :=
      (minpoly.natDegree_eq_one_iff).1 h1
    obtain ⟨a, ha⟩ := hrange
    have : x = (a:ℝ) := ha.symm
    exact this ▸ hE (a:ℝ) a.2
  · let a : E := (minpoly E x).coeff 1
    let b : E := (minpoly E x).coeff 0
    have peq : minpoly E x = X^2 + C a * X + C b :=
      gw_quad_expr _ (minpoly.monic hx) h2
    have hev := minpoly.aeval E x
    rw [peq] at hev
    -- quadratic equation in R
    have eqn : x^2 + (a:ℝ)*x + (b:ℝ) = 0 := by
      simpa [map_add, map_mul] using hev
    let ar : ℝ := (a:ℝ)
    let br : ℝ := (b:ℝ)
    let d : ℝ := ar^2 - 4*br
    have hsqd : (2*x + ar)^2 = d := by
      dsimp [d, ar, br]
      nlinarith
    have hd0 : 0 ≤ d := by
      rw [← hsqd]; positivity
    have hs : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd0
    have habs : 2*x + ar = Real.sqrt d ∨ 2*x + ar = -(Real.sqrt d) := by
      exact (sq_eq_sq_iff_eq_or_eq_neg).1 (hsqd.trans hs.symm)
    have haC : IsConstructible ar := hE (a:ℝ) a.2
    have hbC : IsConstructible br := hE (b:ℝ) b.2
    have htwo : IsConstructible (2:ℝ) := by simpa using (IsConstructible.base (2:ℚ))
    have hfour : IsConstructible (4:ℝ) := by simpa using (IsConstructible.base (4:ℚ))
    have hdC : IsConstructible d := by
      dsimp [d]
      have aa : IsConstructible (ar^2) := by
        simpa [pow_two] using (IsConstructible.mul haC haC)
      have fb : IsConstructible ((4:ℝ)*br) := IsConstructible.mul hfour hbC
      exact IsConstructible.add aa (IsConstructible.neg fb)
    have hsC : IsConstructible (Real.sqrt d) := IsConstructible.sqrt hdC
    have hi2 : IsConstructible ((2:ℝ)⁻¹) := IsConstructible.inv htwo
    rcases habs with hp | hm
    · have hxform : x = (Real.sqrt d + (-ar)) * (2:ℝ)⁻¹ := by
        apply (eq_mul_inv_iff_mul_eq₀ (by norm_num : (2:ℝ) ≠ 0)).2
        nlinarith
      rw [hxform]
      exact IsConstructible.mul (IsConstructible.add hsC (IsConstructible.neg haC)) hi2
    · have hxform : x = (-(Real.sqrt d) + (-ar)) * (2:ℝ)⁻¹ := by
        apply (eq_mul_inv_iff_mul_eq₀ (by norm_num : (2:ℝ) ≠ 0)).2
        nlinarith
      rw [hxform]
      exact IsConstructible.mul
        (IsConstructible.add (IsConstructible.neg hsC) (IsConstructible.neg haC)) hi2

private lemma quadratic_extend_constructible
    (E F : IntermediateField ℚ ℝ) (hle : E ≤ F)
    [hfin : FiniteDimensional E (IntermediateField.extendScalars hle)]
    (hrel : Module.finrank E (IntermediateField.extendScalars hle) ≤ 2)
    (hE : ∀ y:ℝ, y ∈ E → IsConstructible y) :
    ∀ y:ℝ, y ∈ F → IsConstructible y := by
  intro y hy
  let T : IntermediateField E ℝ := IntermediateField.extendScalars hle
  letI : FiniteDimensional E T := hfin
  letI : Module.Free E T := Module.Free.of_divisionRing E T
  have hyT : y ∈ T := hy
  have hint_sub : IsIntegral E (⟨y, hyT⟩ : T) := IsIntegral.of_finite E _
  have hint : IsIntegral E y :=
    (IntermediateField.isIntegral_iff (K:=E) (L:=ℝ) (S:=T)).1 hint_sub
  have hle' : (minpoly E (⟨y,hyT⟩ : T)).natDegree ≤ 2 :=
    (minpoly.natDegree_le (⟨y,hyT⟩ : T)).trans hrel
  have heq := minpoly.algHom_eq T.val T.val.injective (⟨y,hyT⟩ : T)
  have hle'' : (minpoly E y).natDegree ≤ 2 := by
    have heqn := congrArg Polynomial.natDegree heq
    change (minpoly E y).natDegree ≤ 2
    change (minpoly E y).natDegree = _ at heqn
    exact heqn.trans_le hle'
  exact root_small_constructible E hE y hint hle''

private lemma abelian_two_construct (k : ℕ) :
    ∀ (F : IntermediateField ℚ ℝ),
      FiniteDimensional ℚ F → IsAbelianGalois ℚ F →
      Module.finrank ℚ F = 2^k →
      ∀ y:ℝ, y ∈ F → IsConstructible y := by
  induction k with
  | zero =>
    intro F hfin hab hr y hy
    letI : FiniteDimensional ℚ F := hfin
    have hfbot : F = (⊥ : IntermediateField ℚ ℝ) :=
      (IntermediateField.finrank_eq_one_iff).1 (by simpa using hr)
    rw [hfbot] at hy
    obtain ⟨q, hq⟩ := (IntermediateField.mem_bot).1 hy
    rw [← hq]
    exact IsConstructible.base q
  | succ k ih =>
    classical
    intro F hfin hab hr y hy
    letI : FiniteDimensional ℚ F := hfin
    letI : IsAbelianGalois ℚ F := hab
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2^ (1:ℕ) ∣ Nat.card (F ≃ₐ[ℚ] F) := by
      rw [IsGalois.card_aut_eq_finrank, hr]
      exact pow_dvd_pow 2 (Nat.le_add_left 1 k)
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := (F ≃ₐ[ℚ] F)) 2 hdvd
    have hH' : Nat.card H = 2 := by simpa using hH
    let E' : IntermediateField ℚ F := IntermediateField.fixedField H
    have erel : Module.finrank E' F = 2 := by
      dsimp [E']
      rw [IntermediateField.finrank_fixedField_eq_card, hH']
    let E : IntermediateField ℚ ℝ := IntermediateField.lift E'
    have hle : E ≤ F := IntermediateField.lift_le E'
    letI : FiniteDimensional ℚ E' := by infer_instance
    letI : FiniteDimensional E' F := by infer_instance
    have emul := Module.finrank_mul_finrank ℚ E' F
    have erank' : Module.finrank ℚ E' = 2^k := by
      rw [erel] at emul
      -- cancel two in the tower formula
      omega
    letI : FiniteDimensional ℚ E :=
      (IntermediateField.liftAlgEquiv E').toLinearEquiv.finiteDimensional
    have eeq : Module.finrank ℚ E' = Module.finrank ℚ E :=
      LinearEquiv.finrank_eq (IntermediateField.liftAlgEquiv E').toLinearEquiv
    have erank : Module.finrank ℚ E = 2^k := eeq ▸ erank'
    have habF : IsAbelianGalois ℚ F := inferInstance
    letI : IsAbelianGalois ℚ E :=
      @IsAbelianGalois.of_algHom ℚ E F _ _ _ _ _
        (IntermediateField.inclusion hle) habF
    have econs : ∀ z:ℝ, z ∈ E → IsConstructible z := ih E (by infer_instance)
      (inferInstance : IsAbelianGalois ℚ E) erank
    let T : IntermediateField E ℝ := IntermediateField.extendScalars hle
    letI : FiniteDimensional ℚ T := hfin
    letI : IsScalarTower ℚ E T := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    letI : FiniteDimensional E T := FiniteDimensional.right ℚ E T
    letI : Module.Free ℚ E := Module.Free.of_divisionRing ℚ E
    letI : Module.Free E T := Module.Free.of_divisionRing E T
    have tmul := Module.finrank_mul_finrank ℚ E T
    have frankT : Module.finrank ℚ T = Module.finrank ℚ F := by rfl
    have trankle : Module.finrank E T ≤ 2 := by
      rw [erank] at tmul
      rw [frankT, hr] at tmul
      -- arithmetic
      have : Module.finrank E T = 2 := by
        have hp : 0 < 2^k := pow_pos (by decide : 0 < (2:ℕ)) _
        -- successor
        simp [pow_succ] at tmul
        omega
      omega
    exact quadratic_extend_constructible E F hle trankle econs y hy

private lemma cyclo_container (n : ℕ) (hn : 0 < n) :
    ∃ L : IntermediateField ℚ ℂ,
      ((tt n).cos : ℂ) ∈ L ∧ IsAbelianGalois ℚ L ∧ FiniteDimensional ℚ L := by
  let z : ℂ := zz n
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({z}:Set ℂ)
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hz : IsPrimitiveRoot z n := by
    simpa [z, zz] using Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)
  letI : IsCyclotomicExtension {n} ℚ L :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin n ℚ ℂ L hz).2 rfl
  letI : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {n} ℚ L
  letI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {n} ℚ L
  have zm : z ∈ L := (IntermediateField.subset_adjoin ℚ ({z}:Set ℂ)) (by simp)
  have hm : ((tt n).cos : ℂ) ∈ L := by
    rw [← zz_add_inv n]
    change (z + z⁻¹) / (2:ℂ) ∈ L
    have htwo : (2:ℂ) ∈ L := by convert L.algebraMap_mem (2:ℚ) using 1 <;> norm_num
    exact L.div_mem (L.add_mem zm (L.inv_mem zm)) htwo
  exact ⟨L, hm, inferInstance, inferInstance⟩



-- The real field generated by the cosine of a cyclotomic angle embeds in
-- the (complex) cyclotomic field.  Since that field is abelian Galois,
-- so is this real field (with its abstract `ℚ`-algebra structure).  In
-- particular it is finite dimensional.  We spell out the embedding: an
-- element of the real adjoin is first sent by `ofReal`, and the fact that
-- its image belongs to `L` is just `adjoin_map`.
private lemma real_cos_field_finite_abelian (n : ℕ) (hn : 0 < n) :
    let c : ℝ := (tt n).cos
    let F : IntermediateField ℚ ℝ :=
      IntermediateField.adjoin ℚ ({c} : Set ℝ)
    FiniteDimensional ℚ F ∧ IsAbelianGalois ℚ F := by
  classical
  dsimp
  -- get the complex cyclotomic container of the element
  obtain ⟨L, hcL, habL, hfinL⟩ := cyclo_container n hn
  letI : IsAbelianGalois ℚ L := habL
  letI : FiniteDimensional ℚ L := hfinL
  let c : ℝ := (tt n).cos
  let F : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ ({c} : Set ℝ)
  let g : ℝ →ₐ[ℚ] ℂ := Complex.ofRealHom.toRatAlgHom
  -- Mapping the real adjoin by the inclusion `ℝ → ℂ` gives the complex
  -- adjoin of the same real element, which is contained in `L`.
  have hmap : F.map g ≤ L := by
    have hgen : IntermediateField.adjoin ℚ ({(c : ℂ)} : Set ℂ) ≤ L :=
      (IntermediateField.adjoin_simple_le_iff).2 (by
        -- `hcL` is stated for `(tt n).cos`
        simpa [c] using hcL)
    -- and the map of the real adjoin is that adjoin
    simpa [F, IntermediateField.adjoin_map, Set.image_singleton, g]
      using hgen
  have hmem (x : F) :
      (g.comp F.val) x ∈ L := by
    have hxmap : g (x : ℝ) ∈ F.map g :=
      (IntermediateField.map_mem_map (S:=F) g).2 x.property
    -- the two expressions are definitional the same
    exact hmap hxmap
  -- codomain-restrict the above inclusion to `L`
  let f : F →ₐ[ℚ] L :=
    (g.comp F.val).codRestrict L.toSubalgebra (fun x => hmem x)
  have hf_inj : Function.Injective f := f.injective
  let hfinF : FiniteDimensional ℚ F :=
    FiniteDimensional.of_injective f.toLinearMap hf_inj
  -- subextensions (or, equivalently, fields with an embedding) of an
  -- abelian Galois extension are abelian Galois over the base.
  let habF : IsAbelianGalois ℚ F :=
    @IsAbelianGalois.of_algHom ℚ F L _ _ _ _ _ f (inferInstance : IsAbelianGalois ℚ L)
  exact ⟨hfinF, habF⟩


-- Consequently the degree of that real simple extension is a two power
-- whenever the full cyclotomic degree is.  We do not need to know whether
-- the relative quadratic is trivial: in either case the real degree divides
-- the totient.
private lemma real_cos_adjoin_finrank_two_power
    (n : ℕ) (hn : 0 < n) (hpow : ∃ k : ℕ, n.totient = 2 ^ k) :
    ∃ k : ℕ,
      Module.finrank ℚ
        (IntermediateField.adjoin ℚ ({(tt n).cos} : Set ℝ)) = 2 ^ k := by
  classical
  let c : ℝ := (tt n).cos
  let F : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ ({c} : Set ℝ)
  obtain ⟨hfinF, habF⟩ := real_cos_field_finite_abelian n hn
  -- Record this as an instance while extracting the integrality of the
  -- generator.  It follows also from the embedding above.
  letI : FiniteDimensional ℚ F := by
    exact hfinF
  have hcF : c ∈ F :=
    (IntermediateField.subset_adjoin ℚ ({c} : Set ℝ)) (by simp)
  have hcintsub : IsIntegral ℚ (⟨c, hcF⟩ : F) :=
    IsIntegral.of_finite ℚ _
  have hcint : IsIntegral ℚ c :=
    (IntermediateField.isIntegral_iff (K:=ℚ) (L:=ℝ) (S:=F)).1 hcintsub
  obtain ⟨K, hK⟩ := hpow
  obtain ⟨d, hd, hrel⟩ := tot_rel n hn
  -- Thus the degree `d` is a divisor of `2^K` in both alternatives.
  have hdvd : d ∣ 2 ^ K := by
    rcases hrel with h1 | h2
    · -- here the two degrees coincide
      rw [← hK]
      exact h1.symm ▸ dvd_refl d
    · -- here the totient is `d*2`
      have : d ∣ n.totient := by
        rw [h2]
        exact dvd_mul_right _ _
      simpa [hK] using this
  obtain ⟨j, hj, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨j, ?_⟩
  -- the usual finrank of a simple integral extension is its minimal
  -- polynomial's degree
  change Module.finrank ℚ F = 2 ^ j
  have hdeg : (minpoly ℚ c).natDegree = d := by
    simpa [c] using hd
  rw [IntermediateField.adjoin.finrank hcint]
  -- `F` is that simple adjoin
  -- after rewriting, substitute the computed degree
  exact hdeg.trans hdj


/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem gauss_wantzel_constructible_polygon (n : ℕ) (hn : 3 ≤ n) :
    IsConstructible (Real.cos (2 * Real.pi / n)) ↔ GaussWantzelNumber n :=
/-ResultProofBegin-/by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < (3:ℕ)) hn
  -- The arithmetic part of the Wantzel criterion is exactly that the
  -- totient is a power of two.  We keep it separate from the geometric,
  -- cyclotomic assertion.
  have hcyc : IsConstructible (Real.cos (2 * Real.pi / n)) ↔
        ∃ k : ℕ, n.totient = 2 ^ k := by
    by_cases htwo : ∃ r : ℕ, n = 2 ^ r
    · obtain ⟨r, rfl⟩ := htwo
      have hrpos : 0 < r := by
        by_contra hz
        have hz' : r = 0 := Nat.eq_zero_of_not_pos hz
        simp [hz'] at hn
      have hr1 : 1 ≤ r := hrpos
      constructor
      · intro _
        refine ⟨r - 1, ?_⟩
        simpa using (Nat.totient_prime_pow Nat.prime_two hrpos)
      · intro _
        exact constructible_cos_two_pi_over_two_pow hr1
    · by_cases hthree : ∃ r : ℕ, n = 3 * 2 ^ r
      · obtain ⟨r, rfl⟩ := hthree
        constructor
        · intro _
          exact totient_three_mul_two_pow_is_two_power r
        · intro _
          exact constructible_cos_two_pi_over_three_mul_two_pow r
      · obtain ⟨r, m, hmodd, hdecomp⟩ :=
          Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hnpos)
        have hm1 : m ≠ 1 := by
          intro hm
          have hn' : n = 2^r := by simpa [hm] using hdecomp
          exact htwo ⟨r, hn'⟩
        have hmpos : 0 < m := Odd.pos hmodd
        have hm2 : 2 ≤ m := by omega
        have hreord : n = m * 2^r := hdecomp.trans (Nat.mul_comm _ _)
        have hm3 : m ≠ 3 := by
          intro h3
          have hn' : n = 3 * 2^r := by simpa [h3, Nat.mul_comm] using hdecomp
          exact hthree ⟨r, hn'⟩
        have hm5 : 5 ≤ m := by
          obtain ⟨j, hj⟩ := hmodd
          have : 2 * j + 1 = m := hj.symm
          omega
        have hoddcyc :
            IsConstructible (Real.cos ((2:ℝ) * Real.pi / (m:ℕ))) ↔
              ∃ k : ℕ, m.totient = 2 ^ k := by
          by_cases hm_eq : m = 5
          · subst m
            constructor
            · intro _
              refine ⟨2, ?_⟩
              norm_num [Nat.totient_prime Nat.prime_five]
            · intro _
              exact constructible_cos_two_pi_over_five
          · by_cases hm_fifteen : m = 15
            · subst m
              constructor
              · intro _
                refine ⟨3, ?_⟩
                decide
              · intro _
                exact constructible_cos_two_pi_over_fifteen
            · constructor
              · intro hc
                have hd : ∃ k:ℕ, (minpoly ℚ ((tt m).cos)).natDegree = 2^k :=
                  constructible_minpoly_degree_power (by simpa [tt] using hc)
                obtain ⟨k,hk⟩ := hd
                obtain ⟨d, hd', hcases⟩ := tot_rel m hmpos
                have hdk : d = 2^k := hd'.symm.trans hk
                rcases hcases with h1 | h2
                · exact ⟨k, h1.trans hdk⟩
                · refine ⟨k+1, ?_⟩
                  rw [h2, hdk, pow_succ]
              · intro hpower
                classical
                let c : ℝ := (tt m).cos
                let F : IntermediateField ℚ ℝ :=
                  IntermediateField.adjoin ℚ ({c} : Set ℝ)
                obtain ⟨hfinF, habF⟩ := real_cos_field_finite_abelian m hmpos
                obtain ⟨j, hj⟩ :=
                  real_cos_adjoin_finrank_two_power m hmpos hpower
                have hdegF : Module.finrank ℚ F = 2 ^ j := by
                  simpa [F, c] using hj
                have hcF : c ∈ F :=
                  (IntermediateField.subset_adjoin ℚ ({c} : Set ℝ)) (by simp)
                have hcons : IsConstructible c :=
                  abelian_two_construct j F hfinF habF hdegF c hcF
                simpa [c, tt] using hcons
        rw [hreord]
        exact (constructible_mul_two_pow_equiv m r hm2).trans
          (hoddcyc.trans (totient_mul_two_pow_power_iff m r hmodd hmpos).symm)
  exact hcyc.trans (gaussWantzel_iff_totient_two_power n hnpos).symm
  /-ResultProofEnd-/
/-ResultEnd-/

end Submission
