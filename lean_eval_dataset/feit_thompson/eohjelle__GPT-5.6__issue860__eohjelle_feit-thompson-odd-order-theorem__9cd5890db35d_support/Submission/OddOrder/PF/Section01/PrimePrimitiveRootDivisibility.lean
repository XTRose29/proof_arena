import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Submission.OddOrder.MathlibSupport.AlgebraicIntegerCongruence

/-!
# Peterfalvi 1.10(b): divisibility from a primitive-root congruence

If an integer is divisible, in the ring of all algebraic integers, by
`1 - eps` for a primitive `p`-th root of unity `eps`, then it is divisible
by the prime `p`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators
open Submission.OddOrder.MathlibSupport

universe u

/-- Peterfalvi 1.10(b), generalized from
`PFsection1.v:int_eqAmod_prime_prim` to an arbitrary algebraically closed
characteristic-zero field over `ℚ`.

This follows the source product argument.  Each conjugate
`1 - eps ^ j`, for `0 < j < p`, divides `n` by an algebraic integer;
multiplying the resulting quotients and using
`prod_one_sub_pow_eq_order` shows that `n ^ (p - 1) / p` is an algebraic
integer.  Since it is rational it is an integer, so primality forces
`p ∣ n`. -/
theorem int_eqAmod_prime_prim_of_isAlgClosed
    {K : Type u} [Field K] [Algebra ℚ K] [IsAlgClosed K] [CharZero K]
    {p : ℕ} {eps : K} (pr_eps : IsPrimitiveRoot eps p)
    (hp : p.Prime) (n : ℤ)
    (hn : IsIntegralModEq (1 - eps) (n : K) 0) :
    (p : ℤ) ∣ n := by
  classical
  let m := p - 1
  have hpPos : 0 < p := hp.pos
  have hpOne : 1 ≤ p := hp.one_le
  have hpSucc : m + 1 = p := by
    simpa [m] using Nat.sub_add_cancel hpOne
  have hepsInt : IsIntegral ℤ eps :=
    IsIntegral.of_pow hpPos (pr_eps.pow_eq_one ▸ isIntegral_one)
  obtain ⟨z, hzInt, hnz⟩ := hn
  simp only [sub_zero] at hnz

  have hfactorInt (k : ℕ) (hk : k ∈ Finset.range m) :
      IsIntegral ℤ ((n : K) / (1 - eps ^ (k + 1))) := by
    have hklt : k < m := Finset.mem_range.mp hk
    have hjlt : k + 1 < p := by
      dsimp [m] at hklt
      omega
    have hjne : k + 1 ≠ 0 := by omega
    have hjcop : (k + 1).Coprime p :=
      (Nat.coprime_of_lt_prime hjne hjlt hp).symm
    obtain ⟨r, _hrlt, hrmod⟩ :=
      Nat.exists_mul_mod_eq_one_of_coprime hjcop hp.one_lt
    have hmod : (k + 1) * r ≡ 1 [MOD p] := by
      change ((k + 1) * r) % p = 1 % p
      rw [Nat.mod_eq_of_lt hp.one_lt]
      exact hrmod
    have hepsPow : (eps ^ (k + 1)) ^ r = eps := by
      rw [← pow_mul]
      simpa using pow_eq_pow_of_modEq hmod pr_eps.pow_eq_one
    let S : K := ∑ i ∈ Finset.range r, (eps ^ (k + 1)) ^ i
    have hSInt : IsIntegral ℤ S := by
      dsimp [S]
      apply IsIntegral.sum
      intro i _hi
      exact (hepsInt.pow (k + 1)).pow i
    have hdenNe : 1 - eps ^ (k + 1) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact (pr_eps.pow_of_coprime (k + 1) hjcop).ne_one hp.one_lt |>.symm
    have hgeom : (1 - eps ^ (k + 1)) * S = 1 - eps := by
      calc
        (1 - eps ^ (k + 1)) * S =
            -((eps ^ (k + 1) - 1) * S) := by ring
        _ = -((eps ^ (k + 1)) ^ r - 1) := by
          rw [show (eps ^ (k + 1) - 1) * S =
              (eps ^ (k + 1)) ^ r - 1 by
            simpa [S] using mul_geom_sum (eps ^ (k + 1)) r]
        _ = 1 - eps := by rw [hepsPow]; ring
    have hratio : (1 - eps) / (1 - eps ^ (k + 1)) = S := by
      apply (div_eq_iff hdenNe).mpr
      simpa [mul_comm] using hgeom.symm
    have hquot : (n : K) / (1 - eps ^ (k + 1)) = S * z := by
      rw [hnz]
      calc
        ((1 - eps) * z) / (1 - eps ^ (k + 1)) =
            ((1 - eps) / (1 - eps ^ (k + 1))) * z := by ring
        _ = S * z := by rw [hratio]
    rw [hquot]
    exact hSInt.mul hzInt

  have hdenProd :
      ∏ k ∈ Finset.range m, (1 - eps ^ (k + 1)) = (p : K) := by
    have pr_eps_m : IsPrimitiveRoot eps (m + 1) := by
      simpa only [hpSucc] using pr_eps
    have hprod := pr_eps_m.prod_one_sub_pow_eq_order
    calc
      ∏ k ∈ Finset.range m, (1 - eps ^ (k + 1)) = (m : K) + 1 := hprod
      _ = (p : K) := by norm_cast
  have hprodInt :
      IsIntegral ℤ
        (∏ k ∈ Finset.range m, (n : K) / (1 - eps ^ (k + 1))) := by
    exact IsIntegral.prod _ hfactorInt
  have hprodEq :
      (∏ k ∈ Finset.range m, (n : K) / (1 - eps ^ (k + 1))) =
        (n : K) ^ m / (p : K) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
      hdenProd]
  have hpowDivInt : IsIntegral ℤ ((n : K) ^ m / (p : K)) := by
    rw [← hprodEq]
    exact hprodInt

  let q : ℚ := ((n ^ m : ℤ) : ℚ) / ((p : ℤ) : ℚ)
  have hqIntK : IsIntegral ℤ (q : K) := by
    simpa [q] using hpowDivInt
  have hqInt : IsIntegral ℤ q := IsIntegral.ratCast_iff.mp hqIntK
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqInt
  have hqDen : q.den = 1 := by
    rw [← ha]
    simp
  have hpNeInt : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpDvdPow : (p : ℤ) ∣ n ^ m := by
    exact (Rat.den_div_intCast_eq_one_iff (n ^ m) (p : ℤ) hpNeInt).mp
      (by simpa [q] using hqDen)
  exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpDvdPow

/-- Peterfalvi 1.10(b), source `PFsection1.v:int_eqAmod_prime_prim`.

This retains the original algebraic-closure interface and delegates to
`int_eqAmod_prime_prim_of_isAlgClosed`. -/
theorem int_eqAmod_prime_prim
    {K : Type u} [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
    {p : ℕ} {eps : K} (pr_eps : IsPrimitiveRoot eps p)
    (hp : p.Prime) (n : ℤ)
    (hn : IsIntegralModEq (1 - eps) (n : K) 0) :
    (p : ℤ) ∣ n := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  exact int_eqAmod_prime_prim_of_isAlgClosed pr_eps hp n hn

end

end Submission.OddOrder.PF
