import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic

/-!
Parity exclusion for the exceptional order in Bender--Glauberman
Theorem 2.5.
-/

namespace Submission.OddOrder.MathlibSupport

/-- An odd natural number cannot be one more than a power of an odd
natural number. -/
theorem odd_ne_odd_pow_add_one {h p n : ℕ} (hh : Odd h) (hp : Odd p) :
    h ≠ p ^ n + 1 := by
  intro heq
  have heven : Even h := by
    rw [heq]
    exact hp.pow.add_one
  exact (Nat.not_even_iff_odd.mpr hh) heven

/-- Prime-base form of `odd_ne_odd_pow_add_one`. -/
theorem odd_ne_prime_pow_add_one {h p n : ℕ} (hh : Odd h)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    h ≠ p ^ n + 1 :=
  odd_ne_odd_pow_add_one hh (hp.odd_of_ne_two hp2)

end Submission.OddOrder.MathlibSupport
