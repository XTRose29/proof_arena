import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.PrimeFin

/-!
# Maximal prime divisors

A nontrivial natural number has a largest prime divisor.  This small wrapper
packages the maximal element of its finite set of prime factors in the form
used by the odd-order development.
-/

namespace Submission.OddOrder.MathlibSupport

/-- Every natural number greater than one has a prime divisor dominating all
of its other prime divisors. -/
theorem exists_maximal_prime_divisor
    {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
      ∀ {q : ℕ}, q.Prime → q ∣ n → q ≤ p := by
  have hnonempty : n.primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr hn
  let p := n.primeFactors.max' hnonempty
  have hpMem : p ∈ n.primeFactors := by
    exact Finset.max'_mem n.primeFactors hnonempty
  refine ⟨p, Nat.prime_of_mem_primeFactors hpMem,
    Nat.dvd_of_mem_primeFactors hpMem, ?_⟩
  intro q hq hqdvd
  have hn0 : n ≠ 0 := (lt_trans Nat.zero_lt_one hn).ne'
  have hqMem : q ∈ n.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hn0).mpr ⟨hq, hqdvd⟩
  exact Finset.le_max' n.primeFactors q hqMem

end Submission.OddOrder.MathlibSupport
