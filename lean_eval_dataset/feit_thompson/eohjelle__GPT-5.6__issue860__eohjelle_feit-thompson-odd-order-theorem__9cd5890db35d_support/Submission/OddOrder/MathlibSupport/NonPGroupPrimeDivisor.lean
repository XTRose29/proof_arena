import Mathlib.GroupTheory.PGroup

/-!
Selecting a prime divisor that witnesses failure to be a `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A finite group which is not a `p`-group has an order divisor prime
different from `p`. -/
theorem exists_prime_ne_dvd_natCard_of_not_isPGroup
    {p : ℕ} [Fact p.Prime] (hG : ¬IsPGroup p G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G := by
  by_contra hnone
  apply hG
  rw [IsPGroup.iff_card]
  have hcard : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hall : ∀ q ∈ (Nat.card G).primeFactorsList, q = p := by
    intro q hq
    obtain ⟨hqprime, hqdvd⟩ := (Nat.mem_primeFactorsList hcard).mp hq
    by_contra hqp
    exact hnone ⟨q, hqprime, hqp, hqdvd⟩
  use (Nat.card G).primeFactorsList.length
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem hall,
    Nat.prod_primeFactorsList hcard]

end Submission.OddOrder.MathlibSupport
