import Submission.OddOrder.MathlibSupport.Hall

/-!
Prime support of a nontrivial finite `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

namespace IsPGroup

variable {G : Type u} [Group G] {p : ℕ}

/-- The prime divisors of the cardinality of a nontrivial finite `p`-group
consist exactly of `p`.
-/
theorem primeSupport_natCard_eq_singleton [Finite G] [Nontrivial G]
    [Fact p.Prime] (hG : IsPGroup p G) :
    primeSupport (Nat.card G) = {p} := by
  ext q
  constructor
  · rintro ⟨hq, hqdiv⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
    rw [hn] at hqdiv
    have hqp : q = p :=
      Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqdiv
    simp [hqp]
  · intro hq
    have hqp : q = p := Set.mem_singleton_iff.mp hq
    subst q
    exact ⟨Fact.out,
      hG.card_eq_or_dvd.resolve_left (Finite.one_lt_card.ne')⟩

end IsPGroup

end Submission.OddOrder.MathlibSupport
