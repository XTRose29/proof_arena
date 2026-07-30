import Submission.OddOrder.MathlibSupport.NonPGroupPrimeDivisor

/-!
A prime-order element criterion for finite p-groups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A finite group is a p-group if it has no nontrivial elements of prime
order different from p. -/
theorem isPGroup_of_prime_order_elements {p : ℕ} [Fact p.Prime]
    (h : ∀ (q : ℕ), q.Prime → q ≠ p →
      ∀ g : G, orderOf g = q → g = 1) :
    IsPGroup p G := by
  by_contra hnot
  obtain ⟨q, hq, hqp, hqcard⟩ :=
    exists_prime_ne_dvd_natCard_of_not_isPGroup hnot
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqcard
  have hgOne : g = 1 := h q hq hqp g hg
  subst g
  simp at hg
  exact hq.ne_one hg.symm

end Submission.OddOrder.MathlibSupport
