import Submission.OddOrder.MathlibSupport.PCore

/-!
Closure of finite p-groups under extensions.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem isPGroup_of_normal_subgroup_and_quotient
    {p : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) : IsPGroup p G := by
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  apply IsPGroup.of_card
  rw [N.card_eq_card_quotient_mul_card_subgroup, hm, hn, ← pow_add]

end Submission.OddOrder.MathlibSupport
