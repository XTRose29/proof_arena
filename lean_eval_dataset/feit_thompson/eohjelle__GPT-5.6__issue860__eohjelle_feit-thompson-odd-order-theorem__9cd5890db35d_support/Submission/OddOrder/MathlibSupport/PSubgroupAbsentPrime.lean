import Mathlib.GroupTheory.PGroup

/-!
Triviality of primary subgroups when their prime is absent from the ambient
group order.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A finite `p`-subgroup of `G` is trivial if `p` does not divide the order
of `G`. -/
theorem subgroup_eq_bot_of_isPGroup_of_not_dvd_natCard
    {p : ℕ} [Fact p.Prime] (H : Subgroup G) (hH : IsPGroup p H)
    (hpG : ¬p ∣ Nat.card G) :
    H = ⊥ := by
  rw [← Subgroup.card_eq_one]
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  cases n with
  | zero => simpa using hn
  | succ n =>
      exfalso
      apply hpG
      have hpH : p ∣ Nat.card H := by
        rw [hn]
        exact dvd_pow_self p (Nat.succ_ne_zero n)
      exact hpH.trans H.card_subgroup_dvd_card

end Submission.OddOrder.MathlibSupport
