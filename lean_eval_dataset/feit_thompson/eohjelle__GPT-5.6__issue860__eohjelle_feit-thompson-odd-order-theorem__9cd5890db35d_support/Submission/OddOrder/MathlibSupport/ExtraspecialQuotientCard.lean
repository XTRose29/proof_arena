import Submission.OddOrder.MathlibSupport.ExtraspecialQuotient

/-!
Cardinality of the center quotient of an extraspecial `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

namespace IsExtraspecial

omit [Finite G] in
/-- The center quotient of a finite `p`-group is again a `p`-group. -/
theorem quotient_center_isPGroup (_hG : IsExtraspecial G)
    {p : ℕ} (hpG : IsPGroup p G) :
    IsPGroup p (G ⧸ Subgroup.center G) :=
  hpG.to_quotient (Subgroup.center G)

/-- An extraspecial `p`-group of order `p ^ (2 * n + 1)` has center quotient
of order `p ^ (2 * n)`. -/
theorem quotient_center_card_eq (hG : IsExtraspecial G)
    {p n : ℕ} [Fact p.Prime] (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1)) :
    Nat.card (G ⧸ Subgroup.center G) = p ^ (2 * n) := by
  have hcenter : Nat.card (Subgroup.center G) = p := hG.center_card_eq hpG
  apply Nat.mul_right_cancel (Fact.out : p.Prime).pos
  calc
    Nat.card (G ⧸ Subgroup.center G) * p =
        Nat.card (G ⧸ Subgroup.center G) *
          Nat.card (Subgroup.center G) := by rw [hcenter]
    _ = Nat.card G :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center G)).symm
    _ = p ^ (2 * n + 1) := hcard
    _ = p ^ (2 * n) * p := by rw [pow_succ]

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
