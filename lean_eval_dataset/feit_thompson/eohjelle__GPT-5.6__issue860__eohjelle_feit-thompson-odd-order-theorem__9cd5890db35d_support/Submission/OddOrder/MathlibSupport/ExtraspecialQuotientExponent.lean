import Mathlib.GroupTheory.Exponent
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientAlternating
import Submission.OddOrder.MathlibSupport.FrattiniPGroup

/-!
Prime exponent of the center quotient of an extraspecial `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

namespace IsExtraspecial

variable {p : ℕ} [Fact p.Prime]

/-- Every element of an extraspecial `p`-group modulo its center has `p`th
power one. -/
theorem quotient_center_pow_prime (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (x : G ⧸ Subgroup.center G) : x ^ p = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  change ((x ^ p : G) : G ⧸ Subgroup.center G) = 1
  apply (QuotientGroup.eq_one_iff (x ^ p)).mpr
  rw [← hG.toIsSpecial.frattini_eq_center]
  exact IsPGroup.pow_prime_mem_frattini hpG x

/-- Every nonidentity class in the center quotient has order exactly `p`. -/
theorem orderOf_quotient_center_eq_prime (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) {x : G ⧸ Subgroup.center G} (hx : x ≠ 1) :
    orderOf x = p :=
  orderOf_eq_prime (hG.quotient_center_pow_prime hpG x) hx

/-- The center quotient of an extraspecial `p`-group has exponent `p`. -/
theorem quotient_center_exponent_eq_prime (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) :
    Monoid.exponent (G ⧸ Subgroup.center G) = p := by
  letI : Nontrivial (G ⧸ Subgroup.center G) :=
    hG.quotient_center_nontrivial
  exact (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr
    (fun _ hx ↦ hG.orderOf_quotient_center_eq_prime hpG hx)

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
