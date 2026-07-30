import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientFinrank

/-!
Normal-subgroup and faithfulness tests for finite `p`-groups and extraspecial
groups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A homomorphism from a finite `p`-group is injective exactly when its
restriction to the center is injective. -/
theorem IsPGroup.monoidHom_injective_iff_center_restrict
    (hpG : IsPGroup p G) {M : Type v} [MulOneClass M] (f : G →* M) :
    Function.Injective f ↔
      Function.Injective (f.restrict (Subgroup.center G)) := by
  constructor
  · intro hf
    exact hf.comp (Subgroup.center G).subtype_injective
  · intro hcenter
    rw [← MonoidHom.ker_eq_bot_iff] at hcenter ⊢
    apply (normal_inf_center_eq_bot_iff hpG f.ker).mp
    apply disjoint_iff.mp
    apply Subgroup.subgroupOf_eq_bot.mp
    simpa only [MonoidHom.ker_restrict] using hcenter

namespace IsExtraspecial

/-- Every nontrivial normal subgroup of an extraspecial `p`-group contains
the center. -/
theorem center_le_normal_of_ne_bot (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    Subgroup.center G ≤ N := by
  letI : Fact (Nat.card (Subgroup.center G)).Prime :=
    ⟨hG.center_card_prime⟩
  rcases (N.subgroupOf (Subgroup.center G)).eq_bot_or_eq_top_of_prime_card with
    hbot | htop
  · have hdisjoint : Disjoint N (Subgroup.center G) :=
      Subgroup.subgroupOf_eq_bot.mp hbot
    have hinf : N ⊓ Subgroup.center G = ⊥ := disjoint_iff.mp hdisjoint
    exact False.elim (hN ((normal_inf_center_eq_bot_iff hpG N).mp hinf))
  · exact Subgroup.subgroupOf_eq_top.mp htop

/-- A normal subgroup of an extraspecial `p`-group is either trivial or
contains the center. -/
theorem normal_eq_bot_or_center_le (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (N : Subgroup G) [N.Normal] :
    N = ⊥ ∨ Subgroup.center G ≤ N := by
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · exact Or.inr (hG.center_le_normal_of_ne_bot hpG N hN)

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
