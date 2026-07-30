import Submission.OddOrder.MathlibSupport.Cardinality

/-!
Strict cardinality descent to proper finite subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem natCard_subgroup_lt_of_lt {H K : Subgroup G} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  refine lt_of_le_of_ne (Subgroup.card_le_of_le hHK.le) ?_
  intro hcard
  exact hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le hcard.ge)

theorem natCard_subgroup_lt_of_ne_top (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hle : Nat.card H ≤ Nat.card G :=
    Nat.le_of_dvd (Nat.card_pos (α := G)) H.card_subgroup_dvd_card
  exact lt_of_le_of_ne hle fun hcard =>
    hH (Subgroup.eq_top_of_card_eq H hcard)

theorem natCard_normalizer_lt_of_not_top_le {D : Set G}
    (hD : ¬(⊤ : Subgroup G) ≤ Subgroup.normalizer D) :
    Nat.card (Subgroup.normalizer D) < Nat.card G := by
  apply natCard_subgroup_lt_of_ne_top
  intro htop
  apply hD
  rw [htop]

/-- Quotienting a finite group by a nontrivial subgroup strictly decreases
cardinality. -/
theorem natCard_quotient_lt_of_ne_bot (H : Subgroup G) (hH : H ≠ ⊥) :
    Nat.card (G ⧸ H) < Nat.card G := by
  have hHcard : 1 < Nat.card H := H.one_lt_card_iff_ne_bot.mpr hH
  calc
    Nat.card (G ⧸ H) < Nat.card (G ⧸ H) * Nat.card H :=
      lt_mul_of_one_lt_right Nat.card_pos hHcard
    _ = Nat.card G :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup H).symm

omit [Finite G] in
/-- Passing to the subgroup type does not change the cardinality of an
included subgroup. -/
theorem natCard_subgroupOf_eq {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  have hcard := Subgroup.card_map_of_injective
    (K := H.subgroupOf K) K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hHK] at hcard
  exact hcard.symm

end Submission.OddOrder.MathlibSupport
