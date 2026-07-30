import Mathlib.GroupTheory.Frattini
import Submission.OddOrder.MathlibSupport.PGroupCenter

/-!
Mathlib-native special and extraspecial finite groups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- A finite group is special when its Frattini subgroup and commutator are
both equal to its center. -/
structure IsSpecial (G : Type u) [Group G] : Prop where
  frattini_eq_center : frattini G = Subgroup.center G
  commutator_eq_center : _root_.commutator G = Subgroup.center G

/-- A finite group is extraspecial when it is special and its center has
prime order. -/
structure IsExtraspecial (G : Type u) [Group G] : Prop extends IsSpecial G where
  center_card_prime : (Nat.card (Subgroup.center G)).Prime

namespace IsExtraspecial

omit [Finite G] in
/-- The center of an extraspecial group is nontrivial. -/
theorem center_ne_bot (hG : IsExtraspecial G) : Subgroup.center G ≠ ⊥ := by
  intro hbot
  apply (IsExtraspecial.center_card_prime hG).ne_one
  simp [hbot]

omit [Finite G] in
/-- An extraspecial group is nontrivial. -/
theorem nontrivial (hG : IsExtraspecial G) : Nontrivial G := by
  haveI : Nontrivial (Subgroup.center G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (center_ne_bot hG)
  exact Function.Injective.nontrivial (Subgroup.center G).subtype_injective

omit [Finite G] in
/-- The commutator subgroup of an extraspecial group is nontrivial. -/
theorem commutator_ne_bot (hG : IsExtraspecial G) :
    _root_.commutator G ≠ ⊥ := by
  rw [hG.toIsSpecial.commutator_eq_center]
  exact center_ne_bot hG

omit [Finite G] in
/-- An extraspecial group is not commutative. -/
theorem not_isMulCommutative (hG : IsExtraspecial G) : ¬IsMulCommutative G := by
  intro hcomm
  letI : IsMulCommutative G := hcomm
  exact commutator_ne_bot hG (_root_.commutator_eq_bot G)

/-- If an extraspecial group is a `p`-group, then its center has order
exactly `p`. -/
theorem center_card_eq (hG : IsExtraspecial G)
    {p : ℕ} [Fact p.Prime] (hpG : IsPGroup p G) :
    Nat.card (Subgroup.center G) = p := by
  have hpCenter : IsPGroup p (Subgroup.center G) :=
    hpG.to_subgroup (Subgroup.center G)
  letI : Nontrivial (Subgroup.center G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (center_ne_bot hG)
  obtain ⟨n, _hn, hcard⟩ := hpCenter.nontrivial_iff_card.mp inferInstance
  have hpowPrime : (p ^ n).Prime := by
    simpa only [hcard] using IsExtraspecial.center_card_prime hG
  have hn : n = 1 := hpowPrime.eq_one_of_pow
  rw [hcard, hn, pow_one]

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
