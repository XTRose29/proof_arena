import Mathlib.FieldTheory.Finiteness
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientBilinear

/-!
Dimensions of the canonical modules attached to an extraspecial `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- A finite `ZMod p`-module of cardinality `p ^ d` has dimension `d`. -/
theorem zmod_finrank_eq_of_natCard {p d : ℕ} [Fact p.Prime]
    {V : Type u} [AddCommGroup V] [Finite V] [Module (ZMod p) V]
    (hcard : Nat.card V = p ^ d) : Module.finrank (ZMod p) V = d := by
  apply Nat.pow_right_injective ((Fact.out : p.Prime).two_le)
  calc
    p ^ Module.finrank (ZMod p) V = Nat.card V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    _ = p ^ d := hcard

variable {G : Type u} [Group G] [Finite G]

namespace IsExtraspecial

variable {p : ℕ} [Fact p.Prime]

/-- The canonical `ZMod p` module on the center is one-dimensional. -/
theorem center_finrank_eq_one (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) :
    letI : CommGroup (Subgroup.center G) := centerCommGroup
    letI : Module (ZMod p) (Additive (Subgroup.center G)) :=
      hG.centerZModModule hpG
    Module.finrank (ZMod p) (Additive (Subgroup.center G)) = 1 := by
  letI : CommGroup (Subgroup.center G) := centerCommGroup
  letI : Module (ZMod p) (Additive (Subgroup.center G)) :=
    hG.centerZModModule hpG
  apply zmod_finrank_eq_of_natCard
  calc
    Nat.card (Additive (Subgroup.center G)) =
        Nat.card (Subgroup.center G) :=
      Nat.card_congr Additive.ofMul
    _ = p := hG.center_card_eq hpG
    _ = p ^ 1 := (pow_one p).symm

/-- If the extraspecial group has order `p ^ (2 * n + 1)`, its canonical
center-quotient module has dimension `2 * n`. -/
theorem quotient_center_finrank_eq (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) {n : ℕ}
    (hcard : Nat.card G = p ^ (2 * n + 1)) :
    letI : CommGroup (G ⧸ Subgroup.center G) :=
      hG.toIsSpecial.quotientCenterCommGroup
    letI : Module (ZMod p) (Additive (G ⧸ Subgroup.center G)) :=
      hG.quotientCenterZModModule hpG
    Module.finrank (ZMod p) (Additive (G ⧸ Subgroup.center G)) =
      2 * n := by
  letI : CommGroup (G ⧸ Subgroup.center G) :=
    hG.toIsSpecial.quotientCenterCommGroup
  letI : Module (ZMod p) (Additive (G ⧸ Subgroup.center G)) :=
    hG.quotientCenterZModModule hpG
  apply zmod_finrank_eq_of_natCard
  calc
    Nat.card (Additive (G ⧸ Subgroup.center G)) =
        Nat.card (G ⧸ Subgroup.center G) :=
      Nat.card_congr Additive.ofMul
    _ = p ^ (2 * n) := hG.quotient_center_card_eq hpG hcard

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
