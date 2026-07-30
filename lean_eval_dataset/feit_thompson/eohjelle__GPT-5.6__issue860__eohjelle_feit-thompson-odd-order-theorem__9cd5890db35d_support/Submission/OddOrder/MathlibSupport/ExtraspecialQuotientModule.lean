import Mathlib.Algebra.Module.ZMod
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientExponent

/-!
Canonical `ZMod p` module structures attached to an extraspecial `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

namespace IsSpecial

/-- The commutative group structure on the quotient of a special group by
its center. -/
abbrev quotientCenterCommGroup (hG : IsSpecial G) :
    CommGroup (G ⧸ Subgroup.center G) := by
  letI : IsMulCommutative (G ⧸ Subgroup.center G) :=
    hG.quotient_center_isMulCommutative
  infer_instance

end IsSpecial

/-- The commutative group structure on the center of an arbitrary group. -/
abbrev centerCommGroup : CommGroup (Subgroup.center G) := by
  letI : IsMulCommutative (Subgroup.center G) := inferInstance
  infer_instance

namespace IsExtraspecial

variable {p : ℕ} [Fact p.Prime]

/-- Every central element of an extraspecial `p`-group has `p`th power
one. -/
theorem center_pow_prime (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (z : Subgroup.center G) : z ^ p = 1 := by
  rw [← hG.center_card_eq hpG]
  exact pow_card_eq_one'

/-- The canonical `ZMod p` module structure on the additive center
quotient. -/
abbrev quotientCenterZModModule (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) :
    letI : CommGroup (G ⧸ Subgroup.center G) :=
      hG.toIsSpecial.quotientCenterCommGroup
    Module (ZMod p) (Additive (G ⧸ Subgroup.center G)) := by
  letI : CommGroup (G ⧸ Subgroup.center G) :=
    hG.toIsSpecial.quotientCenterCommGroup
  exact AddCommGroup.zmodModule fun x ↦ by
    change x.toMul ^ p = 1
    exact hG.quotient_center_pow_prime hpG x.toMul

/-- The canonical `ZMod p` module structure on the additive center. -/
abbrev centerZModModule (hG : IsExtraspecial G) (hpG : IsPGroup p G) :
    letI : CommGroup (Subgroup.center G) := centerCommGroup
    Module (ZMod p) (Additive (Subgroup.center G)) := by
  letI : CommGroup (Subgroup.center G) := centerCommGroup
  exact AddCommGroup.zmodModule fun z ↦ by
    change z.toMul ^ p = 1
    exact hG.center_pow_prime hpG z.toMul

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
