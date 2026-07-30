import Submission.OddOrder.MathlibSupport.Extraspecial

/-!
The center quotient of a special or extraspecial group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

namespace IsSpecial

/-- A special group has nilpotency class at most two. -/
theorem commutator_le_center (hG : IsSpecial G) :
    _root_.commutator G ≤ Subgroup.center G :=
  hG.commutator_eq_center.le

/-- The quotient of a special group by its center is commutative. -/
theorem quotient_center_isMulCommutative (hG : IsSpecial G) :
    IsMulCommutative (G ⧸ Subgroup.center G) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    hG.commutator_le_center

end IsSpecial

namespace IsExtraspecial

/-- The center of an extraspecial group is proper. -/
theorem center_ne_top (hG : IsExtraspecial G) : Subgroup.center G ≠ ⊤ := by
  intro htop
  apply hG.not_isMulCommutative
  exact Subgroup.center_eq_top_iff.mp htop

/-- The quotient of an extraspecial group by its center is nontrivial. -/
theorem quotient_center_nontrivial (hG : IsExtraspecial G) :
    Nontrivial (G ⧸ Subgroup.center G) :=
  QuotientGroup.nontrivial_iff.mpr hG.center_ne_top

/-- The quotient of an extraspecial group by its center is commutative. -/
theorem quotient_center_isMulCommutative (hG : IsExtraspecial G) :
    IsMulCommutative (G ⧸ Subgroup.center G) :=
  hG.toIsSpecial.quotient_center_isMulCommutative

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
