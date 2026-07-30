import Submission.Zipper

namespace Submission.Helpers

/-- The join of a normal subgroup and a subnormal subgroup is subnormal.

This is the quotient-lifting step used in the standard proof of
Wielandt's local subnormality criterion. -/
theorem isSubnormal_sup_of_normal_left
    {G : Type*} [Group G] {A B : Subgroup G}
    (hA : A.Normal) (hB : B.IsSubnormal) :
    (A ⊔ B).IsSubnormal := by
  letI : A.Normal := hA
  have hq : (B.map (QuotientGroup.mk' A)).IsSubnormal :=
    hB.quotient
  have hc :=
    hq.comap (QuotientGroup.mk' A)
  simpa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] using hc

/-- Symmetric form of `isSubnormal_sup_of_normal_left`. -/
theorem isSubnormal_sup_of_normal_right
    {G : Type*} [Group G] {A B : Subgroup G}
    (hA : A.IsSubnormal) (hB : B.Normal) :
    (A ⊔ B).IsSubnormal := by
  rw [sup_comm]
  exact isSubnormal_sup_of_normal_left hB hA

end Submission.Helpers
