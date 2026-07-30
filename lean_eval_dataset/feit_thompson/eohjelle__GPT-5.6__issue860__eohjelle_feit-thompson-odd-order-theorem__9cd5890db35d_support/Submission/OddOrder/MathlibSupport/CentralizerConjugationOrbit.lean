import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.SubgroupConjugationOrbit

/-!
Center-quotient orbit cardinality from ambient centralizer equalities.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {A : Type u} [Group A]

/-- The `card_clPqH` orbit-cardinality argument in terms of internal
centralizers represented in the ambient group. -/
theorem natCard_centerQuotient_orbit_eq_natCard_of_centralizers
    (P H : Subgroup A) (hHP : H ≤ Subgroup.normalizer P) [Finite H]
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hcenter : H ≤ Subgroup.centralizer (centerWithin P : Set A))
    (hcentralizer : ∀ h : H, h ≠ 1 ->
      centralizerWithin P (Subgroup.zpowers (h : A)) = centerWithin P)
    (q : P ⧸ Subgroup.center P) (hq : q ≠ 1) :
    letI := subgroupConjugationAction P H hHP
    letI := subgroupConjugationCenterQuotientAction P H hHP
    Nat.card (MulAction.orbit H q) = Nat.card H := by
  apply natCard_centerQuotient_orbit_eq_natCard_of_conjugation
    P H hHP hcop
  · intro h z
    have hz : ((z : P) : A) ∈ centerWithin P := by
      rw [← map_center_eq_centerWithin P]
      exact ⟨(z : P), z.property, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hcenter h.property) _ hz).symm
  · intro h hh p hp
    have hcomm : Commute (h : A) (p : A) := by
      apply (mul_inv_eq_iff_eq_mul.mp ?_)
      simpa [mul_assoc] using hp
    have hpcentralizer : (p : A) ∈
        centralizerWithin P (Subgroup.zpowers (h : A)) := by
      refine ⟨p.property, ?_⟩
      change ∀ y ∈ Subgroup.zpowers (h : A), y * (p : A) = (p : A) * y
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hcomm.zpow_left k).eq
    have hpcenterWithin : (p : A) ∈ centerWithin P := by
      rw [← hcentralizer h hh]
      exact hpcentralizer
    have hpmap : (p : A) ∈ (Subgroup.center P).map P.subtype := by
      rw [map_center_eq_centerWithin P]
      exact hpcenterWithin
    obtain ⟨z, hz, hzp⟩ := hpmap
    have hpz : p = z := Subtype.ext hzp.symm
    simpa [hpz] using hz
  · exact hq

end Submission.OddOrder.MathlibSupport
