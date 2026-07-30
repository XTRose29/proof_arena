import Submission.OddOrder.MathlibSupport.CoprimeCentralQuotientOrbit

/-!
Actions by group automorphisms descend through characteristic subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulDistribMulAction G X]

/-- A characteristic subgroup is preserved by every element of a
multiplicative automorphism action, so the action descends to its quotient. -/
theorem characteristicQuotientAction (N : Subgroup X) [hN : N.Characteristic] :
    MulAction.QuotientAction G N where
  inv_mul_mem g a a' haa' := by
    rw [← smul_inv' g a, ← smul_mul']
    let phi : MulAut X := MulDistribMulAction.toMulAut G X g
    change phi (a⁻¹ * a') ∈ N
    have hmem := SetLike.ext_iff.mp
      (hN.fixed phi) (a⁻¹ * a')
    exact hmem.mpr haa'

/-- The center is characteristic, hence every automorphism action descends to
the center quotient. -/
theorem centerQuotientAction :
    MulAction.QuotientAction G (Subgroup.center X) :=
  characteristicQuotientAction (Subgroup.center X)

end Submission.OddOrder.MathlibSupport
