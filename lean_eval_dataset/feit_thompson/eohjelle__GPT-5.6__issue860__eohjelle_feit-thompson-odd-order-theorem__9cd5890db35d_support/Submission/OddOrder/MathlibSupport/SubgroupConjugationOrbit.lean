import Submission.OddOrder.MathlibSupport.SubgroupConjugationQuotientAction

/-!
Full-size center-quotient orbits for coprime subgroup conjugation actions.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {A : Type u} [Group A]

/-- Coprime ambient conjugation with center as the fixed-point subgroup gives
full-size nonidentity orbits on the center quotient. -/
theorem natCard_centerQuotient_orbit_eq_natCard_of_conjugation
    (P H : Subgroup A) (hHP : H ≤ Subgroup.normalizer P) [Finite H]
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hcenter : ∀ h : H, ∀ z : Subgroup.center P,
      (h : A) * (z : P) = (z : P) * (h : A))
    (hfixed : ∀ h : H, h ≠ 1 -> ∀ p : P,
      (h : A) * (p : A) * (h : A)⁻¹ = p ->
        p ∈ Subgroup.center P)
    (q : P ⧸ Subgroup.center P) (hq : q ≠ 1) :
    letI := subgroupConjugationAction P H hHP
    letI := subgroupConjugationCenterQuotientAction P H hHP
    Nat.card (MulAction.orbit H q) = Nat.card H := by
  letI := subgroupConjugationAction P H hHP
  letI := subgroupConjugationCenterQuotientAction P H hHP
  apply natCard_quotient_orbit_eq_natCard_of_coprime_kernel
    (Subgroup.center P) q hq hcop
  · intro h z
    apply Subtype.ext
    change (h : A) * (z : P) * (h : A)⁻¹ = z
    calc
      (h : A) * (z : P) * (h : A)⁻¹ =
          (z : P) * (h : A) * (h : A)⁻¹ := by rw [hcenter h z]
      _ = z := by simp
  · intro h hh p hp
    apply hfixed h hh p
    exact congrArg Subtype.val hp

end Submission.OddOrder.MathlibSupport
