import Submission.OddOrder.MathlibSupport.FixedOneMulActionOrbitCount

/-!
The center-quotient orbit count underlying `card_clPqH`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {A : Type u} [Group A]

/-- Under the `card_clPqH` centralizer hypotheses, the center quotient is the
identity coset together with uniformly `|H|`-element nonidentity orbits. -/
theorem natCard_centerQuotient_eq_one_add_orbits_mul_natCard_of_centralizers
    (P H : Subgroup A) (hHP : H ≤ Subgroup.normalizer P)
    [Finite P] [Finite H]
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hcenter : H ≤ Subgroup.centralizer (centerWithin P : Set A))
    (hcentralizer : ∀ h : H, h ≠ 1 ->
      centralizerWithin P (Subgroup.zpowers (h : A)) = centerWithin P) :
    letI := subgroupConjugationAction P H hHP
    letI := subgroupConjugationCenterQuotientAction P H hHP
    Nat.card (P ⧸ Subgroup.center P) =
      1 + Nat.card
          (nonidentityFixedOneOrbitQuotient
            (G := H) (X := P ⧸ Subgroup.center P)) * Nat.card H := by
  letI := subgroupConjugationAction P H hHP
  letI := subgroupConjugationCenterQuotientAction P H hHP
  apply natCard_eq_one_add_fixedOneOrbits_mul_natCard
  · intro h
    change h • ((1 : P) : P ⧸ Subgroup.center P) =
      ((1 : P) : P ⧸ Subgroup.center P)
    rw [MulAction.Quotient.smul_coe]
    simp
  · exact centerQuotient_fixed_eq_one_of_centralizers
      P H hHP hcop hcenter hcentralizer

end Submission.OddOrder.MathlibSupport
