import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairRestrictionPGroup
import Submission.OddOrder.MathlibSupport.PGroupPrimeOrderCriterion

/-!
Cross-prime element reduction for local quotient-pair restriction kernels.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem localDerivedRestrictionKernel_isPGroup_of_prime_order_elements
    {p : ℕ} [Fact p.Prime]
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (hcross : ∀ (q : ℕ), q.Prime → q ≠ p →
      ∀ a : localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM,
        orderOf a = q → a = 1) :
    IsPGroup p
      (localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM) :=
  isPGroup_of_prime_order_elements hcross

/-- To prove the larger local derived subgroup p-primary, it suffices to
prove the smaller one p-primary and exclude nontrivial cross-prime elements
from the restriction kernel. -/
theorem local_commutator_isPGroup_of_restriction_prime_order
    {p : ℕ} [Fact p.Prime]
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (hsmall : IsPGroup p
      (_root_.commutator (localQuotientPair M hxNM hyNM)))
    (hcross : ∀ (q : ℕ), q.Prime → q ≠ p →
      ∀ a : localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM,
        orderOf a = q → a = 1) :
    IsPGroup p
      (_root_.commutator (localQuotientPair E hxNE hyNE)) := by
  apply local_commutator_isPGroup_of_restriction
    hME hxNE hyNE hxNM hyNM hsmall
  exact localDerivedRestrictionKernel_isPGroup_of_prime_order_elements
    hME hxNE hyNE hxNM hyNM hcross

end Submission.OddOrder.BG.AppendixAB
