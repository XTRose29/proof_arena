import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairRestriction
import Submission.OddOrder.MathlibSupport.PGroupMapKernel

/-!
Lifting p-primary derived subgroups along local quotient-pair restriction.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The kernel of local restriction on the derived subgroup of the larger
local quotient pair. -/
noncomputable def localDerivedRestrictionKernel
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G)) :
    Subgroup (_root_.commutator (localQuotientPair E hxNE hyNE)) :=
  ((localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM).restrict
    (_root_.commutator (localQuotientPair E hxNE hyNE))).ker

/-- If the smaller local derived subgroup and the kernel of restriction on
the larger local derived subgroup are p-groups, then the larger local derived
subgroup is a p-group. -/
theorem local_commutator_isPGroup_of_restriction
    {p : ℕ} {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (hsmall : IsPGroup p
      (_root_.commutator (localQuotientPair M hxNM hyNM)))
    (hker : IsPGroup p
      (localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM)) :
    IsPGroup p
      (_root_.commutator (localQuotientPair E hxNE hyNE)) := by
  let D := _root_.commutator (localQuotientPair E hxNE hyNE)
  let f := localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM
  apply isPGroup_of_map_and_restrict_ker D f
  · rw [localQuotientPairRestrictionHom_map_commutator
      hME hxNE hyNE hxNM hyNM]
    exact hsmall
  · exact hker

end Submission.OddOrder.BG.AppendixAB
