import ChallengeDeps
import Submission.WielandtCriterion

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

theorem baer_suzuki {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔
      ∀ g : G, IsPGroup p
        (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  constructor
  · exact Helpers.baerSuzuki_forward x
  · intro h
    apply Helpers.mem_pCore_of_singletonClosure_isSubnormal x h
    apply Helpers.isSubnormal_of_subnormal_in_sup_conjugate
    intro g
    rw [Helpers.conj_smul_subgroup_eq_map]
    exact Helpers.singletonClosure_locally_subnormal_of_pairwise x h g

end Submission
