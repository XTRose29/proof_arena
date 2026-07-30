import ChallengeDeps
import Submission.Helpers

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

/-- The two natural definitions of the `p`-core coincide:
`Submission.Helpers.opCore p G` (the intersection of all Sylow `p`-subgroups)
equals `pCore p G` (the supremum of all normal `p`-subgroups). -/
theorem opCore_eq_pCore {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] :
    Submission.Helpers.opCore p G = pCore p G := by
  apply le_antisymm
  · -- opCore is itself a normal p-subgroup, so it lies in the supremum.
    refine le_sSup ?_
    exact ⟨Submission.Helpers.opCore.normal p G,
      Submission.Helpers.opCore_isPGroup p G⟩
  · -- Each normal p-subgroup is ≤ opCore (Isaacs Problem 1B.2).
    refine sSup_le ?_
    rintro N ⟨hNn, hNp⟩
    haveI := hNn
    exact Submission.Helpers.normal_pgroup_le_opCore hNp

/-- **Baer-Suzuki theorem (single-element p-core form).** An element `x` of a
finite group `G` lies in the `p`-core `O_p(G)` iff every pair `(x, x^g)` of
conjugates generates a `p`-group. -/
theorem baer_suzuki {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔
      ∀ g : G, IsPGroup p
        (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  rw [← opCore_eq_pCore]
  exact Submission.Helpers.baerSuzukiP x

end Submission
