import Submission.BFCProfileLimit

namespace Submission

open Helpers
open scoped Filter Topology

@[unused_variables_ignore_fn]
meta def ignoreUnusedGeneratedGroupBinder : Lean.Linter.IgnoreFunction :=
  fun stx _ _ => stx.isIdent && stx.getId == `hG

theorem commProb_closed :
    IsClosed ({p : ℝ | ∃ (G : Type) (_hG : Group G), commProb G = p}) := by
  change IsClosed CommProbRange
  apply isClosed_CommProbRange_of_fixed_smallConjIndex_one
  intro p hp hp_pos hfixed
  rcases hfixed with ⟨M, φ, _hφ, hprob, hindex⟩
  let W : ℕ → FiniteCommProbWitness := fun n =>
    clusterWitness hp hp_pos (φ n)
  have hlower : ∀ n, p / 2 < (W n).probability := by
    intro n
    exact clusterWitness_lower hp hp_pos (φ n)
  have hindexW : ∀ n, (W n).smallConjIndex M = 1 := by
    intro n
    exact hindex n
  obtain ⟨B, hB⟩ :=
    exists_uniform_commutator_bound_of_fixed_smallConjIndex_one
      W hp_pos hlower M hindexW
  have hbound : ∀ n, (W n).commutatorCard ≤ B := by
    intro n
    simpa [FiniteCommProbWitness.commutatorCard] using hB n
  have hprobW : Filter.Tendsto (fun n => (W n).probability)
      Filter.atTop (𝓝 p) := hprob
  exact bfc_probability_limit_dichotomy W B hbound hprobW

end Submission
