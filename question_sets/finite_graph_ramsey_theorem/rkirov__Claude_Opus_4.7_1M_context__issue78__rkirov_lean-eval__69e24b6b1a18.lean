/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: finite_graph_ramsey_theorem
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 69e24b6b1a18117485ef55663d4773900655e033
issue_number: 78
-/
import Mathlib
import Submission.Helpers

open SimpleGraph

namespace Submission

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s hr hs
  obtain ⟨N, hN⟩ := Submission.Helpers.ramsey_subset r s hr hs
  refine ⟨N, ?_⟩
  intro G
  rcases hN G (Finset.univ : Finset (Fin N)) (by simp) with
    ⟨K, _, hK⟩ | ⟨K, _, hK⟩
  · exact Or.inl hK.not_cliqueFree
  · exact Or.inr hK.not_cliqueFree

end Submission
