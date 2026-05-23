/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: finite_graph_ramsey_theorem
user: rkirov
model: Claude Opus 4.7
submission_repo: rkirov/lean-eval
submission_ref: 212bebf172ea4a345071d0b3fc40a978515d09c6
issue_number: 21
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
