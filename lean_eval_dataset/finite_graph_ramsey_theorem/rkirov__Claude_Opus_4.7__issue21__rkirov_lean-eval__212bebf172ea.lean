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
