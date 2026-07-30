import Mathlib
import Submission.Helpers

open SimpleGraph

namespace Submission

private theorem compl_induce {α : Type} (G : SimpleGraph α) (s : Set α) :
    (G.induce s)ᶜ = Gᶜ.induce s := by
  ext x y
  simp [Subtype.ext_iff]

private theorem exists_finite_ramsey :
    ∀ r s : ℕ, ∃ n : ℕ, ∀ (α : Type) [Fintype α], n ≤ Fintype.card α →
      ∀ G : SimpleGraph α, ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r
  induction r with
  | zero =>
      intro s
      refine ⟨0, ?_⟩
      intro α _ _ G
      exact Or.inl not_cliqueFree_zero
  | succ r ihr =>
      intro s
      induction s with
      | zero =>
          refine ⟨0, ?_⟩
          intro α _ _ G
          exact Or.inr not_cliqueFree_zero
      | succ s ihs =>
          obtain ⟨n₁, hn₁⟩ := ihr (s + 1)
          obtain ⟨n₂, hn₂⟩ := ihs
          refine ⟨n₁ + n₂ + 1, ?_⟩
          intro α _ hcard G
          classical
          by_contra hbad
          simp only [not_or, not_not] at hbad
          obtain ⟨hG, hGc⟩ := hbad
          have hcard_pos : 0 < Fintype.card α := by omega
          let v : α := Classical.choice (Fintype.card_pos_iff.mp hcard_pos)
          by_cases hlarge : n₁ ≤ Fintype.card (G.neighborSet v)
          · rcases hn₁ (G.neighborSet v) hlarge (G.induce (G.neighborSet v)) with h | h
            · apply h
              rw [cliqueFree_induce_iff]
              have hu : G.CliqueFreeOn Set.univ (r + 1) := hG.cliqueFreeOn
              simpa using
                CliqueFreeOn.of_succ (G := G) (s := Set.univ) hu (Set.mem_univ v)
            · apply h
              rw [compl_induce, cliqueFree_induce_iff]
              exact hGc.cliqueFreeOn
          · have hlarge' : n₂ ≤ Fintype.card (Gᶜ.neighborSet v) := by
              rw [Gᶜ.card_neighborSet_eq_degree, G.degree_compl]
              rw [G.card_neighborSet_eq_degree] at hlarge
              omega
            rcases hn₂ (Gᶜ.neighborSet v) hlarge'
                (G.induce (Gᶜ.neighborSet v)) with h | h
            · apply h
              rw [cliqueFree_induce_iff]
              exact hG.cliqueFreeOn
            · apply h
              rw [compl_induce, cliqueFree_induce_iff]
              have hu : Gᶜ.CliqueFreeOn Set.univ (s + 1) := hGc.cliqueFreeOn
              simpa using
                CliqueFreeOn.of_succ (G := Gᶜ) (s := Set.univ) hu (Set.mem_univ v)

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s _ _
  obtain ⟨n, hn⟩ := exists_finite_ramsey r s
  exact ⟨n, fun G => hn (Fin n) (by simp) G⟩

end Submission
