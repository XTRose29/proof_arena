import Submission.OddOrder.MathlibSupport.BaerSuzukiNormalizerInduction
import Submission.OddOrder.MathlibSupport.BaerSuzukiSecondNormalizerWitness

/-!
The final maximality contradiction in the hard Baer-Suzuki branch.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Two normalizing conjugates on opposite sides of the selected Sylow
subgroup enlarge the maximal candidate, a contradiction. -/
theorem false_of_maximal_isBaerSuzukiSetCandidate
    {p : ℕ} {x y₁ y₂ : G} {P : Subgroup G} {D : Set G}
    (hDPE : D ⊆ (P : Set G) ∩ conjugatesOf x)
    (hDmax : ∀ {D' : Set G}, IsBaerSuzukiSetCandidate p x P D' →
      D ⊆ D' → D' ⊆ D)
    (hself : D ⊆ Subgroup.normalizer D)
    (hpN : IsPGroup p (normalizerConjugacyGenerated x D))
    (hy₁class : y₁ ∈ conjugatesOf x)
    (hy₁N : y₁ ∈ Subgroup.normalizer D) (hy₁P : y₁ ∉ P)
    (hy₂P : y₂ ∈ P) (hy₂class : y₂ ∈ conjugatesOf x)
    (hy₂N : y₂ ∈ Subgroup.normalizer D) (hy₂D : y₂ ∉ D) : False := by
  let D' : Set G := Set.insert y₂ D
  have hD'candidate : IsBaerSuzukiSetCandidate p x P D' := by
    refine ⟨?_, y₁, hy₁class, hy₁P, ?_⟩
    · intro z hz
      rcases hz with rfl | hz
      · exact ⟨hy₂P, hy₂class⟩
      · exact hDPE hz
    · apply IsPGroup.to_le hpN
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact Subgroup.subset_closure ⟨hy₁class, hy₁N⟩
      · rcases hz with rfl | hz
        · exact Subgroup.subset_closure ⟨hy₂class, hy₂N⟩
        · exact Subgroup.subset_closure ⟨(hDPE hz).2, hself hz⟩
  have hD'D : D' ⊆ D := hDmax hD'candidate (Set.subset_insert y₂ D)
  exact hy₂D (hD'D (Set.mem_insert y₂ D))

end Submission.OddOrder.MathlibSupport
