import Submission.OddOrder.MathlibSupport.BaerSuzukiSetCandidate

/-!
The intersection identity for a maximal set-shaped Baer-Suzuki candidate.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A maximal set candidate is exactly the conjugacy-class part of its
witness-generated p-group that lies in the selected Sylow subgroup. -/
theorem exists_witness_maximal_isBaerSuzukiSetCandidate
    {p : ℕ} {x : G} {P : Subgroup G} {D : Set G}
    (hD : IsBaerSuzukiSetCandidate p x P D)
    (hDmax : ∀ {D' : Set G}, IsBaerSuzukiSetCandidate p x P D' →
      D ⊆ D' → D' ⊆ D) :
    ∃ y ∈ conjugatesOf x, y ∉ P ∧
      let B := Subgroup.closure (Set.insert y D)
      IsPGroup p B ∧
        D = ((P : Set G) ∩ (B : Set G)) ∩ conjugatesOf x := by
  obtain ⟨hDPE, y, hyclass, hyP, hB⟩ := hD
  let B : Subgroup G := Subgroup.closure (Set.insert y D)
  let D' : Set G := ((P : Set G) ∩ (B : Set G)) ∩ conjugatesOf x
  have hDB : D ⊆ B := by
    intro z hz
    exact Subgroup.subset_closure (Set.mem_insert_of_mem y hz)
  have hDD' : D ⊆ D' := by
    intro z hz
    exact ⟨⟨(hDPE hz).1, hDB hz⟩, (hDPE hz).2⟩
  have hD'candidate : IsBaerSuzukiSetCandidate p x P D' := by
    refine ⟨?_, y, hyclass, hyP, ?_⟩
    · intro z hz
      exact ⟨hz.1.1, hz.2⟩
    · apply IsPGroup.to_le hB
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact Subgroup.subset_closure (Set.mem_insert _ D)
      · exact hz.1.2
  have hD'D : D' ⊆ D := hDmax hD'candidate hDD'
  refine ⟨y, hyclass, hyP, ?_⟩
  dsimp
  exact ⟨hB, Set.Subset.antisymm hDD' hD'D⟩

end Submission.OddOrder.MathlibSupport
