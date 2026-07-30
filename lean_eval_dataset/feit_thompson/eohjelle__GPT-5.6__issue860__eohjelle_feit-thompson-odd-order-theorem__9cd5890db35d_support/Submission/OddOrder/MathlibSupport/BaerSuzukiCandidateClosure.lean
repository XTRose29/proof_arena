import Submission.OddOrder.MathlibSupport.BaerSuzukiMaximal

/-!
The intersection identity forced by maximality of a Baer-Suzuki candidate.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A maximal candidate `D` is exactly the part of its witness-generated
p-group lying in the selected Sylow subgroup and conjugacy-class closure. -/
theorem exists_witness_maximal_isBaerSuzukiCandidate {p : ℕ} {x : G}
    {P D : Subgroup G} (hD : IsBaerSuzukiCandidate p x P D)
    (hDmax : ∀ {D' : Subgroup G}, IsBaerSuzukiCandidate p x P D' →
      D ≤ D' → D' ≤ D) :
    ∃ y ∈ conjugatesOf x, y ∉ P ∧
      let B := Subgroup.zpowers y ⊔ D
      IsPGroup p B ∧ D = P ⊓ B ⊓ conjugacyClassGenerated x := by
  obtain ⟨hDP, hDE, y, hyclass, hyP, hB⟩ := hD
  let B : Subgroup G := Subgroup.zpowers y ⊔ D
  let D' : Subgroup G := P ⊓ B ⊓ conjugacyClassGenerated x
  have hDD' : D ≤ D' := by
    refine le_inf (le_inf hDP ?_) hDE
    exact le_sup_right
  have hD'B : D' ≤ B := inf_le_left.trans inf_le_right
  have hD'candidate : IsBaerSuzukiCandidate p x P D' := by
    refine ⟨inf_le_left.trans inf_le_left, inf_le_right,
      y, hyclass, hyP, ?_⟩
    apply IsPGroup.to_le hB
    exact sup_le le_sup_left hD'B
  have hD'D : D' ≤ D := hDmax hD'candidate hDD'
  refine ⟨y, hyclass, hyP, ?_⟩
  dsimp
  exact ⟨hB, le_antisymm hDD' hD'D⟩

end Submission.OddOrder.MathlibSupport
