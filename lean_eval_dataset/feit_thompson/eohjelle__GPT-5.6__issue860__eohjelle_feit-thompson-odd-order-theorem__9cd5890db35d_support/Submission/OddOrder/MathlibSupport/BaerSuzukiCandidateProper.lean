import Submission.OddOrder.MathlibSupport.BaerSuzukiCandidateClosure

/-!
Properness of a maximal-candidate witness inside the selected Sylow subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Any Baer-Suzuki candidate for a Sylow subgroup of the conjugacy-class
closure is a proper subgroup of that Sylow subgroup. -/
theorem isBaerSuzukiCandidate_lt_sylow {p : ℕ} {x : G}
    (P₀ : Sylow p (conjugacyClassGenerated x)) {D : Subgroup G}
    (hD : IsBaerSuzukiCandidate p x
      ((P₀ : Subgroup (conjugacyClassGenerated x)).map
        (conjugacyClassGenerated x).subtype) D) :
    D < (P₀ : Subgroup (conjugacyClassGenerated x)).map
      (conjugacyClassGenerated x).subtype := by
  let E : Subgroup G := conjugacyClassGenerated x
  let P : Subgroup G := (P₀ : Subgroup E).map E.subtype
  change IsBaerSuzukiCandidate p x P D at hD
  change D < P
  obtain ⟨hDP, hDE, y, hyclass, hyP, hB⟩ := hD
  refine lt_of_le_of_ne hDP ?_
  intro hDPeq
  let B : Subgroup G := Subgroup.zpowers y ⊔ D
  have hBE : B ≤ E := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr
        (conjugatesOf_subset_conjugacyClassGenerated x hyclass)
    · exact hDE
  have hBsub : IsPGroup p (B.subgroupOf E) := by
    exact hB.comap_subtype
  have hP₀B : (P₀ : Subgroup E) ≤ B.subgroupOf E := by
    intro z hz
    change (z : G) ∈ B
    apply (show D ≤ B from le_sup_right)
    rw [hDPeq]
    exact ⟨z, hz, rfl⟩
  have hBsubeq : B.subgroupOf E = (P₀ : Subgroup E) :=
    P₀.is_maximal' hBsub hP₀B
  have hyB : y ∈ B :=
    (show Subgroup.zpowers y ≤ B from le_sup_left) (Subgroup.mem_zpowers y)
  let yE : E := ⟨y, hBE hyB⟩
  have hyP₀ : yE ∈ P₀ := by
    change yE ∈ (P₀ : Subgroup E)
    rw [← hBsubeq]
    exact hyB
  apply hyP
  exact ⟨yE, hyP₀, rfl⟩

end Submission.OddOrder.MathlibSupport
