import Submission.OddOrder.MathlibSupport.BaerSuzukiCandidateProper
import Submission.OddOrder.MathlibSupport.PGroupNormalizer

/-!
Normalizer growth for a Baer-Suzuki candidate in its selected Sylow subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A Baer-Suzuki candidate has a normalizing element in the selected Sylow
subgroup that lies strictly outside the candidate. -/
theorem exists_sylow_mem_normalizer_not_candidate {p : ℕ} [Fact p.Prime]
    {x : G} (P₀ : Sylow p (conjugacyClassGenerated x)) {D : Subgroup G}
    (hD : IsBaerSuzukiCandidate p x
      ((P₀ : Subgroup (conjugacyClassGenerated x)).map
        (conjugacyClassGenerated x).subtype) D) :
    ∃ z : G,
      z ∈ (P₀ : Subgroup (conjugacyClassGenerated x)).map
          (conjugacyClassGenerated x).subtype ∧
      z ∈ Subgroup.normalizer (D : Set G) ∧ z ∉ D := by
  let E : Subgroup G := conjugacyClassGenerated x
  let P : Subgroup G := (P₀ : Subgroup E).map E.subtype
  change IsBaerSuzukiCandidate p x P D at hD
  change ∃ z : G, z ∈ P ∧ z ∈ Subgroup.normalizer (D : Set G) ∧ z ∉ D
  have hP : IsPGroup p P := P₀.isPGroup'.map E.subtype
  have hDP : D < P := isBaerSuzukiCandidate_lt_sylow P₀ hD
  have hgrowth : D < P ⊓ Subgroup.normalizer (D : Set G) :=
    lt_inf_normalizer_of_isPGroup hP hDP
  obtain ⟨z, hz, hzD⟩ := SetLike.exists_of_lt hgrowth
  exact ⟨z, hz.1, hz.2, hzD⟩

end Submission.OddOrder.MathlibSupport
