import Submission.OddOrder.MathlibSupport.BaerSuzukiMaximal

/-!
Maximal Baer-Suzuki candidates containing the distinguished element.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Select an inclusion-maximal Baer-Suzuki candidate above `zpowers x`.
In particular, the selected candidate contains the distinguished element. -/
theorem exists_maximal_isBaerSuzukiCandidate_mem [Finite G]
    {p : ℕ} {x : G} {P : Subgroup G}
    (hpairs : ConjugacyPairsArePGroup p x) (hxP : x ∈ P)
    (hproper : ¬ conjugatesOf x ⊆ P) :
    ∃ D : Subgroup G, IsBaerSuzukiCandidate p x P D ∧ x ∈ D ∧
      ∀ {D' : Subgroup G}, IsBaerSuzukiCandidate p x P D' →
        D ≤ D' → D' ≤ D := by
  classical
  let X : Subgroup G := Subgroup.zpowers x
  let s : Set (Subgroup G) :=
    {D | IsBaerSuzukiCandidate p x P D ∧ X ≤ D}
  have hs : s.Nonempty := by
    refine ⟨X, zpowers_isBaerSuzukiCandidate hpairs hxP hproper, le_rfl⟩
  obtain ⟨D, hD, hDmax⟩ := s.toFinite.exists_maximal hs
  refine ⟨D, hD.1, hD.2 (Subgroup.mem_zpowers x), ?_⟩
  intro D' hD' hDD'
  apply hDmax
  · exact ⟨hD', hD.2.trans hDD'⟩
  · exact hDD'

end Submission.OddOrder.MathlibSupport
