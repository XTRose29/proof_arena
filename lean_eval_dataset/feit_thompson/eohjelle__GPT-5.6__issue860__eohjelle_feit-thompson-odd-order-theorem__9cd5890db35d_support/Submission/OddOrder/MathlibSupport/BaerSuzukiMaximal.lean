import Submission.OddOrder.MathlibSupport.BaerSuzukiNormalCase

/-!
Maximal-subgroup selection for the hard branch of Baer-Suzuki.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.AppendixAB

variable {G : Type*} [Group G]

/-- A subgroup used in the maximal-`D` step of Baer-Suzuki. -/
def IsBaerSuzukiCandidate (p : ℕ) (x : G) (P D : Subgroup G) : Prop :=
  D ≤ P ∧ D ≤ conjugacyClassGenerated x ∧
    ∃ y ∈ conjugatesOf x, y ∉ P ∧
      IsPGroup p (Subgroup.zpowers y ⊔ D : Subgroup G)

theorem zpowers_isBaerSuzukiCandidate {p : ℕ} {x : G} {P : Subgroup G}
    (hpairs : ConjugacyPairsArePGroup p x) (hxP : x ∈ P)
    (hproper : ¬ conjugatesOf x ⊆ P) :
    IsBaerSuzukiCandidate p x P (Subgroup.zpowers x) := by
  refine ⟨Subgroup.zpowers_le.mpr hxP,
    Subgroup.zpowers_le.mpr (mem_conjugacyClassGenerated x), ?_⟩
  obtain ⟨y, hyclass, hyP⟩ := Set.not_subset.mp hproper
  refine ⟨y, hyclass, hyP, ?_⟩
  have hypair := hpairs y hyclass x mem_conjugatesOf_self
  rw [pairGenerated] at hypair
  exact hypair

/-- Select an inclusion-maximal Baer-Suzuki candidate. -/
theorem exists_maximal_isBaerSuzukiCandidate [Finite G]
    {p : ℕ} {x : G} {P : Subgroup G}
    (hpairs : ConjugacyPairsArePGroup p x) (hxP : x ∈ P)
    (hproper : ¬ conjugatesOf x ⊆ P) :
    ∃ D : Subgroup G, IsBaerSuzukiCandidate p x P D ∧
      ∀ {D' : Subgroup G}, IsBaerSuzukiCandidate p x P D' →
        D ≤ D' → D' ≤ D := by
  classical
  let s : Set (Subgroup G) := {D | IsBaerSuzukiCandidate p x P D}
  have hs : s.Nonempty :=
    ⟨Subgroup.zpowers x,
      zpowers_isBaerSuzukiCandidate hpairs hxP hproper⟩
  obtain ⟨D, hD, hDmax⟩ := s.toFinite.exists_maximal hs
  exact ⟨D, hD, fun hD' hDD' ↦ hDmax hD' hDD'⟩

end Submission.OddOrder.MathlibSupport
