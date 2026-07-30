import Submission.OddOrder.MathlibSupport.BaerSuzukiPairs

/-!
Faithful set-based maximal candidates for the Baer-Suzuki proof.

MathComp's candidate `D` is a set of conjugates, not a subgroup.  Retaining
that distinction is essential in the normalizer-induction branch.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.AppendixAB

variable {G : Type*} [Group G]

/-- A set-shaped candidate in the hard branch of Baer-Suzuki. -/
def IsBaerSuzukiSetCandidate (p : ℕ) (x : G) (P : Subgroup G)
    (D : Set G) : Prop :=
  D ⊆ (P : Set G) ∩ conjugatesOf x ∧
    ∃ y ∈ conjugatesOf x, y ∉ P ∧
      IsPGroup p (Subgroup.closure (Set.insert y D))

theorem singleton_isBaerSuzukiSetCandidate {p : ℕ} {x : G}
    {P : Subgroup G} (hpairs : ConjugacyPairsArePGroup p x)
    (hxP : x ∈ P) (hproper : ¬ conjugatesOf x ⊆ P) :
    IsBaerSuzukiSetCandidate p x P ({x} : Set G) := by
  refine ⟨?_, ?_⟩
  · rintro z rfl
    exact ⟨hxP, mem_conjugatesOf_self⟩
  · obtain ⟨y, hyclass, hyP⟩ := Set.not_subset.mp hproper
    refine ⟨y, hyclass, hyP, ?_⟩
    apply IsPGroup.to_le (hpairs y hyclass x mem_conjugatesOf_self)
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact mem_pairGenerated_left _ _
    · rw [Set.mem_singleton_iff] at hz
      subst z
      exact mem_pairGenerated_right _ _

/-- Select an inclusion-maximal set candidate above the initial singleton. -/
theorem exists_maximal_isBaerSuzukiSetCandidate [Finite G]
    {p : ℕ} {x : G} {P : Subgroup G}
    (hpairs : ConjugacyPairsArePGroup p x) (hxP : x ∈ P)
    (hproper : ¬ conjugatesOf x ⊆ P) :
    ∃ D : Set G, IsBaerSuzukiSetCandidate p x P D ∧ x ∈ D ∧
      ∀ {D' : Set G}, IsBaerSuzukiSetCandidate p x P D' →
        D ⊆ D' → D' ⊆ D := by
  classical
  let s : Set (Set G) :=
    {D | IsBaerSuzukiSetCandidate p x P D ∧ ({x} : Set G) ⊆ D}
  have hs : s.Nonempty := by
    exact ⟨{x}, singleton_isBaerSuzukiSetCandidate hpairs hxP hproper,
      Set.Subset.rfl⟩
  obtain ⟨D, hD, hDmax⟩ := s.toFinite.exists_maximal hs
  refine ⟨D, hD.1, hD.2 (Set.mem_singleton x), ?_⟩
  intro D' hD' hDD'
  apply hDmax
  · exact ⟨hD', hD.2.trans hDD'⟩
  · exact hDD'

end Submission.OddOrder.MathlibSupport
