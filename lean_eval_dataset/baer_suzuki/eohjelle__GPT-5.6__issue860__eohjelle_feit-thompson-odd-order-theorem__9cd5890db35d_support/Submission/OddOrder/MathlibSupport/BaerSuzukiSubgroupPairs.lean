import Submission.OddOrder.MathlibSupport.BaerSuzukiPairs
import Submission.OddOrder.MathlibSupport.PairGeneratedSubtype

/-!
Inheritance of the Baer-Suzuki pair hypothesis by subgroup types.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.AppendixAB

variable {G : Type*} [Group G]

/-- An ambient conjugacy-class element satisfies the one-sided Baer-Suzuki
hypothesis inside every subgroup that contains it. -/
theorem conjugatePairsArePGroup_subtype_of_mem_conjugatesOf
    {p : ℕ} {x a : G} {H : Subgroup G}
    (hpairs : ConjugacyPairsArePGroup p x)
    (ha : a ∈ conjugatesOf x) (haH : a ∈ H) :
    ConjugatePairsArePGroup p (⟨a, haH⟩ : H) := by
  intro h
  apply pairGenerated_subtype_isPGroup
  change IsPGroup p
    (pairGenerated a ((h : G) * a * (h : G)⁻¹))
  apply hpairs a ha ((h : G) * a * (h : G)⁻¹)
  exact ha.trans (isConj_iff.mpr ⟨(h : G), rfl⟩)

theorem conjugacyPairsArePGroup_subtype_of_mem_conjugatesOf
    {p : ℕ} {x a : G} {H : Subgroup G}
    (hpairs : ConjugacyPairsArePGroup p x)
    (ha : a ∈ conjugatesOf x) (haH : a ∈ H) :
    ConjugacyPairsArePGroup p (⟨a, haH⟩ : H) :=
  conjugacyPairsArePGroup_of_conjugatePairsArePGroup
    (conjugatePairsArePGroup_subtype_of_mem_conjugatesOf hpairs ha haH)

end Submission.OddOrder.MathlibSupport
