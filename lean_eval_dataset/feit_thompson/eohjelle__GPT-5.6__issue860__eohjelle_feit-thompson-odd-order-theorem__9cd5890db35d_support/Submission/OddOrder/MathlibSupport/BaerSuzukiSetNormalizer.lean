import Submission.OddOrder.MathlibSupport.BaerSuzukiSetCandidateClosure

/-!
Self-normalization of the maximal set candidate in Baer-Suzuki.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- The intersection identity forces every element of the candidate set to
normalize that set. -/
theorem baerSuzukiSetCandidate_subset_normalizer
    {x : G} {P B : Subgroup G} {D : Set G}
    (hD : D = ((P : Set G) ∩ (B : Set G)) ∩ conjugatesOf x) :
    D ⊆ Subgroup.normalizer D := by
  intro z hz
  apply Subgroup.mem_normalizer_fintype
  intro w hw
  rw [hD] at hz hw ⊢
  obtain ⟨⟨hzP, hzB⟩, hzclass⟩ := hz
  obtain ⟨⟨hwP, hwB⟩, hwclass⟩ := hw
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact P.mul_mem (P.mul_mem hzP hwP) (P.inv_mem hzP)
  · exact B.mul_mem (B.mul_mem hzB hwB) (B.inv_mem hzB)
  · exact hwclass.trans (isConj_iff.mpr ⟨z, rfl⟩)

end Submission.OddOrder.MathlibSupport
