import Submission.RationalMapPredicate

noncomputable section

namespace Submission.Helpers

lemma isRationalMap_zero (K : Set ℂ) :
    IsRationalMap K (0 : C(K, ℂ)) := by
  refine ⟨0, 1, ?_, ?_⟩
  · simp
  · simp

end Submission.Helpers
