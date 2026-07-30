import ChallengeDeps
import Submission.Check

open LeanEval.Analysis
open MeasureTheory
open scoped BigOperators NNReal

namespace Submission

theorem hausdorff_positivity {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsPositiveMomentConfiguration a ↔ ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n := by
  constructor
  · exact test_diff_nonneg_of_positive
  · exact test_positive_of_diff

end Submission
