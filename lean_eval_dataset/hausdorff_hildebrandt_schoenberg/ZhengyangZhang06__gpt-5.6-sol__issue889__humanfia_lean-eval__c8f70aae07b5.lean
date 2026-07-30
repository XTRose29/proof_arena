import ChallengeDeps
import Submission.Helpers
import Submission.Explore

open LeanEval.Analysis
open MeasureTheory
open scoped BigOperators NNReal

namespace Submission

theorem hausdorff_hildebrandt_schoenberg {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a ↔ HausdorffBounded a := by
  constructor
  · exact Helpers.momentConfiguration_hausdorffBounded a
  · exact Helpers.hausdorffBounded_momentConfiguration a

end Submission
