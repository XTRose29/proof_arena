import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory

namespace Submission

theorem hippocrates_lunes (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b) := by
  exact Helpers.hippocrates_lunes_measure a b ha hb

end Submission
