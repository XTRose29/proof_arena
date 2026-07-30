import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open MeasureTheory Submodule

namespace Submission

theorem H1_not_closedComplemented :
    ¬ H1.ClosedComplemented := by
  exact Helpers.not_H1_closedComplemented

end Submission
