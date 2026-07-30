import ChallengeDeps
import Submission.Helpers

open LeanEval.Dynamics
open Filter Topology

namespace Submission

theorem furstenberg_topological_recurrence {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (T : X ≃ₜ X) :
    ∃ x : X, IsMultiplyRecurrent (T : X → X) x := by
  simpa only [IsMultiplyRecurrent] using
    Helpers.exists_multiply_recurrent_of_continuous (T : X → X) T.continuous

end Submission
