import ChallengeDeps
import Submission.Convergence

open LeanEval.NumberTheory.BrunConstant
open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Submission

theorem brun_constant_converges :
    Summable twinPrimeReciprocalTerm := by
  exact BrunSieve.summable_twinPrimeReciprocalTerm

end Submission
