import ChallengeDeps
import Submission.unit_distance_upper_bound

namespace Submission

theorem unit_distance_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        (LeanEval.Combinatorics.unitDist P : ℝ) ≤
          C * (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
  exact UnitDistanceUpperBoundProof.unit_distance_upper_bound

end Submission
