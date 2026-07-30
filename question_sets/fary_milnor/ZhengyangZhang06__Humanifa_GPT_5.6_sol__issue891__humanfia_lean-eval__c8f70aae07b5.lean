import ChallengeDeps
import Submission.StrictEndpoint

open LeanEval.Geometry.FaryMilnorProblem
open Set
open scoped Real
open WithLp

namespace Submission

theorem fary_milnor_total_curvature {r : ℝ → Space} (_hknot : IsSmoothKnot r)
    (_hK : totalCurvature r ≤ 4 * Real.pi) :
    IsUnknotted r := by
  apply Helpers.isUnknotted_of_nontrivial_curvature_gt _hK
  exact Helpers.totalCurvature_gt_four_pi_of_not_unknotted _hknot

end Submission
