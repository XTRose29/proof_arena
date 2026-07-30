import ChallengeDeps
import Submission.Helpers
import Submission.AreaWinding

open LeanEval.Geometry.HopfUmlaufsatz

namespace Submission

theorem hopf_umlaufsatz {r : ℝ → Plane} {α : ℝ → ℝ}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (hα : IsTangentAngleLift r α) :
    totalCurvature α = 2 * Real.pi := by
  calc
    totalCurvature α = α period - α 0 :=
      Helpers.totalCurvature_eq_angle_sub hα
    _ = period := AreaWinding.angle_period_sub_eq_period hr hα
    _ = 2 * Real.pi := rfl

end Submission
