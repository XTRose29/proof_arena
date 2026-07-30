import Submission.PlaneLift

open LeanEval.Geometry.FaryMilnorProblem
open Set
open scoped Real
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

@[simp] theorem bridgeHeightContraction_zero (low high x : ℝ) :
    bridgeHeightContraction low high 0 x = bridgeHeightMidpoint low high := by
  unfold bridgeHeightContraction bridgeHeightMidpoint
  ring

noncomputable def constantBridgeDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) : Space :=
  centralMateDirectionMinMax hknot u hdata
    (bridgeHeightMidpoint (height r u a) (height r u b))

theorem constantBridgeDirectionMinMax_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    constantBridgeDirectionMinMax hknot u hdata ≠ 0 := by
  apply centralMateDirectionMinMax_ne_zero hknot u hdata
  exact ⟨left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt,
    bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt⟩

theorem inner_constantBridgeDirectionMinMax_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    inner ℝ u (constantBridgeDirectionMinMax hknot u hdata) = 0 := by
  apply inner_centralMateDirectionMinMax_eq_zero hknot u hdata
  exact ⟨left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt,
    bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt⟩

@[simp] theorem contractedMateDirectionMinMax_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    contractedMateDirectionMinMax hknot u hdata 0 x =
      constantBridgeDirectionMinMax hknot u hdata := by
  simp [contractedMateDirectionMinMax, constantBridgeDirectionMinMax]

theorem contractedBridgeCurveMinMax_zero_eq_lift {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    contractedBridgeCurveMinMax hknot u hdata 0 =
      liftPlanarCurveAlong u (planarBridgeCurve r u)
        (fun _ => constantBridgeDirectionMinMax hknot u hdata) := by
  funext t
  simp [contractedBridgeCurveMinMax, liftPlanarCurveAlong, planarBridgeCurve]

theorem isUnknotted_contractedBridgeCurveMinMax_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1)
    {a b : ℝ} (hdata : MinMaxBridgeData r u a b) :
    IsUnknotted (contractedBridgeCurveMinMax hknot u hdata 0) := by
  rw [contractedBridgeCurveMinMax_zero_eq_lift]
  apply isUnknotted_liftPlanarCurveAlong_of_planar
  · intro t
    simp [planarBridgeCurve]
  · refine ⟨planarUnknotMinMax r u a b, ?_, ?_, ?_, ?_⟩
    · exact contDiff_planarUnknotMinMax hknot u hdata.left_mem.1
        hdata.left_lt_right hdata.right_mem.2
    · intro t
      exact planarUnknotMinMax_zero u a b t
    · intro t
      exact planarUnknotMinMax_one hdata.left_mem.1 hdata.left_lt_right
        hdata.right_mem.2 t
    · intro s _hs
      exact isSmoothKnot_planarUnknotMinMax hknot u hdata s
  · exact hu
  · exact constantBridgeDirectionMinMax_ne_zero hknot u hdata
  · exact inner_constantBridgeDirectionMinMax_eq_zero hknot u hdata

end Submission.Helpers
