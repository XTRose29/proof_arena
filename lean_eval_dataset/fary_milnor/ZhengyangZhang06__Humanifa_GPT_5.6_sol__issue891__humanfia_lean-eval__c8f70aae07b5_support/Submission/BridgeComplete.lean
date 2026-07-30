import Submission.AnalyticConcat

open LeanEval.Geometry.FaryMilnorProblem
open Set
open scoped Real
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

@[simp] theorem height_neg (r : ℝ → Space) (u : Space) (t : ℝ) :
    height r (-u) t = -height r u t := by
  simp [height]

@[simp] theorem directionalUnitTangent_neg (r : ℝ → Space) (u : Space) (t : ℝ) :
    directionalUnitTangent r (-u) t = -directionalUnitTangent r u t := by
  simp [directionalUnitTangent]

theorem deriv_directionalUnitTangent_neg (r : ℝ → Space) (u : Space) (t : ℝ) :
    deriv (directionalUnitTangent r (-u)) t =
      -deriv (directionalUnitTangent r u) t := by
  have hfun : directionalUnitTangent r (-u) =
      -(directionalUnitTangent r u) := by
    funext x
    exact directionalUnitTangent_neg r u x
  rw [hfun, deriv.neg]

theorem MaxMinBridgeData.toMinMax_neg {r : ℝ → Space} {u : Space} {a b : ℝ}
    (hdata : MaxMinBridgeData r u a b) : MinMaxBridgeData r (-u) a b where
  left_mem := hdata.left_mem
  right_mem := hdata.right_mem
  left_lt_right := hdata.left_lt_right
  height_mono := by
    intro x hx y hy hxy
    rw [height_neg, height_neg]
    exact neg_lt_neg (hdata.height_anti hx hy hxy)
  height_anti_wrap := by
    intro x hx y hy hxy
    rw [height_neg, height_neg]
    exact neg_lt_neg (hdata.height_mono_wrap hx hy hxy)
  tangent_pos := by
    intro z hz
    rw [directionalUnitTangent_neg]
    exact neg_pos.mpr (hdata.tangent_neg z hz)
  tangent_neg_wrap := by
    intro z hz
    rw [directionalUnitTangent_neg]
    exact neg_lt_zero.mpr (hdata.tangent_pos_wrap z hz)
  tangent_left := by
    rw [directionalUnitTangent_neg, hdata.tangent_left, neg_zero]
  tangent_right := by
    rw [directionalUnitTangent_neg, hdata.tangent_right, neg_zero]
  tangent_deriv_left := by
    rw [deriv_directionalUnitTangent_neg]
    exact neg_pos.mpr hdata.tangent_deriv_left
  tangent_deriv_right := by
    rw [deriv_directionalUnitTangent_neg]
    exact neg_lt_zero.mpr hdata.tangent_deriv_right

theorem IsKnotIsotopic.isUnknotted {p q : ℝ → Space}
    (hpq : IsKnotIsotopic p q) (hq : IsUnknotted q) : IsUnknotted p := by
  have hqcircle : IsKnotIsotopic q standardCircle := by
    simpa [IsKnotIsotopic, IsUnknotted] using hq
  simpa [IsKnotIsotopic, IsUnknotted] using hpq.trans hqcircle

theorem isUnknotted_of_minMaxBridgeData {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) : IsUnknotted r := by
  obtain ⟨k, hk0, hk1, hstraightSmooth, hstraight0, hstraight1,
      hstraightKnot⟩ :=
    exists_straightContractedBridgeMinMax_isotopy hknot hu hdata
  let qk := contractedBridgeCurveMinMax hknot u hdata k
  let q0 := contractedBridgeCurveMinMax hknot u hdata 0
  have hstraight : IsKnotIsotopic r qk := by
    refine ⟨straightContractedBridgeMinMax hknot u hdata k,
      hstraightSmooth, hstraight0, ?_, hstraightKnot⟩
    intro t
    exact hstraight1 t
  have hcontract : IsKnotIsotopic qk q0 := by
    refine ⟨contractMateDirectionIsotopyMinMax hknot u hdata k,
      contDiff_contractMateDirectionIsotopyMinMax hknot u hdata hk0 hk1,
      ?_, ?_, ?_⟩
    · intro t
      exact contractMateDirectionIsotopyMinMax_zero hknot u hdata k t
    · intro t
      exact contractMateDirectionIsotopyMinMax_one hknot u hdata k t
    · intro s _hs
      exact isSmoothKnot_contractMateDirectionIsotopyMinMax
        hknot hu hdata hk0 hk1
  apply (hstraight.trans hcontract).isUnknotted
  exact isUnknotted_contractedBridgeCurveMinMax_zero hknot hu hdata

theorem isUnknotted_of_maxMinBridgeData {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b : ℝ}
    (hdata : MaxMinBridgeData r u a b) : IsUnknotted r := by
  apply isUnknotted_of_minMaxBridgeData hknot (u := -u)
  · simpa using hu
  · exact hdata.toMinMax_neg

theorem isUnknotted_of_bridgeOrientationData {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1)
    (hdata : (∃ a b, MinMaxBridgeData r u a b) ∨
      ∃ a b, MaxMinBridgeData r u a b) : IsUnknotted r := by
  rcases hdata with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
  · exact isUnknotted_of_minMaxBridgeData hknot hu hab
  · exact isUnknotted_of_maxMinBridgeData hknot hu hab

end Submission.Helpers
