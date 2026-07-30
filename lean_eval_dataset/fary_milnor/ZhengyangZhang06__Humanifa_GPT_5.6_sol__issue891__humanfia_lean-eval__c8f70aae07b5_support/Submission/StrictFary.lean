import Submission.BridgePerturb
import Submission.CroftonCompact

open LeanEval.Geometry.FaryMilnorProblem
open Set
open scoped Real
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

theorem isUnknotted_of_not_hasFourAlternatingSigns
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1)
    (hno : ¬ HasFourAlternatingSigns r u) : IsUnknotted r := by
  let f := directionalUnitTangent r u
  have hnoValues : ¬ HasFourAlternatingValues period f := by
    simpa [HasFourAlternatingValues, HasFourAlternatingSigns, f] using hno
  by_cases hfzero : f = 0
  · have hhalf : 0 < period / 2 := div_pos period_pos (by norm_num)
    have hhalfP : period / 2 < period := by linarith [period_pos]
    have hweak : WeakMinMaxSignData period f 0 (period / 2) := by
      refine ⟨⟨le_rfl, period_pos⟩, ⟨hhalf.le, hhalfP⟩, hhalf,
        ?_, ?_, ?_, ?_⟩
      · intro z _hz
        rw [hfzero]
        simp
      · intro z _hz
        rw [hfzero]
        simp
      · rw [hfzero]
        simp
      · rw [hfzero]
        simp
    apply isUnknotted_of_weak_bridge_sign_data hknot hu
    exact Or.inl ⟨0, period / 2, hweak⟩
  · obtain ⟨hpos, hneg⟩ :=
      exists_pos_neg_directionalUnitTangent_of_ne_zero hknot u hfzero
    have hsign := exists_weak_bridge_sign_data period_pos
      (continuous_directionalUnitTangent hknot u)
      (periodic_directionalUnitTangent hknot u) hnoValues hpos hneg
    exact isUnknotted_of_weak_bridge_sign_data hknot hu hsign

theorem isUnknotted_of_totalCurvature_lt_four_pi
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hK : totalCurvature r < 4 * Real.pi) : IsUnknotted r := by
  obtain ⟨u, hu, hno⟩ := exists_unit_not_hasFourAlternatingSigns_of_lt hknot hK
  exact isUnknotted_of_not_hasFourAlternatingSigns hknot hu hno

end Submission.Helpers
