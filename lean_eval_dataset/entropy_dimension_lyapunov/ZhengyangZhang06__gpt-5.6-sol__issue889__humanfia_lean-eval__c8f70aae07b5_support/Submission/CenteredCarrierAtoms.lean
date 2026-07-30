import Submission.CenteredJoin

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

lemma dimH_centeredJoin_atom_eq_dimMeasure
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_pres : MeasurePreserving T mu mu)
    (hmu_erg : Ergodic T mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {s : Set EucPlane} (hP_subset : ∀ A ∈ P, A ⊆ s)
    (hs_dim : dimH s = dimMeasure mu)
    {m n : ℕ} (hmn : 0 < m + n) {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n) (hmu_A : mu A ≠ 0) :
    dimH A = dimMeasure mu := by
  classical
  rw [centeredJoin, preimagePartition] at hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  have hT_inv_pres : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hmu_pres
  have hB_measurable : MeasurableSet B :=
    measurableSet_of_mem_iteratedJoin T P hmu_pres.measurable hP.measurable
      (m + n) hB
  have hmu_B : mu B ≠ 0 := by
    intro hzero
    apply hmu_A
    rw [(hT_inv_pres.iterate m).measure_preimage hB_measurable.nullMeasurableSet,
      hzero]
  calc
    dimH ((T_inv^[m]) ⁻¹' B) = dimH (T^[m] '' B) := by
      congr 1
      exact (congrFun
        (Set.image_eq_preimage_of_inverse
          (hT_left.iterate m) (hT_right.iterate m)) B).symm
    _ = dimH B :=
      dimH_image_iterate_eq_of_contDiff_inverse T T_inv hT_smooth
        hT_inv_smooth hT_left m B
    _ = dimMeasure mu :=
      dimH_iteratedJoin_atom_eq_dimMeasure T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right mu hmu_erg P hP hP_subset hs_dim hmn hB hmu_B

end Submission.Helpers
