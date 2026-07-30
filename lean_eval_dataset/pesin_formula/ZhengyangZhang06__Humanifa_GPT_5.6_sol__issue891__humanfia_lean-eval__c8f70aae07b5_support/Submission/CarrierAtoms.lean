import Submission.DimensionOrbit
import Submission.PartitionSupport

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

lemma iteratedJoin_atom_subset_of_partition_atoms
    (T : EucPlane → EucPlane) (P : Finset (Set EucPlane))
    {s : Set EucPlane} (hP_subset : ∀ A ∈ P, A ⊆ s)
    {n : ℕ} (hn : 0 < n) {A : Set EucPlane}
    (hA : A ∈ iteratedJoin T P n) :
    A ⊆ s := by
  rw [iteratedJoin] at hA
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
  intro x hx
  let k : Fin n := ⟨0, hn⟩
  have hxk : T^[k.val] x ∈ f k := Set.mem_iInter.mp hx k
  have hfk : f k ∈ P := Fintype.mem_piFinset.mp hf k
  simpa [k] using hP_subset (f k) hfk hxk

lemma dimH_iteratedJoin_atom_eq_dimMeasure
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {s : Set EucPlane} (hP_subset : ∀ A ∈ P, A ⊆ s)
    (hs_dim : dimH s = dimMeasure mu)
    {n : ℕ} (hn : 0 < n) {A : Set EucPlane}
    (hA : A ∈ iteratedJoin T P n) (hmu_A : mu A ≠ 0) :
    dimH A = dimMeasure mu := by
  apply le_antisymm
  · calc
      dimH A ≤ dimH s :=
        dimH_mono (iteratedJoin_atom_subset_of_partition_atoms T P hP_subset hn hA)
      _ = dimMeasure mu := hs_dim
  · exact dimMeasure_le_dimH_of_measure_ne_zero_ergodic T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right mu hmu_erg
      (measurableSet_of_mem_iteratedJoin T P
        hT_smooth.continuous.measurable hP.measurable n hA) hmu_A

end Submission.Helpers
