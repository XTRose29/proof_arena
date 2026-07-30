import Submission.Information
import Submission.EntropyLight

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

lemma mem_iUnion_lightAtoms_iff_information_gt_ae
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (c : ℝ) :
    ∀ᵐ x ∂mu,
      x ∈ ⋃ A ∈ lightAtoms mu P c, A ↔
        c < partitionInformation mu P x := by
  filter_upwards
      [ae_existsUnique_partition_atom mu P hP,
       partitionInformation_eq_neg_log_atom_ae mu P hP,
       partition_atom_measureReal_pos_ae mu P] with x hxunique hxinfo hxpos
  constructor
  · intro hxlight
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxlight
    obtain ⟨hAlight, hxA⟩ := Set.mem_iUnion.mp hxA
    have hA := (Finset.mem_filter.mp hAlight).1
    have hsmall := (Finset.mem_filter.mp hAlight).2
    have hlog : Real.log (mu.real A) < -c :=
      (Real.log_lt_iff_lt_exp (hxpos A hA hxA)).2 hsmall
    rw [hxinfo A hA hxA]
    linarith
  · intro hcinfo
    obtain ⟨A, hA, hxA⟩ := hxunique.exists
    have hlog : Real.log (mu.real A) < -c := by
      rw [hxinfo A hA hxA] at hcinfo
      linarith
    have hsmall : mu.real A < Real.exp (-c) :=
      (Real.log_lt_iff_lt_exp (hxpos A hA hxA)).1 hlog
    apply Set.mem_iUnion_of_mem A
    apply Set.mem_iUnion_of_mem (Finset.mem_filter.mpr ⟨hA, hsmall⟩)
    exact hxA

end Submission.Helpers
