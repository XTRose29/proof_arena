import Submission.EntropySubadditive

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

/-- Pointwise information of a finite measurable partition.  Away from the
null overlaps and null complement of the partition, this is the negative
logarithm of the measure of the unique atom containing the point. -/
noncomputable def partitionInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M)) (x : M) : ℝ :=
  ∑ A ∈ P, A.indicator (fun _ => -Real.log (mu.real A)) x

lemma measurable_partitionInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M))
    (hP : ∀ A ∈ P, MeasurableSet A) :
    Measurable (partitionInformation mu P) := by
  unfold partitionInformation
  apply Finset.measurable_sum
  intro A hA
  exact measurable_const.indicator (hP A hA)

lemma integrable_partitionInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Integrable (partitionInformation mu P) mu := by
  unfold partitionInformation
  apply integrable_finsetSum
  intro A hA
  exact (integrable_const _).indicator (hP A hA)

lemma integral_partitionInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    ∫ x, partitionInformation mu P x ∂mu = partitionEntropy mu P := by
  change (∫ x, ∑ A ∈ P,
      A.indicator (fun _ => -Real.log (mu.real A)) x ∂mu) = _
  rw [partitionEntropy]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [integral_indicator_const _ (hP A hA), smul_eq_mul]
    simp only [Real.negMulLog, measureReal_def]
    ring
  · intro A hA
    exact (integrable_const _).indicator (hP A hA)

lemma ae_existsUnique_partition_atom
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M))
    (hP : IsMeasurablePartition mu P) :
    ∀ᵐ x ∂mu, ∃! A : Set M, A ∈ P ∧ x ∈ A := by
  have hcover : ∀ᵐ x ∂mu, x ∈ ⋃ A ∈ P, A := mem_ae_iff.mpr hP.cover
  have hseparate :
      ∀ᵐ x ∂mu, ∀ A ∈ P, ∀ B ∈ P, A ≠ B → x ∉ A ∩ B := by
    rw [Filter.eventually_all_finset]
    intro A hA
    rw [Filter.eventually_all_finset]
    intro B hB
    by_cases hAB : A = B
    · exact Filter.Eventually.of_forall fun _x hne => (hne hAB).elim
    · exact (measure_eq_zero_iff_ae_notMem.mp
        (hP.disjoint A hA B hB hAB)).mono fun _x hx _hne => hx
  filter_upwards [hcover, hseparate] with x hxcover hxseparate
  obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxcover
  obtain ⟨hA, hxA⟩ := Set.mem_iUnion.mp hxA
  refine ⟨A, ⟨hA, hxA⟩, ?_⟩
  intro B hB
  by_contra hBA
  exact hxseparate A hA B hB.1 (Ne.symm hBA) ⟨hxA, hB.2⟩

lemma partitionInformation_eq_neg_log_atom_ae
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M))
    (hP : IsMeasurablePartition mu P) :
    ∀ᵐ x ∂mu, ∀ A ∈ P, x ∈ A →
      partitionInformation mu P x = -Real.log (mu.real A) := by
  filter_upwards [ae_existsUnique_partition_atom mu P hP] with x hxunique
  intro A hA hxA
  unfold partitionInformation
  rw [Finset.sum_eq_single A]
  · simp [hxA]
  · intro B hB hBA
    have hxB : x ∉ B := by
      intro hxB
      exact hBA (hxunique.unique ⟨hB, hxB⟩ ⟨hA, hxA⟩)
    simp [hxB]
  · exact fun hAnot => (hAnot hA).elim

lemma partition_atom_measureReal_pos_ae
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) :
    ∀ᵐ x ∂mu, ∀ A ∈ P, x ∈ A → 0 < mu.real A := by
  rw [Filter.eventually_all_finset]
  intro A _hA
  by_cases hmuA : mu A = 0
  · exact (measure_eq_zero_iff_ae_notMem.mp hmuA).mono
      fun _x hxnot hxA => (hxnot hxA).elim
  · exact Filter.Eventually.of_forall fun _x _hxA =>
      ENNReal.toReal_pos hmuA (measure_ne_top mu A)

end Submission.Helpers
