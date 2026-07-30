import Submission.TwoSidedConditionalEntropy

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

noncomputable def fiberPartition
    {M J : Type*} [Fintype J] (Y : M → J) : Finset (Set M) :=
  Finset.univ.image fun y => Y ⁻¹' {y}

noncomputable def observationEntropy
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    (mu : Measure M) (Y : M → J) : ℝ :=
  ∑ y : J, Real.negMulLog (mu.real (Y ⁻¹' {y}))

noncomputable def conditionalPartitionEntropy
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    (mu : Measure M) (Y : M → J) (Q : Finset (Set M)) : ℝ :=
  ∑ A ∈ Q, ∫ x, Real.negMulLog (finiteConditionalProbability mu Y A x) ∂mu

lemma isMeasurablePartition_fiberPartition
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) (Y : M → J) (hY : Measurable Y) :
    IsMeasurablePartition mu (fiberPartition Y) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hA
    exact hY (measurableSet_singleton y)
  · have hunion : (⋃ A ∈ fiberPartition Y, A) = Set.univ := by
      ext x
      simp [fiberPartition]
    rw [hunion]
    simp
  · intro A hA B hB hAB
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hB
    have hyz : y ≠ z := by
      intro hyz
      subst z
      exact hAB rfl
    have hinter : Y ⁻¹' ({y} : Set J) ∩ Y ⁻¹' {z} = ∅ := by
      ext x
      constructor
      · rintro ⟨hxy, hxz⟩
        exact (hyz (hxy.symm.trans hxz)).elim
      · intro hx
        exact hx.elim
    rw [hinter]
    simp

lemma partitionEntropy_fiberPartition
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    (mu : Measure M) (Y : M → J) :
    partitionEntropy mu (fiberPartition Y) = observationEntropy mu Y := by
  classical
  unfold partitionEntropy fiberPartition observationEntropy
  have hdisj : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint
      (fun y => Y ⁻¹' ({y} : Set J)) := by
    intro y _hy z _hz hyz
    change Disjoint (Y ⁻¹' ({y} : Set J)) (Y ⁻¹' {z})
    rw [Set.disjoint_left]
    intro x hxy hxz
    exact hyz (hxy.symm.trans hxz)
  simpa [measureReal_def] using
    (Finset.sum_image_of_disjoint
      (f := fun y => Y ⁻¹' ({y} : Set J))
      (g := fun A => Real.negMulLog (mu A).toReal)
      (I := Finset.univ) (by simp) hdisj)

lemma sum_negMulLog_eq_negMulLog_sum_add
    {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, Real.negMulLog (p i)) =
      Real.negMulLog (∑ i, p i) +
        (∑ i, p i) * ∑ i, Real.negMulLog (p i / ∑ j, p j) := by
  classical
  let r : ℝ := ∑ i, p i
  have hr_nonneg : 0 ≤ r := Finset.sum_nonneg fun i _ => hp i
  by_cases hr : r = 0
  · have hp_zero (i : I) : p i = 0 := by
      apply le_antisymm
      · have hle : p i ≤ r := by
          exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
        simpa [hr] using hle
      · exact hp i
    simp [hp_zero]
  · calc
      (∑ i, Real.negMulLog (p i)) =
          ∑ i, ((p i / r) * Real.negMulLog r +
            r * Real.negMulLog (p i / r)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Real.negMulLog_mul]
        congr 1
        exact (mul_div_cancel₀ (p i) hr).symm
      _ = (∑ i, p i / r) * Real.negMulLog r +
          r * ∑ i, Real.negMulLog (p i / r) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ = Real.negMulLog r +
          r * ∑ i, Real.negMulLog (p i / r) := by
        have hsum : ∑ i, p i / r = 1 := by
          rw [← Finset.sum_div]
          exact div_self hr
        rw [hsum, one_mul]
      _ = Real.negMulLog (∑ i, p i) +
          (∑ i, p i) * ∑ i, Real.negMulLog (p i / ∑ j, p j) := by
        rfl

lemma negMulLog_sum_le_sum_negMulLog
    {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Real.negMulLog (∑ i, p i) ≤ ∑ i, Real.negMulLog (p i) := by
  classical
  rw [sum_negMulLog_eq_negMulLog_sum_add p hp]
  apply le_add_of_nonneg_right
  apply mul_nonneg
  · exact Finset.sum_nonneg fun i _ => hp i
  · apply Finset.sum_nonneg
    intro i _hi
    apply Real.negMulLog_nonneg
    · exact div_nonneg (hp i) (Finset.sum_nonneg fun j _ => hp j)
    · by_cases hzero : ∑ j, p j = 0
      · simp [hzero]
      · apply (div_le_one (lt_of_le_of_ne
          (Finset.sum_nonneg fun j _ => hp j) (Ne.symm hzero))).2
        exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

lemma integral_negMulLog_finiteConditionalProbability
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (hY : Measurable Y) (A : Set M) :
    (∫ x, Real.negMulLog (finiteConditionalProbability mu Y A x) ∂mu) =
      ∑ y : J, mu.real (Y ⁻¹' {y}) *
        Real.negMulLog
          (mu.real (A ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})) := by
  classical
  let r : J → ℝ := fun y =>
    mu.real (A ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})
  have heq :
      (fun x => Real.negMulLog (finiteConditionalProbability mu Y A x)) =
        fun x => ∑ y : J, (Y ⁻¹' {y}).indicator
          (fun _ => Real.negMulLog (r y)) x := by
    funext x
    rw [Finset.sum_eq_single (Y x)]
    · rw [Set.indicator_of_mem (show x ∈ Y ⁻¹' ({Y x} : Set J) by rfl)]
      simp only [r]
      rw [finiteConditionalProbability_apply]
    · intro y _hy hyx
      rw [Set.indicator_of_notMem]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Ne.symm hyx
    · simp
  rw [heq, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _hy
    rw [integral_indicator_const _ (hY (measurableSet_singleton y)), smul_eq_mul]
  · intro y _hy
    exact (integrable_const _).indicator (hY (measurableSet_singleton y))

lemma indexedJointEntropy_eq_add_conditional
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    (Q : Finset (Set M)) (hQ : IsMeasurablePartition mu Q) :
    (∑ y : J, ∑ A : ↥Q,
        Real.negMulLog (mu.real (Y ⁻¹' {y} ∩ A.1))) =
      observationEntropy mu Y + conditionalPartitionEntropy mu Y Q := by
  classical
  let p : J → ↥Q → ℝ := fun y A => mu.real (Y ⁻¹' {y} ∩ A.1)
  let row : J → ℝ := fun y => mu.real (Y ⁻¹' {y})
  have hp (y : J) (A : ↥Q) : 0 ≤ p y A := measureReal_nonneg
  have hrow (y : J) : ∑ A : ↥Q, p y A = row y := by
    calc
      (∑ A : ↥Q, p y A) =
          ∑ A ∈ Q, mu.real (Y ⁻¹' {y} ∩ A) := by
        simpa [p] using Finset.sum_coe_sort Q
          (fun A => mu.real (Y ⁻¹' {y} ∩ A))
      _ = row y := sum_measureReal_inter_partition mu hQ (Y ⁻¹' {y})
        (hY (measurableSet_singleton y))
  have hchain (y : J) :
      (∑ A : ↥Q, Real.negMulLog (p y A)) =
        Real.negMulLog (row y) + row y *
          ∑ A : ↥Q, Real.negMulLog (p y A / row y) := by
    rw [sum_negMulLog_eq_negMulLog_sum_add (p y) (hp y), hrow y]
  calc
    (∑ y : J, ∑ A : ↥Q,
        Real.negMulLog (mu.real (Y ⁻¹' {y} ∩ A.1))) =
        ∑ y : J, (Real.negMulLog (row y) + row y *
          ∑ A : ↥Q, Real.negMulLog (p y A / row y)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      simpa [p] using hchain y
    _ = (∑ y : J, Real.negMulLog (row y)) +
        ∑ A : ↥Q, ∑ y : J,
          row y * Real.negMulLog (p y A / row y) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = observationEntropy mu Y + conditionalPartitionEntropy mu Y Q := by
      unfold observationEntropy conditionalPartitionEntropy
      congr 1
      calc
        (∑ A : ↥Q, ∑ y : J,
            row y * Real.negMulLog (p y A / row y)) =
            ∑ A ∈ Q, ∑ y : J,
              row y * Real.negMulLog
                (mu.real (Y ⁻¹' {y} ∩ A) / row y) := by
          simpa [p] using Finset.sum_coe_sort Q (fun A : Set M => ∑ y : J,
            row y * Real.negMulLog
              (mu.real (Y ⁻¹' {y} ∩ A) / row y))
        _ = ∑ A ∈ Q, ∫ x,
            Real.negMulLog (finiteConditionalProbability mu Y A x) ∂mu := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [integral_negMulLog_finiteConditionalProbability mu Y hY A]
          apply Finset.sum_congr rfl
          intro y _hy
          simp only [row]
          rw [Set.inter_comm]

lemma partitionEntropy_le_observation_add_conditional
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    (Q : Finset (Set M)) (hQ : IsMeasurablePartition mu Q) :
    partitionEntropy mu Q ≤
      observationEntropy mu Y + conditionalPartitionEntropy mu Y Q := by
  classical
  let p : J → ↥Q → ℝ := fun y A => mu.real (Y ⁻¹' {y} ∩ A.1)
  have hp (y : J) (A : ↥Q) : 0 ≤ p y A := measureReal_nonneg
  have hcol (A : ↥Q) : ∑ y : J, p y A = mu.real A.1 := by
    have hsum := sum_measureReal_inter_fibers mu Y hY
      (hQ.measurable A.1 A.2) Set.univ
    simpa [p, Set.inter_comm] using hsum
  calc
    partitionEntropy mu Q =
        ∑ A : ↥Q, Real.negMulLog (mu.real A.1) := by
      unfold partitionEntropy
      exact (Finset.sum_coe_sort Q (fun A => Real.negMulLog (mu.real A))).symm
    _ ≤ ∑ A : ↥Q, ∑ y : J, Real.negMulLog (p y A) := by
      apply Finset.sum_le_sum
      intro A _hA
      rw [← hcol A]
      apply negMulLog_sum_le_sum_negMulLog (fun y => p y A) (fun y => hp y A)
    _ = ∑ y : J, ∑ A : ↥Q, Real.negMulLog (p y A) := Finset.sum_comm
    _ = observationEntropy mu Y + conditionalPartitionEntropy mu Y Q := by
      simpa [p] using indexedJointEntropy_eq_add_conditional mu Y hY Q hQ

lemma twoSidedConditionalPartitionEntropy_eq
    (mu : Measure EucPlane)
    (T T_inv : EucPlane → EucPlane)
    (P Q : Finset (Set EucPlane)) (n : ℕ) :
    twoSidedConditionalPartitionEntropy mu T T_inv P Q n =
      conditionalPartitionEntropy mu (twoSidedObservation T T_inv P n) Q := by
  rfl

end Submission.Helpers
