import Submission.PartitionLabels

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma conditionalObservationEntropy_nonneg
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (Y : M → J) :
    0 ≤ conditionalObservationEntropy mu X Y := by
  classical
  unfold conditionalObservationEntropy
  apply Finset.sum_nonneg
  intro y _hy
  apply mul_nonneg measureReal_nonneg
  apply Finset.sum_nonneg
  intro i _hi
  apply Real.negMulLog_nonneg
  · exact div_nonneg measureReal_nonneg measureReal_nonneg
  · by_cases hzero : mu.real (Y ⁻¹' {y}) = 0
    · simp [hzero, measureReal_mono_null Set.inter_subset_left hzero]
    · exact (div_le_one
        (lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero))).2
          (measureReal_mono Set.inter_subset_left)

lemma observationEntropy_le_pair
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X) (Y : M → J) (hY : Measurable Y) :
    observationEntropy mu X ≤ observationEntropy mu (fun x => (X x, Y x)) := by
  calc
    observationEntropy mu X ≤ observationEntropy mu X +
        conditionalObservationEntropy mu Y X :=
      le_add_of_nonneg_right (conditionalObservationEntropy_nonneg mu Y X)
    _ = observationEntropy mu (fun x => (Y x, X x)) :=
      (observationEntropy_pair mu Y hY X hX).symm
    _ = observationEntropy mu (fun x => (X x, Y x)) :=
      (observationEntropy_pair_swap mu X Y).symm

lemma observationEntropy_le_add_conditional
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X) (Y : M → J) (hY : Measurable Y) :
    observationEntropy mu X ≤
      observationEntropy mu Y + conditionalObservationEntropy mu X Y := by
  exact (observationEntropy_le_pair mu X hX Y hY).trans_eq
    (observationEntropy_pair mu X hX Y hY)

lemma observationEntropy_congr_ae
    {M I : Type*} [MeasurableSpace M] [Fintype I]
    (mu : Measure M) (X Y : M → I) (hXY : X =ᵐ[mu] Y) :
    observationEntropy mu X = observationEntropy mu Y := by
  classical
  unfold observationEntropy
  apply Finset.sum_congr rfl
  intro i _hi
  apply congrArg Real.negMulLog
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hXY] with x hx
  apply propext
  change X x = i ↔ Y x = i
  rw [hx]

lemma observationEntropy_graph
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    (mu : Measure M) (f : J → I) (Y : M → J) :
    observationEntropy mu (fun x => (f (Y x), Y x)) = observationEntropy mu Y := by
  classical
  unfold observationEntropy
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_eq_single (f j)]
  · apply congrArg Real.negMulLog
    apply congrArg ENNReal.toReal
    apply congrArg mu
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨congrArg f hx, hx⟩
  · intro i _hi hif
    have hempty : (fun x => (f (Y x), Y x)) ⁻¹' {(i, j)} = (∅ : Set M) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨hfi, hyj⟩
      apply hif
      exact hfi.symm.trans (congrArg f hyj)
    rw [hempty]
    simp
  · simp

lemma observationEntropy_comp_le
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (f : J → I) (Y : M → J) (hY : Measurable Y) :
    observationEntropy mu (fun x => f (Y x)) ≤ observationEntropy mu Y := by
  have hcomp : Measurable (fun x => f (Y x)) :=
    (measurable_of_finite f).comp hY
  exact (observationEntropy_le_pair mu (fun x => f (Y x)) hcomp Y hY).trans_eq
    (observationEntropy_graph mu f Y)

lemma observationEntropy_le_of_ae_determined
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [Inhabited I]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (Z : M → J) (hZ : Measurable Z)
    (good : Set M) (hfull : mu goodᶜ = 0)
    (hdet : ∀ x ∈ good, ∀ y ∈ good, Z x = Z y → X x = X y) :
    observationEntropy mu X ≤ observationEntropy mu Z := by
  classical
  let decode : J → I := fun z =>
    if h : ∃ x, x ∈ good ∧ Z x = z then X (Classical.choose h) else default
  have hdecode : X =ᵐ[mu] fun x => decode (Z x) := by
    filter_upwards [mem_ae_iff.mpr hfull] with x hx
    have hexists : ∃ y, y ∈ good ∧ Z y = Z x := ⟨x, hx, rfl⟩
    rw [show decode (Z x) = X (Classical.choose hexists) by
      simp only [decode, dif_pos hexists]]
    exact hdet x hx (Classical.choose hexists)
      (Classical.choose_spec hexists).1 (Classical.choose_spec hexists).2.symm
  calc
    observationEntropy mu X = observationEntropy mu (fun x => decode (Z x)) :=
      observationEntropy_congr_ae mu X (fun x => decode (Z x)) hdecode
    _ ≤ observationEntropy mu Z := observationEntropy_comp_le mu decode Z hZ

lemma entropyW_le_of_observationBlock_entropy_le
    {M I : Type*} [MeasurableSpace M]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (P Q : Finset (Set M))
    (hP : IsMeasurablePartition mu P)
    (hQ : IsMeasurablePartition mu Q)
    (Y : M → I) (hY : Measurable Y) (C : ℕ)
    (hblock : ∀ n,
      observationEntropy mu (observationBlock T Y n) ≤
        partitionEntropy mu (iteratedJoin T P (n + C))) :
    entropyW mu T Q ≤
      entropyW mu T P + conditionalPartitionEntropy mu Y Q := by
  classical
  have hQne := measurable_partition_nonempty mu hQ
  let d : ↥Q := ⟨hQne.choose, hQne.choose_spec⟩
  let c : ℝ := conditionalPartitionEntropy mu Y Q
  have hraw (n : ℕ) :
      partitionEntropy mu (iteratedJoin T Q n) ≤
        partitionEntropy mu (iteratedJoin T P n) +
          partitionEntropy mu (iteratedJoin T P C) + n * c := by
    have hlabel : Measurable (partitionIndexLabel Q d) :=
      measurable_partitionIndexLabel Q hQ.measurable d
    have hblockLabel := measurable_observationBlock
      T hT.measurable (partitionIndexLabel Q d) hlabel n
    have hblockY := measurable_observationBlock T hT.measurable Y hY n
    calc
      partitionEntropy mu (iteratedJoin T Q n) =
          observationEntropy mu
            (observationBlock T (partitionIndexLabel Q d) n) :=
        (observationEntropy_observationBlock_partitionIndexLabel
          mu T hT Q hQ d n).symm
      _ ≤ observationEntropy mu (observationBlock T Y n) +
          conditionalObservationEntropy mu
            (observationBlock T (partitionIndexLabel Q d) n)
            (observationBlock T Y n) :=
        observationEntropy_le_add_conditional mu
          (observationBlock T (partitionIndexLabel Q d) n) hblockLabel
          (observationBlock T Y n) hblockY
      _ ≤ observationEntropy mu (observationBlock T Y n) +
          n * conditionalObservationEntropy mu (partitionIndexLabel Q d) Y :=
        add_le_add le_rfl
          (conditionalObservationEntropy_observationBlock_le
            mu T hT (partitionIndexLabel Q d) hlabel Y hY n)
      _ = observationEntropy mu (observationBlock T Y n) + n * c := by
        rw [conditionalObservationEntropy_partitionIndexLabel mu Y hY Q hQ d]
      _ ≤ partitionEntropy mu (iteratedJoin T P (n + C)) + n * c :=
        add_le_add (hblock n) le_rfl
      _ ≤ (partitionEntropy mu (iteratedJoin T P n) +
            partitionEntropy mu (iteratedJoin T P C)) + n * c :=
        add_le_add
          (partitionEntropy_iteratedJoin_add_le
            mu T T_inv hT_right hT P hP n C) le_rfl
      _ = partitionEntropy mu (iteratedJoin T P n) +
          partitionEntropy mu (iteratedJoin T P C) + n * c := rfl
  have hrate : ∀ᶠ n : ℕ in atTop,
      partitionEntropy mu (iteratedJoin T Q n) / n ≤
        partitionEntropy mu (iteratedJoin T P n) / n +
          partitionEntropy mu (iteratedJoin T P C) / n + c := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      partitionEntropy mu (iteratedJoin T Q n) / n ≤
          (partitionEntropy mu (iteratedJoin T P n) +
            partitionEntropy mu (iteratedJoin T P C) + n * c) / n :=
        div_le_div_of_nonneg_right (hraw n) hnpos.le
      _ = partitionEntropy mu (iteratedJoin T P n) / n +
          partitionEntropy mu (iteratedJoin T P C) / n + c := by
        field_simp
  have hQrate := tendsto_partitionEntropy_iteratedJoin_div_entropyW
    mu T T_inv hT_right hT Q hQ
  have hPrate := tendsto_partitionEntropy_iteratedJoin_div_entropyW
    mu T T_inv hT_right hT P hP
  have hconstant : Tendsto
      (fun n : ℕ => partitionEntropy mu (iteratedJoin T P C) / n)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat
      (partitionEntropy mu (iteratedJoin T P C))
  have hrhs : Tendsto
      (fun n : ℕ => partitionEntropy mu (iteratedJoin T P n) / n +
        partitionEntropy mu (iteratedJoin T P C) / n + c)
      atTop (nhds (entropyW mu T P + c)) := by
    simpa using (hPrate.add hconstant).add tendsto_const_nhds
  apply le_of_not_gt
  intro hgt
  let midpoint := (entropyW mu T P + c + entropyW mu T Q) / 2
  have hlower : entropyW mu T P + c < midpoint := by
    dsimp [midpoint]
    linarith
  have hupper : midpoint < entropyW mu T Q := by
    dsimp [midpoint]
    linarith
  have hQeventually : ∀ᶠ n : ℕ in atTop,
      midpoint < partitionEntropy mu (iteratedJoin T Q n) / n :=
    (tendsto_order.1 hQrate).1 midpoint hupper
  have hPeventually : ∀ᶠ n : ℕ in atTop,
      partitionEntropy mu (iteratedJoin T P n) / n +
          partitionEntropy mu (iteratedJoin T P C) / n + c < midpoint :=
    (tendsto_order.1 hrhs).2 midpoint hlower
  obtain ⟨n, hn, hQn, hPn⟩ :=
    (hrate.and (hQeventually.and hPeventually)).exists
  exact (not_lt_of_ge hn) (hPn.trans hQn)

end Submission.Helpers
