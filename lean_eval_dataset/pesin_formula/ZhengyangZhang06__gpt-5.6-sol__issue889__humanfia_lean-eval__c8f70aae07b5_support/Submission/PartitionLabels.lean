import Submission.ObservationBlocks

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

noncomputable def decodePartitionSymbol
    {M : Type*} (P : Finset (Set M)) (d : ↥P) (s : ↥P → Bool) : ↥P :=
  if h : ∃ A : ↥P, s A = true then Classical.choose h else d

noncomputable def partitionLabel
    {M : Type*} (P : Finset (Set M)) (d : ↥P) (x : M) : ↥P :=
  decodePartitionSymbol P d (partitionSymbol P x)

noncomputable def partitionIndexLabel
    {M : Type*} (P : Finset (Set M)) (d : ↥P) (x : M) :
    Fin (Fintype.card ↥P) :=
  Fintype.equivFin ↥P (partitionLabel P d x)

lemma measurable_partitionLabel
    {M : Type*} [MeasurableSpace M]
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (d : ↥P) :
    Measurable (partitionLabel P d) := by
  exact (measurable_of_finite (decodePartitionSymbol P d)).comp
    (measurable_partitionSymbol P hP)

lemma measurable_partitionIndexLabel
    {M : Type*} [MeasurableSpace M]
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (d : ↥P) :
    Measurable (partitionIndexLabel P d) := by
  unfold partitionIndexLabel partitionLabel
  exact (measurable_of_finite fun s =>
    Fintype.equivFin ↥P (decodePartitionSymbol P d s)).comp
      (measurable_partitionSymbol P hP)

lemma partitionLabel_eq_of_unique
    {M : Type*} (P : Finset (Set M)) (d : ↥P) {x : M}
    (hx : ∃! A : Set M, A ∈ P ∧ x ∈ A)
    {A : Set M} (hA : A ∈ P) (hxA : x ∈ A) :
    partitionLabel P d x = ⟨A, hA⟩ := by
  classical
  have hexists : ∃ B : ↥P, partitionSymbol P x B = true := by
    refine ⟨⟨A, hA⟩, ?_⟩
    simp [partitionSymbol, hxA]
  unfold partitionLabel decodePartitionSymbol
  rw [dif_pos hexists]
  apply Subtype.ext
  let B : ↥P := Classical.choose hexists
  have hBsymbol : partitionSymbol P x B = true := Classical.choose_spec hexists
  have hxB : x ∈ B.1 := by
    simpa [partitionSymbol] using hBsymbol
  exact hx.unique ⟨B.2, hxB⟩ ⟨hA, hxA⟩

lemma partitionLabel_fiber_ae_eq
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M))
  (hP : IsMeasurablePartition mu P) (d : ↥P) (A : ↥P) :
    partitionLabel P d ⁻¹' {A} =ᵐ[mu] (A.1 : Set M) := by
  filter_upwards [ae_existsUnique_partition_atom mu P hP] with x hx
  apply propext
  change (partitionLabel P d x = A) ↔ x ∈ A.1
  constructor
  · intro hlabel
    obtain ⟨B, hBP, hxB⟩ := hx.exists
    have hBlabel := partitionLabel_eq_of_unique P d hx hBP hxB
    rw [hlabel] at hBlabel
    exact hBlabel ▸ hxB
  · intro hxA
    exact partitionLabel_eq_of_unique P d hx A.2 hxA

lemma measureReal_partitionLabel_fiber
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (d : ↥P) (A : ↥P) :
    mu.real (partitionLabel P d ⁻¹' {A}) = mu.real A.1 := by
  exact congrArg ENNReal.toReal (measure_congr (partitionLabel_fiber_ae_eq mu P hP d A))

lemma observationEntropy_partitionLabel
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (d : ↥P) :
    observationEntropy mu (partitionLabel P d) = partitionEntropy mu P := by
  unfold observationEntropy partitionEntropy
  calc
    (∑ A : ↥P, Real.negMulLog (mu.real (partitionLabel P d ⁻¹' {A}))) =
        ∑ A : ↥P, Real.negMulLog (mu.real A.1) := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [measureReal_partitionLabel_fiber mu P hP d A]
    _ = ∑ A ∈ P, Real.negMulLog (mu.real A) :=
      Finset.sum_coe_sort P (fun A => Real.negMulLog (mu.real A))

lemma observationEntropy_partitionIndexLabel
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (d : ↥P) :
    observationEntropy mu (partitionIndexLabel P d) = partitionEntropy mu P := by
  calc
    observationEntropy mu (partitionIndexLabel P d) =
        observationEntropy mu (partitionLabel P d) := by
      exact observationEntropy_equiv mu (Fintype.equivFin ↥P)
        (partitionLabel P d)
    _ = partitionEntropy mu P := observationEntropy_partitionLabel mu P hP d

lemma conditionalObservationEntropy_partitionLabel
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (d : ↥P) :
    conditionalObservationEntropy mu (partitionLabel P d) Y =
      conditionalPartitionEntropy mu Y P := by
  classical
  have hinter (y : J) (A : ↥P) :
    mu.real (Y ⁻¹' {y} ∩ partitionLabel P d ⁻¹' {A}) =
        mu.real (Y ⁻¹' {y} ∩ A.1) := by
    have hsets : Set.inter (Y ⁻¹' {y}) (partitionLabel P d ⁻¹' {A}) =ᵐ[mu]
        Set.inter (Y ⁻¹' {y}) (A.1 : Set M) :=
      (partitionLabel_fiber_ae_eq mu P hP d A).mono fun x hx => by
        exact congrArg (fun h : Prop => (Y ⁻¹' {y}) x ∧ h) hx
    exact congrArg ENNReal.toReal (measure_congr hsets)
  unfold conditionalObservationEntropy conditionalPartitionEntropy
  calc
    (∑ y : J, mu.real (Y ⁻¹' {y}) *
        ∑ A : ↥P, Real.negMulLog
          (mu.real (Y ⁻¹' {y} ∩ partitionLabel P d ⁻¹' {A}) /
            mu.real (Y ⁻¹' {y}))) =
        ∑ y : J, mu.real (Y ⁻¹' {y}) *
          ∑ A : ↥P, Real.negMulLog
            (mu.real (Y ⁻¹' {y} ∩ A.1) / mu.real (Y ⁻¹' {y})) := by
      apply Finset.sum_congr rfl
      intro y _hy
      congr 1
      apply Finset.sum_congr rfl
      intro A _hA
      rw [hinter y A]
    _ = ∑ A : ↥P, ∑ y : J, mu.real (Y ⁻¹' {y}) *
          Real.negMulLog
            (mu.real (A.1 ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _hA
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Set.inter_comm]
    _ = ∑ A : ↥P, ∫ x,
        Real.negMulLog (finiteConditionalProbability mu Y A.1 x) ∂mu := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [integral_negMulLog_finiteConditionalProbability mu Y hY A.1]
    _ = ∑ A ∈ P, ∫ x,
        Real.negMulLog (finiteConditionalProbability mu Y A x) ∂mu :=
      Finset.sum_coe_sort P fun A =>
        ∫ x, Real.negMulLog (finiteConditionalProbability mu Y A x) ∂mu

lemma conditionalObservationEntropy_partitionIndexLabel
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (d : ↥P) :
    conditionalObservationEntropy mu (partitionIndexLabel P d) Y =
      conditionalPartitionEntropy mu Y P := by
  classical
  let e := Fintype.equivFin ↥P
  have hfiber (A : ↥P) :
      partitionIndexLabel P d ⁻¹' {e A} = partitionLabel P d ⁻¹' {A} := by
    ext x
    simp [partitionIndexLabel, e]
  calc
    conditionalObservationEntropy mu (partitionIndexLabel P d) Y =
        conditionalObservationEntropy mu (partitionLabel P d) Y := by
      unfold conditionalObservationEntropy
      apply Finset.sum_congr rfl
      intro y _hy
      congr 1
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro A _hA
      rw [hfiber A]
    _ = conditionalPartitionEntropy mu Y P :=
      conditionalObservationEntropy_partitionLabel mu Y hY P hP d

lemma iteratedJoin_eq_image_subtype_names
    {M : Type*} (T : M → M) (P : Finset (Set M)) (n : ℕ) :
    iteratedJoin T P n = (Finset.univ : Finset (Fin n → ↥P)).image
      (fun f => ⋂ k : Fin n, T^[k.val] ⁻¹' (f k).1) := by
  classical
  ext A
  constructor
  · intro hA
    rw [iteratedJoin] at hA
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
    let g : Fin n → ↥P := fun k => ⟨f k, Fintype.mem_piFinset.mp hf k⟩
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
  · intro hA
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hA
    rw [iteratedJoin]
    exact Finset.mem_image.mpr ⟨(fun k => (f k).1),
      Fintype.mem_piFinset.mpr (fun k => (f k).2), rfl⟩

lemma observationBlock_partitionLabel_fiber_ae_eq
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (d : ↥P) (n : ℕ) (f : Fin n → ↥P) :
    observationBlock T (partitionLabel P d) n ⁻¹' {f} =ᵐ[mu]
      ⋂ k : Fin n, T^[k.val] ⁻¹' (f k).1 := by
  have hunique : ∀ᵐ x ∂mu, ∀ k : Fin n,
      ∃! A : Set M, A ∈ P ∧ T^[k.val] x ∈ A := by
    rw [ae_all_iff]
    intro k
    exact ae_existsUnique_partition_atom_iterate mu T hT P hP k.val
  filter_upwards [hunique] with x hx
  apply propext
  change (observationBlock T (partitionLabel P d) n x = f) ↔
    x ∈ ⋂ k : Fin n, T^[k.val] ⁻¹' (f k).1
  rw [Set.mem_iInter]
  constructor
  · intro hlabel k
    have hk := congrFun hlabel k
    obtain ⟨A, hAP, hxA⟩ := (hx k).exists
    have hAlabel := partitionLabel_eq_of_unique P d (hx k) hAP hxA
    change partitionLabel P d (T^[k.val] x) = f k at hk
    rw [hAlabel] at hk
    exact hk ▸ hxA
  · intro hxmem
    funext k
    exact partitionLabel_eq_of_unique P d (hx k) (f k).2 (hxmem k)

lemma iteratedAtom_measure_zero_of_name_collision
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {n : ℕ} {f g : Fin n → ↥P} (hfg : f ≠ g)
    (hatom : (⋂ k : Fin n, T^[k.val] ⁻¹' (f k).1) =
      ⋂ k : Fin n, T^[k.val] ⁻¹' (g k).1) :
    mu (⋂ k : Fin n, T^[k.val] ⁻¹' (f k).1) = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hfg
  have hsets : (⋂ j : Fin n, T^[j.val] ⁻¹' (f j).1) ⊆
      T^[k.val] ⁻¹' ((f k).1 ∩ (g k).1) := by
    intro x hx
    have hxf := Set.mem_iInter.mp hx k
    have hxg := Set.mem_iInter.mp (hatom ▸ hx) k
    exact ⟨hxf, hxg⟩
  apply measure_mono_null hsets
  exact (hT.iterate k.val).preimage_null
    (hP.disjoint (f k).1 (f k).2 (g k).1 (g k).2 (Subtype.coe_ne_coe.mpr hk))

lemma observationEntropy_observationBlock_partitionLabel
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (d : ↥P) (n : ℕ) :
    observationEntropy mu (observationBlock T (partitionLabel P d) n) =
      partitionEntropy mu (iteratedJoin T P n) := by
  classical
  let atom : (Fin n → ↥P) → Set M := fun f =>
    ⋂ k : Fin n, T^[k.val] ⁻¹' (f k).1
  have hfiber (f : Fin n → ↥P) :
      mu.real (observationBlock T (partitionLabel P d) n ⁻¹' {f}) =
        mu.real (atom f) :=
    congrArg ENNReal.toReal
      (measure_congr (observationBlock_partitionLabel_fiber_ae_eq
        mu T hT P hP d n f))
  have hcollision : ((Finset.univ : Finset (Fin n → ↥P)) : Set (Fin n → ↥P)).Pairwise
      fun f g => atom f = atom g → Real.negMulLog (mu.real (atom f)) = 0 := by
    intro f _hf g _hg hfg hatom
    have hzero := iteratedAtom_measure_zero_of_name_collision
      mu T hT P hP hfg hatom
    have hzero' : mu (atom f) = 0 := by
      simpa [atom] using hzero
    rw [measureReal_def, hzero']
    simp
  unfold observationEntropy partitionEntropy
  rw [iteratedJoin_eq_image_subtype_names T P n]
  calc
    (∑ f : Fin n → ↥P,
        Real.negMulLog
          (mu.real (observationBlock T (partitionLabel P d) n ⁻¹' {f}))) =
        ∑ f : Fin n → ↥P, Real.negMulLog (mu.real (atom f)) := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [hfiber f]
    _ = ∑ A ∈ (Finset.univ : Finset (Fin n → ↥P)).image atom,
        Real.negMulLog (mu.real A) := by
      symm
      exact Finset.sum_image_of_pairwise_eq_zero hcollision

lemma observationEntropy_observationBlock_partitionIndexLabel
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (d : ↥P) (n : ℕ) :
    observationEntropy mu (observationBlock T (partitionIndexLabel P d) n) =
      partitionEntropy mu (iteratedJoin T P n) := by
  let e : (Fin n → ↥P) ≃ (Fin n → Fin (Fintype.card ↥P)) :=
    Equiv.piCongrRight fun _ => Fintype.equivFin ↥P
  have heq : observationBlock T (partitionIndexLabel P d) n =
      fun x => e (observationBlock T (partitionLabel P d) n x) := by
    funext x k
    rfl
  rw [heq, observationEntropy_equiv mu e]
  exact observationEntropy_observationBlock_partitionLabel mu T hT P hP d n

lemma measurable_partition_nonempty
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P) : P.Nonempty := by
  by_contra hPempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hPempty] at hP
  simpa using hP.cover

end Submission.Helpers
