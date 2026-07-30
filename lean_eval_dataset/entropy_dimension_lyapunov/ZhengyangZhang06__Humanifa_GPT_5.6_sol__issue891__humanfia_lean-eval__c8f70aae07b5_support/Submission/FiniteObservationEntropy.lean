import Submission.ConditionalPartitionEntropy

namespace Submission.Helpers

open MeasureTheory

noncomputable def conditionalObservationEntropy
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    (mu : Measure M) (X : M → I) (Y : M → J) : ℝ :=
  ∑ y : J, mu.real (Y ⁻¹' {y}) *
    ∑ i : I, Real.negMulLog
      (mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) / mu.real (Y ⁻¹' {y}))

lemma observationEntropy_pair
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X) (Y : M → J) (hY : Measurable Y) :
    observationEntropy mu (fun x => (X x, Y x)) =
      observationEntropy mu Y + conditionalObservationEntropy mu X Y := by
  classical
  let p : J → I → ℝ := fun y i => mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i})
  let row : J → ℝ := fun y => mu.real (Y ⁻¹' {y})
  have hp (y : J) (i : I) : 0 ≤ p y i := measureReal_nonneg
  have hrow (y : J) : ∑ i : I, p y i = row y := by
    simpa [p, row] using sum_measureReal_inter_fibers mu X hX
      (hY (measurableSet_singleton y)) Set.univ
  have hchain (y : J) :
      (∑ i : I, Real.negMulLog (p y i)) =
        Real.negMulLog (row y) + row y *
          ∑ i : I, Real.negMulLog (p y i / row y) := by
    rw [sum_negMulLog_eq_negMulLog_sum_add (p y) (hp y), hrow y]
  unfold observationEntropy conditionalObservationEntropy
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : I, ∑ y : J,
        Real.negMulLog (mu.real ((fun z => (X z, Y z)) ⁻¹' {(x, y)}))) =
        ∑ y : J, ∑ i : I, Real.negMulLog (p y i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro i _hi
      congr 2
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Prod.mk.injEq]
      aesop
    _ = ∑ y : J, (Real.negMulLog (row y) + row y *
        ∑ i : I, Real.negMulLog (p y i / row y)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact hchain y
    _ = (∑ y : J, Real.negMulLog (mu.real (Y ⁻¹' {y}))) +
        ∑ y : J, mu.real (Y ⁻¹' {y}) *
          ∑ i : I, Real.negMulLog
            (mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) /
              mu.real (Y ⁻¹' {y})) := by
      rw [Finset.sum_add_distrib]

lemma conditionalObservationEntropy_eq_sub
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X) (Y : M → J) (hY : Measurable Y) :
    conditionalObservationEntropy mu X Y =
      observationEntropy mu (fun x => (X x, Y x)) - observationEntropy mu Y := by
  rw [observationEntropy_pair mu X hX Y hY]
  ring

lemma observationEntropy_equiv
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    (mu : Measure M) (e : I ≃ J) (X : M → I) :
    observationEntropy mu (fun x => e (X x)) = observationEntropy mu X := by
  classical
  unfold observationEntropy
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 2
  ext x
  simp

lemma observationEntropy_pair_swap
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    (mu : Measure M) (X : M → I) (Y : M → J) :
    observationEntropy mu (fun x => (X x, Y x)) =
      observationEntropy mu (fun x => (Y x, X x)) := by
  let e : I × J ≃ J × I := Equiv.prodComm I J
  simpa [e] using
    (observationEntropy_equiv mu e (fun x => (X x, Y x))).symm

lemma observationEntropy_pair_assoc
    {M I J K : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype J] [Fintype K]
    (mu : Measure M) (X : M → I) (Y : M → J) (Z : M → K) :
    observationEntropy mu (fun x => ((X x, Z x), Y x)) =
      observationEntropy mu (fun x => (X x, (Y x, Z x))) := by
  let e : (I × K) × J ≃ I × (J × K) :=
    { toFun := fun a => (a.1.1, (a.2, a.1.2))
      invFun := fun a => ((a.1, a.2.2), a.2.1)
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  simpa [e] using
    (observationEntropy_equiv mu e (fun x => ((X x, Z x), Y x))).symm

lemma conditionalObservationEntropy_equiv
    {M I I' J J' : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace I'] [MeasurableSingletonClass I']
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace J'] [MeasurableSingletonClass J']
    (mu : Measure M) [IsProbabilityMeasure mu]
    (eX : I ≃ I') (eY : J ≃ J')
    (X : M → I) (hX : Measurable X) (Y : M → J) (hY : Measurable Y) :
    conditionalObservationEntropy mu (fun x => eX (X x)) (fun x => eY (Y x)) =
      conditionalObservationEntropy mu X Y := by
  rw [conditionalObservationEntropy_eq_sub mu (fun x => eX (X x))
      ((measurable_of_finite eX).comp hX) (fun x => eY (Y x))
        ((measurable_of_finite eY).comp hY),
    conditionalObservationEntropy_eq_sub mu X hX Y hY,
    observationEntropy_equiv mu eY Y]
  let ePair : I × J ≃ I' × J' := eX.prodCongr eY
  rw [show (fun x => (eX (X x), eY (Y x))) =
      fun x => ePair (X x, Y x) by rfl,
    observationEntropy_equiv mu ePair (fun x => (X x, Y x))]

lemma conditionalObservationEntropy_chain
    {M I J K : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype J] [Fintype K]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X)
    (Y : M → J) (hY : Measurable Y)
    (Z : M → K) (hZ : Measurable Z) :
    conditionalObservationEntropy mu (fun x => (X x, Z x)) Y =
      conditionalObservationEntropy mu Z Y +
        conditionalObservationEntropy mu X (fun x => (Y x, Z x)) := by
  rw [conditionalObservationEntropy_eq_sub mu (fun x => (X x, Z x))
      (hX.prodMk hZ) Y hY,
    conditionalObservationEntropy_eq_sub mu Z hZ Y hY,
    conditionalObservationEntropy_eq_sub mu X hX (fun x => (Y x, Z x))
      (hY.prodMk hZ),
    observationEntropy_pair_assoc mu X Y Z,
    observationEntropy_pair_swap mu Z Y]
  ring

lemma conditionalObservationEntropy_pair_le
    {M I J K : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype J] [Fintype K]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X)
    (Z : M → K) (hZ : Measurable Z)
    (Y : M → J) (hY : Measurable Y) :
    conditionalObservationEntropy mu (fun x => (X x, Z x)) Y ≤
      conditionalObservationEntropy mu X Y +
        conditionalObservationEntropy mu Z Y := by
  classical
  let row : J → ℝ := fun y => mu.real (Y ⁻¹' {y})
  let p : J → I → K → ℝ := fun y i k =>
    mu.real (Y ⁻¹' {y} ∩ (X ⁻¹' {i} ∩ Z ⁻¹' {k}))
  have hp (y : J) (i : I) (k : K) : 0 ≤ p y i k := measureReal_nonneg
  have hsum_k (y : J) (i : I) : ∑ k : K, p y i k =
      mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) := by
    simpa [p, Set.inter_assoc] using sum_measureReal_inter_fibers mu Z hZ
      ((hY (measurableSet_singleton y)).inter
        (hX (measurableSet_singleton i))) Set.univ
  have hsum_i (y : J) (k : K) : ∑ i : I, p y i k =
      mu.real (Y ⁻¹' {y} ∩ Z ⁻¹' {k}) := by
    simpa [p, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
      sum_measureReal_inter_fibers mu X hX
        ((hY (measurableSet_singleton y)).inter
          (hZ (measurableSet_singleton k))) Set.univ
  have htotal (y : J) : ∑ i : I, ∑ k : K, p y i k = row y := by
    rw [show (∑ i : I, ∑ k : K, p y i k) =
        ∑ i : I, mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hsum_k y i]
    simpa [row] using sum_measureReal_inter_fibers mu X hX
      (hY (measurableSet_singleton y)) Set.univ
  have hy (y : J) : row y *
      (∑ i : I, ∑ k : K, Real.negMulLog (p y i k / row y)) ≤
        row y * ((∑ i : I, Real.negMulLog
          (mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) / row y)) +
          ∑ k : K, Real.negMulLog
            (mu.real (Y ⁻¹' {y} ∩ Z ⁻¹' {k}) / row y)) := by
    by_cases hrow : row y = 0
    · simp [hrow]
    · have hrow_pos : 0 < row y := lt_of_le_of_ne measureReal_nonneg (Ne.symm hrow)
      let q : I → K → ℝ := fun i k => p y i k / row y
      have hq (i : I) (k : K) : 0 ≤ q i k := div_nonneg (hp y i k) hrow_pos.le
      have hqtotal : ∑ i : I, ∑ k : K, q i k = 1 := by
        simp only [q, ← Finset.sum_div]
        rw [htotal y, div_self hrow]
      have hjoint := finite_joint_entropy_le_marginals q hq hqtotal
      apply mul_le_mul_of_nonneg_left _ hrow_pos.le
      convert hjoint using 1
      · rfl
      · apply congrArg₂ (fun a b : ℝ => a + b)
        · apply Finset.sum_congr rfl
          intro i _hi
          congr 2
          rw [← Finset.sum_div, hsum_k]
        · apply Finset.sum_congr rfl
          intro k _hk
          congr 2
          rw [← Finset.sum_div, hsum_i]
  unfold conditionalObservationEntropy
  calc
    (∑ y : J, mu.real (Y ⁻¹' {y}) *
        ∑ a : I × K, Real.negMulLog
          (mu.real (Y ⁻¹' {y} ∩ (fun x => (X x, Z x)) ⁻¹' {a}) /
            mu.real (Y ⁻¹' {y}))) =
        ∑ y : J, row y * ∑ i : I, ∑ k : K,
          Real.negMulLog (p y i k / row y) := by
      apply Finset.sum_congr rfl
      intro y _hy
      congr 1
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro k _hk
      congr 3
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Prod.mk.injEq]
    _ ≤ ∑ y : J, row y *
        ((∑ i : I, Real.negMulLog
          (mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) / row y)) +
        ∑ k : K, Real.negMulLog
          (mu.real (Y ⁻¹' {y} ∩ Z ⁻¹' {k}) / row y)) :=
      Finset.sum_le_sum fun y _hy => hy y
    _ = (∑ y : J, mu.real (Y ⁻¹' {y}) *
          ∑ i : I, Real.negMulLog
            (mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) / mu.real (Y ⁻¹' {y}))) +
        ∑ y : J, mu.real (Y ⁻¹' {y}) *
          ∑ k : K, Real.negMulLog
            (mu.real (Y ⁻¹' {y} ∩ Z ⁻¹' {k}) / mu.real (Y ⁻¹' {y})) := by
      simp only [row, mul_add, Finset.sum_add_distrib]

lemma conditionalObservationEntropy_mono_conditioning
    {M I J K : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype J] [Fintype K]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X)
    (Y : M → J) (hY : Measurable Y)
    (Z : M → K) (hZ : Measurable Z) :
    conditionalObservationEntropy mu X (fun x => (Y x, Z x)) ≤
      conditionalObservationEntropy mu X Y := by
  have hsub := conditionalObservationEntropy_pair_le
    mu X hX Z hZ Y hY
  rw [conditionalObservationEntropy_chain mu X hX Y hY Z hZ] at hsub
  linarith

lemma conditionalObservationEntropy_pair_pair_le
    {M I₁ I₂ J₁ J₂ : Type*} [MeasurableSpace M]
    [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂]
    [MeasurableSpace I₁] [MeasurableSingletonClass I₁]
    [MeasurableSpace I₂] [MeasurableSingletonClass I₂]
    [MeasurableSpace J₁] [MeasurableSingletonClass J₁]
    [MeasurableSpace J₂] [MeasurableSingletonClass J₂]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X₁ : M → I₁) (hX₁ : Measurable X₁)
    (X₂ : M → I₂) (hX₂ : Measurable X₂)
    (Y₁ : M → J₁) (hY₁ : Measurable Y₁)
    (Y₂ : M → J₂) (hY₂ : Measurable Y₂) :
    conditionalObservationEntropy mu (fun x => (X₁ x, X₂ x))
        (fun x => (Y₁ x, Y₂ x)) ≤
      conditionalObservationEntropy mu X₁ Y₁ +
        conditionalObservationEntropy mu X₂ Y₂ := by
  have hpair := conditionalObservationEntropy_pair_le mu X₁ hX₁ X₂ hX₂
    (fun x => (Y₁ x, Y₂ x)) (hY₁.prodMk hY₂)
  have hfirst := conditionalObservationEntropy_mono_conditioning
    mu X₁ hX₁ Y₁ hY₁ Y₂ hY₂
  have hsecondSwap : conditionalObservationEntropy mu X₂ (fun x => (Y₁ x, Y₂ x)) =
      conditionalObservationEntropy mu X₂ (fun x => (Y₂ x, Y₁ x)) := by
    let eX : I₂ ≃ I₂ := Equiv.refl I₂
    let eY : J₁ × J₂ ≃ J₂ × J₁ := Equiv.prodComm J₁ J₂
    simpa [eX, eY] using
      (conditionalObservationEntropy_equiv mu eX eY X₂ hX₂
        (fun x => (Y₁ x, Y₂ x)) (hY₁.prodMk hY₂)).symm
  have hsecondBase := conditionalObservationEntropy_mono_conditioning
    mu X₂ hX₂ Y₂ hY₂ Y₁ hY₁
  rw [hsecondSwap] at hpair
  exact hpair.trans (add_le_add hfirst hsecondBase)

lemma observationEntropy_comp_measurePreserving
    {M I : Type*} [MeasurableSpace M] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : Measure M) (S : M → M) (hS : MeasurePreserving S mu mu)
    (X : M → I) (hX : Measurable X) :
    observationEntropy mu (fun x => X (S x)) = observationEntropy mu X := by
  unfold observationEntropy
  apply Finset.sum_congr rfl
  intro i _hi
  have hpre := hS.measure_preimage
    (hX (measurableSet_singleton i)).nullMeasurableSet
  exact congrArg Real.negMulLog (congrArg ENNReal.toReal hpre)

lemma conditionalObservationEntropy_comp_measurePreserving
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (S : M → M) (hS : MeasurePreserving S mu mu)
    (X : M → I) (hX : Measurable X) (Y : M → J) (hY : Measurable Y) :
    conditionalObservationEntropy mu (fun x => X (S x)) (fun x => Y (S x)) =
      conditionalObservationEntropy mu X Y := by
  have hpair := observationEntropy_comp_measurePreserving mu S hS
    (fun x => (X x, Y x)) (hX.prodMk hY)
  have hy := observationEntropy_comp_measurePreserving mu S hS Y hY
  rw [conditionalObservationEntropy_eq_sub mu (fun x => X (S x))
      (hX.comp hS.measurable) (fun x => Y (S x)) (hY.comp hS.measurable),
    conditionalObservationEntropy_eq_sub mu X hX Y hY, hy]
  exact congrArg (fun z => z - observationEntropy mu Y) hpair

end Submission.Helpers
