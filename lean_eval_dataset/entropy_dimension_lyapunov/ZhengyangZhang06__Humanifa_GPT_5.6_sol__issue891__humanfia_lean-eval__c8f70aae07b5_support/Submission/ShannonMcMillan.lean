import Submission.ConditionalInformation

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma partitionSymbol_eq_iff_mem_atom_of_unique
    {M : Type*} (P : Finset (Set M))
    {x y : M}
    (hxunique : ∃! A : Set M, A ∈ P ∧ x ∈ A)
    (hyunique : ∃! A : Set M, A ∈ P ∧ y ∈ A)
    {A : Set M} (hAP : A ∈ P) (hxA : x ∈ A) :
    partitionSymbol P y = partitionSymbol P x ↔ y ∈ A := by
  constructor
  · intro hsymbol
    have hcoord := congrFun hsymbol (⟨A, hAP⟩ : ↥P)
    simpa [partitionSymbol, hxA] using hcoord
  · intro hyA
    funext C
    by_cases hCA : C.1 = A
    · subst A
      simp [partitionSymbol, hxA, hyA]
    · have hxC : x ∉ C.1 := by
        intro hxC
        exact hCA (hxunique.unique ⟨C.2, hxC⟩ ⟨hAP, hxA⟩)
      have hyC : y ∉ C.1 := by
        intro hyC
        exact hCA (hyunique.unique ⟨C.2, hyC⟩ ⟨hAP, hyA⟩)
      simp [partitionSymbol, hxC, hyC]

lemma ae_partitionSymbol_eq_iff_mem_atom
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {x : M} (hxunique : ∃! A : Set M, A ∈ P ∧ x ∈ A)
    {A : Set M} (hAP : A ∈ P) (hxA : x ∈ A) :
    ∀ᵐ y ∂mu, partitionSymbol P y = partitionSymbol P x ↔ y ∈ A := by
  filter_upwards [ae_existsUnique_partition_atom mu P hP] with y hyunique
  exact partitionSymbol_eq_iff_mem_atom_of_unique
    P hxunique hyunique hAP hxA

lemma ae_existsUnique_partition_atom_iterate
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (k : ℕ) :
    ∀ᵐ x ∂mu, ∃! A : Set M, A ∈ P ∧ T^[k] x ∈ A := by
  exact (hT.iterate k).quasiMeasurePreserving.tendsto_ae
    (ae_existsUnique_partition_atom mu P hP)

lemma futureObservation_fiber_ae_eq_preimage_iteratedAtom
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (n : ℕ) {x : M}
    (hxunique : ∀ k : Fin (n + 1),
      ∃! A : Set M, A ∈ P ∧ T^[k.val + 1] x ∈ A)
    (f : Fin (n + 1) → Set M)
    (hf : ∀ k, f k ∈ P)
    (hxf : ∀ k, T^[k.val + 1] x ∈ f k) :
    futureObservation T P n ⁻¹' {futureObservation T P n x} =ᵐ[mu]
      T ⁻¹' (⋂ k : Fin (n + 1), T^[k.val] ⁻¹' f k) := by
  have hyunique : ∀ᵐ y ∂mu, ∀ k : Fin (n + 1),
      ∃! A : Set M, A ∈ P ∧ T^[k.val + 1] y ∈ A := by
    rw [ae_all_iff]
    intro k
    exact ae_existsUnique_partition_atom_iterate
      mu T hT P hP (k.val + 1)
  filter_upwards [hyunique] with y hyunique
  apply propext
  change (futureObservation T P n y = futureObservation T P n x) ↔
    T y ∈ ⋂ k : Fin (n + 1), T^[k.val] ⁻¹' f k
  constructor
  · intro hobs
    apply Set.mem_iInter.mpr
    intro k
    change T^[k.val] (T y) ∈ f k
    rw [← Function.iterate_succ_apply]
    let j : Set.Iic n := ⟨k.val, Nat.le_of_lt_succ k.isLt⟩
    have hsymbol := congrFun hobs j
    have hmem := (partitionSymbol_eq_iff_mem_atom_of_unique
      P (hxunique k) (hyunique k) (hf k) (hxf k)).mp
        (by simpa [futureObservation, futureSymbol, j] using hsymbol)
    simpa [Nat.add_comm] using hmem
  · intro hy
    funext j
    let k : Fin (n + 1) := ⟨j.1, Nat.lt_succ_iff.mpr j.2⟩
    have hyk := Set.mem_iInter.mp hy k
    change T^[k.val] (T y) ∈ f k at hyk
    rw [← Function.iterate_succ_apply] at hyk
    have hsymbol := (partitionSymbol_eq_iff_mem_atom_of_unique
      P (hxunique k) (hyunique k) (hf k) (hxf k)).mpr
        (by simpa [Nat.add_comm] using hyk)
    simpa [futureObservation, futureSymbol, k] using hsymbol

lemma mem_iteratedJoin_one_of_mem
    {M : Type*} (T : M → M) (P : Finset (Set M))
    {A : Set M} (hAP : A ∈ P) :
    A ∈ iteratedJoin T P 1 := by
  classical
  rw [iteratedJoin]
  let f : Fin 1 → Set M := fun _ => A
  apply Finset.mem_image.mpr
  refine ⟨f, Fintype.mem_piFinset.mpr (fun _ => hAP), ?_⟩
  ext x
  simp [f]

lemma mem_iteratedJoin_succ_of_mem_tail
    {M : Type*} (T : M → M) (P : Finset (Set M))
    {A B : Set M} (hAP : A ∈ P) {n : ℕ}
    (hB : B ∈ iteratedJoin T P (n + 1)) :
    A ∩ T ⁻¹' B ∈ iteratedJoin T P (n + 2) := by
  classical
  rw [show n + 2 = 1 + (n + 1) by omega, iteratedJoin_add]
  unfold partitionJoin preimagePartition
  apply Finset.mem_image.mpr
  refine ⟨(A, T ⁻¹' B), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact mem_iteratedJoin_one_of_mem T P hAP
  · exact Finset.mem_image.mpr ⟨B, hB, rfl⟩

lemma futureConditionalProbability_eq_atom_ratio
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (n : ℕ) {x : M}
    (hxunique : ∀ k : Fin (n + 1),
      ∃! A : Set M, A ∈ P ∧ T^[k.val + 1] x ∈ A)
    {A B : Set M}
    (hB : B ∈ iteratedJoin T P (n + 1)) (hTxB : T x ∈ B) :
    futureConditionalProbability mu T P A n x =
      mu.real (A ∩ T ⁻¹' B) / mu.real B := by
  classical
  rw [iteratedJoin] at hB
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hB
  have hfP : ∀ k, f k ∈ P := Fintype.mem_piFinset.mp hf
  have hxf : ∀ k, T^[k.val + 1] x ∈ f k := by
    intro k
    have hk := Set.mem_iInter.mp hTxB k
    change T^[k.val] (T x) ∈ f k at hk
    rwa [← Function.iterate_succ_apply] at hk
  have heq := futureObservation_fiber_ae_eq_preimage_iteratedAtom
    mu T hT P hP n hxunique f hfP hxf
  let B : Set M := ⋂ k : Fin (n + 1), T^[k.val] ⁻¹' f k
  have hBmem : B ∈ iteratedJoin T P (n + 1) := by
    rw [iteratedJoin]
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  have hBmeas : MeasurableSet B :=
    measurableSet_of_mem_iteratedJoin T P hT.measurable hP.measurable
      (n + 1) hBmem
  have hdenom :
      mu.real (futureObservation T P n ⁻¹' {futureObservation T P n x}) =
        mu.real B := by
    have hmeasure :
      mu (futureObservation T P n ⁻¹' {futureObservation T P n x}) =
          mu B := by
      calc
        mu (futureObservation T P n ⁻¹' {futureObservation T P n x}) =
            mu (T ⁻¹' B) := measure_congr heq
        _ = mu B := hT.measure_preimage hBmeas.nullMeasurableSet
    exact congrArg ENNReal.toReal hmeasure
  have hinter :
      (A ∩ (futureObservation T P n ⁻¹' {futureObservation T P n x}) : Set M) =ᵐ[mu]
        (A ∩ T ⁻¹' B : Set M) := by
    filter_upwards [heq] with y hy
    exact congrArg (fun p : Prop => y ∈ A ∧ p) hy
  have hnum :
      mu.real (A ∩
          (futureObservation T P n ⁻¹' {futureObservation T P n x})) =
        mu.real (A ∩ T ⁻¹' B) := by
    rw [measureReal_def, measureReal_def, measure_congr hinter]
  rw [futureConditionalProbability, finiteConditionalProbability_apply,
    hnum, hdenom]

lemma futureConditionalInformation_eq_neg_log_of_unique
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (P : Finset (Set M))
    (n : ℕ) {x : M}
    (hxunique : ∃! A : Set M, A ∈ P ∧ x ∈ A)
    {A : Set M} (hAP : A ∈ P) (hxA : x ∈ A) :
    futureConditionalInformation mu T P n x =
      -Real.log (futureConditionalProbability mu T P A n x) := by
  unfold futureConditionalInformation
  rw [Finset.sum_eq_single A]
  · simp [hxA]
  · intro B hBP hBA
    have hxB : x ∉ B := by
      intro hxB
      exact hBA (hxunique.unique ⟨hBP, hxB⟩ ⟨hAP, hxA⟩)
    simp [hxB]
  · exact fun hAnot => (hAnot hAP).elim

lemma ae_partitionInformation_succ_chain
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (n : ℕ) :
    ∀ᵐ x ∂mu,
      partitionInformation mu (iteratedJoin T P (n + 2)) x =
        futureConditionalInformation mu T P n x +
          partitionInformation mu (iteratedJoin T P (n + 1)) (T x) := by
  let Q : Finset (Set M) := iteratedJoin T P (n + 1)
  let R : Finset (Set M) := iteratedJoin T P (n + 2)
  have hQ : IsMeasurablePartition mu Q :=
    isMeasurablePartition_iteratedJoin mu T hT P hP (n + 1)
  have hR : IsMeasurablePartition mu R :=
    isMeasurablePartition_iteratedJoin mu T hT P hP (n + 2)
  have hfutureUnique : ∀ᵐ x ∂mu, ∀ k : Fin (n + 1),
      ∃! A : Set M, A ∈ P ∧ T^[k.val + 1] x ∈ A := by
    rw [ae_all_iff]
    intro k
    exact ae_existsUnique_partition_atom_iterate
      mu T hT P hP (k.val + 1)
  have hQunique : ∀ᵐ x ∂mu, ∃! B : Set M, B ∈ Q ∧ T x ∈ B :=
    hT.quasiMeasurePreserving.tendsto_ae
      (ae_existsUnique_partition_atom mu Q hQ)
  have hQinfo : ∀ᵐ x ∂mu, ∀ B ∈ Q, T x ∈ B →
      partitionInformation mu Q (T x) = -Real.log (mu.real B) :=
    hT.quasiMeasurePreserving.tendsto_ae
      (partitionInformation_eq_neg_log_atom_ae mu Q hQ)
  have hQpos : ∀ᵐ x ∂mu, ∀ B ∈ Q, T x ∈ B → 0 < mu.real B :=
    hT.quasiMeasurePreserving.tendsto_ae
      (partition_atom_measureReal_pos_ae mu Q)
  filter_upwards
      [ae_existsUnique_partition_atom mu P hP, hfutureUnique, hQunique,
       partitionInformation_eq_neg_log_atom_ae mu R hR,
       hQinfo, partition_atom_measureReal_pos_ae mu R, hQpos]
      with x hxP hxfuture hxQ hRinfo hQinfo hRpos hQpos
  obtain ⟨A, hAP, hxA⟩ := hxP.exists
  obtain ⟨B, hBQ, hTxB⟩ := hxQ.exists
  let C : Set M := A ∩ T ⁻¹' B
  have hCR : C ∈ R := by
    exact mem_iteratedJoin_succ_of_mem_tail T P hAP hBQ
  have hxC : x ∈ C := ⟨hxA, hTxB⟩
  have hq := futureConditionalProbability_eq_atom_ratio
    mu T hT P hP n hxfuture (A := A) (B := B) hBQ hTxB
  change partitionInformation mu R x =
    futureConditionalInformation mu T P n x + partitionInformation mu Q (T x)
  rw [hRinfo C hCR hxC,
    futureConditionalInformation_eq_neg_log_of_unique
      mu T P n hxP hAP hxA,
    hQinfo B hBQ hTxB, hq]
  rw [Real.log_div (hRpos C hCR hxC).ne' (hQpos B hBQ hTxB).ne']
  ring

lemma integral_futureConditionalInformation_eq_entropy_sub
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (n : ℕ) :
    (∫ x, futureConditionalInformation mu T P n x ∂mu) =
      partitionEntropy mu (iteratedJoin T P (n + 2)) -
        partitionEntropy mu (iteratedJoin T P (n + 1)) := by
  let Q : Finset (Set M) := iteratedJoin T P (n + 1)
  let R : Finset (Set M) := iteratedJoin T P (n + 2)
  have hQ : IsMeasurablePartition mu Q :=
    isMeasurablePartition_iteratedJoin mu T hT P hP (n + 1)
  have hR : IsMeasurablePartition mu R :=
    isMeasurablePartition_iteratedJoin mu T hT P hP (n + 2)
  have hinfoQ : Integrable (partitionInformation mu Q) mu :=
    integrable_partitionInformation mu Q hQ.measurable
  have hinfoR : Integrable (partitionInformation mu R) mu :=
    integrable_partitionInformation mu R hR.measurable
  have hcond : Integrable (futureConditionalInformation mu T P n) mu :=
    integrable_futureConditionalInformation mu T hT.measurable P hP.measurable n
  have hcomp : Integrable (fun x => partitionInformation mu Q (T x)) mu :=
    integrable_comp_measurePreserving hT hinfoQ
  have heq := integral_congr_ae
    (ae_partitionInformation_succ_chain mu T hT P hP n)
  change (∫ x, partitionInformation mu R x ∂mu) =
      ∫ x, futureConditionalInformation mu T P n x +
        partitionInformation mu Q (T x) ∂mu at heq
  rw [integral_add hcond hcomp,
    integral_comp_measurePreserving hT hinfoQ,
    integral_partitionInformation mu R hR.measurable,
    integral_partitionInformation mu Q hQ.measurable] at heq
  change (∫ x, futureConditionalInformation mu T P n x ∂mu) =
    partitionEntropy mu R - partitionEntropy mu Q
  linarith

lemma integral_futureConditionalInformationLimit_eq_entropyW
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    (∫ x, futureConditionalInformationLimit
      mu T hT.measurable P hP.measurable x ∂mu) = entropyW mu T P := by
  let u : ℕ → ℝ := fun n => partitionEntropy mu (iteratedJoin T P n)
  let a : ℕ → ℝ := fun n => ∫ x, futureConditionalInformation mu T P n x ∂mu
  let L : ℝ := ∫ x, futureConditionalInformationLimit
    mu T hT.measurable P hP.measurable x ∂mu
  have ha_tend : Tendsto a atTop (nhds L) := by
    simpa [a, L] using tendsto_integral_futureConditionalInformationLimit
      mu T hT.measurable P hP.measurable
  have hinc (n : ℕ) : a n = u (n + 2) - u (n + 1) := by
    exact integral_futureConditionalInformation_eq_entropy_sub
      mu T hT P hP n
  have hsum (N : ℕ) :
      ∑ i ∈ Finset.range N, a i = u (N + 1) - u 1 := by
    calc
      (∑ i ∈ Finset.range N, a i) =
          ∑ i ∈ Finset.range N, (u (i + 2) - u (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hinc i
      _ = ∑ i ∈ Finset.range N,
          ((fun k => u (k + 1)) (i + 1) - (fun k => u (k + 1)) i) := by
        rfl
      _ = u (N + 1) - u 1 := Finset.sum_range_sub (fun k => u (k + 1)) N
  have havg_eq (N : ℕ) :
      (N⁻¹ : ℝ) * ∑ i ∈ Finset.range N, a i =
        (u (N + 1) - u 1) / N := by
    rw [hsum]
    simp [div_eq_mul_inv, mul_comm]
  have hcesaro : Tendsto
      (fun N : ℕ => (N⁻¹ : ℝ) * ∑ i ∈ Finset.range N, a i)
      atTop (nhds L) := ha_tend.cesaro
  have hu : Tendsto (fun n => u n / n) atTop (nhds (entropyW mu T P)) := by
    simpa [u] using tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT P hP
  have hshift : Tendsto (fun N => u (N + 1) / (N + 1))
      atTop (nhds (entropyW mu T P)) :=
    by simpa [Function.comp_def, Nat.cast_add] using
      hu.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfactorBase : Tendsto (fun N : ℕ => 1 + ((N : ℝ))⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hfactor : Tendsto
      (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
    apply hfactorBase.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    norm_num [Nat.cast_add]
    field_simp [hN0]
  have hprod := hshift.mul hfactor
  have hshiftDiv : Tendsto (fun N : ℕ => u (N + 1) / N)
      atTop (nhds (entropyW mu T P)) := by
    have hprod' : Tendsto (fun N : ℕ => u (N + 1) / N)
        atTop (nhds (entropyW mu T P * 1)) := by
      apply hprod.congr'
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num [Nat.cast_add]
      field_simp [hN0, hN1]
    simpa using hprod'
  have huOneDiv : Tendsto (fun N : ℕ => u 1 / N) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun N : ℕ => u 1 * ((N : ℝ))⁻¹) atTop (nhds (u 1 * 0)))
  have hentropyAverage : Tendsto
      (fun N : ℕ => (u (N + 1) - u 1) / N)
      atTop (nhds (entropyW mu T P)) := by
    simpa [sub_div] using hshiftDiv.sub huOneDiv
  have hcesaroEntropy : Tendsto
      (fun N : ℕ => (N⁻¹ : ℝ) * ∑ i ∈ Finset.range N, a i)
      atTop (nhds (entropyW mu T P)) := by
    apply hentropyAverage.congr'
    exact Filter.Eventually.of_forall fun N => (havg_eq N).symm
  exact tendsto_nhds_unique hcesaro hcesaroEntropy

lemma partitionInformation_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (P : Finset (Set M)) (x : M) :
    0 ≤ partitionInformation mu P x := by
  unfold partitionInformation
  apply Finset.sum_nonneg
  intro A _hAP
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA]
    exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)
  · simp [Set.indicator_of_notMem hxA]

lemma partitionInformation_chain_sum
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (P : Finset (Set M))
    {x : M}
    (hchain : ∀ k n,
      partitionInformation mu (iteratedJoin T P (n + 2)) (T^[k] x) =
        futureConditionalInformation mu T P n (T^[k] x) +
          partitionInformation mu (iteratedJoin T P (n + 1)) (T^[k + 1] x)) :
    ∀ k N,
      partitionInformation mu (iteratedJoin T P (N + 1)) (T^[k] x) =
        (∑ j ∈ Finset.range N,
          futureConditionalInformation mu T P (N - 1 - j) (T^[k + j] x)) +
          partitionInformation mu (iteratedJoin T P 1) (T^[k + N] x) := by
  intro k N
  induction N generalizing k with
  | zero => simp
  | succ N ih =>
      calc
        partitionInformation mu (iteratedJoin T P (N + 1 + 1)) (T^[k] x) =
            futureConditionalInformation mu T P N (T^[k] x) +
              partitionInformation mu (iteratedJoin T P (N + 1))
                (T^[k + 1] x) := by
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hchain k N
        _ = futureConditionalInformation mu T P N (T^[k] x) +
            ((∑ j ∈ Finset.range N,
              futureConditionalInformation mu T P (N - 1 - j)
                (T^[k + 1 + j] x)) +
              partitionInformation mu (iteratedJoin T P 1)
                (T^[k + 1 + N] x)) := by
          rw [ih (k + 1)]
        _ = (futureConditionalInformation mu T P N (T^[k] x) +
            ∑ j ∈ Finset.range N,
              futureConditionalInformation mu T P (N - 1 - j)
                (T^[k + 1 + j] x)) +
              partitionInformation mu (iteratedJoin T P 1)
                (T^[k + 1 + N] x) := by ring
        _ = (∑ j ∈ Finset.range (N + 1),
            futureConditionalInformation mu T P (N + 1 - 1 - j)
              (T^[k + j] x)) +
              partitionInformation mu (iteratedJoin T P 1)
                (T^[k + (N + 1)] x) := by
          congr 1
          · rw [Finset.sum_range_succ']
            conv_rhs => rw [add_comm]
            simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.add_zero]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]
          · congr 2
            omega

lemma ae_all_partitionInformation_succ_chain_iterate
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    ∀ᵐ x ∂mu, ∀ k n,
      partitionInformation mu (iteratedJoin T P (n + 2)) (T^[k] x) =
        futureConditionalInformation mu T P n (T^[k] x) +
          partitionInformation mu (iteratedJoin T P (n + 1)) (T^[k + 1] x) := by
  rw [ae_all_iff]
  intro k
  rw [ae_all_iff]
  intro n
  have h := (hT.iterate k).quasiMeasurePreserving.tendsto_ae
    (ae_partitionInformation_succ_chain mu T hT P hP n)
  filter_upwards [h] with x hx
  simpa [Function.iterate_succ_apply'] using hx

def futureInformationBadSet
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M)
    (P : Finset (Set M)) (hT : Measurable T)
    (hP : ∀ A ∈ P, MeasurableSet A)
    (delta : ℝ) (N : ℕ) : Set M :=
  ⋃ r : {r : ℕ // N ≤ r},
    {x | futureConditionalInformation mu T P r.1 x <
      futureConditionalInformationLimit mu T hT P hP x - delta}

lemma measurableSet_futureInformationBadSet
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M)
    (P : Finset (Set M)) (hT : Measurable T)
    (hP : ∀ A ∈ P, MeasurableSet A)
    (delta : ℝ) (N : ℕ) :
    MeasurableSet (futureInformationBadSet mu T P hT hP delta N) := by
  unfold futureInformationBadSet
  apply MeasurableSet.iUnion
  intro r
  exact measurableSet_lt
    (measurable_futureConditionalInformation mu T hT P hP r.1)
    ((measurable_futureConditionalInformationLimit mu T hT P hP).sub
      measurable_const)

lemma mem_futureInformationBadSet_iff
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M)
    (P : Finset (Set M)) (hT : Measurable T)
    (hP : ∀ A ∈ P, MeasurableSet A)
    (delta : ℝ) (N : ℕ) (x : M) :
    x ∈ futureInformationBadSet mu T P hT hP delta N ↔
      ∃ r, N ≤ r ∧ futureConditionalInformation mu T P r x <
        futureConditionalInformationLimit mu T hT P hP x - delta := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    exact ⟨r.1, r.2, hr⟩
  · rintro ⟨r, hrN, hr⟩
    exact Set.mem_iUnion_of_mem (⟨r, hrN⟩ : {r : ℕ // N ≤ r}) hr

lemma tendsto_integral_futureInformationBadSet
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto
      (fun N => ∫ x,
        (futureInformationBadSet mu T P hT hP delta N).indicator
          (futureConditionalInformationLimit mu T hT P hP) x ∂mu)
      atTop (nhds 0) := by
  let cInf := futureConditionalInformationLimit mu T hT P hP
  have hdom : Tendsto
      (fun N => ∫ x,
        (futureInformationBadSet mu T P hT hP delta N).indicator cInf x ∂mu)
      atTop (nhds (∫ _x, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖cInf x‖)
    · intro N
      exact ((measurable_futureConditionalInformationLimit mu T hT P hP).indicator
        (measurableSet_futureInformationBadSet mu T P hT hP delta N)).aestronglyMeasurable
    · exact (integrable_futureConditionalInformationLimit mu T hT P hP).norm
    · intro N
      exact Filter.Eventually.of_forall fun x =>
        norm_indicator_le_norm_self _ _
    · filter_upwards
        [ae_tendsto_futureConditionalInformation mu T hT P hP] with x hx
      have hevent : ∀ᶠ r in atTop,
          cInf x - delta < futureConditionalInformation mu T P r x :=
        (tendsto_order.1 hx).1 _ (sub_lt_self (cInf x) hdelta)
      obtain ⟨N0, hN0⟩ := eventually_atTop.1 hevent
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N0] with N hN
      rw [Set.indicator_of_notMem]
      intro hbad
      obtain ⟨r, hNr, hr⟩ :=
        (mem_futureInformationBadSet_iff mu T P hT hP delta N x).mp hbad
      exact (not_lt_of_ge (hN0 r (hN.trans hNr)).le) hr
  simpa [cInf] using hdom

lemma futureConditionalInformation_lower_bound_badSet
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (T : M → M) (P : Finset (Set M))
    (hT : Measurable T) (hP : ∀ A ∈ P, MeasurableSet A)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {N r : ℕ} (hNr : N ≤ r) (x : M) :
    futureConditionalInformationLimit mu T hT P hP x - delta -
        (futureInformationBadSet mu T P hT hP delta N).indicator
          (futureConditionalInformationLimit mu T hT P hP) x ≤
      futureConditionalInformation mu T P r x := by
  by_cases hxbad : x ∈ futureInformationBadSet mu T P hT hP delta N
  · rw [Set.indicator_of_mem hxbad]
    linarith [futureConditionalInformation_nonneg mu T P r x]
  · rw [Set.indicator_of_notMem hxbad, sub_zero]
    apply le_of_not_gt
    intro hlt
    apply hxbad
    exact (mem_futureInformationBadSet_iff mu T P hT hP delta N x).mpr
      ⟨r, hNr, hlt⟩

lemma partitionInformation_lower_birkhoffAverage
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (P : Finset (Set M))
    (hT : Measurable T) (hP : ∀ A ∈ P, MeasurableSet A)
    {x : M}
    (hchain : ∀ k n,
      partitionInformation mu (iteratedJoin T P (n + 2)) (T^[k] x) =
        futureConditionalInformation mu T P n (T^[k] x) +
          partitionInformation mu (iteratedJoin T P (n + 1)) (T^[k + 1] x))
    {delta : ℝ} (hdelta : 0 ≤ delta) (N0 : ℕ)
    {L : ℕ} (hL : 0 < L) :
    ((L : ℝ) / (L + N0 + 1 : ℕ)) *
        (birkhoffAverage ℝ T
            (futureConditionalInformationLimit mu T hT P hP) L x - delta -
          birkhoffAverage ℝ T
            ((futureInformationBadSet mu T P hT hP delta N0).indicator
              (futureConditionalInformationLimit mu T hT P hP)) L x) ≤
      partitionInformation mu (iteratedJoin T P (L + N0 + 1)) x /
        (L + N0 + 1 : ℕ) := by
  let cInf := futureConditionalInformationLimit mu T hT P hP
  let badInfo := (futureInformationBadSet mu T P hT hP delta N0).indicator cInf
  let total := L + N0
  have hindex (j : ℕ) (hj : j ∈ Finset.range L) :
      N0 ≤ total - 1 - j := by
    have hjlt := Finset.mem_range.mp hj
    dsimp [total]
    omega
  have hterm (j : ℕ) (hj : j ∈ Finset.range L) :
      cInf (T^[j] x) - delta - badInfo (T^[j] x) ≤
        futureConditionalInformation mu T P (total - 1 - j) (T^[j] x) := by
    exact futureConditionalInformation_lower_bound_badSet
      mu T P hT hP hdelta (hindex j hj) (T^[j] x)
  have hsum_le :
      (∑ j ∈ Finset.range L,
          (cInf (T^[j] x) - delta - badInfo (T^[j] x))) ≤
        partitionInformation mu (iteratedJoin T P (total + 1)) x := by
    calc
      (∑ j ∈ Finset.range L,
          (cInf (T^[j] x) - delta - badInfo (T^[j] x))) ≤
          ∑ j ∈ Finset.range L,
            futureConditionalInformation mu T P (total - 1 - j) (T^[j] x) :=
        Finset.sum_le_sum hterm
      _ ≤ ∑ j ∈ Finset.range total,
            futureConditionalInformation mu T P (total - 1 - j) (T^[j] x) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr
            ((Finset.mem_range.mp hj).trans_le (Nat.le_add_right L N0))
        · intro j _hj _hjL
          exact futureConditionalInformation_nonneg
            mu T P (total - 1 - j) (T^[j] x)
      _ ≤ (∑ j ∈ Finset.range total,
            futureConditionalInformation mu T P (total - 1 - j) (T^[j] x)) +
          partitionInformation mu (iteratedJoin T P 1) (T^[total] x) :=
        le_add_of_nonneg_right (partitionInformation_nonneg
          mu (iteratedJoin T P 1) (T^[total] x))
      _ = partitionInformation mu (iteratedJoin T P (total + 1)) x := by
        simpa using (partitionInformation_chain_sum mu T P hchain 0 total).symm
  have hdenom : (0 : ℝ) < (L + N0 + 1 : ℕ) := by positivity
  change ((L : ℝ) / (L + N0 + 1 : ℕ)) *
      (birkhoffAverage ℝ T cInf L x - delta -
        birkhoffAverage ℝ T badInfo L x) ≤
    partitionInformation mu (iteratedJoin T P (L + N0 + 1)) x /
      (L + N0 + 1 : ℕ)
  rw [show ((L : ℝ) / (L + N0 + 1 : ℕ)) *
      (birkhoffAverage ℝ T cInf L x - delta -
        birkhoffAverage ℝ T badInfo L x) =
      ((L : ℝ) * (birkhoffAverage ℝ T cInf L x - delta -
        birkhoffAverage ℝ T badInfo L x)) / (L + N0 + 1 : ℕ) by ring]
  apply (div_le_div_iff_of_pos_right hdenom).2
  calc
    (L : ℝ) * (birkhoffAverage ℝ T cInf L x - delta -
          birkhoffAverage ℝ T badInfo L x) =
        ∑ j ∈ Finset.range L,
          (cInf (T^[j] x) - delta - badInfo (T^[j] x)) := by
      rw [birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum]
      simp only [smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp [hL0]
    _ ≤ partitionInformation mu (iteratedJoin T P (total + 1)) x := hsum_le
    _ = partitionInformation mu (iteratedJoin T P (L + N0 + 1)) x := by
      congr 2

lemma ae_eventually_partitionInformation_div_gt_entropy_sub
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ n in atTop,
      entropyW mu T P - epsilon <
        partitionInformation mu (iteratedJoin T P n) x / n := by
  let delta : ℝ := epsilon / 4
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  have hbadTend := tendsto_integral_futureInformationBadSet
    mu T hT.measurable P hP.measurable hdelta
  have hbadEventually : ∀ᶠ N in atTop,
      (∫ x,
        (futureInformationBadSet mu T P hT.measurable hP.measurable delta N).indicator
          (futureConditionalInformationLimit
            mu T hT.measurable P hP.measurable) x ∂mu) < delta :=
    (tendsto_order.1 hbadTend).2 delta hdelta
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hbadEventually
  let cInf := futureConditionalInformationLimit mu T hT.measurable P hP.measurable
  let badSet := futureInformationBadSet
    mu T P hT.measurable hP.measurable delta N0
  let badInfo := badSet.indicator cInf
  have hbadIntegral : (∫ x, badInfo x ∂mu) < delta := by
    exact hN0 N0 le_rfl
  have hcMeas : Measurable cInf :=
    measurable_futureConditionalInformationLimit mu T hT.measurable P hP.measurable
  have hcInt : Integrable cInf mu :=
    integrable_futureConditionalInformationLimit mu T hT.measurable P hP.measurable
  have hbadMeas : MeasurableSet badSet :=
    measurableSet_futureInformationBadSet
      mu T P hT.measurable hP.measurable delta N0
  have hbadInfoMeas : Measurable badInfo := hcMeas.indicator hbadMeas
  have hbadInfoInt : Integrable badInfo mu := hcInt.indicator hbadMeas
  have hcAverage := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg cInf hcMeas hcInt
  have hbadAverage := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg badInfo hbadInfoMeas hbadInfoInt
  have hchain := ae_all_partitionInformation_succ_chain_iterate
    mu T hT P hP
  filter_upwards [hcAverage, hbadAverage, hchain] with x hcx hbadx hxchain
  let C : ℕ := N0 + 1
  have hdenTop : Tendsto (fun L : ℕ => (((L + C : ℕ) : ℝ)))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat C)
  have hinvDen : Tendsto (fun L : ℕ => (((L + C : ℕ) : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hdenTop
  have hratioBase : Tendsto
      (fun L : ℕ => 1 - (C : ℝ) * (((L + C : ℕ) : ℝ))⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinvDen)
  have hratio : Tendsto
      (fun L : ℕ => (L : ℝ) / (L + C : ℕ)) atTop (nhds 1) := by
    apply hratioBase.congr'
    exact Filter.Eventually.of_forall fun L => by
      have hC : 0 < C := by simp [C]
      have hden0 : (C : ℝ) + (L : ℝ) ≠ 0 := by positivity
      norm_num [Nat.cast_add]
      field_simp [hden0]
      ring
  have hinside : Tendsto
      (fun L => birkhoffAverage ℝ T cInf L x - delta -
        birkhoffAverage ℝ T badInfo L x)
      atTop (nhds ((∫ y, cInf y ∂mu) - delta - ∫ y, badInfo y ∂mu)) :=
    hcx.sub tendsto_const_nhds |>.sub hbadx
  have hrhs : Tendsto
      (fun L : ℕ => ((L : ℝ) / (L + C : ℕ)) *
        (birkhoffAverage ℝ T cInf L x - delta -
          birkhoffAverage ℝ T badInfo L x))
      atTop
      (nhds (1 * ((∫ y, cInf y ∂mu) - delta - ∫ y, badInfo y ∂mu))) :=
    hratio.mul hinside
  have hcIntegral : (∫ y, cInf y ∂mu) = entropyW mu T P := by
    exact integral_futureConditionalInformationLimit_eq_entropyW
      mu T T_inv hT_right hT P hP
  have hlimitLower : entropyW mu T P - epsilon <
      1 * ((∫ y, cInf y ∂mu) - delta - ∫ y, badInfo y ∂mu) := by
    rw [hcIntegral]
    dsimp [delta] at hbadIntegral ⊢
    linarith
  have hrhsEventually : ∀ᶠ L : ℕ in atTop,
      entropyW mu T P - epsilon <
        ((L : ℝ) / (L + C : ℕ)) *
          (birkhoffAverage ℝ T cInf L x - delta -
            birkhoffAverage ℝ T badInfo L x) :=
    (tendsto_order.1 hrhs).1 _ hlimitLower
  obtain ⟨L0, hL0⟩ := eventually_atTop.1
    (hrhsEventually.and (eventually_gt_atTop 0))
  apply eventually_atTop.2
  refine ⟨L0 + C, ?_⟩
  intro n hn
  let L := n - C
  have hCn : C ≤ n := (Nat.le_add_left C L0).trans hn
  have hLC : L + C = n := Nat.sub_add_cancel hCn
  have hL0le : L0 ≤ L := Nat.le_sub_of_add_le hn
  obtain ⟨hrhsLower, hLpos⟩ := hL0 L hL0le
  have hgeom := partitionInformation_lower_birkhoffAverage
    mu T P hT.measurable hP.measurable hxchain hdelta.le N0 hLpos
  have hfinal := hrhsLower.trans_le hgeom
  simpa [cInf, badInfo, badSet, C, L, hLC, Nat.add_assoc] using hfinal

lemma ae_eventually_mem_entropy_lightAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      x ∈ ⋃ A ∈ lightAtoms mu (iteratedJoin T P n)
        ((entropyW mu T P - epsilon) * n), A := by
  have hlower := ae_eventually_partitionInformation_div_gt_entropy_sub
    mu T T_inv hT_right hT hErg P hP hepsilon
  have hthreshold : ∀ᵐ x ∂mu, ∀ n : ℕ,
      (x ∈ ⋃ A ∈ lightAtoms mu (iteratedJoin T P n)
          ((entropyW mu T P - epsilon) * n), A ↔
        (entropyW mu T P - epsilon) * n <
          partitionInformation mu (iteratedJoin T P n) x) := by
    apply ae_all_iff.2
    intro n
    exact mem_iUnion_lightAtoms_iff_information_gt_ae
      mu (iteratedJoin T P n)
        (isMeasurablePartition_iteratedJoin mu T hT P hP n)
        ((entropyW mu T P - epsilon) * n)
  filter_upwards [hlower, hthreshold] with x hxlower hxthreshold
  filter_upwards [hxlower, eventually_gt_atTop 0] with n hn hnpos
  apply (hxthreshold n).2
  have hnposReal : (0 : ℝ) < n := by exact_mod_cast hnpos
  exact (lt_div_iff₀ hnposReal).mp hn

end Submission.Helpers
