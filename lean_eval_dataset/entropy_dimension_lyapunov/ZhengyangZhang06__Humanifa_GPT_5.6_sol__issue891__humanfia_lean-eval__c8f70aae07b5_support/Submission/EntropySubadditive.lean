import Submission.CenteredNameStability

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

lemma finite_joint_entropy_le_marginals
    {I J : Type*} [Fintype I] [Fintype J]
    (p : I → J → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (htotal : ∑ i, ∑ j, p i j = 1) :
    (∑ i, ∑ j, Real.negMulLog (p i j)) ≤
      (∑ i, Real.negMulLog (∑ j, p i j)) +
        ∑ j, Real.negMulLog (∑ i, p i j) := by
  classical
  let row : I → ℝ := fun i => ∑ j, p i j
  let col : J → ℝ := fun j => ∑ i, p i j
  let cond : I → J → ℝ := fun i j =>
    if row i = 0 then 0 else p i j / row i
  have hrow_nonneg (i : I) : 0 ≤ row i := by
    exact Finset.sum_nonneg fun j _ => hp i j
  have hrow_sum : ∑ i, row i = 1 := by
    simpa [row] using htotal
  have hp_le_row (i : I) (j : J) : p i j ≤ row i := by
    exact Finset.single_le_sum (fun j _ => hp i j) (Finset.mem_univ j)
  have hp_zero (i : I) (hi : row i = 0) (j : J) : p i j = 0 := by
    exact le_antisymm (by simpa [hi] using hp_le_row i j) (hp i j)
  have hcond_nonneg (i : I) (j : J) : 0 ≤ cond i j := by
    dsimp [cond]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hp i j) (hrow_nonneg i)
  have hrow_mul_cond (i : I) (j : J) : row i * cond i j = p i j := by
    dsimp [cond]
    split_ifs with hi
    · simp [hi, hp_zero i hi j]
    · exact mul_div_cancel₀ (p i j) hi
  have hsum_cond (i : I) :
      (∑ j, cond i j) * Real.negMulLog (row i) =
        Real.negMulLog (row i) := by
    by_cases hi : row i = 0
    · simp [cond, hi]
    · have hsum : ∑ j, cond i j = 1 := by
        dsimp [cond]
        simp only [hi, if_false, ← Finset.sum_div]
        exact div_self hi
      rw [hsum, one_mul]
  have hcol_cond (j : J) : ∑ i, row i * cond i j = col j := by
    simp only [hrow_mul_cond, col]
  have hjensen (j : J) :
      (∑ i, row i * Real.negMulLog (cond i j)) ≤
        Real.negMulLog (col j) := by
    have h := Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (w := row) (p := fun i => cond i j)
      (fun i _ => hrow_nonneg i) hrow_sum
      (fun i _ => hcond_nonneg i j)
    simpa [smul_eq_mul, hcol_cond] using h
  calc
    (∑ i, ∑ j, Real.negMulLog (p i j)) =
        ∑ i, ∑ j,
          (cond i j * Real.negMulLog (row i) +
            row i * Real.negMulLog (cond i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← hrow_mul_cond i j, Real.negMulLog_mul]
    _ = (∑ i, Real.negMulLog (row i)) +
        ∑ j, ∑ i, row i * Real.negMulLog (cond i j) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_mul, hsum_cond]
      · exact Finset.sum_comm
    _ ≤ (∑ i, Real.negMulLog (row i)) +
        ∑ j, Real.negMulLog (col j) := by
      gcongr with j
      exact hjensen j
    _ = (∑ i, Real.negMulLog (∑ j, p i j)) +
        ∑ j, Real.negMulLog (∑ i, p i j) := by
      rfl

noncomputable def partitionJoin
    {M : Type*} (P Q : Finset (Set M)) : Finset (Set M) :=
  (P.product Q).image fun AB => AB.1 ∩ AB.2

lemma sum_measureReal_partition_eq_one
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P) :
    ∑ A ∈ P, mu.real A = 1 := by
  have hpairwise : Set.Pairwise (P : Set (Set M)) fun A B => AEDisjoint mu A B := by
    intro A hA B hB hAB
    exact hP.disjoint A hA B hB hAB
  rw [← measureReal_biUnion_finset₀ hpairwise
    (fun A hA => (hP.measurable A hA).nullMeasurableSet)]
  rw [measureReal_def, measure_of_measure_compl_eq_zero hP.cover, measure_univ]
  simp

lemma sum_measureReal_inter_partition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    {Q : Finset (Set M)} (hQ : IsMeasurablePartition mu Q)
    (A : Set M) (hA : MeasurableSet A) :
    ∑ B ∈ Q, mu.real (A ∩ B) = mu.real A := by
  have hpairwise : Set.Pairwise (Q : Set (Set M))
      fun B C => AEDisjoint mu (A ∩ B) (A ∩ C) := by
    intro B hB C hC hBC
    have hdisjoint : AEDisjoint mu B C := hQ.disjoint B hB C hC hBC
    exact hdisjoint.mono Set.inter_subset_right Set.inter_subset_right
  rw [← measureReal_biUnion_finset₀ hpairwise
    (fun B hB => (hA.inter (hQ.measurable B hB)).nullMeasurableSet)]
  have hunion : (⋃ B ∈ Q, A ∩ B) = A ∩ (⋃ B ∈ Q, B) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    aesop
  rw [hunion, measureReal_def, measure_inter_eq_of_compl_eq_zero mu hQ.cover]
  rfl

lemma partitionEntropy_partitionJoin_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P Q : Finset (Set M)}
    (hP : IsMeasurablePartition mu P) (hQ : IsMeasurablePartition mu Q) :
    partitionEntropy mu (partitionJoin P Q) ≤
      partitionEntropy mu P + partitionEntropy mu Q := by
  classical
  let p : ↥P → ↥Q → ℝ := fun A B => mu.real (A.1 ∩ B.1)
  have hp (A : ↥P) (B : ↥Q) : 0 ≤ p A B := measureReal_nonneg
  have hrow (A : ↥P) : ∑ B, p A B = mu.real A.1 := by
    calc
      (∑ B : ↥Q, p A B) = ∑ B ∈ Q, mu.real (A.1 ∩ B) := by
        simpa [p] using Finset.sum_coe_sort Q
          (fun B => mu.real (A.1 ∩ B))
      _ = mu.real A.1 := sum_measureReal_inter_partition mu hQ A.1
        (hP.measurable A.1 A.2)
  have hcol (B : ↥Q) : ∑ A, p A B = mu.real B.1 := by
    have h := sum_measureReal_inter_partition mu hP B.1
      (hQ.measurable B.1 B.2)
    calc
      (∑ A : ↥P, p A B) = ∑ A ∈ P, mu.real (A ∩ B.1) := by
        simpa [p] using Finset.sum_coe_sort P
          (fun A => mu.real (A ∩ B.1))
      _ = mu.real B.1 := by simpa [Set.inter_comm] using h
  have htotal : ∑ A, ∑ B, p A B = 1 := by
    simp_rw [hrow]
    rw [Finset.sum_coe_sort]
    exact sum_measureReal_partition_eq_one mu hP
  have hjoint := finite_joint_entropy_le_marginals p hp htotal
  unfold partitionEntropy partitionJoin
  calc
    (∑ A ∈ (P.product Q).image (fun AB => AB.1 ∩ AB.2),
        Real.negMulLog (mu.real A)) ≤
        ∑ AB ∈ P.product Q,
          Real.negMulLog (mu.real (AB.1 ∩ AB.2)) := by
      apply Finset.sum_image_le_of_nonneg
      intro A hA
      exact Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one
    _ = ∑ A : ↥P, ∑ B : ↥Q,
        Real.negMulLog (p A B) := by
      change (∑ AB ∈ P ×ˢ Q,
          Real.negMulLog (mu.real (AB.1 ∩ AB.2))) = _
      rw [Finset.sum_product]
      calc
        (∑ A ∈ P, ∑ B ∈ Q,
            Real.negMulLog (mu.real (A ∩ B))) =
            ∑ A : ↥P, ∑ B ∈ Q,
              Real.negMulLog (mu.real (A.1 ∩ B)) := by
          exact (Finset.sum_coe_sort P fun A =>
            ∑ B ∈ Q, Real.negMulLog (mu.real (A ∩ B))).symm
        _ = ∑ A : ↥P, ∑ B : ↥Q,
            Real.negMulLog (p A B) := by
          apply Finset.sum_congr rfl
          intro A _hA
          simpa [p] using (Finset.sum_coe_sort Q fun B =>
            Real.negMulLog (mu.real (A.1 ∩ B))).symm
    _ ≤ (∑ A : ↥P, Real.negMulLog (∑ B : ↥Q, p A B)) +
        ∑ B : ↥Q, Real.negMulLog (∑ A : ↥P, p A B) := hjoint
    _ = (∑ A ∈ P, Real.negMulLog (mu.real A)) +
        ∑ B ∈ Q, Real.negMulLog (mu.real B) := by
      simp_rw [hrow, hcol]
      exact congrArg₂ (fun a b : ℝ => a + b)
        (Finset.sum_coe_sort P fun A => Real.negMulLog (mu.real A))
        (Finset.sum_coe_sort Q fun B => Real.negMulLog (mu.real B))

lemma iteratedAtom_append
    {M : Type*} (T : M → M) {m n : ℕ}
    (f : Fin m → Set M) (g : Fin n → Set M) :
    (⋂ k : Fin (m + n), T^[k.val] ⁻¹' Fin.append f g k) =
      (⋂ i : Fin m, T^[i.val] ⁻¹' f i) ∩
        T^[m] ⁻¹' (⋂ j : Fin n, T^[j.val] ⁻¹' g j) := by
  ext x
  constructor
  · intro hx
    constructor
    · apply Set.mem_iInter.mpr
      intro i
      have hi := Set.mem_iInter.mp hx (Fin.castAdd n i)
      simpa using hi
    · apply Set.mem_iInter.mpr
      intro j
      have hj := Set.mem_iInter.mp hx (Fin.natAdd m j)
      change T^[j.val] (T^[m] x) ∈ g j
      rw [← Function.iterate_add_apply]
      simpa [Nat.add_comm] using hj
  · rintro ⟨hf, hg⟩
    apply Set.mem_iInter.mpr
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa using Set.mem_iInter.mp hf i
    · intro j
      have hj := Set.mem_iInter.mp hg j
      simp only [Set.mem_preimage, Fin.append_right]
      change T^[m + j.val] x ∈ g j
      rw [Nat.add_comm, Function.iterate_add_apply]
      exact hj

lemma iteratedJoin_add
    {M : Type*} (T : M → M) (P : Finset (Set M)) (m n : ℕ) :
    iteratedJoin T P (m + n) =
      partitionJoin (iteratedJoin T P m)
        (preimagePartition (T^[m]) (iteratedJoin T P n)) := by
  classical
  ext A
  constructor
  · intro hA
    rw [iteratedJoin] at hA
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hA
    let f : Fin m → Set M := fun i => h (Fin.castAdd n i)
    let g : Fin n → Set M := fun j => h (Fin.natAdd m j)
    have hf : f ∈ Fintype.piFinset fun _ : Fin m => P := by
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Fintype.mem_piFinset.mp hh (Fin.castAdd n i)
    have hg : g ∈ Fintype.piFinset fun _ : Fin n => P := by
      apply Fintype.mem_piFinset.mpr
      intro j
      exact Fintype.mem_piFinset.mp hh (Fin.natAdd m j)
    have happend : Fin.append f g = h := by
      exact Fin.append_castAdd_natAdd
    rw [← happend, iteratedAtom_append]
    unfold partitionJoin preimagePartition
    apply Finset.mem_image.mpr
    refine ⟨((⋂ i : Fin m, T^[i.val] ⁻¹' f i),
      T^[m] ⁻¹' (⋂ j : Fin n, T^[j.val] ⁻¹' g j)), ?_, rfl⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    · exact Finset.mem_image.mpr ⟨
        (⋂ j : Fin n, T^[j.val] ⁻¹' g j),
        Finset.mem_image.mpr ⟨g, hg, rfl⟩, rfl⟩
  · intro hA
    unfold partitionJoin preimagePartition at hA
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hAB
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hC
    rw [← iteratedAtom_append]
    rw [iteratedJoin]
    exact Finset.mem_image.mpr ⟨Fin.append f g,
      Fintype.mem_piFinset.mpr (Fin.addCases
        (fun i => by simpa using Fintype.mem_piFinset.mp hf i)
        (fun j => by simpa using Fintype.mem_piFinset.mp hg j)), rfl⟩

lemma partitionEntropy_iteratedJoin_add_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (m n : ℕ) :
    partitionEntropy mu (iteratedJoin T P (m + n)) ≤
      partitionEntropy mu (iteratedJoin T P m) +
        partitionEntropy mu (iteratedJoin T P n) := by
  rw [iteratedJoin_add]
  calc
    partitionEntropy mu
        (partitionJoin (iteratedJoin T P m)
          (preimagePartition (T^[m]) (iteratedJoin T P n))) ≤
        partitionEntropy mu (iteratedJoin T P m) +
          partitionEntropy mu
            (preimagePartition (T^[m]) (iteratedJoin T P n)) :=
      partitionEntropy_partitionJoin_le mu
        (isMeasurablePartition_iteratedJoin mu T hT P hP m)
        (isMeasurablePartition_preimagePartition mu (T^[m]) (hT.iterate m)
          (iteratedJoin T P n)
          (isMeasurablePartition_iteratedJoin mu T hT P hP n))
    _ = partitionEntropy mu (iteratedJoin T P m) +
        partitionEntropy mu (iteratedJoin T P n) := by
      rw [partitionEntropy_preimagePartition mu (T^[m]) (hT.iterate m)
        ((hT_right.iterate m).surjective) (iteratedJoin T P n)
        (isMeasurablePartition_iteratedJoin mu T hT P hP n).measurable]

lemma subadditive_partitionEntropy_iteratedJoin
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    Subadditive (fun n => partitionEntropy mu (iteratedJoin T P n)) :=
  partitionEntropy_iteratedJoin_add_le mu T T_inv hT_right hT P hP

lemma tendsto_partitionEntropy_iteratedJoin_div_entropyW
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    Filter.Tendsto
      (fun n => partitionEntropy mu (iteratedJoin T P n) / n)
      Filter.atTop (nhds (entropyW mu T P)) := by
  let u : ℕ → ℝ := fun n => partitionEntropy mu (iteratedJoin T P n)
  have hsub : Subadditive u :=
    subadditive_partitionEntropy_iteratedJoin mu T T_inv hT_right hT P hP
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (partitionEntropy_nonneg mu _) (Nat.cast_nonneg n)
  have htend := hsub.tendsto_lim hbdd
  have hlimsup : Filter.limsup (fun n => u n / n) Filter.atTop = hsub.lim :=
    htend.limsup_eq
  simpa [entropyW, u, hlimsup] using htend

end Submission.Helpers
