import Submission.SmallPartitions

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

noncomputable def preimagePartition
    {M : Type*} (F : M → M) (P : Finset (Set M)) : Finset (Set M) :=
  P.image fun A => F ⁻¹' A

lemma isMeasurablePartition_preimagePartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (F : M → M) (hF : MeasurePreserving F mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    IsMeasurablePartition mu (preimagePartition F P) := by
  classical
  constructor
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact (hP.measurable B hB).preimage hF.measurable
  · have hcover_eq :
        (⋃ A ∈ preimagePartition F P, A)ᶜ =
          F ⁻¹' (⋃ A ∈ P, A)ᶜ := by
      ext x
      simp [preimagePartition]
    rw [hcover_eq]
    exact hF.preimage_null hP.cover
  · intro A hA B hB hAB
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    have hA'B' : A' ≠ B' := by
      intro h
      exact hAB (congrArg (fun C => F ⁻¹' C) h)
    rw [← Set.preimage_inter]
    exact hF.preimage_null (hP.disjoint A' hA' B' hB' hA'B')

lemma partitionEntropy_preimagePartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (F : M → M) (hF : MeasurePreserving F mu mu)
    (hF_surj : Function.Surjective F)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    partitionEntropy mu (preimagePartition F P) = partitionEntropy mu P := by
  classical
  unfold partitionEntropy preimagePartition
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [hF.measure_preimage (hP A hA).nullMeasurableSet]
  · exact hF_surj.preimage_injective.injOn

noncomputable def centeredJoin
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M))
    (m n : ℕ) : Finset (Set M) :=
  preimagePartition (T_inv^[m]) (iteratedJoin T P (m + n))

lemma isMeasurablePartition_centeredJoin
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (m n : ℕ) :
    IsMeasurablePartition mu (centeredJoin T T_inv P m n) := by
  exact isMeasurablePartition_preimagePartition mu (T_inv^[m])
    (hT_inv.iterate m) (iteratedJoin T P (m + n))
      (isMeasurablePartition_iteratedJoin mu T hT P hP (m + n))

lemma partitionEntropy_centeredJoin
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (m n : ℕ) :
    partitionEntropy mu (centeredJoin T T_inv P m n) =
      partitionEntropy mu (iteratedJoin T P (m + n)) := by
  exact partitionEntropy_preimagePartition mu (T_inv^[m]) (hT_inv.iterate m)
    (hT_left.iterate m).surjective (iteratedJoin T P (m + n))
      (isMeasurablePartition_iteratedJoin mu T hT P hP (m + n)).measurable

lemma iterate_after_inverse_cancel
    {M : Type*} {T T_inv : M → M}
    (hT_right : Function.RightInverse T_inv T)
    (m j : ℕ) (x : M) :
    T^[m + j] (T_inv^[m] x) = T^[j] x := by
  rw [Nat.add_comm, Function.iterate_add_apply, (hT_right.iterate m) x]

lemma iterate_before_inverse_cancel
    {M : Type*} {T T_inv : M → M}
    (hT_right : Function.RightInverse T_inv T)
    {k m : ℕ} (hkm : k ≤ m) (x : M) :
    T^[k] (T_inv^[m] x) = T_inv^[m - k] x := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [Nat.add_sub_cancel_left]
  rw [Function.iterate_add_apply, (hT_right.iterate k)]

lemma iterate_sub_inverse_cancel
    {M : Type*} {T T_inv : M → M}
    (hT_right : Function.RightInverse T_inv T)
    {q m : ℕ} (hqm : q ≤ m) (x : M) :
    T^[m - q] (T_inv^[m] x) = T_inv^[q] x := by
  rw [iterate_before_inverse_cancel hT_right (Nat.sub_le m q)]
  rw [Nat.sub_sub_self hqm]

lemma exists_iteratedJoin_atom_of_mem_centeredJoin_atom
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M))
    {m n : ℕ} {A : Set M} (hA : A ∈ centeredJoin T T_inv P m n)
    {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ B ∈ iteratedJoin T P (m + n),
      T_inv^[m] x ∈ B ∧ T_inv^[m] y ∈ B := by
  rw [centeredJoin, preimagePartition] at hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  exact ⟨B, hB, hx, hy⟩

lemma edist_forward_iterate_le_of_mem_centeredJoin_atom
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (P : Finset (Set EucPlane))
    {r : ℝ≥0∞} (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ r)
    {m n : ℕ} {A : Set EucPlane} (hA : A ∈ centeredJoin T T_inv P m n)
    {x y : EucPlane} (hx : x ∈ A) (hy : y ∈ A)
    (j : Fin n) :
    edist (T^[j.val] x) (T^[j.val] y) ≤ r := by
  obtain ⟨B, hB, hxB, hyB⟩ :=
    exists_iteratedJoin_atom_of_mem_centeredJoin_atom T T_inv P hA hx hy
  have hk : m + j.val < m + n := Nat.add_lt_add_left j.isLt m
  have hclose := edist_iterate_le_of_mem_iteratedJoin_atom
    T P hP_diam hB hxB hyB ⟨m + j.val, hk⟩
  simpa [iterate_after_inverse_cancel hT_right] using hclose

lemma edist_backward_iterate_le_of_mem_centeredJoin_atom
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (P : Finset (Set EucPlane))
    {r : ℝ≥0∞} (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ r)
    {m n : ℕ} {A : Set EucPlane} (hA : A ∈ centeredJoin T T_inv P m n)
    {x y : EucPlane} (hx : x ∈ A) (hy : y ∈ A)
    {q : ℕ} (hq_pos : 0 < q) (hq_le : q ≤ m) :
    edist (T_inv^[q] x) (T_inv^[q] y) ≤ r := by
  obtain ⟨B, hB, hxB, hyB⟩ :=
    exists_iteratedJoin_atom_of_mem_centeredJoin_atom T T_inv P hA hx hy
  have hk : m - q < m + n := by omega
  have hclose := edist_iterate_le_of_mem_iteratedJoin_atom
    T P hP_diam hB hxB hyB ⟨m - q, hk⟩
  simpa [iterate_sub_inverse_cancel hT_right hq_le] using hclose

end Submission.Helpers
