import Submission.Helpers

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma iterate_rev_cancel
    {M : Type*} {T T_inv : M → M}
    (hT_right : Function.RightInverse T_inv T)
    {n : ℕ} (k : Fin n) (x : M) :
    T^[k.rev.val] (T_inv^[n.pred] x) = T_inv^[k.val] x := by
  have hk := k.isLt
  have hsum : k.rev.val + k.val = n.pred := by
    rw [Fin.val_rev, Nat.pred_eq_sub_one]
    omega
  rw [← hsum, Function.iterate_add_apply]
  exact (hT_right.iterate k.rev.val) _

lemma preimage_iteratedAtom_inverse
    {M : Type*} {T T_inv : M → M}
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (f : Fin n → Set M) :
    T_inv^[n.pred] ⁻¹'
        (⋂ k : Fin n, T^[k.val] ⁻¹' f k.rev) =
      ⋂ k : Fin n, T_inv^[k.val] ⁻¹' f k := by
  ext x
  simp only [Set.mem_preimage, Set.mem_iInter]
  constructor
  · intro hx k
    have hk := hx k.rev
    rw [Fin.rev_rev, iterate_rev_cancel hT_right k x] at hk
    exact hk
  · intro hx k
    have hk := hx k.rev
    have hcancel := iterate_rev_cancel hT_right k.rev x
    rw [Fin.rev_rev] at hcancel
    rw [hcancel]
    exact hk

lemma iteratedJoin_inverse
    {M : Type*} (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (P : Finset (Set M)) (n : ℕ) :
    iteratedJoin T_inv P n =
      (iteratedJoin T P n).image
        (fun A => T_inv^[n.pred] ⁻¹' A) := by
  classical
  ext A
  rw [iteratedJoin, iteratedJoin]
  constructor
  · intro hA
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
    let g : Fin n → Set M := fun k => f k.rev
    have hg : g ∈ Fintype.piFinset (fun _ : Fin n => P) := by
      exact Fintype.mem_piFinset.mpr fun k =>
        Fintype.mem_piFinset.mp hf k.rev
    apply Finset.mem_image.mpr
    refine ⟨⋂ k : Fin n, T^[k.val] ⁻¹' g k, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    · simpa [g] using preimage_iteratedAtom_inverse hT_right n f
  · intro hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hB
    let f : Fin n → Set M := fun k => g k.rev
    have hf : f ∈ Fintype.piFinset (fun _ : Fin n => P) := by
      exact Fintype.mem_piFinset.mpr fun k =>
        Fintype.mem_piFinset.mp hg k.rev
    apply Finset.mem_image.mpr
    refine ⟨f, hf, ?_⟩
    simpa [f] using (preimage_iteratedAtom_inverse hT_right n f).symm

lemma measurableSet_of_mem_iteratedJoin
    {M : Type*} [MeasurableSpace M]
    (T : M → M) (P : Finset (Set M))
    (hT : Measurable T)
    (hP : ∀ A ∈ P, MeasurableSet A)
    (n : ℕ) {A : Set M} (hA : A ∈ iteratedJoin T P n) :
    MeasurableSet A := by
  rw [iteratedJoin] at hA
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
  exact MeasurableSet.iInter fun k =>
    (hP (f k) (Fintype.mem_piFinset.mp hf k)).preimage (hT.iterate k.val)

lemma isMeasurablePartition_iteratedJoin
    {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T : M → M)
    (hT : MeasurePreserving T μ μ)
    (P : Finset (Set M)) (hP : IsMeasurablePartition μ P)
    (n : ℕ) :
    IsMeasurablePartition μ (iteratedJoin T P n) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    exact measurableSet_of_mem_iteratedJoin T P hT.measurable hP.measurable n hA
  · let U : Set M := ⋃ A ∈ P, A
    let bad : Set M := ⋃ k : Fin n, T^[k.val] ⁻¹' Uᶜ
    have hbad : μ bad = 0 := by
      apply measure_iUnion_null
      intro k
      exact (hT.iterate k.val).preimage_null hP.cover
    apply measure_mono_null (t := bad) _ hbad
    intro x hx
    by_contra hxbad
    have hex : ∀ k : Fin n, ∃ A ∈ P, T^[k.val] x ∈ A := by
      intro k
      have hkU : T^[k.val] x ∈ U := by
        by_contra hkU
        apply hxbad
        exact Set.mem_iUnion_of_mem k hkU
      change T^[k.val] x ∈ ⋃ A ∈ P, A at hkU
      obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hkU
      obtain ⟨hAP, hxA⟩ := Set.mem_iUnion.mp hA
      exact ⟨A, hAP, hxA⟩
    choose f hfP hxf using hex
    apply hx
    apply Set.mem_iUnion_of_mem (⋂ k : Fin n, T^[k.val] ⁻¹' f k)
    apply Set.mem_iUnion_of_mem
      (Finset.mem_image.mpr
        ⟨f, Fintype.mem_piFinset.mpr hfP, rfl⟩)
    exact Set.mem_iInter.mpr hxf
  · intro A hA B hB hAB
    exact iteratedJoin_measure_inter_eq_zero μ T P hP hT n hA hB hAB

lemma partitionEntropy_iteratedJoin_inverse
    {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T μ μ)
    (hT_inv : MeasurePreserving T_inv μ μ)
    (P : Finset (Set M))
    (hP : ∀ A ∈ P, MeasurableSet A)
    (n : ℕ) :
    partitionEntropy μ (iteratedJoin T_inv P n) =
      partitionEntropy μ (iteratedJoin T P n) := by
  rw [iteratedJoin_inverse T T_inv hT_right]
  rw [partitionEntropy, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [(hT_inv.iterate n.pred).measure_preimage
      (measurableSet_of_mem_iteratedJoin T P hT.measurable hP n hA).nullMeasurableSet]
  · exact (hT_left.iterate n.pred).surjective.preimage_injective.injOn

lemma entropyW_inverse
    {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T μ μ)
    (hT_inv : MeasurePreserving T_inv μ μ)
    (P : Finset (Set M)) (hP : IsMeasurablePartition μ P) :
    entropyW μ T_inv P = entropyW μ T P := by
  unfold entropyW
  congr 1
  funext n
  rw [partitionEntropy_iteratedJoin_inverse μ T T_inv hT_left hT_right
    hT hT_inv P hP.measurable n]

lemma kolmogorovSinaiEntropy_inverse
    {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T μ μ)
    (hT_inv : MeasurePreserving T_inv μ μ) :
    kolmogorovSinaiEntropy μ T_inv = kolmogorovSinaiEntropy μ T := by
  unfold kolmogorovSinaiEntropy
  congr 1
  ext h
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, (entropyW_inverse μ T T_inv hT_left hT_right hT hT_inv P hP).symm⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, entropyW_inverse μ T T_inv hT_left hT_right hT hT_inv P hP⟩

lemma kolmogorovSinaiEntropy_inverse_diffeomorphism
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (μ : Measure EucPlane)
    (hμ_pres : MeasurePreserving T μ μ) :
    kolmogorovSinaiEntropy μ T_inv = kolmogorovSinaiEntropy μ T := by
  exact kolmogorovSinaiEntropy_inverse μ T T_inv hT_left hT_right hμ_pres
    (measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth hT_left hT_right μ hμ_pres)

end Submission.Helpers
