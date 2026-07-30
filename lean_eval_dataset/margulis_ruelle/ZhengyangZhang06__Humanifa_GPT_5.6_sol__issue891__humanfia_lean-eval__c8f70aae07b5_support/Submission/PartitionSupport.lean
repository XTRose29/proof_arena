import Submission.EntropyInverse

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

noncomputable def restrictPartition
    {M : Type*} (P : Finset (Set M)) (s : Set M) : Finset (Set M) :=
  P.image fun A => A ∩ s

lemma measure_inter_eq_of_compl_eq_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) {s : Set M} (hmu_s : mu sᶜ = 0) (A : Set M) :
    mu (A ∩ s) = mu A := by
  apply measure_congr
  filter_upwards [mem_ae_iff.mpr hmu_s] with x hx
  exact propext (and_iff_left hx)

lemma isMeasurablePartition_restrictPartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) {P : Finset (Set M)}
    (hP : IsMeasurablePartition mu P)
    {s : Set M} (hs : MeasurableSet s) (hmu_s : mu sᶜ = 0) :
    IsMeasurablePartition mu (restrictPartition P s) := by
  classical
  constructor
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact (hP.measurable B hB).inter hs
  · apply measure_mono_null _ (measure_union_null hP.cover hmu_s)
    intro x hx
    by_cases hxs : x ∈ s
    · left
      intro hxP
      rcases Set.mem_iUnion.mp hxP with ⟨A, hxP⟩
      rcases Set.mem_iUnion.mp hxP with ⟨hA, hxA⟩
      apply hx
      apply Set.mem_iUnion_of_mem (A ∩ s)
      apply Set.mem_iUnion_of_mem (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
      exact ⟨hxA, hxs⟩
    · exact Or.inr hxs
  · intro A hA B hB hAB
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    have hA'B' : A' ≠ B' := by
      intro h
      exact hAB (congrArg (fun C => C ∩ s) h)
    apply measure_mono_null _ (hP.disjoint A' hA' B' hB' hA'B')
    intro x hx
    exact ⟨hx.1.1, hx.2.1⟩

lemma partitionEntropy_restrictPartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) {P : Finset (Set M)}
    (hP : IsMeasurablePartition mu P)
    {s : Set M} (hmu_s : mu sᶜ = 0) :
    partitionEntropy mu (restrictPartition P s) = partitionEntropy mu P := by
  classical
  unfold partitionEntropy restrictPartition
  rw [Finset.sum_image_of_pairwise_eq_zero]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [measure_inter_eq_of_compl_eq_zero mu hmu_s A]
  · intro A hA B hB hAB hEq
    have hsubset : A ∩ s ⊆ A ∩ B := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have : x ∈ B ∩ s := by simpa [hEq] using hx
      exact this.1
    have hzero : mu (A ∩ s) = 0 :=
      measure_mono_null hsubset (hP.disjoint A hA B hB hAB)
    simp [hzero]

lemma entropyW_eq_limsup_restrictPartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) {P : Finset (Set M)}
    (hP : IsMeasurablePartition mu P)
    (hT : MeasurePreserving T mu mu)
    {s : Set M} (hmu_s : mu sᶜ = 0) :
    entropyW mu T P =
      Filter.limsup
        (fun n : ℕ =>
          partitionEntropy mu (restrictPartition (iteratedJoin T P n) s) / n)
        Filter.atTop := by
  unfold entropyW
  congr 1
  funext n
  rw [partitionEntropy_restrictPartition mu
    (isMeasurablePartition_iteratedJoin mu T hT P hP n) hmu_s]

lemma preimage_iterate_eq_of_image_eq
    (T : EucPlane → EucPlane) (hT_inj : Function.Injective T)
    {s : Set EucPlane} (hs : T '' s = s) (n : ℕ) :
    T^[n] ⁻¹' s = s := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx_image : T^[n] x ∈ T^[n] '' s := by
      rw [image_iterate_eq_of_image_eq T hs n]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx_image
    have : y = x := (hT_inj.iterate n) hyx
    simpa [this] using hy
  · intro x hx
    rw [← image_iterate_eq_of_image_eq T hs n]
    exact ⟨x, hx, rfl⟩

lemma iInter_preimage_inter_invariant
    (T : EucPlane → EucPlane) (hT_inj : Function.Injective T)
    {s : Set EucPlane} (hs : T '' s = s)
    {n : ℕ} (hn : 0 < n) (f : Fin n → Set EucPlane) :
    (⋂ k : Fin n, T^[k.val] ⁻¹' (f k ∩ s)) =
      (⋂ k : Fin n, T^[k.val] ⁻¹' f k) ∩ s := by
  ext x
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · intro hx
    refine ⟨fun k => (hx k).1, ?_⟩
    simpa using (hx ⟨0, hn⟩).2
  · rintro ⟨hxf, hxs⟩ k
    refine ⟨hxf k, ?_⟩
    have hxpre : x ∈ T^[k.val] ⁻¹' s := by
      rw [preimage_iterate_eq_of_image_eq T hT_inj hs k.val]
      exact hxs
    exact hxpre

lemma iteratedJoin_restrictPartition
    (T : EucPlane → EucPlane) (hT_inj : Function.Injective T)
    (P : Finset (Set EucPlane)) {s : Set EucPlane} (hs : T '' s = s)
    (n : ℕ) (hn : 0 < n) :
    restrictPartition (iteratedJoin T P n) s =
      iteratedJoin T (restrictPartition P s) n := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    rw [iteratedJoin] at hB ⊢
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hB
    let g : Fin n → Set EucPlane := fun k => f k ∩ s
    apply Finset.mem_image.mpr
    refine ⟨g, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro k
      exact Finset.mem_image.mpr
        ⟨f k, Fintype.mem_piFinset.mp hf k, rfl⟩
    · simpa [g] using
        iInter_preimage_inter_invariant T hT_inj hs hn f
  · intro hA
    rw [iteratedJoin] at hA ⊢
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hA
    have hex : ∀ k : Fin n, ∃ A ∈ P, g k = A ∩ s := by
      intro k
      obtain ⟨A, hA, hAg⟩ :=
        Finset.mem_image.mp (Fintype.mem_piFinset.mp hg k)
      exact ⟨A, hA, hAg.symm⟩
    choose f hfP hgf using hex
    have hgfun : g = fun k => f k ∩ s := funext hgf
    subst g
    apply Finset.mem_image.mpr
    refine ⟨⋂ k : Fin n, T^[k.val] ⁻¹' f k, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨f, Fintype.mem_piFinset.mpr hfP, rfl⟩
    · exact (iInter_preimage_inter_invariant T hT_inj hs hn f).symm

lemma partitionEntropy_iteratedJoin_restrictPartition
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T : EucPlane → EucPlane) (hT_inj : Function.Injective T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {s : Set EucPlane} (hmu_s : mu sᶜ = 0) (hs : T '' s = s)
    (n : ℕ) :
    partitionEntropy mu (iteratedJoin T (restrictPartition P s) n) =
      partitionEntropy mu (iteratedJoin T P n) := by
  cases n with
  | zero => simp [iteratedJoin]
  | succ n =>
      rw [← partitionEntropy_restrictPartition mu
        (isMeasurablePartition_iteratedJoin mu T hT P hP n.succ) hmu_s]
      rw [iteratedJoin_restrictPartition T hT_inj P hs n.succ n.succ_pos]

lemma entropyW_restrictPartition
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T : EucPlane → EucPlane) (hT_inj : Function.Injective T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {s : Set EucPlane} (hmu_s : mu sᶜ = 0) (hs : T '' s = s) :
    entropyW mu T (restrictPartition P s) = entropyW mu T P := by
  unfold entropyW
  congr 1
  funext n
  rw [partitionEntropy_iteratedJoin_restrictPartition mu T hT_inj hT P hP hmu_s hs n]

lemma kolmogorovSinaiEntropy_eq_sSup_supported
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T : EucPlane → EucPlane) (hT_inj : Function.Injective T)
    (hT : MeasurePreserving T mu mu)
    {s : Set EucPlane} (hs_measurable : MeasurableSet s)
    (hmu_s : mu sᶜ = 0) (hs : T '' s = s) :
    kolmogorovSinaiEntropy mu T =
      sSup {h : ℝ | ∃ P : Finset (Set EucPlane),
        IsMeasurablePartition mu P ∧
          (∀ A ∈ P, A ⊆ s) ∧ entropyW mu T P = h} := by
  unfold kolmogorovSinaiEntropy
  congr 1
  ext h
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨restrictPartition P s,
      isMeasurablePartition_restrictPartition mu hP hs_measurable hmu_s, ?_, ?_⟩
    · intro A hA
      obtain ⟨B, _hB, rfl⟩ := Finset.mem_image.mp hA
      exact Set.inter_subset_right
    · exact entropyW_restrictPartition mu T hT_inj hT P hP hmu_s hs
  · rintro ⟨P, hP, _hPs, hEntropy⟩
    exact ⟨P, hP, hEntropy⟩

end Submission.Helpers
