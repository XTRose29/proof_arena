import Submission.EntropyLight

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma lightAtoms_preimagePartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (F : M → M) (hF : MeasurePreserving F mu mu)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (c : ℝ) :
    lightAtoms mu (preimagePartition F P) c =
      preimagePartition F (lightAtoms mu P c) := by
  classical
  unfold lightAtoms preimagePartition
  rw [Finset.filter_image]
  congr 1
  apply Finset.filter_congr
  intro A hA
  rw [measureReal_def, hF.measure_preimage (hP A hA).nullMeasurableSet]
  rfl

lemma measureReal_iUnion_lightAtoms_preimagePartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (F : M → M) (hF : MeasurePreserving F mu mu)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (c : ℝ) :
    mu.real (⋃ A ∈ lightAtoms mu (preimagePartition F P) c, A) =
      mu.real (⋃ A ∈ lightAtoms mu P c, A) := by
  classical
  rw [lightAtoms_preimagePartition mu F hF P hP c]
  have hU : (⋃ A ∈ preimagePartition F (lightAtoms mu P c), A) =
      F ⁻¹' (⋃ A ∈ lightAtoms mu P c, A) := by
    ext x
    simp [preimagePartition]
  have hmeas : MeasurableSet (⋃ A ∈ lightAtoms mu P c, A) :=
    Finset.measurableSet_biUnion _ fun A hA =>
      hP A (Finset.mem_filter.mp hA).1
  rw [hU, measureReal_def,
    hF.measure_preimage hmeas.nullMeasurableSet]
  rfl

lemma measureReal_iUnion_lightAtoms_centeredJoin
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (m n : ℕ) (c : ℝ) :
    mu.real (⋃ A ∈ lightAtoms mu (centeredJoin T T_inv P m n) c, A) =
      mu.real (⋃ A ∈ lightAtoms mu (iteratedJoin T P (m + n)) c, A) := by
  unfold centeredJoin
  exact measureReal_iUnion_lightAtoms_preimagePartition mu (T_inv^[m])
    (hT_inv.iterate m) (iteratedJoin T P (m + n))
      (isMeasurablePartition_iteratedJoin mu T hT P hP (m + n)).measurable c

lemma exists_centered_entropy_light_atoms_limsup_ne_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (hP_card : 1 < P.card)
    (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_entropy : 2 * epsilon < entropyW mu T P) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      mu (limsup
        (fun k =>
          ⋃ A ∈ lightAtoms mu
              (centeredJoin T T_inv P (m (N k)) (n (N k)))
              ((entropyW mu T P - 2 * epsilon) * N k), A)
        atTop) ≠ 0 := by
  obtain ⟨N, hN_top, hN_mass, _hN_limsup⟩ :=
    exists_entropy_light_atoms_limsup_ne_zero
      mu T hT P hP hP_card hepsilon hepsilon_entropy
  let delta : ℝ := epsilon / (2 * Real.log (P.card : ℝ))
  let U : ℕ → Set M := fun k =>
    ⋃ A ∈ lightAtoms mu
        (centeredJoin T T_inv P (m (N k)) (n (N k)))
        ((entropyW mu T P - 2 * epsilon) * N k), A
  have hdelta_pos : 0 < delta := by
    have hP_card_real : (1 : ℝ) < P.card := by exact_mod_cast hP_card
    exact div_pos hepsilon (mul_pos zero_lt_two (Real.log_pos hP_card_real))
  have hU_measurable (k : ℕ) : MeasurableSet (U k) := by
    apply Finset.measurableSet_biUnion
    intro A hA
    exact (isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP
      (m (N k)) (n (N k))).measurable A (Finset.mem_filter.mp hA).1
  have hU_mass (k : ℕ) : delta ≤ mu.real (U k) := by
    calc
      delta ≤ mu.real
          (⋃ A ∈ lightAtoms mu (iteratedJoin T P (N k))
            ((entropyW mu T P - 2 * epsilon) * N k), A) := by
        simpa [delta] using hN_mass k
      _ = mu.real (U k) := by
        change mu.real
            (⋃ A ∈ lightAtoms mu (iteratedJoin T P (N k))
              ((entropyW mu T P - 2 * epsilon) * N k), A) =
          mu.real
            (⋃ A ∈ lightAtoms mu
              (centeredJoin T T_inv P (m (N k)) (n (N k)))
              ((entropyW mu T P - 2 * epsilon) * N k), A)
        rw [measureReal_iUnion_lightAtoms_centeredJoin mu T T_inv hT hT_inv
          P hP (m (N k)) (n (N k))
            ((entropyW mu T P - 2 * epsilon) * N k)]
        rw [hsplit]
  refine ⟨N, hN_top, ?_⟩
  exact measure_limsup_ne_zero_of_measureReal_ge mu U hU_measurable
    hdelta_pos hU_mass

end Submission.Helpers
