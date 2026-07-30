import Submission.CarrierAtoms

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

lemma sum_measureReal_positive_atoms_eq_one
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P) :
    ∑ A ∈ P.filter fun A => mu A ≠ 0, mu.real A = 1 := by
  classical
  have hpairwise : Set.Pairwise (P : Set (Set M)) fun A B => AEDisjoint mu A B := by
    intro A hA B hB hAB
    exact hP.disjoint A hA B hB hAB
  have hsum : ∑ A ∈ P, mu.real A = 1 := by
    rw [← measureReal_biUnion_finset₀ hpairwise
      (fun A hA => (hP.measurable A hA).nullMeasurableSet)]
    rw [measureReal_def, measure_of_measure_compl_eq_zero hP.cover, measure_univ]
    simp
  rw [Finset.sum_filter]
  calc
    (∑ A ∈ P, if mu A ≠ 0 then mu.real A else 0) = ∑ A ∈ P, mu.real A := by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases hmuA : mu A ≠ 0
      · simp [hmuA]
      · rw [if_neg hmuA]
        exact ((measureReal_eq_zero_iff).2 (not_ne_iff.mp hmuA)).symm
    _ = 1 := hsum

lemma partitionEntropy_eq_sum_positive_atoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M)) :
    partitionEntropy mu P =
      ∑ A ∈ P.filter fun A => mu A ≠ 0, Real.negMulLog (mu.real A) := by
  classical
  rw [partitionEntropy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hmuA : mu A ≠ 0
  · simp [hmuA, measureReal_def]
  · simp [not_ne_iff.mp hmuA]

lemma partitionEntropy_le_log_card_positive_atoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P) :
    partitionEntropy mu P ≤
      Real.log ((P.filter fun A => mu A ≠ 0).card : ℝ) := by
  classical
  let Q := P.filter fun A => mu A ≠ 0
  have hsum : ∑ A ∈ Q, mu.real A = 1 := by
    simpa [Q] using sum_measureReal_positive_atoms_eq_one mu hP
  have hQ_nonempty : Q.Nonempty := by
    by_contra hQ
    rw [Finset.not_nonempty_iff_eq_empty.mp hQ] at hsum
    simp at hsum
  have hQ_pos : (0 : ℝ) < Q.card := by
    exact_mod_cast Finset.card_pos.mpr hQ_nonempty
  have hweights : ∑ _A ∈ Q, (Q.card : ℝ)⁻¹ = 1 := by
    simp [hQ_pos.ne']
  have hJensen := Real.concaveOn_negMulLog.le_map_sum
    (t := Q) (w := fun _A => (Q.card : ℝ)⁻¹) (p := fun A => mu.real A)
    (fun _A _hA => (inv_nonneg.mpr hQ_pos.le)) hweights
    (fun _A _hA => measureReal_nonneg)
  have hweighted_sum :
      ∑ A ∈ Q, (Q.card : ℝ)⁻¹ • mu.real A = (Q.card : ℝ)⁻¹ := by
    simp_rw [smul_eq_mul]
    rw [← Finset.mul_sum, hsum, mul_one]
  have hscaled :
      (Q.card : ℝ)⁻¹ * (∑ A ∈ Q, Real.negMulLog (mu.real A)) ≤
        (Q.card : ℝ)⁻¹ * Real.log (Q.card : ℝ) := by
    calc
      (Q.card : ℝ)⁻¹ * (∑ A ∈ Q, Real.negMulLog (mu.real A)) =
          ∑ A ∈ Q, (Q.card : ℝ)⁻¹ • Real.negMulLog (mu.real A) := by
            simp [Finset.mul_sum]
      _ ≤ Real.negMulLog
          (∑ A ∈ Q, (Q.card : ℝ)⁻¹ • mu.real A) := hJensen
      _ = Real.negMulLog ((Q.card : ℝ)⁻¹) := by
        rw [hweighted_sum]
      _ = (Q.card : ℝ)⁻¹ * Real.log (Q.card : ℝ) := by
        rw [Real.negMulLog, Real.log_inv]
        ring
  rw [partitionEntropy_eq_sum_positive_atoms mu P]
  change (∑ A ∈ Q, Real.negMulLog (mu.real A)) ≤ Real.log (Q.card : ℝ)
  nlinarith [inv_pos.mpr hQ_pos]

lemma partitionEntropy_iteratedJoin_le_log_card_positive_atoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (n : ℕ) :
    partitionEntropy mu (iteratedJoin T P n) ≤
      Real.log
        (((iteratedJoin T P n).filter fun A => mu A ≠ 0).card : ℝ) := by
  exact partitionEntropy_le_log_card_positive_atoms mu
    (isMeasurablePartition_iteratedJoin mu T hT P hP n)

lemma positive_atoms_nonempty
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P) :
    (P.filter fun A => mu A ≠ 0).Nonempty := by
  have hsum := sum_measureReal_positive_atoms_eq_one mu hP
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsum
  simp at hsum

lemma card_iteratedJoin_le_pow
    {M : Type*} (T : M → M) (P : Finset (Set M)) (n : ℕ) :
    (iteratedJoin T P n).card ≤ P.card ^ n := by
  classical
  rw [iteratedJoin]
  calc
    ((Fintype.piFinset fun _ : Fin n => P).image
        fun f : Fin n → Set M => ⋂ k : Fin n, T^[k.val] ⁻¹' f k).card ≤
        (Fintype.piFinset fun _ : Fin n => P).card := Finset.card_image_le
    _ = ∏ _k : Fin n, P.card := Fintype.card_piFinset _
    _ = P.card ^ n := by simp

lemma log_card_positive_iteratedJoin_div_le_log_card
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (n : ℕ) :
    Real.log
        (((iteratedJoin T P n).filter fun A => mu A ≠ 0).card : ℝ) / n ≤
      Real.log (P.card : ℝ) := by
  classical
  let Q := (iteratedJoin T P n).filter fun A => mu A ≠ 0
  have hQ_nonempty : Q.Nonempty := by
    exact positive_atoms_nonempty mu
      (isMeasurablePartition_iteratedJoin mu T hT P hP n)
  have hQ_pos : (0 : ℝ) < Q.card := by
    exact_mod_cast Finset.card_pos.mpr hQ_nonempty
  have hP_nonempty : P.Nonempty := by
    exact (positive_atoms_nonempty mu hP).mono (Finset.filter_subset _ _)
  have hP_one : 1 ≤ (P.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hP_nonempty
  have hcard_nat : Q.card ≤ P.card ^ n := by
    exact (Finset.card_filter_le _ _).trans (card_iteratedJoin_le_pow T P n)
  have hcard : (Q.card : ℝ) ≤ (P.card : ℝ) ^ n := by
    exact_mod_cast hcard_nat
  have hlog : Real.log (Q.card : ℝ) ≤ Real.log ((P.card : ℝ) ^ n) :=
    Real.log_le_log hQ_pos hcard
  cases n with
  | zero =>
      simpa using Real.log_nonneg hP_one
  | succ n =>
      rw [Real.log_pow] at hlog
      calc
        Real.log (Q.card : ℝ) / ((n + 1 : ℕ) : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) * Real.log (P.card : ℝ) /
              ((n + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hlog (by positivity)
        _ = Real.log (P.card : ℝ) := by
          field_simp

lemma entropyW_le_limsup_log_card_positive_atoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    entropyW mu T P ≤
      Filter.limsup
        (fun n : ℕ =>
          Real.log
              (((iteratedJoin T P n).filter fun A => mu A ≠ 0).card : ℝ) / n)
        Filter.atTop := by
  unfold entropyW
  apply Filter.limsup_le_limsup
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (partitionEntropy_iteratedJoin_le_log_card_positive_atoms mu T hT P hP n)
        (Nat.cast_nonneg n)
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop fun n =>
      div_nonneg (partitionEntropy_nonneg mu (iteratedJoin T P n)) (Nat.cast_nonneg n)
  · exact Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun n =>
        log_card_positive_iteratedJoin_div_le_log_card mu T hT P hP n)

lemma carrier_entropy_growth_reduction
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_pres : MeasurePreserving T mu mu)
    (hmu_erg : Ergodic T mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {s : Set EucPlane} (hP_subset : ∀ A ∈ P, A ⊆ s)
    (hs_dim : dimH s = dimMeasure mu) :
    entropyW mu T P ≤
        Filter.limsup
          (fun n : ℕ =>
            Real.log
                (((iteratedJoin T P n).filter fun A => mu A ≠ 0).card : ℝ) / n)
          Filter.atTop ∧
      ∀ n : ℕ, 0 < n → ∀ A ∈ iteratedJoin T P n, mu A ≠ 0 →
        dimH A = dimMeasure mu := by
  refine ⟨entropyW_le_limsup_log_card_positive_atoms mu T hmu_pres P hP, ?_⟩
  intro n hn A hA hmu_A
  exact dimH_iteratedJoin_atom_eq_dimMeasure T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hmu_erg P hP hP_subset hs_dim hn hA hmu_A

end Submission.Helpers
