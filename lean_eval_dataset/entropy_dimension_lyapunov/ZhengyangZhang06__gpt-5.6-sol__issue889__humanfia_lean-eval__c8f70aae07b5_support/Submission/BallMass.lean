import Submission.HyperbolicBalance

namespace Submission.Helpers

open MeasureTheory
open scoped ENNReal

lemma measure_le_card_mul_exp_neg_of_cover_lightAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P Q : Finset (Set M)) (c : ℝ)
    (hQ : Q ⊆ lightAtoms mu P c)
    {s : Set M} (hcover : s ⊆ ⋃ A ∈ Q, A) :
    mu s ≤ ENNReal.ofReal (Q.card * Real.exp (-c)) := by
  calc
    mu s ≤ mu (⋃ A ∈ Q, A) := measure_mono hcover
    _ ≤ ∑ A ∈ Q, mu A := measure_biUnion_finset_le Q id
    _ ≤ ∑ _A ∈ Q, ENNReal.ofReal (Real.exp (-c)) := by
      apply Finset.sum_le_sum
      intro A hA
      have hlight := (Finset.mem_filter.mp (hQ hA)).2
      calc
        mu A = ENNReal.ofReal (mu.real A) := (ofReal_measureReal).symm
        _ ≤ ENNReal.ofReal (Real.exp (-c)) :=
          ENNReal.ofReal_le_ofReal (le_of_lt hlight)
    _ = ENNReal.ofReal (Q.card * Real.exp (-c)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg Q.card), ENNReal.ofReal_natCast]
      simp

lemma measure_le_card_mul_exp_neg_of_ae_cover_lightAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P Q : Finset (Set M)) (c : ℝ)
    (hQ : Q ⊆ lightAtoms mu P c)
    {s : Set M} (hcover : mu (s \ ⋃ A ∈ Q, A) = 0) :
    mu s ≤ ENNReal.ofReal (Q.card * Real.exp (-c)) := by
  calc
    mu s ≤ mu (⋃ A ∈ Q, A) := measure_mono_ae (ae_le_set.mpr hcover)
    _ ≤ ENNReal.ofReal (Q.card * Real.exp (-c)) :=
      measure_le_card_mul_exp_neg_of_cover_lightAtoms mu P Q c hQ
        (Set.Subset.rfl)

lemma measure_closedEBall_le_of_lightAtoms_multiplicity
    {M : Type*} [MeasurableSpace M] [PseudoEMetricSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) (c : ℝ)
    {x : M} {r : ℝ≥0∞} {q : ℕ}
    (hmultiplicity : ∃ Q : Finset (Set M),
      Q ⊆ lightAtoms mu P c ∧ Q.card ≤ q ∧
        Metric.closedEBall x r ⊆ ⋃ A ∈ Q, A) :
    mu (Metric.closedEBall x r) ≤ ENNReal.ofReal (q * Real.exp (-c)) := by
  obtain ⟨Q, hQ, hQ_card, hcover⟩ := hmultiplicity
  calc
    mu (Metric.closedEBall x r) ≤
        ENNReal.ofReal (Q.card * Real.exp (-c)) :=
      measure_le_card_mul_exp_neg_of_cover_lightAtoms mu P Q c hQ hcover
    _ ≤ ENNReal.ofReal (q * Real.exp (-c)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hQ_card)
        (Real.exp_pos (-c)).le

lemma measure_closedEBall_le_of_ae_lightAtoms_multiplicity
    {M : Type*} [MeasurableSpace M] [PseudoEMetricSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) (c : ℝ)
    {x : M} {r : ℝ≥0∞} {q : ℕ}
    (hmultiplicity : ∃ Q : Finset (Set M),
      Q ⊆ lightAtoms mu P c ∧ Q.card ≤ q ∧
        mu (Metric.closedEBall x r \ ⋃ A ∈ Q, A) = 0) :
    mu (Metric.closedEBall x r) ≤ ENNReal.ofReal (q * Real.exp (-c)) := by
  obtain ⟨Q, hQ, hQ_card, hcover⟩ := hmultiplicity
  calc
    mu (Metric.closedEBall x r) ≤
        ENNReal.ofReal (Q.card * Real.exp (-c)) :=
      measure_le_card_mul_exp_neg_of_ae_cover_lightAtoms
        mu P Q c hQ hcover
    _ ≤ ENNReal.ofReal (q * Real.exp (-c)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hQ_card)
        (Real.exp_pos (-c)).le

end Submission.Helpers
