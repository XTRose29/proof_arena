import Submission.CenteredShannonMcMillanEventually
import Submission.UniformEventually

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma measure_closedBall_le_exp_neg_of_mem_light_atom
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (P : Finset (Set M)) {c r : ℝ} {carrier : Set M} {x : M}
    (hcarrier_full : mu carrierᶜ = 0)
    (hxlight : x ∈ ⋃ A ∈ lightAtoms mu P c, A)
    (hsubset : ∀ A ∈ lightAtoms mu P c, x ∈ A →
      Metric.closedBall x r ∩ carrier ⊆ A) :
    mu (Metric.closedBall x r) ≤ ENNReal.ofReal (Real.exp (-c)) := by
  classical
  obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxlight
  obtain ⟨hAlight, hxA⟩ := Set.mem_iUnion.mp hxA
  have hAmeasure : mu.real A < Real.exp (-c) :=
    (Finset.mem_filter.mp hAlight).2
  calc
    mu (Metric.closedBall x r) =
        mu (Metric.closedBall x r ∩ carrier) :=
      (measure_inter_eq_of_compl_eq_zero mu hcarrier_full _).symm
    _ ≤ mu A := measure_mono (hsubset A hAlight hxA)
    _ = ENNReal.ofReal (mu.real A) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c)) :=
      ENNReal.ofReal_le_ofReal hAmeasure.le

lemma le_dimMeasure_of_eventual_light_atoms_exponential_ball_subset
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {carrier : Set EucPlane}
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    (P : ℕ → Finset (Set EucPlane))
    (d : NNReal) (hd : 0 < d)
    {R h : ℝ} (hR : 0 < R) (N0 : ℕ)
    (hbudget : ∀ n, N0 ≤ n → R * (d : ℝ) * (n + 1 : ℕ) ≤ h * n)
    [NoAtoms mu]
    (hlight : ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      x ∈ ⋃ A ∈ lightAtoms mu (P n) (h * n), A)
    (hsubset : ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ∀ A ∈ lightAtoms mu (P n) (h * n), x ∈ A →
        Metric.closedBall x (Real.exp (-R * n)) ∩ carrier ⊆ A) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  have hball : ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      mu (Metric.closedBall x (Real.exp (-R * n))) ≤
        ENNReal.ofReal (Real.exp (-h * n)) := by
    filter_upwards [hlight, hsubset] with x hxlight hxsubset
    filter_upwards [hxlight, hxsubset] with n hnlight hnsubset
    simpa only [neg_mul] using
      (measure_closedBall_le_exp_neg_of_mem_light_atom
        mu (P n) hcarrier_full hnlight hnsubset)
  exact le_dimMeasure_of_ae_eventually_exponential_closedBall_le
    mu hcarrier_measurable hcarrier_full hcarrier_dim d hd hR N0
      hbudget hball

lemma le_dimMeasure_of_balanced_centered_exponential_ball_subset
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {carrier : Set EucPlane}
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hepsilon : 0 < epsilon)
    (d : NNReal) (hd : 0 < d)
    {R : ℝ} (hR : 0 < R) (N0 : ℕ)
    (hbudget : ∀ n, N0 ≤ n →
      R * (d : ℝ) * (n + 1 : ℕ) ≤ (entropyW mu T P - epsilon) * n)
    [NoAtoms mu]
    (hsubset : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ A ∈ lightAtoms mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L))
          ((entropyW mu T P - epsilon) * L),
        x ∈ A → Metric.closedBall x (Real.exp (-R * L)) ∩ carrier ⊆ A) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  let Q : ℕ → Finset (Set EucPlane) := fun L =>
    centeredJoin T T_inv P
      (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L)
  have hlight := ae_eventually_mem_balanced_centered_entropy_lightAtoms
    mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv P hP
      hlam1 hlam2 hepsilon
  apply le_dimMeasure_of_eventual_light_atoms_exponential_ball_subset
    mu hcarrier_measurable hcarrier_full hcarrier_dim Q d hd hR N0 hbudget
  · simpa [Q] using hlight
  · simpa [Q] using hsubset

lemma le_dimMeasure_of_balanced_centered_exponential_ball_subset_of_rate
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {carrier : Set EucPlane}
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hepsilon : 0 < epsilon)
    (d : NNReal) (hd : 0 < d)
    {R : ℝ} (hR : 0 < R)
    (hrate : R * (d : ℝ) < entropyW mu T P - epsilon)
    [NoAtoms mu]
    (hsubset : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ A ∈ lightAtoms mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L))
          ((entropyW mu T P - epsilon) * L),
        x ∈ A → Metric.closedBall x (Real.exp (-R * L)) ∩ carrier ⊆ A) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  obtain ⟨N, hbudget⟩ := exists_nat_exponential_budget
    d hd hR hrate
  exact le_dimMeasure_of_balanced_centered_exponential_ball_subset
    mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv P hP
      hcarrier_measurable hcarrier_full hcarrier_dim hlam1 hlam2 hepsilon
      d hd hR N hbudget hsubset

lemma entropyW_sub_le_dimMeasure_mul_rate_of_balanced_ball_subset
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {carrier : Set EucPlane}
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    (hdim_top : dimMeasure mu ≠ ⊤)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hepsilon : 0 < epsilon)
    {R : ℝ} (hR : 0 < R)
    [NoAtoms mu]
    (hsubset : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ A ∈ lightAtoms mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L))
          ((entropyW mu T P - epsilon) * L),
        x ∈ A → Metric.closedBall x (Real.exp (-R * L)) ∩ carrier ⊆ A) :
    entropyW mu T P - epsilon ≤ (dimMeasure mu).toReal * R := by
  let h := entropyW mu T P - epsilon
  by_cases hh : h ≤ 0
  · exact hh.trans (mul_nonneg ENNReal.toReal_nonneg hR.le)
  have hh_pos : 0 < h := lt_of_not_ge hh
  apply le_of_not_gt
  intro hdim_lt
  have hquot_pos : 0 < h / R := div_pos hh_pos hR
  have hdim_quot : (dimMeasure mu).toReal < h / R :=
    (lt_div_iff₀ hR).2 hdim_lt
  let dReal := ((dimMeasure mu).toReal + h / R) / 2
  have hdReal_pos : 0 < dReal := by
    dsimp [dReal]
    positivity
  let d : NNReal := ⟨dReal, hdReal_pos.le⟩
  have hd : 0 < d := hdReal_pos
  have hd_coe : (d : ℝ) = dReal := rfl
  have hd_lt_quot : (d : ℝ) < h / R := by
    rw [hd_coe]
    dsimp [dReal]
    linarith
  have hrate : R * (d : ℝ) < entropyW mu T P - epsilon := by
    change R * (d : ℝ) < h
    simpa [mul_comm] using (lt_div_iff₀ hR).mp hd_lt_quot
  have hd_le :=
    le_dimMeasure_of_balanced_centered_exponential_ball_subset_of_rate
      mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv P hP
        hcarrier_measurable hcarrier_full hcarrier_dim
        hlam1 hlam2 hepsilon d hd hR hrate hsubset
  have hd_toReal : (d : ℝ) ≤ (dimMeasure mu).toReal := by
    have := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hdim_top).2 hd_le
    simpa using this
  rw [hd_coe] at hd_toReal
  dsimp [dReal] at hd_toReal
  linarith

end Submission.Helpers
