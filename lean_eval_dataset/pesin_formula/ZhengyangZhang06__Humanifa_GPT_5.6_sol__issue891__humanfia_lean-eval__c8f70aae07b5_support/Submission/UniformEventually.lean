import Submission.GeometricFrostman

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma exists_measurable_set_ne_zero_forall_ge_of_ae_eventually
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (hmu : mu ≠ 0)
    (p : M → ℕ → Prop)
    (hp_measurable : ∀ n, MeasurableSet {x | p x n})
    (hp : ∀ᵐ x ∂mu, ∀ᶠ n in atTop, p x n) :
    ∃ N, MeasurableSet {x | ∀ n, N ≤ n → p x n} ∧
      mu {x | ∀ n, N ≤ n → p x n} ≠ 0 := by
  let S : ℕ → Set M := fun N => {x | ∀ n, N ≤ n → p x n}
  have hS_measurable (N : ℕ) : MeasurableSet (S N) := by
    have hS_eq : S N = ⋂ n : ℕ, ⋂ (_h : N ≤ n), {x | p x n} := by
      ext x
      simp [S]
    rw [hS_eq]
    exact MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun _hn => hp_measurable n
  have hUnion_ae : ∀ᵐ x ∂mu, x ∈ ⋃ N, S N := by
    filter_upwards [hp] with x hx
    obtain ⟨N, hN⟩ := eventually_atTop.1 hx
    exact Set.mem_iUnion_of_mem N (fun n hn => hN n hn)
  have hSome : ∃ N, mu (S N) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hUnion_zero : mu (⋃ N, S N) = 0 := measure_iUnion_null hnone
    have hUnion_compl : mu (⋃ N, S N)ᶜ = 0 := mem_ae_iff.mp hUnion_ae
    have hUniv : mu Set.univ = 0 := by
      have hEq := measure_of_measure_compl_eq_zero hUnion_compl
      rw [hUnion_zero] at hEq
      exact hEq.symm
    exact hmu (Measure.measure_univ_eq_zero.mp hUniv)
  obtain ⟨N, hN⟩ := hSome
  exact ⟨N, hS_measurable N, hN⟩

lemma measurable_closedBallMeasure
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M]
    (mu : Measure M) [IsFiniteMeasure mu] (r : ℝ) :
    Measurable fun x => mu (Metric.closedBall x r) := by
  let S : Set (M × M) := {p | dist p.2 p.1 ≤ r}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  simpa [S, Metric.closedBall] using
    (measurable_measure_prodMk_left_finite (ν := mu) hS)

lemma le_dimMeasure_of_ae_eventually_exponential_closedBall_le
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {carrier : Set EucPlane}
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_dim : dimH carrier = LeanEval.Dynamics.dimMeasure mu)
    (d : NNReal) (hd : 0 < d)
    {R h : ℝ} (hR : 0 < R) (N0 : ℕ)
    (hbudget : ∀ n, N0 ≤ n → R * (d : ℝ) * (n + 1 : ℕ) ≤ h * n)
    [NoAtoms mu]
    (hball : ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      mu (Metric.closedBall x (Real.exp (-R * n))) ≤
        ENNReal.ofReal (Real.exp (-h * n))) :
    (d : ℝ≥0∞) ≤ LeanEval.Dynamics.dimMeasure mu := by
  let p : EucPlane → ℕ → Prop := fun x n =>
    x ∈ carrier ∧
      mu (Metric.closedBall x (Real.exp (-R * n))) ≤
        ENNReal.ofReal (Real.exp (-h * n))
  have hp_measurable (n : ℕ) : MeasurableSet {x | p x n} := by
    apply hcarrier_measurable.inter
    exact measurableSet_le
      (measurable_closedBallMeasure mu (Real.exp (-R * n))) measurable_const
  have hp : ∀ᵐ x ∂mu, ∀ᶠ n in atTop, p x n := by
    filter_upwards [mem_ae_iff.mpr hcarrier_full, hball] with x hx hxn
    filter_upwards [hxn] with n hn
    exact ⟨hx, hn⟩
  obtain ⟨N, hS_measurable, hS_ne_zero⟩ :=
    exists_measurable_set_ne_zero_forall_ge_of_ae_eventually
      mu (Measure.measure_univ_ne_zero.mp (by simp)) p hp_measurable hp
  let s : Set EucPlane := {x | ∀ n, N ≤ n → p x n}
  have hs_carrier : s ⊆ carrier := by
    intro x hx
    exact (hx N le_rfl).1
  apply le_dimMeasure_of_exponential_closedBall_le mu hS_measurable hS_ne_zero
    hs_carrier hcarrier_dim d hd hR (max N N0)
  · intro n hn
    exact hbudget n ((le_max_right N N0).trans hn)
  · intro x _hx
    exact measure_singleton x
  · intro x hx n hn
    exact (hx n ((le_max_left N N0).trans hn)).2

end Submission.Helpers
