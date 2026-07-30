import Submission.GeneratorConditionalExpectation

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

noncomputable def twoSidedObservation
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M))
    (n : ℕ) (x : M) : (j : Set.Iic n) → (↥P → Bool) :=
  fun j => natTwoSidedPartitionCode T T_inv P x j.1

lemma measurable_twoSidedObservation
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    Measurable (twoSidedObservation T T_inv P n) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply j.1).comp
    (measurable_natTwoSidedPartitionCode T T_inv hT hT_inv P hP)

lemma twoSidedCodeFiltration_eq_comap
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    twoSidedCodeFiltration T T_inv hT hT_inv P hP n =
      MeasurableSpace.comap (twoSidedObservation T T_inv P n) inferInstance := by
  exact Filtration.natural_eq_comap
    (fun k x => natTwoSidedPartitionCode T T_inv P x k)
    (fun k => ((measurable_pi_apply k).comp
      (measurable_natTwoSidedPartitionCode
        T T_inv hT hT_inv P hP)).stronglyMeasurable) n

noncomputable def twoSidedConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M) (P : Finset (Set M))
    (A : Set M) (n : ℕ) : M → ℝ :=
  finiteConditionalProbability mu (twoSidedObservation T T_inv P n) A

lemma measurable_twoSidedConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M)
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    (A : Set M) (n : ℕ) :
    Measurable (twoSidedConditionalProbability mu T T_inv P A n) := by
  exact (stronglyMeasurable_finiteConditionalProbability
    mu (twoSidedObservation T T_inv P n) A).mono
      (measurable_twoSidedObservation T T_inv hT hT_inv P hP n).comap_le
    |>.measurable

lemma twoSidedConditionalProbability_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M) (P : Finset (Set M))
    (A : Set M) (n : ℕ) (x : M) :
    0 ≤ twoSidedConditionalProbability mu T T_inv P A n x := by
  exact finiteConditionalProbability_nonneg
    mu (twoSidedObservation T T_inv P n) A x

lemma twoSidedConditionalProbability_le_one
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (T T_inv : M → M) (P : Finset (Set M))
    (A : Set M) (n : ℕ) (x : M) :
    twoSidedConditionalProbability mu T T_inv P A n x ≤ 1 := by
  exact finiteConditionalProbability_le_one
    mu (twoSidedObservation T T_inv P n) A x

lemma twoSidedConditionalProbability_ae_eq_condExp
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) (n : ℕ) :
    twoSidedConditionalProbability mu T T_inv P A n =ᵐ[mu]
      mu[A.indicator (fun _ => (1 : ℝ)) |
        twoSidedCodeFiltration T T_inv hT hT_inv P hP n] := by
  rw [twoSidedCodeFiltration_eq_comap T T_inv hT hT_inv P hP n]
  exact finiteConditionalProbability_ae_eq_condExp
    mu (twoSidedObservation T T_inv P n)
      (measurable_twoSidedObservation T T_inv hT hT_inv P hP n) hA

lemma ae_tendsto_twoSidedConditionalProbability_indicator_of_shrinking
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s) (hfull : mu sᶜ = 0)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L))
    {A : Set EucPlane} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n => twoSidedConditionalProbability mu T T_inv P A n x)
      atTop (nhds (A.indicator (fun _ => (1 : ℝ)) x)) := by
  have heq : ∀ᵐ x ∂mu, ∀ n : ℕ,
      twoSidedConditionalProbability mu T T_inv P A n x =
        mu[A.indicator (fun _ => (1 : ℝ)) |
          twoSidedCodeFiltration T T_inv hT hT_inv P hP n] x := by
    rw [ae_all_iff]
    exact twoSidedConditionalProbability_ae_eq_condExp
      mu T T_inv hT hT_inv P hP hA
  have htend := ae_tendsto_condExp_twoSidedCode_indicator_of_shrinking
    mu T T_inv hT_right hT hT_inv P hP hs hfull hR good
      hs_good hs_atom hpair hA
  filter_upwards [heq, htend] with x hxeq hxtend
  exact hxtend.congr' (Filter.Eventually.of_forall fun n => (hxeq n).symm)

lemma tendsto_integral_negMulLog_twoSidedConditionalProbability_zero
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s) (hfull : mu sᶜ = 0)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L))
    {A : Set EucPlane} (hA : MeasurableSet A) :
    Tendsto
      (fun n => ∫ x, Real.negMulLog
        (twoSidedConditionalProbability mu T T_inv P A n x) ∂mu)
      atTop (nhds 0) := by
  have htend : Tendsto
      (fun n => ∫ x, Real.negMulLog
        (twoSidedConditionalProbability mu T T_inv P A n x) ∂mu)
      atTop
      (nhds (∫ x, Real.negMulLog
        (A.indicator (fun _ => (1 : ℝ)) x) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (Real.continuous_negMulLog.measurable.comp
        (measurable_twoSidedConditionalProbability
          mu T T_inv hT hT_inv P hP A n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        have hnonneg := twoSidedConditionalProbability_nonneg
          mu T T_inv P A n x
        have hle := twoSidedConditionalProbability_le_one
          mu T T_inv P A n x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.negMulLog_nonneg hnonneg hle)]
        exact (Real.negMulLog_le_one_sub_self hnonneg).trans
          (sub_le_self 1 hnonneg)
    · filter_upwards
        [ae_tendsto_twoSidedConditionalProbability_indicator_of_shrinking
          mu T T_inv hT_right hT hT_inv P hP hs hfull hR good
            hs_good hs_atom hpair hA] with x hx
      exact Real.continuous_negMulLog.continuousAt.tendsto.comp hx
  have hzero : (fun x : EucPlane => Real.negMulLog
      (A.indicator (fun _ => (1 : ℝ)) x)) = 0 := by
    funext x
    by_cases hx : x ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  simpa [hzero] using htend

noncomputable def twoSidedConditionalPartitionEntropy
    (mu : Measure EucPlane)
    (T T_inv : EucPlane → EucPlane)
    (P Q : Finset (Set EucPlane)) (n : ℕ) : ℝ :=
  ∑ A ∈ Q, ∫ x, Real.negMulLog
    (twoSidedConditionalProbability mu T T_inv P A n x) ∂mu

lemma tendsto_twoSidedConditionalPartitionEntropy_zero_of_shrinking
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    (Q : Finset (Set EucPlane)) (hQ : ∀ A ∈ Q, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s) (hfull : mu sᶜ = 0)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    Tendsto (twoSidedConditionalPartitionEntropy mu T T_inv P Q)
      atTop (nhds 0) := by
  unfold twoSidedConditionalPartitionEntropy
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Q fun A hAQ =>
        tendsto_integral_negMulLog_twoSidedConditionalProbability_zero
          mu T T_inv hT_right hT hT_inv P hP hs hfull hR good
            hs_good hs_atom hpair (hQ A hAQ))

end Submission.Helpers
