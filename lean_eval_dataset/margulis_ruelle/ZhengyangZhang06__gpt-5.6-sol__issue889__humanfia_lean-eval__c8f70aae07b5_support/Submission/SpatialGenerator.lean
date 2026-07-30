import Submission.GeneratorEntropy
import Submission.GeneratorConditionalExpectation

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

noncomputable def spatialPrefixObservation
    {M : Type*} (bit : ℕ → M → Bool) (n : ℕ) (x : M) :
    Set.Iic n → Bool :=
  fun k => bit k.1 x

lemma measurable_spatialCode
    {M : Type*} [MeasurableSpace M]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k)) :
    Measurable fun x k => bit k x := by
  apply measurable_pi_lambda
  exact hbit

lemma measurable_spatialPrefixObservation
    {M : Type*} [MeasurableSpace M]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k)) (n : ℕ) :
    Measurable (spatialPrefixObservation bit n) := by
  apply measurable_pi_lambda
  intro k
  exact hbit k.1

noncomputable def spatialCodeFiltration
    {M : Type*} [MeasurableSpace M]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k)) :
    Filtration ℕ ‹MeasurableSpace M› :=
  Filtration.natural bit fun k => (hbit k).stronglyMeasurable

lemma spatialCodeFiltration_eq_comap
    {M : Type*} [MeasurableSpace M]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k)) (n : ℕ) :
    spatialCodeFiltration bit hbit n =
      MeasurableSpace.comap (spatialPrefixObservation bit n) inferInstance := by
  exact Filtration.natural_eq_comap bit
    (fun k => (hbit k).stronglyMeasurable) n

lemma iSup_spatialCodeFiltration_eq_comap
    {M : Type*} [MeasurableSpace M]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k)) :
    (⨆ n, spatialCodeFiltration bit hbit n) =
      MeasurableSpace.comap (fun x k => bit k x) inferInstance := by
  have hcomap : MeasurableSpace.comap (fun x k => bit k x) inferInstance =
      ⨆ k, MeasurableSpace.comap (bit k) inferInstance := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def]
  rw [hcomap]
  apply le_antisymm
  · apply iSup_le
    intro n
    change (⨆ k ≤ n, MeasurableSpace.comap (bit k) inferInstance) ≤ _
    apply iSup₂_le
    intro k hk
    exact le_iSup (fun j => MeasurableSpace.comap (bit j) inferInstance) k
  · apply iSup_le
    intro k
    apply le_iSup_of_le k
    change MeasurableSpace.comap (bit k) inferInstance ≤
      ⨆ j ≤ k, MeasurableSpace.comap (bit j) inferInstance
    exact le_iSup₂_of_le k le_rfl le_rfl

lemma fiberPartition_observationBlock
    {M J : Type*} [Fintype J]
    (T : M → M) (Y : M → J) (n : ℕ) :
    fiberPartition (observationBlock T Y n) =
      iteratedJoin T (fiberPartition Y) n := by
  classical
  ext A
  constructor
  · intro hA
    rw [fiberPartition] at hA
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hA
    rw [iteratedJoin]
    refine Finset.mem_image.mpr ⟨fun k => Y ⁻¹' ({f k} : Set J), ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro k
      exact Finset.mem_image.mpr ⟨f k, Finset.mem_univ _, rfl⟩
    · ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro hx
        funext k
        change Y (T^[k.val] x) = f k
        exact hx k
      · intro hx k
        exact congrFun hx k
  · intro hA
    rw [iteratedJoin] at hA
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hA
    have hexists (k : Fin n) :
        ∃ y : J, g k = Y ⁻¹' ({y} : Set J) := by
      obtain ⟨y, _hy, hgy⟩ := Finset.mem_image.mp
        (Fintype.mem_piFinset.mp hg k)
      exact ⟨y, hgy.symm⟩
    choose f hf using hexists
    rw [fiberPartition]
    refine Finset.mem_image.mpr ⟨f, Finset.mem_univ _, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · intro hx k
      rw [hf k]
      exact congrFun hx k
    · intro hx
      funext k
      change Y (T^[k.val] x) = f k
      simpa [hf k] using hx k

lemma observationEntropy_observationBlock_fiberPartition
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    (mu : Measure M) (T : M → M) (Y : M → J) (n : ℕ) :
    observationEntropy mu (observationBlock T Y n) =
      partitionEntropy mu (iteratedJoin T (fiberPartition Y) n) := by
  rw [← partitionEntropy_fiberPartition]
  rw [fiberPartition_observationBlock]

lemma entropyW_le_fiberPartition_add_conditional
    {M J : Type*} [MeasurableSpace M]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M) (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (Y : M → J) (hY : Measurable Y)
    (Q : Finset (Set M)) (hQ : IsMeasurablePartition mu Q) :
    entropyW mu T Q ≤ entropyW mu T (fiberPartition Y) +
      conditionalPartitionEntropy mu Y Q := by
  apply entropyW_le_of_observationBlock_entropy_le
    mu T T_inv hT_right hT (fiberPartition Y) Q
      (isMeasurablePartition_fiberPartition mu Y hY) hQ Y hY 0
  intro n
  exact (observationEntropy_observationBlock_fiberPartition mu T Y n).le

noncomputable def spatialConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (bit : ℕ → M → Bool) (A : Set M) (n : ℕ) : M → ℝ :=
  finiteConditionalProbability mu (spatialPrefixObservation bit n) A

lemma measurable_spatialConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (bit : ℕ → M → Bool)
    (hbit : ∀ k, Measurable (bit k)) (A : Set M) (n : ℕ) :
    Measurable (spatialConditionalProbability mu bit A n) := by
  exact (stronglyMeasurable_finiteConditionalProbability
    mu (spatialPrefixObservation bit n) A).mono
      (measurable_spatialPrefixObservation bit hbit n).comap_le |>.measurable

lemma spatialConditionalProbability_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (bit : ℕ → M → Bool) (A : Set M) (n : ℕ) (x : M) :
    0 ≤ spatialConditionalProbability mu bit A n x := by
  exact finiteConditionalProbability_nonneg
    mu (spatialPrefixObservation bit n) A x

lemma spatialConditionalProbability_le_one
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (bit : ℕ → M → Bool) (A : Set M) (n : ℕ) (x : M) :
    spatialConditionalProbability mu bit A n x ≤ 1 := by
  exact finiteConditionalProbability_le_one
    mu (spatialPrefixObservation bit n) A x

lemma spatialConditionalProbability_ae_eq_condExp
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    {A : Set M} (hA : MeasurableSet A) (n : ℕ) :
    spatialConditionalProbability mu bit A n =ᵐ[mu]
      mu[A.indicator (fun _ => (1 : ℝ)) | spatialCodeFiltration bit hbit n] := by
  rw [spatialCodeFiltration_eq_comap bit hbit n]
  exact finiteConditionalProbability_ae_eq_condExp
    mu (spatialPrefixObservation bit n)
      (measurable_spatialPrefixObservation bit hbit n) hA

lemma ae_tendsto_condExp_spatialCode_indicator
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => fun k => bit k x.1))
    {A : Set M} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n => (mu[A.indicator (fun _ => (1 : ℝ)) |
        spatialCodeFiltration bit hbit n]) x)
      atTop (nhds (A.indicator (fun _ => (1 : ℝ)) x)) := by
  have hlevy := tendsto_ae_condExp
    (μ := mu) (ℱ := spatialCodeFiltration bit hbit)
      (A.indicator (fun _ => (1 : ℝ)))
  rw [iSup_spatialCodeFiltration_eq_comap bit hbit] at hlevy
  have hcond := condExp_indicator_comap_ae_eq_of_full_measurableEmbedding
    mu (fun x k => bit k x) (measurable_spatialCode bit hbit)
      hfull hemb hA
  filter_upwards [hlevy, hcond] with x hx hcx
  simpa [hcx] using hx

lemma ae_tendsto_spatialConditionalProbability_indicator
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => fun k => bit k x.1))
    {A : Set M} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n => spatialConditionalProbability mu bit A n x)
      atTop (nhds (A.indicator (fun _ => (1 : ℝ)) x)) := by
  have heq : ∀ᵐ x ∂mu, ∀ n : ℕ,
      spatialConditionalProbability mu bit A n x =
        mu[A.indicator (fun _ => (1 : ℝ)) |
          spatialCodeFiltration bit hbit n] x := by
    rw [ae_all_iff]
    exact spatialConditionalProbability_ae_eq_condExp mu bit hbit hA
  have htend := ae_tendsto_condExp_spatialCode_indicator
    mu bit hbit hfull hemb hA
  filter_upwards [heq, htend] with x hxeq hxtend
  exact hxtend.congr' (Eventually.of_forall fun n => (hxeq n).symm)

lemma tendsto_integral_negMulLog_spatialConditionalProbability_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => fun k => bit k x.1))
    {A : Set M} (hA : MeasurableSet A) :
    Tendsto
      (fun n => ∫ x, Real.negMulLog
        (spatialConditionalProbability mu bit A n x) ∂mu)
      atTop (nhds 0) := by
  have htend : Tendsto
      (fun n => ∫ x, Real.negMulLog
        (spatialConditionalProbability mu bit A n x) ∂mu)
      atTop
      (nhds (∫ x, Real.negMulLog
        (A.indicator (fun _ => (1 : ℝ)) x) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (Real.continuous_negMulLog.measurable.comp
        (measurable_spatialConditionalProbability mu bit hbit A n))
          |>.aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall fun x => by
        have hnonneg := spatialConditionalProbability_nonneg mu bit A n x
        have hle := spatialConditionalProbability_le_one mu bit A n x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.negMulLog_nonneg hnonneg hle)]
        exact (Real.negMulLog_le_one_sub_self hnonneg).trans
          (sub_le_self 1 hnonneg)
    · filter_upwards
        [ae_tendsto_spatialConditionalProbability_indicator
          mu bit hbit hfull hemb hA] with x hx
      exact Real.continuous_negMulLog.continuousAt.tendsto.comp hx
  have hzero : (fun x : M => Real.negMulLog
      (A.indicator (fun _ => (1 : ℝ)) x)) = 0 := by
    funext x
    by_cases hx : x ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  simpa [hzero] using htend

lemma tendsto_spatialConditionalPartitionEntropy_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    (Q : Finset (Set M)) (hQ : ∀ A ∈ Q, MeasurableSet A)
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => fun k => bit k x.1)) :
    Tendsto
      (fun n => conditionalPartitionEntropy mu
        (spatialPrefixObservation bit n) Q)
      atTop (nhds 0) := by
  change Tendsto
    (fun n => ∑ A ∈ Q, ∫ x, Real.negMulLog
      (spatialConditionalProbability mu bit A n x) ∂mu)
    atTop (nhds 0)
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Q fun A hAQ =>
      tendsto_integral_negMulLog_spatialConditionalProbability_zero
        mu bit hbit hfull hemb (hQ A hAQ))

lemma entropyW_le_of_uniform_spatial_prefix_bound
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M) (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => fun k => bit k x.1))
    {U : ℝ}
    (hupper : ∀ n, entropyW mu T
      (fiberPartition (spatialPrefixObservation bit n)) ≤ U)
    (Q : Finset (Set M)) (hQ : IsMeasurablePartition mu Q) :
    entropyW mu T Q ≤ U := by
  have hcond := tendsto_spatialConditionalPartitionEntropy_zero
    mu bit hbit Q hQ.measurable hfull hemb
  have hrhs : Tendsto
      (fun n => U + conditionalPartitionEntropy mu
        (spatialPrefixObservation bit n) Q)
      atTop (nhds U) := by
    simpa using tendsto_const_nhds.add hcond
  apply ge_of_tendsto' hrhs
  intro n
  calc
    entropyW mu T Q ≤ entropyW mu T
          (fiberPartition (spatialPrefixObservation bit n)) +
        conditionalPartitionEntropy mu
          (spatialPrefixObservation bit n) Q :=
      entropyW_le_fiberPartition_add_conditional
        mu T T_inv hT_right hT (spatialPrefixObservation bit n)
          (measurable_spatialPrefixObservation bit hbit n) Q hQ
    _ ≤ U + conditionalPartitionEntropy mu
          (spatialPrefixObservation bit n) Q := by
      exact add_le_add (hupper n) le_rfl

lemma kolmogorovSinaiEntropy_le_of_uniform_spatial_prefix_bound
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M) (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (bit : ℕ → M → Bool) (hbit : ∀ k, Measurable (bit k))
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => fun k => bit k x.1))
    {U : ℝ}
    (hupper : ∀ n, entropyW mu T
      (fiberPartition (spatialPrefixObservation bit n)) ≤ U) :
    kolmogorovSinaiEntropy mu T ≤ U := by
  unfold kolmogorovSinaiEntropy
  apply csSup_le
  · exact ⟨0, ⟨{Set.univ}, isMeasurablePartition_singleton_univ mu,
      entropyW_singleton_univ mu T⟩⟩
  · intro h hh
    obtain ⟨Q, hQ, rfl⟩ := hh
    exact entropyW_le_of_uniform_spatial_prefix_bound
      mu T T_inv hT_right hT bit hbit hfull hemb hupper Q hQ

end Submission.Helpers
