import Submission.InformationAtoms
import Submission.PointwiseErgodic
import Mathlib.Probability.Martingale.Convergence

namespace Submission.Helpers

open Filter MeasureTheory

noncomputable def finiteConditionalProbability
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    (mu : Measure M) (Y : M → J) (A : Set M) (x : M) : ℝ :=
  ∑ y : J, (Y ⁻¹' {y}).indicator
    (fun _ => mu.real (A ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})) x

lemma finiteConditionalProbability_apply
    {M J : Type*} [MeasurableSpace M] [Fintype J] [DecidableEq J]
    (mu : Measure M) (Y : M → J) (A : Set M) (x : M) :
    finiteConditionalProbability mu Y A x =
      mu.real (A ∩ Y ⁻¹' {Y x}) / mu.real (Y ⁻¹' {Y x}) := by
  classical
  rw [finiteConditionalProbability, Finset.sum_eq_single (Y x)]
  · have hx : x ∈ Y ⁻¹' ({Y x} : Set J) := rfl
    rw [Set.indicator_of_mem hx]
  · intro y _hy hyx
    have hx : x ∉ Y ⁻¹' ({y} : Set J) := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Ne.symm hyx
    rw [Set.indicator_of_notMem hx]
  · simp

lemma finiteConditionalProbability_nonneg
    {M J : Type*} [MeasurableSpace M] [Fintype J] [DecidableEq J]
    (mu : Measure M) (Y : M → J) (A : Set M) (x : M) :
    0 ≤ finiteConditionalProbability mu Y A x := by
  rw [finiteConditionalProbability_apply]
  exact div_nonneg (measureReal_nonneg) (measureReal_nonneg)

lemma finiteConditionalProbability_le_one
    {M J : Type*} [MeasurableSpace M] [Fintype J] [DecidableEq J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (A : Set M) (x : M) :
    finiteConditionalProbability mu Y A x ≤ 1 := by
  rw [finiteConditionalProbability_apply]
  by_cases hzero : mu.real (Y ⁻¹' {Y x}) = 0
  · simp [hzero, measureReal_mono_null Set.inter_subset_right hzero]
  · apply (div_le_one (lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero))).2
    exact measureReal_mono Set.inter_subset_right

lemma stronglyMeasurable_finiteConditionalProbability
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) (Y : M → J) (A : Set M) :
    StronglyMeasurable[MeasurableSpace.comap Y inferInstance]
      (finiteConditionalProbability mu Y A) := by
  apply Measurable.stronglyMeasurable
  unfold finiteConditionalProbability
  apply Finset.measurable_sum
  intro y _hy
  apply measurable_const.indicator
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨{y}, measurableSet_singleton y, rfl⟩

lemma integrable_finiteConditionalProbability
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (hY : Measurable Y) (A : Set M) :
    Integrable (finiteConditionalProbability mu Y A) mu := by
  unfold finiteConditionalProbability
  apply integrable_finsetSum
  intro y _hy
  exact (integrable_const _).indicator (hY (measurableSet_singleton y))

lemma sum_measureReal_inter_fibers
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    {A : Set M} (hA : MeasurableSet A)
    (t : Set J) :
    ∑ y : J, t.indicator (fun y => mu.real (A ∩ Y ⁻¹' {y})) y =
      mu.real (A ∩ Y ⁻¹' t) := by
  classical
  let Q : Finset J := Finset.univ.filter fun y => y ∈ t
  have hpairwise : Set.Pairwise (Q : Set J)
      (Function.onFun (AEDisjoint mu) fun y => A ∩ Y ⁻¹' {y}) := by
    intro y _hy z _hz hyz
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro x hxy hxz
    have hy : Y x = y := Set.mem_singleton_iff.mp hxy.2
    have hz : Y x = z := Set.mem_singleton_iff.mp hxz.2
    exact hyz (hy.symm.trans hz)
  have hmeasurable : ∀ y ∈ Q, NullMeasurableSet (A ∩ Y ⁻¹' {y}) mu := by
    intro y _hy
    exact (hA.inter (hY (measurableSet_singleton y))).nullMeasurableSet
  have hunion : (⋃ y ∈ Q, A ∩ Y ⁻¹' {y}) = A ∩ Y ⁻¹' t := by
    ext x
    simp [Q]
  calc
    (∑ y : J, t.indicator (fun y => mu.real (A ∩ Y ⁻¹' {y})) y) =
        ∑ y ∈ Q, mu.real (A ∩ Y ⁻¹' {y}) := by
      simpa [Q, Set.indicator] using
        (Finset.sum_filter (s := Finset.univ) (fun y : J => y ∈ t)
          (fun y => mu.real (A ∩ Y ⁻¹' {y}))).symm
    _ = mu.real (A ∩ Y ⁻¹' t) := by
      rw [← measureReal_biUnion_finset₀ hpairwise hmeasurable, hunion]

lemma measureReal_mul_div_fiber
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] (A B : Set M) :
    mu.real B * (mu.real (A ∩ B) / mu.real B) = mu.real (A ∩ B) := by
  by_cases hB : mu.real B = 0
  · have hAB : mu.real (A ∩ B) = 0 :=
      measureReal_mono_null Set.inter_subset_right hB
    simp [hB, hAB]
  · exact mul_div_cancel₀ _ hB

lemma integrable_indicator_comp_finiteConditionalProbability
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    {A : Set M} (hA : MeasurableSet A) (phi : ℝ → ℝ) :
    Integrable (fun x => A.indicator
      (fun _ => phi (finiteConditionalProbability mu Y A x)) x) mu := by
  classical
  let r : J → ℝ := fun y =>
    mu.real (A ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})
  have heq :
      (fun x => A.indicator
          (fun _ => phi (finiteConditionalProbability mu Y A x)) x) =
        fun x => ∑ y : J, (A ∩ Y ⁻¹' {y}).indicator
          (fun _ => phi (r y)) x := by
    funext x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Finset.sum_eq_single (Y x)]
      · rw [Set.indicator_of_mem]
        · simp only [r]
          rw [finiteConditionalProbability_apply]
        · exact ⟨hxA, rfl⟩
      · intro y _hy hyx
        rw [Set.indicator_of_notMem]
        intro hxy
        exact hyx hxy.2.symm
      · simp
    · rw [Set.indicator_of_notMem hxA]
      symm
      apply Finset.sum_eq_zero
      intro y _hy
      rw [Set.indicator_of_notMem]
      exact fun hxy => hxA hxy.1
  rw [heq]
  apply integrable_finsetSum
  intro y _hy
  exact (integrable_const _).indicator
    (hA.inter (hY (measurableSet_singleton y)))

lemma integral_indicator_neg_log_finiteConditionalProbability
    {M J : Type*} [MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    {A : Set M} (hA : MeasurableSet A) :
    (∫ x, A.indicator
        (fun _ => -Real.log (finiteConditionalProbability mu Y A x)) x ∂mu) =
      ∫ x, Real.negMulLog (finiteConditionalProbability mu Y A x) ∂mu := by
  classical
  let r : J → ℝ := fun y =>
    mu.real (A ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})
  have hleft :
      (fun x => A.indicator
          (fun _ => -Real.log (finiteConditionalProbability mu Y A x)) x) =
        fun x => ∑ y : J, (A ∩ Y ⁻¹' {y}).indicator
          (fun _ => -Real.log (r y)) x := by
    funext x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Finset.sum_eq_single (Y x)]
      · rw [Set.indicator_of_mem]
        · simp only [r]
          rw [finiteConditionalProbability_apply]
        · exact ⟨hxA, rfl⟩
      · intro y _hy hyx
        rw [Set.indicator_of_notMem]
        intro hxy
        exact hyx hxy.2.symm
      · simp
    · rw [Set.indicator_of_notMem hxA]
      symm
      apply Finset.sum_eq_zero
      intro y _hy
      rw [Set.indicator_of_notMem]
      exact fun hxy => hxA hxy.1
  have hright :
      (fun x => Real.negMulLog (finiteConditionalProbability mu Y A x)) =
        fun x => ∑ y : J, (Y ⁻¹' {y}).indicator
          (fun _ => Real.negMulLog (r y)) x := by
    funext x
    rw [Finset.sum_eq_single (Y x)]
    · rw [Set.indicator_of_mem (show x ∈ Y ⁻¹' ({Y x} : Set J) by rfl)]
      simp only [r]
      rw [finiteConditionalProbability_apply]
    · intro y _hy hyx
      rw [Set.indicator_of_notMem]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Ne.symm hyx
    · simp
  rw [hleft, hright, integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _hy
    rw [integral_indicator_const _
        (hA.inter (hY (measurableSet_singleton y))),
      integral_indicator_const _ (hY (measurableSet_singleton y)),
      smul_eq_mul, smul_eq_mul]
    rw [Real.negMulLog]
    have hmul := measureReal_mul_div_fiber mu A (Y ⁻¹' {y})
    change mu.real (Y ⁻¹' {y}) * r y = mu.real (A ∩ Y ⁻¹' {y}) at hmul
    rw [← hmul]
    ring
  · intro y _hy
    exact (integrable_const _).indicator (hY (measurableSet_singleton y))
  · intro y _hy
    exact (integrable_const _).indicator
      (hA.inter (hY (measurableSet_singleton y)))

lemma finiteConditionalProbability_ae_eq_condExp
    {M J : Type*} [mM : MeasurableSpace M] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsFiniteMeasure mu]
    (Y : M → J) (hY : Measurable Y)
    {A : Set M} (hA : MeasurableSet A) :
    finiteConditionalProbability mu Y A =ᵐ[mu]
      mu[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Y inferInstance] := by
  classical
  have hm : MeasurableSpace.comap Y inferInstance ≤ mM := hY.comap_le
  have hf : Integrable (A.indicator fun _ => (1 : ℝ)) mu :=
    (integrable_const _).indicator hA
  have hg : Integrable (finiteConditionalProbability mu Y A) mu :=
    integrable_finiteConditionalProbability mu Y hY A
  apply ae_eq_condExp_of_forall_setIntegral_eq
    (m := MeasurableSpace.comap Y inferInstance) (m₀ := mM) (μ := mu)
    (f := A.indicator fun _ => (1 : ℝ))
    (g := finiteConditionalProbability mu Y A)
    hm hf (fun _s _hs _hmu => hg.integrableOn)
  · intro s hs _hmu
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨t, ht, rfl⟩
    change (∫ x in Y ⁻¹' t,
      ∑ y : J, (Y ⁻¹' {y}).indicator
        (fun _ => mu.real (A ∩ Y ⁻¹' {y}) / mu.real (Y ⁻¹' {y})) x ∂mu) = _
    rw [integral_finsetSum]
    · calc
        (∑ y : J, ∫ x in Y ⁻¹' t,
            (Y ⁻¹' {y}).indicator
              (fun _ => mu.real (A ∩ Y ⁻¹' {y}) /
                mu.real (Y ⁻¹' {y})) x ∂mu) =
            ∑ y : J, t.indicator
              (fun y => mu.real (A ∩ Y ⁻¹' {y})) y := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [setIntegral_indicator (hY (measurableSet_singleton y)),
            setIntegral_const, smul_eq_mul]
          by_cases hyt : y ∈ t
          · rw [Set.indicator_of_mem hyt]
            have hinter : Y ⁻¹' t ∩ Y ⁻¹' {y} = Y ⁻¹' {y} := by
              ext x
              simp only [Set.mem_inter_iff, Set.mem_preimage,
                Set.mem_singleton_iff]
              constructor
              · exact fun hx => hx.2
              · intro hxy
                exact ⟨by rw [hxy]; exact hyt, hxy⟩
            rw [hinter]
            exact measureReal_mul_div_fiber mu A (Y ⁻¹' {y})
          · rw [Set.indicator_of_notMem hyt]
            have hinter : Y ⁻¹' t ∩ Y ⁻¹' {y} = ∅ := by
              ext x
              change (Y x ∈ t ∧ Y x = y) ↔ False
              constructor
              · rintro ⟨hxt, hxy⟩
                rw [hxy] at hxt
                exact (hyt hxt).elim
              · exact fun hx => hx.elim
            simp [hinter]
        _ = mu.real (A ∩ Y ⁻¹' t) :=
          sum_measureReal_inter_fibers mu Y hY hA t
        _ = mu.real (Y ⁻¹' t ∩ A) := by rw [Set.inter_comm]
        _ = ∫ x in Y ⁻¹' t, A.indicator (fun _ => (1 : ℝ)) x ∂mu := by
          rw [setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    · intro y _hy
      exact ((integrable_const _).indicator
        (hY (measurableSet_singleton y))).integrableOn
  · exact (stronglyMeasurable_finiteConditionalProbability mu Y A).aestronglyMeasurable

noncomputable def partitionSymbol
    {M : Type*} (P : Finset (Set M)) (x : M) : ↥P → Bool :=
  fun A => A.1.indicator (fun _ => true) x

lemma measurable_partitionSymbol
    {M : Type*} [MeasurableSpace M]
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Measurable (partitionSymbol P) := by
  apply measurable_pi_lambda
  intro A
  exact measurable_const.indicator (hP A.1 A.2)

noncomputable def futureSymbol
    {M : Type*} (T : M → M) (P : Finset (Set M))
    (k : ℕ) (x : M) : ↥P → Bool :=
  partitionSymbol P (T^[k + 1] x)

lemma measurable_futureSymbol
    {M : Type*} [MeasurableSpace M]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (k : ℕ) :
    Measurable (futureSymbol T P k) := by
  exact (measurable_partitionSymbol P hP).comp (hT.iterate (k + 1))

noncomputable def futureFiltration
    {M : Type*} [MeasurableSpace M]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Filtration ℕ ‹MeasurableSpace M› :=
  Filtration.natural (fun k => futureSymbol T P k)
    (fun k => (measurable_futureSymbol T hT P hP k).stronglyMeasurable)

noncomputable def futureObservation
    {M : Type*} (T : M → M) (P : Finset (Set M))
    (n : ℕ) (x : M) : (j : Set.Iic n) → (↥P → Bool) :=
  fun j => futureSymbol T P j.1 x

lemma measurable_futureObservation
    {M : Type*} [MeasurableSpace M]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    Measurable (futureObservation T P n) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_futureSymbol T hT P hP j.1

lemma futureFiltration_eq_comap
    {M : Type*} [MeasurableSpace M]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    futureFiltration T hT P hP n =
      MeasurableSpace.comap (futureObservation T P n) inferInstance := by
  exact Filtration.natural_eq_comap
    (fun k => futureSymbol T P k)
    (fun k => (measurable_futureSymbol T hT P hP k).stronglyMeasurable) n

noncomputable def futureConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (P : Finset (Set M))
    (A : Set M) (n : ℕ) : M → ℝ :=
  finiteConditionalProbability mu (futureObservation T P n) A

lemma measurable_futureConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    (A : Set M) (n : ℕ) :
    Measurable (futureConditionalProbability mu T P A n) := by
  exact (stronglyMeasurable_finiteConditionalProbability
    mu (futureObservation T P n) A).mono
      (measurable_futureObservation T hT P hP n).comap_le |>.measurable

lemma futureConditionalProbability_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (P : Finset (Set M))
    (A : Set M) (n : ℕ) (x : M) :
    0 ≤ futureConditionalProbability mu T P A n x := by
  exact finiteConditionalProbability_nonneg
    mu (futureObservation T P n) A x

lemma futureConditionalProbability_le_one
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (T : M → M) (P : Finset (Set M))
    (A : Set M) (n : ℕ) (x : M) :
    futureConditionalProbability mu T P A n x ≤ 1 := by
  exact finiteConditionalProbability_le_one
    mu (futureObservation T P n) A x

noncomputable def futureConditionalProbabilityLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    (A : Set M) : M → ℝ :=
  mu[A.indicator (fun _ => (1 : ℝ)) |
    ⨆ n, futureFiltration T hT P hP n]

lemma futureConditionalProbability_ae_eq_condExp
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) (n : ℕ) :
    futureConditionalProbability mu T P A n =ᵐ[mu]
      mu[A.indicator (fun _ => (1 : ℝ)) |
        futureFiltration T hT P hP n] := by
  rw [futureFiltration_eq_comap T hT P hP n]
  exact finiteConditionalProbability_ae_eq_condExp
    mu (futureObservation T P n)
      (measurable_futureObservation T hT P hP n) hA

lemma ae_tendsto_futureConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu,
      Tendsto (fun n => futureConditionalProbability mu T P A n x)
        atTop (nhds (futureConditionalProbabilityLimit mu T hT P hP A x)) := by
  have heq : ∀ᵐ x ∂mu, ∀ n : ℕ,
      futureConditionalProbability mu T P A n x =
        mu[A.indicator (fun _ => (1 : ℝ)) |
          futureFiltration T hT P hP n] x := by
    rw [ae_all_iff]
    exact futureConditionalProbability_ae_eq_condExp mu T hT P hP hA
  have htend := tendsto_ae_condExp
    (ℱ := futureFiltration T hT P hP)
    (μ := mu) (A.indicator fun _ => (1 : ℝ))
  filter_upwards [heq, htend] with x hxeq hxtend
  exact hxtend.congr' (Filter.Eventually.of_forall fun n => (hxeq n).symm)

lemma ae_futureConditionalProbabilityLimit_mem_Icc
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu,
      futureConditionalProbabilityLimit mu T hT P hP A x ∈ Set.Icc 0 1 := by
  filter_upwards
      [ae_tendsto_futureConditionalProbability mu T hT P hP hA] with x hx
  exact isClosed_Icc.mem_of_tendsto hx (Filter.Eventually.of_forall fun n =>
    ⟨futureConditionalProbability_nonneg mu T P A n x,
      futureConditionalProbability_le_one mu T P A n x⟩)

lemma integrable_negMulLog_futureConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    (A : Set M) (n : ℕ) :
    Integrable (fun x =>
      Real.negMulLog (futureConditionalProbability mu T P A n x)) mu := by
  apply Integrable.of_bound
    ((Real.continuous_negMulLog.measurable.comp
      (measurable_futureConditionalProbability mu T hT P hP A n)).aestronglyMeasurable)
    1
  exact Filter.Eventually.of_forall fun x => by
    have hnonneg := futureConditionalProbability_nonneg mu T P A n x
    have hle := futureConditionalProbability_le_one mu T P A n x
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg hnonneg hle)]
    exact (Real.negMulLog_le_one_sub_self hnonneg).trans (sub_le_self 1 hnonneg)

lemma integrable_negMulLog_futureConditionalProbabilityLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) :
    Integrable (fun x =>
      Real.negMulLog
        (futureConditionalProbabilityLimit mu T hT P hP A x)) mu := by
  have hm : (⨆ n, futureFiltration T hT P hP n) ≤ ‹MeasurableSpace M› :=
    iSup_le fun n => (futureFiltration T hT P hP).le n
  apply Integrable.of_bound
    ((Real.continuous_negMulLog.measurable.comp
      (stronglyMeasurable_condExp.mono hm).measurable).aestronglyMeasurable)
    1
  filter_upwards
      [ae_futureConditionalProbabilityLimit_mem_Icc mu T hT P hP
        hA] with x hx
  change |Real.negMulLog
    (futureConditionalProbabilityLimit mu T hT P hP A x)| ≤ 1
  rw [abs_of_nonneg (Real.negMulLog_nonneg hx.1 hx.2)]
  exact (Real.negMulLog_le_one_sub_self hx.1).trans (sub_le_self 1 hx.1)

lemma tendsto_integral_negMulLog_futureConditionalProbability
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) :
    Tendsto
      (fun n => ∫ x, Real.negMulLog
        (futureConditionalProbability mu T P A n x) ∂mu)
      atTop
      (nhds (∫ x, Real.negMulLog
        (futureConditionalProbabilityLimit mu T hT P hP A x) ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (Real.continuous_negMulLog.measurable.comp
      (measurable_futureConditionalProbability mu T hT P hP A n)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      have hnonneg := futureConditionalProbability_nonneg mu T P A n x
      have hle := futureConditionalProbability_le_one mu T P A n x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg hnonneg hle)]
      exact (Real.negMulLog_le_one_sub_self hnonneg).trans
        (sub_le_self 1 hnonneg)
  · filter_upwards
      [ae_tendsto_futureConditionalProbability mu T hT P hP hA] with x hx
    exact Real.continuous_negMulLog.continuousAt.tendsto.comp hx

lemma ae_pos_condExp_indicator_on_set
    {M : Type*} [mM : MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    {m : MeasurableSpace M}
    (hm : m ≤ mM) {A : Set M} (hA : MeasurableSet[mM] A) :
    ∀ᵐ x ∂mu, x ∈ A →
      0 < mu[A.indicator (fun _ => (1 : ℝ)) | m] x := by
  let q : M → ℝ := mu[A.indicator (fun _ => (1 : ℝ)) | m]
  let Z : Set M := {x | q x = 0}
  have hf : Integrable (A.indicator fun _ => (1 : ℝ)) mu :=
    (integrable_const _).indicator hA
  have hq_nonneg : 0 ≤ᵐ[mu] q := by
    exact condExp_nonneg (Filter.Eventually.of_forall fun x => by
      simp only [Pi.zero_apply]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hZ : MeasurableSet[m] Z := by
    exact measurableSet_eq_fun stronglyMeasurable_condExp.measurable measurable_const
  have hset := setIntegral_condExp
    (m := m) (m₀ := mM) (μ := mu)
    (f := A.indicator fun _ => (1 : ℝ)) hm hf hZ
  have hleft : (∫ x in Z, q x ∂mu) = 0 := by
    apply setIntegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun x hx => hx
  have hright : (∫ x in Z, A.indicator (fun _ => (1 : ℝ)) x ∂mu) =
      mu.real (Z ∩ A) := by
    rw [setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
  rw [hleft, hright] at hset
  have hZA : mu (Z ∩ A) = 0 :=
    (measureReal_eq_zero_iff).mp hset.symm
  filter_upwards [hq_nonneg, measure_eq_zero_iff_ae_notMem.mp hZA] with x hxq hxZA hxA
  exact lt_of_le_of_ne hxq fun hzero => hxZA ⟨hzero.symm, hxA⟩

lemma integrable_indicator_neg_log_condExp_and_integral
    {M : Type*} [mM : MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    {m : MeasurableSpace M} (hm : m ≤ mM)
    {A : Set M} (hA : MeasurableSet[mM] A) :
    Integrable (fun x => A.indicator
      (fun _ => -Real.log (mu[A.indicator (fun _ => (1 : ℝ)) | m] x)) x) mu ∧
      (∫ x, A.indicator
        (fun _ => -Real.log (mu[A.indicator (fun _ => (1 : ℝ)) | m] x)) x ∂mu) =
        ∫ x, Real.negMulLog
          (mu[A.indicator (fun _ => (1 : ℝ)) | m] x) ∂mu := by
  let q : M → ℝ := mu[A.indicator (fun _ => (1 : ℝ)) | m]
  let ell : M → ℝ := fun x => -Real.log (q x)
  let g : M → ℝ := fun x => A.indicator (fun _ => ell x) x
  let z : M → ℝ := fun x => Real.negMulLog (q x)
  let phi : ℕ → Set M := fun n => {x | |ell x| ≤ (n : ℝ)}
  have hq_strong : StronglyMeasurable[m] q := stronglyMeasurable_condExp
  have hell_strong : StronglyMeasurable[m] ell := by
    exact (Real.measurable_log.comp hq_strong.measurable).neg.stronglyMeasurable
  have hphi_m (n : ℕ) : MeasurableSet[m] (phi n) := by
    change MeasurableSet[m] {x | ‖ell x‖ ≤ (n : ℝ)}
    exact measurableSet_le hell_strong.measurable.norm measurable_const
  have hphi (n : ℕ) : MeasurableSet[mM] (phi n) := hm _ (hphi_m n)
  letI : MeasurableSpace M := mM
  have hcover : @AECover M ℕ mM mu atTop phi := by
    refine ⟨Filter.Eventually.of_forall fun x => ?_, fun n => hphi n⟩
    obtain ⟨N, hN⟩ := exists_nat_ge |ell x|
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans (by exact_mod_cast hn)
  have honeA : Integrable (A.indicator fun _ => (1 : ℝ)) mu :=
    (integrable_const _).indicator hA
  have hq_nonneg : 0 ≤ᵐ[mu] q := by
    exact condExp_nonneg (Filter.Eventually.of_forall fun x => by
      simp only [Pi.zero_apply]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hq_le_one : q ≤ᵐ[mu] fun _ => (1 : ℝ) := by
    have hmono := condExp_mono (m := m) (μ := mu)
      honeA (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx])
    simpa [q, condExp_const hm] using hmono
  have hz : Integrable z mu := by
    apply Integrable.of_bound
      ((Real.continuous_negMulLog.measurable.comp
        (hq_strong.mono hm).measurable).aestronglyMeasurable) 1
    filter_upwards [hq_nonneg, hq_le_one] with x hx0 hx1
    change |Real.negMulLog (q x)| ≤ 1
    rw [abs_of_nonneg (Real.negMulLog_nonneg hx0 hx1)]
    exact (Real.negMulLog_le_one_sub_self hx0).trans (sub_le_self 1 hx0)
  have hg_strong : StronglyMeasurable[mM] g := by
    exact (hell_strong.mono hm).indicator hA
  have hg_nonneg : 0 ≤ᵐ[mu] g := by
    filter_upwards [hq_nonneg, hq_le_one] with x hx0 hx1
    by_cases hxA : x ∈ A
    · simp only [g, Set.indicator_of_mem hxA, ell]
      exact neg_nonneg.mpr (Real.log_nonpos hx0 hx1)
    · simp [g, Set.indicator_of_notMem hxA]
  have hg_on (n : ℕ) : IntegrableOn g (phi n) mu := by
    apply IntegrableOn.of_bound (measure_lt_top mu (phi n))
      (hg_strong.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      (n : ℝ)
    filter_upwards [ae_restrict_mem (hphi n)] with x hx
    by_cases hxA : x ∈ A
    · simp only [g, Set.indicator_of_mem hxA, Real.norm_eq_abs]
      exact hx
    · simp [g, Set.indicator_of_notMem hxA, Nat.cast_nonneg]
  have hseteq (n : ℕ) :
      (∫ x in phi n, g x ∂mu) = ∫ x in phi n, z x ∂mu := by
    let f : M → ℝ := fun x => (phi n).indicator (fun _ => ell x) x
    have hf_strong : StronglyMeasurable[m] f :=
      hell_strong.indicator (hphi_m n)
    have hf_bound : ∀ x, ‖f x‖ ≤ (n : ℝ) := by
      intro x
      by_cases hx : x ∈ phi n
      · simp only [f, Set.indicator_of_mem hx, Real.norm_eq_abs]
        exact hx
      · simp [f, Set.indicator_of_notMem hx, Nat.cast_nonneg]
    have hf_mul : Integrable
        (f * A.indicator fun _ => (1 : ℝ)) mu := by
      exact honeA.bdd_mul (hf_strong.mono hm).aestronglyMeasurable
        (Filter.Eventually.of_forall hf_bound)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (μ := mu) hf_strong hf_mul honeA
    rw [← integral_indicator (hphi n), ← integral_indicator (hphi n)]
    calc
      (∫ x, (phi n).indicator g x ∂mu) =
          ∫ x, (f * A.indicator fun _ => (1 : ℝ)) x ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hxphi : x ∈ phi n <;> by_cases hxA : x ∈ A <;>
            simp [f, g, Set.indicator_of_mem, Set.indicator_of_notMem,
              hxphi, hxA]
      _ = ∫ x, mu[(f * A.indicator fun _ => (1 : ℝ)) | m] x ∂mu := by
        symm
        exact integral_condExp hm
      _ = ∫ x, (f * q) x ∂mu := integral_congr_ae hpull
      _ = ∫ x, (phi n).indicator z x ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hxphi : x ∈ phi n
          · rw [Set.indicator_of_mem hxphi]
            simp only [Pi.mul_apply, f, Set.indicator_of_mem hxphi, ell, z,
              Real.negMulLog]
            ring
          · simp [f, Set.indicator_of_notMem hxphi]
  have hz_tend : Tendsto (fun n => ∫ x in phi n, z x ∂mu)
      atTop (nhds (∫ x, z x ∂mu)) :=
    hcover.integral_tendsto_of_countably_generated hz
  have hg_tend : Tendsto (fun n => ∫ x in phi n, g x ∂mu)
      atTop (nhds (∫ x, z x ∂mu)) :=
    hz_tend.congr' (Filter.Eventually.of_forall fun n => (hseteq n).symm)
  have hg_int : Integrable g mu :=
    hcover.integrable_of_integral_tendsto_of_nonneg_ae
      (∫ x, z x ∂mu) hg_on hg_nonneg hg_tend
  have hg_eq : (∫ x, g x ∂mu) = ∫ x, z x ∂mu :=
    hcover.integral_eq_of_tendsto_of_nonneg_ae
      (∫ x, z x ∂mu) hg_nonneg hg_on hg_tend
  simpa [q, ell, g, z] using And.intro hg_int hg_eq

lemma ae_futureConditionalProbabilityLimit_pos_on_set
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    {A : Set M} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu, x ∈ A →
      0 < futureConditionalProbabilityLimit mu T hT P hP A x := by
  exact ae_pos_condExp_indicator_on_set
    (mM := ‹MeasurableSpace M›)
    (m := ⨆ n, futureFiltration T hT P hP n) mu
    (iSup_le fun n => (futureFiltration T hT P hP).le n) hA

noncomputable def futureConditionalInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (P : Finset (Set M))
    (n : ℕ) (x : M) : ℝ :=
  ∑ A ∈ P, A.indicator
    (fun _ => -Real.log (futureConditionalProbability mu T P A n x)) x

noncomputable def futureConditionalInformationLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A)
    (x : M) : ℝ :=
  ∑ A ∈ P, A.indicator
    (fun _ => -Real.log
      (futureConditionalProbabilityLimit mu T hT P hP A x)) x

lemma ae_tendsto_futureConditionalInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    ∀ᵐ x ∂mu,
      Tendsto (fun n => futureConditionalInformation mu T P n x)
        atTop (nhds (futureConditionalInformationLimit mu T hT P hP x)) := by
  have htend : ∀ᵐ x ∂mu, ∀ A ∈ P,
      Tendsto (fun n => futureConditionalProbability mu T P A n x)
        atTop (nhds (futureConditionalProbabilityLimit mu T hT P hP A x)) := by
    rw [eventually_all_finset]
    intro A hAP
    exact ae_tendsto_futureConditionalProbability mu T hT P hP (hP A hAP)
  have hpos : ∀ᵐ x ∂mu, ∀ A ∈ P, x ∈ A →
      0 < futureConditionalProbabilityLimit mu T hT P hP A x := by
    rw [eventually_all_finset]
    intro A hAP
    exact ae_futureConditionalProbabilityLimit_pos_on_set
      mu T hT P hP (hP A hAP)
  filter_upwards [htend, hpos] with x hxtend hxpos
  unfold futureConditionalInformation futureConditionalInformationLimit
  apply tendsto_finsetSum
  intro A hAP
  by_cases hxA : x ∈ A
  · simp only [Set.indicator_of_mem hxA]
    exact (Real.continuousAt_log (ne_of_gt (hxpos A hAP hxA))).neg.tendsto.comp
      (hxtend A hAP)
  · simp [Set.indicator_of_notMem hxA]

lemma measurable_futureConditionalInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    Measurable (futureConditionalInformation mu T P n) := by
  unfold futureConditionalInformation
  apply Finset.measurable_sum
  intro A hAP
  exact (Real.measurable_log.comp
    (measurable_futureConditionalProbability mu T hT P hP A n)).neg.indicator
      (hP A hAP)

lemma futureConditionalInformation_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (T : M → M) (P : Finset (Set M)) (n : ℕ) (x : M) :
    0 ≤ futureConditionalInformation mu T P n x := by
  unfold futureConditionalInformation
  apply Finset.sum_nonneg
  intro A _hAP
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA]
    exact neg_nonneg.mpr (Real.log_nonpos
      (futureConditionalProbability_nonneg mu T P A n x)
      (futureConditionalProbability_le_one mu T P A n x))
  · simp [Set.indicator_of_notMem hxA]

lemma measurable_futureConditionalInformationLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Measurable (futureConditionalInformationLimit mu T hT P hP) := by
  unfold futureConditionalInformationLimit
  apply Finset.measurable_sum
  intro A hAP
  have hm : (⨆ n, futureFiltration T hT P hP n) ≤ ‹MeasurableSpace M› :=
    iSup_le fun n => (futureFiltration T hT P hP).le n
  exact (Real.measurable_log.comp
    (stronglyMeasurable_condExp.mono hm).measurable).neg.indicator (hP A hAP)

lemma ae_futureConditionalInformationLimit_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    0 ≤ᵐ[mu] futureConditionalInformationLimit mu T hT P hP := by
  have hbounds : ∀ᵐ x ∂mu, ∀ A ∈ P,
      futureConditionalProbabilityLimit mu T hT P hP A x ∈ Set.Icc 0 1 := by
    rw [eventually_all_finset]
    intro A hAP
    exact ae_futureConditionalProbabilityLimit_mem_Icc
      mu T hT P hP (hP A hAP)
  filter_upwards [hbounds] with x hxbounds
  unfold futureConditionalInformationLimit
  apply Finset.sum_nonneg
  intro A hAP
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA]
    exact neg_nonneg.mpr (Real.log_nonpos
      (hxbounds A hAP).1 (hxbounds A hAP).2)
  · simp [Set.indicator_of_notMem hxA]

lemma integrable_futureConditionalInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    Integrable (futureConditionalInformation mu T P n) mu := by
  unfold futureConditionalInformation
  apply integrable_finsetSum
  intro A hAP
  exact integrable_indicator_comp_finiteConditionalProbability
    mu (futureObservation T P n)
      (measurable_futureObservation T hT P hP n) (hP A hAP)
      (fun p => -Real.log p)

lemma integral_futureConditionalInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (n : ℕ) :
    (∫ x, futureConditionalInformation mu T P n x ∂mu) =
      ∑ A ∈ P, ∫ x, Real.negMulLog
        (futureConditionalProbability mu T P A n x) ∂mu := by
  unfold futureConditionalInformation
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro A hAP
    exact integral_indicator_neg_log_finiteConditionalProbability
      mu (futureObservation T P n)
        (measurable_futureObservation T hT P hP n) (hP A hAP)
  · intro A hAP
    exact integrable_indicator_comp_finiteConditionalProbability
      mu (futureObservation T P n)
        (measurable_futureObservation T hT P hP n) (hP A hAP)
        (fun p => -Real.log p)

lemma tendsto_integral_futureConditionalInformation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Tendsto
      (fun n => ∫ x, futureConditionalInformation mu T P n x ∂mu)
      atTop
      (nhds (∑ A ∈ P, ∫ x, Real.negMulLog
        (futureConditionalProbabilityLimit mu T hT P hP A x) ∂mu)) := by
  have hsum : Tendsto
      (fun n => ∑ A ∈ P, ∫ x, Real.negMulLog
        (futureConditionalProbability mu T P A n x) ∂mu)
      atTop
      (nhds (∑ A ∈ P, ∫ x, Real.negMulLog
        (futureConditionalProbabilityLimit mu T hT P hP A x) ∂mu)) := by
    apply tendsto_finsetSum
    intro A hAP
    exact tendsto_integral_negMulLog_futureConditionalProbability
      mu T hT P hP (hP A hAP)
  convert hsum using 1
  ext n
  exact integral_futureConditionalInformation mu T hT P hP n

lemma integrable_futureConditionalInformationLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Integrable (futureConditionalInformationLimit mu T hT P hP) mu := by
  unfold futureConditionalInformationLimit
  apply integrable_finsetSum
  intro A hAP
  have hm : (⨆ n, futureFiltration T hT P hP n) ≤ ‹MeasurableSpace M› :=
    iSup_le fun n => (futureFiltration T hT P hP).le n
  simpa [futureConditionalProbabilityLimit] using
    (integrable_indicator_neg_log_condExp_and_integral
      (mM := ‹MeasurableSpace M›) mu hm (hP A hAP)).1

lemma integral_futureConditionalInformationLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    (∫ x, futureConditionalInformationLimit mu T hT P hP x ∂mu) =
      ∑ A ∈ P, ∫ x, Real.negMulLog
        (futureConditionalProbabilityLimit mu T hT P hP A x) ∂mu := by
  unfold futureConditionalInformationLimit
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro A hAP
    have hm : (⨆ n, futureFiltration T hT P hP n) ≤ ‹MeasurableSpace M› :=
      iSup_le fun n => (futureFiltration T hT P hP).le n
    simpa [futureConditionalProbabilityLimit] using
      (integrable_indicator_neg_log_condExp_and_integral
        (mM := ‹MeasurableSpace M›) mu hm (hP A hAP)).2
  · intro A hAP
    have hm : (⨆ n, futureFiltration T hT P hP n) ≤ ‹MeasurableSpace M› :=
      iSup_le fun n => (futureFiltration T hT P hP).le n
    simpa [futureConditionalProbabilityLimit] using
      (integrable_indicator_neg_log_condExp_and_integral
        (mM := ‹MeasurableSpace M›) mu hm (hP A hAP)).1

lemma tendsto_integral_futureConditionalInformationLimit
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : Measurable T)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Tendsto
      (fun n => ∫ x, futureConditionalInformation mu T P n x ∂mu)
      atTop
      (nhds (∫ x, futureConditionalInformationLimit mu T hT P hP x ∂mu)) := by
  rw [integral_futureConditionalInformationLimit mu T hT P hP]
  exact tendsto_integral_futureConditionalInformation mu T hT P hP

end Submission.Helpers
