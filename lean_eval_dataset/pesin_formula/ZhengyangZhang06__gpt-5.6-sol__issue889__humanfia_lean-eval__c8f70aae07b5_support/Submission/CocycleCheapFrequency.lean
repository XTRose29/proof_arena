import Submission.NonlinearStoppingGrowth
import Submission.PointwiseErgodic

namespace Submission.Helpers

open Filter MeasureTheory

lemma badCount_le_natCast (cheap : ℕ → Prop) (k m : ℕ) :
    badCount cheap k m ≤ m := by
  classical
  calc
    badCount cheap k m ≤ ∑ _j ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      split <;> norm_num
    _ = m := by simp

lemma badCount_orbit_cocycleCheapSet_eq_birkhoffSum
    {M : Type*} (T : M → M) (f : ℕ → M → ℝ)
    (a : ℝ) (N m : ℕ) (x : M) :
    badCount (fun j => T^[j] x ∈ cocycleCheapSet f a N) 0 m =
      birkhoffSum T (cocycleBadIndicator f a N) m x := by
  classical
  simp only [badCount, birkhoffSum, Nat.zero_add, cocycleBadIndicator]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Set.indicator_apply]
  by_cases hcheap : T^[j] x ∈ cocycleCheapSet f a N <;> simp [hcheap]

theorem tendsto_measureReal_compl_cocycleCheapSet_zero_of_ae_tendsto
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (f : ℕ → M → ℝ) (hf : ∀ n, Measurable (f n))
    {rate a : ℝ} (hra : rate < a)
    (hconv : ∀ᵐ x ∂mu, Tendsto (fun n : ℕ => f n x / n)
      atTop (nhds rate)) :
    Tendsto (fun N => mu.real (cocycleCheapSet f a N)ᶜ)
      atTop (nhds 0) := by
  have hfullUnion : mu (⋃ N : ℕ, cocycleCheapSet f a N)ᶜ = 0 := by
    apply mem_ae_iff.mp
    filter_upwards [hconv] with x hxconv
    rw [mem_iUnion_cocycleCheapSet_iff]
    have hlt : ∀ᶠ n : ℕ in atTop, f n x / n < a :=
      (tendsto_order.1 hxconv).2 a hra
    obtain ⟨n, hnlt, hnpos⟩ :=
      (hlt.and (eventually_gt_atTop 0)).exists
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    refine ⟨n, hnpos, le_of_lt ?_⟩
    exact (div_lt_iff₀ hnreal).mp hnlt
  have hinter : ⋂ N : ℕ, (cocycleCheapSet f a N)ᶜ =
      (⋃ N : ℕ, cocycleCheapSet f a N)ᶜ := by simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun N => (measurableSet_cocycleCheapSet hf a N).compl.nullMeasurableSet)
    (fun N L hNL => Set.compl_subset_compl.mpr
      (monotone_cocycleCheapSet f a hNL))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun N => (mu (cocycleCheapSet f a N)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun N => measure_ne_top mu (cocycleCheapSet f a N)ᶜ)).2 hmeasure

lemma integrable_cocycleBadIndicator
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {f : ℕ → M → ℝ}
    (hf : ∀ n, Measurable (f n)) (a : ℝ) (N : ℕ) :
    Integrable (cocycleBadIndicator f a N) mu := by
  apply Integrable.of_bound
    (measurable_cocycleBadIndicator hf a N).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    have hnonneg := cocycleBadIndicator_nonneg f a N x
    have hle : cocycleBadIndicator f a N x ≤ 1 := by
      classical
      rw [cocycleBadIndicator, Set.indicator_apply]
      split <;> simp
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

theorem exists_ae_eventually_badCount_mul_lt
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (f : ℕ → M → ℝ) (hf : ∀ n, Measurable (f n))
    {rate a C eta : ℝ} (hra : rate < a) (heta : 0 < eta)
    (hconv : ∀ᵐ x ∂mu, Tendsto (fun n : ℕ => f n x / n)
      atTop (nhds rate)) :
    ∃ N : ℕ, 0 < N ∧ ∀ᵐ x ∂mu, ∀ᶠ m : ℕ in atTop,
      C * badCount (fun j => T^[j] x ∈ cocycleCheapSet f a N) 0 m <
        eta * m := by
  have hmeasure :=
    tendsto_measureReal_compl_cocycleCheapSet_zero_of_ae_tendsto
      mu f hf hra hconv
  have hscaled : Tendsto
      (fun N => C * mu.real (cocycleCheapSet f a N)ᶜ)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hmeasure
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C * mu.real (cocycleCheapSet f a N)ᶜ < eta :=
    (tendsto_order.1 hscaled).2 eta heta
  obtain ⟨N, hNsmall, hNpos⟩ :=
    (hsmall.and (eventually_gt_atTop 0)).exists
  refine ⟨N, hNpos, ?_⟩
  have havg := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg (cocycleBadIndicator f a N)
      (measurable_cocycleBadIndicator hf a N)
      (integrable_cocycleBadIndicator mu hf a N)
  filter_upwards [havg] with x hxavg
  have hscaledAvg : Tendsto
      (fun m => C * birkhoffAverage ℝ T (cocycleBadIndicator f a N) m x)
      atTop (nhds (C * mu.real (cocycleCheapSet f a N)ᶜ)) := by
    simpa [integral_cocycleBadIndicator mu hf a N] using
      tendsto_const_nhds.mul hxavg
  have heventually : ∀ᶠ m : ℕ in atTop,
      C * birkhoffAverage ℝ T (cocycleBadIndicator f a N) m x < eta :=
    (tendsto_order.1 hscaledAvg).2 eta hNsmall
  filter_upwards [heventually, eventually_gt_atTop 0] with m hm hmpos
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  rw [badCount_orbit_cocycleCheapSet_eq_birkhoffSum]
  rw [birkhoffAverage, smul_eq_mul] at hm
  have hm' :
      (C * birkhoffSum T (cocycleBadIndicator f a N) m x) / m < eta := by
    calc
      (C * birkhoffSum T (cocycleBadIndicator f a N) m x) / m =
          C * ((m : ℝ)⁻¹ *
            birkhoffSum T (cocycleBadIndicator f a N) m x) := by
        field_simp [hmreal.ne']
      _ < eta := hm
  exact (div_lt_iff₀ hmreal).mp hm'

end Submission.Helpers
