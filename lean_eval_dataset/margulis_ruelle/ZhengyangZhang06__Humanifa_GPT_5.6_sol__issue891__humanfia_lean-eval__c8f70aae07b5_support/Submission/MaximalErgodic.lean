import Submission.MaximalCombinatorics
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving

namespace Submission.Helpers

open Filter MeasureTheory

def positiveMaxSet
    {M : Type*} (T : M → M) (f : M → ℝ) (N : ℕ) : Set M :=
  ⋃ n ∈ Finset.Icc 1 N, {x | 0 < birkhoffSum T f n x}

lemma measurable_birkhoffSum
    {M : Type*} [MeasurableSpace M]
    {T : M → M} (hT : Measurable T) {f : M → ℝ} (hf : Measurable f)
    (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  fun_prop

lemma measurableSet_positiveMaxSet
    {M : Type*} [MeasurableSpace M]
    {T : M → M} (hT : Measurable T) {f : M → ℝ} (hf : Measurable f)
    (N : ℕ) :
    MeasurableSet (positiveMaxSet T f N) := by
  apply Finset.measurableSet_biUnion
  intro n hn
  exact measurableSet_lt measurable_const (measurable_birkhoffSum hT hf n)

lemma mem_positiveMaxSet_iff
    {M : Type*} (T : M → M) (f : M → ℝ) (N : ℕ) (x : M) :
    x ∈ positiveMaxSet T f N ↔
      HasPositiveWindow (fun k => f (T^[k] x)) N 0 := by
  constructor
  · intro hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn, hsum⟩ := Set.mem_iUnion.mp hxn
    have hn' := Finset.mem_Icc.mp hn
    refine ⟨n, hn'.1, hn'.2, ?_⟩
    simpa [windowSum, birkhoffSum] using hsum
  · rintro ⟨n, hnpos, hnN, hsum⟩
    apply Set.mem_iUnion_of_mem n
    apply Set.mem_iUnion_of_mem (Finset.mem_Icc.mpr ⟨hnpos, hnN⟩)
    simpa [windowSum, birkhoffSum] using hsum

lemma integrable_comp_measurePreserving
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {T : M → M} (hT : MeasurePreserving T mu mu)
    {f : M → ℝ} (hf : Integrable f mu) :
    Integrable (fun x => f (T x)) mu := by
  have hfmap : Integrable f (Measure.map T mu) := by
    simpa [hT.map_eq] using hf
  simpa [Function.comp_def] using hfmap.comp_aemeasurable hT.aemeasurable

lemma integral_comp_measurePreserving
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {T : M → M} (hT : MeasurePreserving T mu mu)
    {f : M → ℝ} (hf : Integrable f mu) :
    ∫ x, f (T x) ∂mu = ∫ x, f x ∂mu := by
  have hfmap : Integrable f (Measure.map T mu) := by
    simpa [hT.map_eq] using hf
  have hmap := integral_map hT.aemeasurable hfmap.aestronglyMeasurable
  rw [hT.map_eq] at hmap
  exact hmap.symm

lemma birkhoffSum_indicator_positiveMaxSet_eq_selectedWindowSum
    {M : Type*} (T : M → M) (f : M → ℝ) (N m : ℕ) (x : M) :
    birkhoffSum T ((positiveMaxSet T f N).indicator f) m x =
      selectedWindowSum (fun k => f (T^[k] x)) N m := by
  classical
  unfold birkhoffSum selectedWindowSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [Set.indicator_apply]
  apply if_congr
  · rw [mem_positiveMaxSet_iff]
    have horbit :
        (fun j => f (T^[j] (T^[k] x))) =
          fun j => f (T^[k + j] x) := by
      funext j
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [horbit]
    simpa using
      (hasPositiveWindow_shift (fun j => f (T^[j] x)) N k 0)
  · rfl
  · rfl

lemma integral_birkhoffSum
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {T : M → M} (hT : MeasurePreserving T mu mu)
    {f : M → ℝ} (hf : Integrable f mu) (m : ℕ) :
    ∫ x, birkhoffSum T f m x ∂mu = m * ∫ x, f x ∂mu := by
  change (∫ x, ∑ k ∈ Finset.range m, f (T^[k] x) ∂mu) = _
  rw [integral_finsetSum]
  · simp_rw [integral_comp_measurePreserving (hT.iterate _) hf]
    simp
  · intro k hk
    exact integrable_comp_measurePreserving (hT.iterate k) hf

lemma integrable_birkhoffSum
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {T : M → M} (hT : MeasurePreserving T mu mu)
    {f : M → ℝ} (hf : Integrable f mu) (m : ℕ) :
    Integrable (birkhoffSum T f m) mu := by
  unfold birkhoffSum
  apply integrable_finsetSum
  intro k hk
  exact integrable_comp_measurePreserving (hT.iterate k) hf

theorem integral_positiveMaxSet_nonneg_of_lowerBound
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {B : ℝ} (hB : 0 ≤ B) (hf_lower : ∀ x, -B ≤ f x)
    (N : ℕ) :
    0 ≤ ∫ x in positiveMaxSet T f N, f x ∂mu := by
  let E := positiveMaxSet T f N
  let g := E.indicator f
  have hE : MeasurableSet E :=
    measurableSet_positiveMaxSet hT.measurable hf_measurable N
  have hg : Integrable g mu := hf.indicator hE
  have hpoint (m : ℕ) (x : M) :
      -(N : ℝ) * B ≤ birkhoffSum T g m x := by
    rw [show g = E.indicator f by rfl, show E = positiveMaxSet T f N by rfl,
      birkhoffSum_indicator_positiveMaxSet_eq_selectedWindowSum]
    exact neg_mul_le_selectedWindowSum_of_lowerBound
      (fun k => f (T^[k] x)) N m hB (fun k => hf_lower _)
  have hintegral (m : ℕ) :
      -(N : ℝ) * B ≤ m * ∫ x, g x ∂mu := by
    calc
      -(N : ℝ) * B = ∫ _x : M, (-(N : ℝ) * B) ∂mu := by simp
      _ ≤ ∫ x, birkhoffSum T g m x ∂mu :=
        integral_mono (integrable_const _) (integrable_birkhoffSum hT hg m)
          (hpoint m)
      _ = m * ∫ x, g x ∂mu := integral_birkhoffSum hT hg m
  have hgintegral : 0 ≤ ∫ x, g x ∂mu := by
    by_contra hnonneg
    have hneg : ∫ x, g x ∂mu < 0 := lt_of_not_ge hnonneg
    have hdenom : 0 < -(∫ x, g x ∂mu) := neg_pos.mpr hneg
    obtain ⟨m, hm⟩ := exists_nat_gt
      ((N : ℝ) * B / -(∫ x, g x ∂mu))
    have hmul : (N : ℝ) * B < (m : ℝ) * -(∫ x, g x ∂mu) :=
      (div_lt_iff₀ hdenom).mp hm
    have hle := hintegral m
    nlinarith
  rw [← integral_indicator hE]
  exact hgintegral

theorem integral_positiveMaxSet_nonneg_of_bounded
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {B : ℝ} (hB : 0 ≤ B) (hf_bound : ∀ x, |f x| ≤ B)
    (N : ℕ) :
    0 ≤ ∫ x in positiveMaxSet T f N, f x ∂mu :=
  integral_positiveMaxSet_nonneg_of_lowerBound
    mu T hT f hf_measurable hf hB (fun x => neg_le_of_abs_le (hf_bound x)) N

def positiveMaxSetInfinite
    {M : Type*} (T : M → M) (f : M → ℝ) : Set M :=
  ⋃ N : ℕ, positiveMaxSet T f N

lemma monotone_positiveMaxSet
    {M : Type*} (T : M → M) (f : M → ℝ) :
    Monotone (positiveMaxSet T f) := by
  intro N L hNL x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hn, hxsum⟩ := Set.mem_iUnion.mp hxn
  apply Set.mem_iUnion_of_mem n
  apply Set.mem_iUnion_of_mem
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hNL⟩)
  exact hxsum

lemma measurableSet_positiveMaxSetInfinite
    {M : Type*} [MeasurableSpace M]
    {T : M → M} (hT : Measurable T) {f : M → ℝ} (hf : Measurable f) :
    MeasurableSet (positiveMaxSetInfinite T f) := by
  exact MeasurableSet.iUnion fun N => measurableSet_positiveMaxSet hT hf N

theorem integral_positiveMaxSetInfinite_nonneg_of_lowerBound
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {B : ℝ} (hB : 0 ≤ B) (hf_lower : ∀ x, -B ≤ f x) :
    0 ≤ ∫ x in positiveMaxSetInfinite T f, f x ∂mu := by
  have htend := tendsto_setIntegral_of_monotone
    (fun N => measurableSet_positiveMaxSet hT.measurable hf_measurable N)
    (monotone_positiveMaxSet T f)
    (hf.integrableOn)
  exact ge_of_tendsto' htend fun N =>
    integral_positiveMaxSet_nonneg_of_lowerBound
      mu T hT f hf_measurable hf hB hf_lower N

theorem integral_positiveMaxSetInfinite_nonneg_of_bounded
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {B : ℝ} (hB : 0 ≤ B) (hf_bound : ∀ x, |f x| ≤ B) :
    0 ≤ ∫ x in positiveMaxSetInfinite T f, f x ∂mu :=
  integral_positiveMaxSetInfinite_nonneg_of_lowerBound
    mu T hT f hf_measurable hf hB (fun x => neg_le_of_abs_le (hf_bound x))

def lowerTruncation {M : Type*} (f : M → ℝ) (n : ℕ) (x : M) : ℝ :=
  max (f x) (-(n : ℝ))

lemma measurable_lowerTruncation
    {M : Type*} [MeasurableSpace M] {f : M → ℝ} (hf : Measurable f)
    (n : ℕ) :
    Measurable (lowerTruncation f n) := by
  exact hf.max measurable_const

lemma integrable_lowerTruncation
    {M : Type*} [MeasurableSpace M] {mu : Measure M} [IsFiniteMeasure mu]
    {f : M → ℝ} (hf : Integrable f mu) (n : ℕ) :
    Integrable (lowerTruncation f n) mu := by
  exact hf.sup (integrable_const _)

lemma neg_natCast_le_lowerTruncation
    {M : Type*} (f : M → ℝ) (n : ℕ) (x : M) :
    -(n : ℝ) ≤ lowerTruncation f n x := by
  exact le_max_right _ _

lemma abs_lowerTruncation_le
    {M : Type*} (f : M → ℝ) (n : ℕ) (x : M) :
    |lowerTruncation f n x| ≤ |f x| := by
  unfold lowerTruncation
  by_cases h : -(n : ℝ) ≤ f x
  · rw [max_eq_left h]
  · have hlt : f x < -(n : ℝ) := lt_of_not_ge h
    have hneg : f x < 0 := hlt.trans_le (neg_nonpos.mpr (Nat.cast_nonneg n))
    rw [max_eq_right hlt.le, abs_neg, abs_of_nonneg (Nat.cast_nonneg n),
      abs_of_neg hneg]
    linarith

lemma lowerTruncation_eventually_eq
    {M : Type*} (f : M → ℝ) (x : M) :
    ∀ᶠ n : ℕ in atTop, lowerTruncation f n x = f x := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-f x)
  filter_upwards [eventually_ge_atTop n] with m hm
  unfold lowerTruncation
  rw [max_eq_left]
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma positiveMaxSet_lowerTruncation_eventually_iff
    {M : Type*} (T : M → M) (f : M → ℝ) (N : ℕ) (x : M) :
    ∀ᶠ b : ℕ in atTop,
      (x ∈ positiveMaxSet T (lowerTruncation f b) N ↔
        x ∈ positiveMaxSet T f N) := by
  have hvalues : ∀ᶠ b : ℕ in atTop, ∀ k ∈ Finset.range N,
      lowerTruncation f b (T^[k] x) = f (T^[k] x) :=
    (Finset.range N).eventually_all.2 fun k hk =>
      lowerTruncation_eventually_eq f (T^[k] x)
  filter_upwards [hvalues] with b hb
  rw [mem_positiveMaxSet_iff, mem_positiveMaxSet_iff]
  constructor
  · rintro ⟨n, hnpos, hnN, hsum⟩
    refine ⟨n, hnpos, hnN, ?_⟩
    have heq :
        windowSum (fun k => lowerTruncation f b (T^[k] x)) 0 n =
          windowSum (fun k => f (T^[k] x)) 0 n := by
      unfold windowSum
      apply Finset.sum_congr rfl
      intro k hk
      simpa using hb k (Finset.mem_range.mpr
        ((Finset.mem_range.mp hk).trans_le hnN))
    rw [← heq]
    exact hsum
  · rintro ⟨n, hnpos, hnN, hsum⟩
    refine ⟨n, hnpos, hnN, ?_⟩
    have heq :
        windowSum (fun k => lowerTruncation f b (T^[k] x)) 0 n =
          windowSum (fun k => f (T^[k] x)) 0 n := by
      unfold windowSum
      apply Finset.sum_congr rfl
      intro k hk
      simpa using hb k (Finset.mem_range.mpr
        ((Finset.mem_range.mp hk).trans_le hnN))
    rw [heq]
    exact hsum

theorem integral_positiveMaxSet_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    (N : ℕ) :
    0 ≤ ∫ x in positiveMaxSet T f N, f x ∂mu := by
  classical
  let F : ℕ → M → ℝ := fun b =>
    (positiveMaxSet T (lowerTruncation f b) N).indicator
      (lowerTruncation f b)
  let g : M → ℝ := (positiveMaxSet T f N).indicator f
  have hF_measurable (b : ℕ) : AEStronglyMeasurable (F b) mu := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_lowerTruncation hf_measurable b).indicator
      (measurableSet_positiveMaxSet hT.measurable
        (measurable_lowerTruncation hf_measurable b) N)
  have hbound (b : ℕ) : ∀ᵐ x ∂mu, ‖F b x‖ ≤ |f x| := by
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ positiveMaxSet T (lowerTruncation f b) N
      · simp [F, Set.indicator_of_mem hx, abs_lowerTruncation_le]
      · simp [F, Set.indicator_of_notMem hx]
  have hlim : ∀ᵐ x ∂mu, Tendsto (fun b => F b x) atTop (nhds (g x)) := by
    exact Filter.Eventually.of_forall fun x => by
      have heq : ∀ᶠ b : ℕ in atTop, F b x = g x := by
        filter_upwards
            [lowerTruncation_eventually_eq f x,
             positiveMaxSet_lowerTruncation_eventually_iff T f N x]
          with b hbvalue hbset
        by_cases hx : x ∈ positiveMaxSet T (lowerTruncation f b) N
        · rw [show F b x = lowerTruncation f b x by
              exact Set.indicator_of_mem hx _]
          rw [show g x = f x by
              exact Set.indicator_of_mem (hbset.mp hx) _]
          exact hbvalue
        · rw [show F b x = 0 by exact Set.indicator_of_notMem hx _]
          rw [show g x = 0 by
              exact Set.indicator_of_notMem (fun h => hx (hbset.mpr h)) _]
      exact (tendsto_congr' heq).2 tendsto_const_nhds
  have htend := tendsto_integral_of_dominated_convergence
    (fun x => |f x|) hF_measurable hf.abs hbound hlim
  have hnonneg (b : ℕ) : 0 ≤ ∫ x, F b x ∂mu := by
    have h := integral_positiveMaxSet_nonneg_of_lowerBound
      mu T hT (lowerTruncation f b)
        (measurable_lowerTruncation hf_measurable b)
        (integrable_lowerTruncation hf b) (Nat.cast_nonneg b)
        (neg_natCast_le_lowerTruncation f b) N
    rw [← integral_indicator
      (measurableSet_positiveMaxSet hT.measurable
        (measurable_lowerTruncation hf_measurable b) N)] at h
    exact h
  have hg_nonneg : 0 ≤ ∫ x, g x ∂mu :=
    ge_of_tendsto' htend hnonneg
  rw [← integral_indicator
    (measurableSet_positiveMaxSet hT.measurable hf_measurable N)]
  exact hg_nonneg

theorem integral_positiveMaxSetInfinite_nonneg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu) :
    0 ≤ ∫ x in positiveMaxSetInfinite T f, f x ∂mu := by
  have htend := tendsto_setIntegral_of_monotone
    (fun N => measurableSet_positiveMaxSet hT.measurable hf_measurable N)
    (monotone_positiveMaxSet T f)
    hf.integrableOn
  exact ge_of_tendsto' htend fun N =>
    integral_positiveMaxSet_nonneg mu T hT f hf_measurable hf N

end Submission.Helpers
