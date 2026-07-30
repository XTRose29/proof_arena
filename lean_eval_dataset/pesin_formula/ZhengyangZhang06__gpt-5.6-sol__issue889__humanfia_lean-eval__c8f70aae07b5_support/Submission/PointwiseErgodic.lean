import Submission.MaximalErgodic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

namespace Submission.Helpers

open Filter MeasureTheory

noncomputable def koopmanL2
    {M : Type*} [MeasurableSpace M] (mu : Measure M)
    (T : M → M) (hT : MeasurePreserving T mu mu) :
    Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap

lemma norm_koopmanL2_le_one
    {M : Type*} [MeasurableSpace M] (mu : Measure M)
    (T : M → M) (hT : MeasurePreserving T mu mu) :
    ‖koopmanL2 mu T hT‖ ≤ 1 := by
  change ‖(Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := (2 : ENNReal))
    ℝ T hT).toContinuousLinearMap‖ ≤ 1
  exact LinearIsometry.norm_toContinuousLinearMap_le _

lemma koopmanL2_iterate_coeFn_ae
    {M : Type*} [MeasurableSpace M] (mu : Measure M)
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (F : Lp ℝ 2 mu) (n : ℕ) :
    (koopmanL2 mu T hT)^[n] F =ᵐ[mu] fun x => F (T^[n] x) := by
  rw [show (koopmanL2 mu T hT)^[n] F =
      Lp.compMeasurePreserving (T^[n]) (hT.iterate n) F by
    change (Lp.compMeasurePreserving T hT)^[n] F = _
    rw [Lp.compMeasurePreserving_iterate]]
  exact Lp.coeFn_compMeasurePreserving F (hT.iterate n)

lemma abs_birkhoffAverage_le_of_not_mem_positiveMaxSetInfinite_abs_sub
    {M : Type*} (T : M → M) (f : M → ℝ) {a : ℝ}
    {x : M}
    (hx : x ∉ positiveMaxSetInfinite T (fun y => |f y| - a))
    {n : ℕ} (hn : 0 < n) :
    |birkhoffAverage ℝ T f n x| ≤ a := by
  have hsum_nonpos :
      birkhoffSum T (fun y => |f y| - a) n x ≤ 0 := by
    by_contra hpos
    apply hx
    apply Set.mem_iUnion_of_mem n
    rw [mem_positiveMaxSet_iff]
    exact ⟨n, hn, le_rfl, by
      simpa [windowSum, birkhoffSum] using lt_of_not_ge hpos⟩
  have habs_sum :
      |birkhoffSum T f n x| ≤ birkhoffSum T (fun y => |f y|) n x := by
    unfold birkhoffSum
    simpa using
      (Finset.abs_sum_le_sum_abs (fun k => f (T^[k] x)) (Finset.range n))
  have hsum_abs :
      birkhoffSum T (fun y => |f y|) n x ≤ n * a := by
    unfold birkhoffSum at hsum_nonpos ⊢
    simpa [Finset.sum_sub_distrib] using hsum_nonpos
  calc
    |birkhoffAverage ℝ T f n x| =
        (n : ℝ)⁻¹ * |birkhoffSum T f n x| := by
      simp [birkhoffAverage, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * a) :=
      mul_le_mul_of_nonneg_left (habs_sum.trans hsum_abs) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = a := by field_simp

lemma measure_positiveMaxSetInfinite_abs_sub_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {a : ℝ} (ha : 0 < a) :
    mu (positiveMaxSetInfinite T (fun x => |f x| - a)) ≤
      ENNReal.ofReal ((∫ x, |f x| ∂mu) / a) := by
  let g : M → ℝ := fun x => |f x| - a
  let E : Set M := positiveMaxSetInfinite T g
  have hg_measurable : Measurable g := hf_measurable.abs.sub measurable_const
  have hg : Integrable g mu := hf.abs.sub (integrable_const a)
  have hE : MeasurableSet E :=
    measurableSet_positiveMaxSetInfinite hT.measurable hg_measurable
  have hhopf : 0 ≤ ∫ x in E, g x ∂mu :=
    integral_positiveMaxSetInfinite_nonneg
      mu T hT g hg_measurable hg
  have hmeasure_real :
      a * mu.real E ≤ ∫ x, |f x| ∂mu := by
    have hsplit :
        (∫ x in E, g x ∂mu) =
          (∫ x in E, |f x| ∂mu) - a * mu.real E := by
      rw [show g = fun x => |f x| - a by rfl,
        integral_sub hf.abs.integrableOn (integrable_const a),
        setIntegral_const, smul_eq_mul]
      ring
    rw [hsplit] at hhopf
    exact le_trans (by linarith) (setIntegral_le_integral hf.abs
      (Filter.Eventually.of_forall fun x => abs_nonneg (f x)))
  have hreal_le : mu.real E ≤ (∫ x, |f x| ∂mu) / a := by
    exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using hmeasure_real)
  rw [show positiveMaxSetInfinite T (fun x => |f x| - a) = E by rfl]
  rw [← ENNReal.ofReal_toReal (measure_ne_top mu E)]
  exact ENNReal.ofReal_le_ofReal hreal_le

def robustUpperSet
    {M : Type*} (u : M → ℕ → ℝ) (a : ℝ) : Set M :=
  {x | ∃ k : ℕ, ∃ᶠ n : ℕ in atTop,
    a + 1 / ((k : ℝ) + 1) < u x n}

lemma measurableSet_robustUpperSet
    {M : Type*} [MeasurableSpace M]
    (u : M → ℕ → ℝ) (hu : ∀ n, Measurable fun x => u x n) (a : ℝ) :
    MeasurableSet (robustUpperSet u a) := by
  rw [show robustUpperSet u a =
      ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_hn : N ≤ n),
        {x | a + 1 / ((k : ℝ) + 1) < u x n} by
    ext x
    simp only [robustUpperSet, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_iInter, frequently_atTop]
    aesop]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _hn =>
      measurableSet_lt measurable_const (hu n)

lemma robustUpperSet_congr_of_tendsto_sub_zero
    {M : Type*} (u v : M → ℕ → ℝ) (a : ℝ)
    (h : ∀ x, Tendsto (fun n => u x n - v x n) atTop (nhds 0)) :
    robustUpperSet u a = robustUpperSet v a := by
  ext x
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt
      (half_pos (by positivity : 0 < 1 / ((k : ℝ) + 1)))
    refine ⟨l, ?_⟩
    have hdiff : ∀ᶠ n : ℕ in atTop,
        u x n - v x n < 1 / ((k : ℝ) + 1) / 2 :=
      (tendsto_order.1 (h x)).2 _ (half_pos (by positivity))
    exact (hk.and_eventually hdiff).mono fun n hn => by
      have hl' : 1 / ((l : ℝ) + 1) < 1 / ((k : ℝ) + 1) / 2 := by
        simpa using hl
      linarith [hn.1, hn.2]
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt
      (half_pos (by positivity : 0 < 1 / ((k : ℝ) + 1)))
    refine ⟨l, ?_⟩
    have hdiff : ∀ᶠ n : ℕ in atTop,
        -(1 / ((k : ℝ) + 1) / 2) < u x n - v x n :=
      (tendsto_order.1 (h x)).1 _ (neg_lt_zero.mpr (half_pos (by positivity)))
    exact (hk.and_eventually hdiff).mono fun n hn => by
      have hl' : 1 / ((l : ℝ) + 1) < 1 / ((k : ℝ) + 1) / 2 := by
        simpa using hl
      linarith [hn.1, hn.2]

lemma tendsto_birkhoffAverage_map_sub_of_bounded
    {M : Type*} (T : M → M) (f : M → ℝ) {B : ℝ}
    (hf_bound : ∀ x, |f x| ≤ B) (x : M) :
    Tendsto
      (fun n => birkhoffAverage ℝ T f n (T x) -
        birkhoffAverage ℝ T f n x)
      atTop (nhds 0) := by
  apply tendsto_birkhoffAverage_apply_sub_birkhoffAverage ℝ
  apply isBounded_iff_forall_norm_le.2
  exact ⟨B, Set.forall_mem_range.2 fun n => by
    simpa [Real.norm_eq_abs] using hf_bound (T^[n] x)⟩

lemma preimage_robustUpperSet_birkhoffAverage_of_bounded
    {M : Type*} (T : M → M) (f : M → ℝ) {B a : ℝ}
    (hf_bound : ∀ x, |f x| ≤ B) :
    T ⁻¹' robustUpperSet (fun x n => birkhoffAverage ℝ T f n x) a =
      robustUpperSet (fun x n => birkhoffAverage ℝ T f n x) a := by
  change robustUpperSet
      (fun x n => birkhoffAverage ℝ T f n (T x)) a = _
  exact robustUpperSet_congr_of_tendsto_sub_zero _ _ a
    (tendsto_birkhoffAverage_map_sub_of_bounded T f hf_bound)

lemma robustUpperSet_birkhoffAverage_subset_positiveMaxSetInfinite
    {M : Type*} (T : M → M) (f : M → ℝ) (a : ℝ) :
    robustUpperSet (fun x n => birkhoffAverage ℝ T f n x) a ⊆
      positiveMaxSetInfinite T (fun x => f x - a) := by
  intro x hx
  obtain ⟨k, hk⟩ := hx
  obtain ⟨n, hn, hnavg⟩ := frequently_atTop.mp hk 1
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  apply Set.mem_iUnion_of_mem n
  rw [mem_positiveMaxSet_iff]
  refine ⟨n, hnpos, le_rfl, ?_⟩
  have havg : a < birkhoffAverage ℝ T f n x := by
    have hmargin : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsum : (n : ℝ) * a < birkhoffSum T f n x := by
    rw [birkhoffAverage] at havg
    have havg' : a < birkhoffSum T f n x / (n : ℝ) := by
      simpa [smul_eq_mul, div_eq_inv_mul] using havg
    simpa [mul_comm] using (lt_div_iff₀ hnpos_real).mp havg'
  calc
    0 < birkhoffSum T f n x - (n : ℝ) * a := sub_pos.mpr hsum
    _ = windowSum (fun j => f (T^[j] x) - a) 0 n := by
      simp [windowSum, birkhoffSum, Finset.sum_sub_distrib]

lemma ae_eventually_birkhoffAverage_lt_integral_add_of_bounded
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {B : ℝ} (hf_bound : ∀ x, |f x| ≤ B) :
    ∀ᵐ x ∂mu, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        birkhoffAverage ℝ T f n x < (∫ y, f y ∂mu) + epsilon := by
  let u : M → ℕ → ℝ := fun x n => birkhoffAverage ℝ T f n x
  let I : ℝ := ∫ y, f y ∂mu
  have hu_measurable (n : ℕ) : Measurable fun x => u x n := by
    simpa [u, birkhoffAverage, smul_eq_mul] using
      measurable_const.mul (measurable_birkhoffSum hT.measurable hf_measurable n)
  have hnull (m : ℕ) :
      mu (robustUpperSet u (I + 1 / ((m : ℝ) + 1))) = 0 := by
    let a : ℝ := I + 1 / ((m : ℝ) + 1)
    let S : Set M := robustUpperSet u a
    have hS_measurable : MeasurableSet S :=
      measurableSet_robustUpperSet u hu_measurable a
    have hS_invariant : T ⁻¹' S = S := by
      exact preimage_robustUpperSet_birkhoffAverage_of_bounded
        T f hf_bound
    rcases hErg.prob_eq_zero_or_one hS_measurable hS_invariant with hS | hS
    · exact hS
    · exfalso
      let g : M → ℝ := fun x => f x - a
      let E : Set M := positiveMaxSetInfinite T g
      have hg_measurable : Measurable g := hf_measurable.sub measurable_const
      have hg : Integrable g mu := hf.sub (integrable_const a)
      have hE_measurable : MeasurableSet E :=
        measurableSet_positiveMaxSetInfinite hT.measurable hg_measurable
      have hSE : S ⊆ E := by
        exact robustUpperSet_birkhoffAverage_subset_positiveMaxSetInfinite T f a
      have hS_compl : mu Sᶜ = 0 := by
        rw [measure_compl hS_measurable (by finiteness), measure_univ, hS]
        simp
      have hE_compl : mu Eᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.mpr hSE) hS_compl
      have hhopf : 0 ≤ ∫ x in E, g x ∂mu :=
        integral_positiveMaxSetInfinite_nonneg
          mu T hT g hg_measurable hg
      have hfull : ∀ᵐ x ∂mu, x ∈ E := mem_ae_iff.mpr hE_compl
      have hsetIntegral : (∫ x in E, g x ∂mu) = ∫ x, g x ∂mu := by
        rw [← integral_indicator hE_measurable]
        apply integral_congr_ae
        filter_upwards [hfull] with x hx
        exact Set.indicator_of_mem hx _
      rw [hsetIntegral] at hhopf
      have hglobal : ∫ x, g x ∂mu = I - a := by
        rw [show g = fun x => f x - a by rfl,
          integral_sub hf (integrable_const a), integral_const,
          probReal_univ, one_smul]
      rw [hglobal] at hhopf
      have hmargin : 0 < 1 / ((m : ℝ) + 1) := by positivity
      dsimp [a] at hhopf
      linarith
  have hae : ∀ᵐ x ∂mu, ∀ m : ℕ,
      x ∉ robustUpperSet u (I + 1 / ((m : ℝ) + 1)) := by
    rw [ae_all_iff]
    intro m
    exact measure_eq_zero_iff_ae_notMem.mp (hnull m)
  filter_upwards [hae] with x hx
  intro epsilon hepsilon
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hepsilon)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hepsilon)
  have hnotfreq : ¬∃ᶠ n : ℕ in atTop,
      I + 1 / ((m : ℝ) + 1) + 1 / ((k : ℝ) + 1) < u x n := by
    intro hfreq
    exact hx m ⟨k, hfreq⟩
  filter_upwards [not_frequently.mp hnotfreq] with n hn
  have hle :
      u x n ≤ I + 1 / ((m : ℝ) + 1) + 1 / ((k : ℝ) + 1) :=
    le_of_not_gt hn
  dsimp [u, I] at hle
  linarith

noncomputable def boundedCutoff
    {M : Type*} (f : M → ℝ) (N : ℕ) : M → ℝ :=
  {x | |f x| ≤ N}.indicator f

lemma measurable_boundedCutoff
    {M : Type*} [MeasurableSpace M]
    {f : M → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (boundedCutoff f N) := by
  exact hf.indicator (measurableSet_le hf.abs measurable_const)

lemma integrable_boundedCutoff
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {f : M → ℝ} (hf_measurable : Measurable f) (hf : Integrable f mu) (N : ℕ) :
    Integrable (boundedCutoff f N) mu := by
  exact hf.indicator (measurableSet_le hf_measurable.abs measurable_const)

lemma abs_boundedCutoff_le
    {M : Type*} (f : M → ℝ) (N : ℕ) (x : M) :
    |boundedCutoff f N x| ≤ N := by
  by_cases hx : |f x| ≤ N
  · have hx' : x ∈ {x | |f x| ≤ (N : ℝ)} := hx
    rw [boundedCutoff, Set.indicator_of_mem hx']
    exact hx
  · have hx' : x ∉ {x | |f x| ≤ (N : ℝ)} := hx
    rw [boundedCutoff, Set.indicator_of_notMem hx']
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    simpa only [abs_zero] using hN

lemma boundedCutoff_eventually_eq
    {M : Type*} (f : M → ℝ) (x : M) :
    ∀ᶠ N : ℕ in atTop, boundedCutoff f N x = f x := by
  obtain ⟨N, hN⟩ := exists_nat_ge |f x|
  filter_upwards [eventually_ge_atTop N] with L hNL
  apply Set.indicator_of_mem
  exact hN.trans (by exact_mod_cast hNL)

lemma abs_sub_boundedCutoff_le
    {M : Type*} (f : M → ℝ) (N : ℕ) (x : M) :
    |f x - boundedCutoff f N x| ≤ |f x| := by
  by_cases hx : |f x| ≤ N
  · have hx' : x ∈ {x | |f x| ≤ (N : ℝ)} := hx
    rw [boundedCutoff, Set.indicator_of_mem hx', sub_self, abs_zero]
    exact abs_nonneg (f x)
  · have hx' : x ∉ {x | |f x| ≤ (N : ℝ)} := hx
    rw [boundedCutoff, Set.indicator_of_notMem hx', sub_zero]

lemma tendsto_integral_abs_sub_boundedCutoff
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {f : M → ℝ} (hf_measurable : Measurable f) (hf : Integrable f mu) :
    Tendsto
      (fun N => ∫ x, |f x - boundedCutoff f N x| ∂mu)
      atTop (nhds 0) := by
  have hlim : ∀ᵐ x ∂mu,
      Tendsto (fun N => |f x - boundedCutoff f N x|) atTop (nhds 0) := by
    exact Filter.Eventually.of_forall fun x => by
      have heq : ∀ᶠ N : ℕ in atTop,
          |f x - boundedCutoff f N x| = 0 :=
        (boundedCutoff_eventually_eq f x).mono fun N hN => by simp [hN]
      exact (tendsto_congr' heq).2 tendsto_const_nhds
  have htend := tendsto_integral_of_dominated_convergence
    (fun x => |f x|)
    (fun N => (hf_measurable.sub (measurable_boundedCutoff hf_measurable N)).abs.aestronglyMeasurable)
    hf.abs
    (fun N => Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_abs] using abs_sub_boundedCutoff_le f N x)
    hlim
  simpa using htend

lemma ae_eventually_birkhoffAverage_lt_integral_add
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      birkhoffAverage ℝ T f n x < (∫ y, f y ∂mu) + epsilon := by
  let a : ℝ := epsilon / 4
  let g : ℕ → M → ℝ := fun N => boundedCutoff f N
  let L : ℕ → ℝ := fun N => ∫ x, |f x - g N x| ∂mu
  let I : ℝ := ∫ x, f x ∂mu
  let bad : Set M := {x | ¬∀ᶠ n : ℕ in atTop, birkhoffAverage ℝ T f n x < I + epsilon}
  have ha : 0 < a := by dsimp [a]; linarith
  have hg_measurable (N : ℕ) : Measurable (g N) :=
    measurable_boundedCutoff hf_measurable N
  have hg (N : ℕ) : Integrable (g N) mu :=
    integrable_boundedCutoff hf_measurable hf N
  have hL : Tendsto L atTop (nhds 0) := by
    simpa [L, g] using tendsto_integral_abs_sub_boundedCutoff hf_measurable hf
  have hL_small : ∀ᶠ N : ℕ in atTop, L N < a :=
    (tendsto_order.1 hL).2 a ha
  have hmeasure : ∀ᶠ N : ℕ in atTop,
      mu bad ≤ ENNReal.ofReal (L N / a) := by
    filter_upwards [hL_small] with N hLN
    let d : M → ℝ := fun x => f x - g N x
    let E : Set M := positiveMaxSetInfinite T (fun x => |d x| - a)
    have hd_measurable : Measurable d := hf_measurable.sub (hg_measurable N)
    have hd : Integrable d mu := hf.sub (hg N)
    have hbounded := ae_eventually_birkhoffAverage_lt_integral_add_of_bounded
      mu T hT hErg (g N) (hg_measurable N) (hg N)
        (fun x => abs_boundedCutoff_le f N x)
    have hI : |I - ∫ x, g N x ∂mu| ≤ L N := by
      calc
        |I - ∫ x, g N x ∂mu| = |∫ x, f x - g N x ∂mu| := by
          rw [integral_sub hf (hg N)]
        _ ≤ ∫ x, |f x - g N x| ∂mu := abs_integral_le_integral_abs
        _ = L N := rfl
    have hIg : (∫ x, g N x ∂mu) < I + a := by
      have habs : |I - ∫ x, g N x ∂mu| < a := hI.trans_lt hLN
      linarith [abs_lt.mp habs]
    have hbadE : bad ≤ᵐ[mu] E := by
      filter_upwards [hbounded] with x hxbounded
      intro hxbad
      by_contra hxE
      apply hxbad
      filter_upwards [hxbounded a ha, eventually_gt_atTop 0] with n hgn hn
      have hdiff : |birkhoffAverage ℝ T d n x| ≤ a :=
        abs_birkhoffAverage_le_of_not_mem_positiveMaxSetInfinite_abs_sub
          T d hxE hn
      have havg : birkhoffAverage ℝ T f n x =
          birkhoffAverage ℝ T (g N) n x + birkhoffAverage ℝ T d n x := by
        have hsub := congrFun (congrFun
          (birkhoffAverage_sub (R := ℝ) (f := T) (g := f) (g' := g N)) n) x
        change birkhoffAverage ℝ T d n x =
          birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T (g N) n x at hsub
        linarith
      have hdiff' : birkhoffAverage ℝ T d n x ≤ a :=
        (le_abs_self _).trans hdiff
      have hthree : 3 * a < epsilon := by dsimp [a]; linarith
      rw [havg]
      linarith
    calc
      mu bad ≤ mu E := measure_mono_ae hbadE
      _ ≤ ENNReal.ofReal ((∫ x, |d x| ∂mu) / a) :=
        measure_positiveMaxSetInfinite_abs_sub_le
          mu T hT d hd_measurable hd ha
      _ = ENNReal.ofReal (L N / a) := by rfl
  have hratio : Tendsto (fun N => L N / a) atTop (nhds 0) := by
    simpa using hL.div_const a
  have hofReal : Tendsto (fun N => ENNReal.ofReal (L N / a)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hratio
  have hbad_le : mu bad ≤ 0 := ge_of_tendsto hofReal hmeasure
  have hbad_zero : mu bad = 0 := nonpos_iff_eq_zero.mp hbad_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad_zero] with x hx
  simpa [bad, I] using hx

lemma ae_tendsto_birkhoffAverage_integral
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu) :
    ∀ᵐ x ∂mu,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x)
        atTop (nhds (∫ y, f y ∂mu)) := by
  have hupper : ∀ᵐ x ∂mu, ∀ m : ℕ,
      ∀ᶠ n : ℕ in atTop,
        birkhoffAverage ℝ T f n x <
          (∫ y, f y ∂mu) + 1 / ((m : ℝ) + 1) := by
    rw [ae_all_iff]
    intro m
    exact ae_eventually_birkhoffAverage_lt_integral_add
      mu T hT hErg f hf_measurable hf (by positivity)
  have hupper_neg : ∀ᵐ x ∂mu, ∀ m : ℕ,
      ∀ᶠ n : ℕ in atTop,
        birkhoffAverage ℝ T (-f) n x <
          (∫ y, -f y ∂mu) + 1 / ((m : ℝ) + 1) := by
    rw [ae_all_iff]
    intro m
    exact ae_eventually_birkhoffAverage_lt_integral_add
      mu T hT hErg (-f) hf_measurable.neg hf.neg (by positivity)
  filter_upwards [hupper, hupper_neg] with x hxupper hxupper_neg
  apply tendsto_order.2
  constructor
  · intro b hb
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hb)
    filter_upwards [hxupper_neg m] with n hn
    have havg_neg : birkhoffAverage ℝ T (-f) n x =
        -birkhoffAverage ℝ T f n x := by
      exact congrFun (congrFun
        (birkhoffAverage_neg (R := ℝ) (f := T) (g := f)) n) x
    rw [havg_neg, integral_neg] at hn
    linarith
  · intro b hb
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hb)
    filter_upwards [hxupper m] with n hn
    linarith

end Submission.Helpers
