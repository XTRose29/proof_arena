import Submission.EntropyCardinality

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

noncomputable def lightAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M)) (c : ℝ) : Finset (Set M) :=
  P.filter fun A => mu.real A < Real.exp (-c)

noncomputable def heavyAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (P : Finset (Set M)) (c : ℝ) : Finset (Set M) :=
  P.filter fun A => Real.exp (-c) ≤ mu.real A

lemma mul_le_negMulLog_of_lt_exp_neg
    {p c : ℝ} (hp : 0 ≤ p) (hp_small : p < Real.exp (-c)) :
    c * p ≤ Real.negMulLog p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero]
  have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp_zero)
  have hlog : Real.log p < -c :=
    (Real.log_lt_iff_lt_exp hp_pos).2 hp_small
  calc
    c * p ≤ (-Real.log p) * p :=
      mul_le_mul_of_nonneg_right (le_of_lt (by linarith)) hp
    _ = Real.negMulLog p := by
      rw [Real.negMulLog_def]
      ring

lemma sum_measureReal_subset_le_one
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P Q : Finset (Set M)} (hP : IsMeasurablePartition mu P)
    (hQP : Q ⊆ P) :
    ∑ A ∈ Q, mu.real A ≤ 1 := by
  calc
    (∑ A ∈ Q, mu.real A) ≤ ∑ A ∈ P, mu.real A :=
      Finset.sum_le_sum_of_subset_of_nonneg hQP
        (fun _A _hAP _hAQ => measureReal_nonneg)
    _ = 1 := by
      have hsum := sum_measureReal_positive_atoms_eq_one mu hP
      rw [Finset.sum_filter] at hsum
      calc
        (∑ A ∈ P, mu.real A) =
            ∑ A ∈ P, if mu A ≠ 0 then mu.real A else 0 := by
          apply Finset.sum_congr rfl
          intro A hA
          by_cases hmuA : mu A ≠ 0
          · simp [hmuA]
          · rw [if_neg hmuA]
            exact (measureReal_eq_zero_iff).2 (not_ne_iff.mp hmuA)
        _ = 1 := hsum

lemma sum_measureReal_lightAtoms_le_partitionEntropy_div
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (P : Finset (Set M)) {c : ℝ} (hc : 0 < c) :
    ∑ A ∈ lightAtoms mu P c, mu.real A ≤ partitionEntropy mu P / c := by
  classical
  have hscaled :
      c * (∑ A ∈ lightAtoms mu P c, mu.real A) ≤ partitionEntropy mu P := by
    calc
      c * (∑ A ∈ lightAtoms mu P c, mu.real A) =
          ∑ A ∈ lightAtoms mu P c, c * mu.real A := by
        rw [Finset.mul_sum]
      _ ≤ ∑ A ∈ lightAtoms mu P c, Real.negMulLog (mu.real A) := by
        apply Finset.sum_le_sum
        intro A hA
        exact mul_le_negMulLog_of_lt_exp_neg measureReal_nonneg
          (Finset.mem_filter.mp hA).2
      _ ≤ ∑ A ∈ P, Real.negMulLog (mu.real A) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro A hAP hA_light
          exact Real.negMulLog_nonneg measureReal_nonneg
            (measureReal_mono (Set.subset_univ A) |>.trans_eq (by simp))
      _ = partitionEntropy mu P := by
        rw [partitionEntropy]
        simp [measureReal_def]
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hscaled)

lemma card_heavyAtoms_le_exp
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P)
    (c : ℝ) :
    (heavyAtoms mu P c).card ≤ Real.exp c := by
  classical
  have hmass : ∑ A ∈ heavyAtoms mu P c, mu.real A ≤ 1 :=
    sum_measureReal_subset_le_one mu hP (Finset.filter_subset _ _)
  have hcount :
      Real.exp (-c) * ((heavyAtoms mu P c).card : ℝ) ≤ 1 := by
    calc
      Real.exp (-c) * ((heavyAtoms mu P c).card : ℝ) =
          ∑ _A ∈ heavyAtoms mu P c, Real.exp (-c) := by simp [mul_comm]
      _ ≤ ∑ A ∈ heavyAtoms mu P c, mu.real A := by
        apply Finset.sum_le_sum
        intro A hA
        exact (Finset.mem_filter.mp hA).2
      _ ≤ 1 := hmass
  calc
    ((heavyAtoms mu P c).card : ℝ) =
        Real.exp c *
          (Real.exp (-c) * ((heavyAtoms mu P c).card : ℝ)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp c * 1 :=
      mul_le_mul_of_nonneg_left hcount (Real.exp_pos c).le
    _ = Real.exp c := mul_one _

lemma measureReal_compl_iUnion_heavyAtoms_le_partitionEntropy_div
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P)
    {c : ℝ} (hc : 0 < c) :
    mu.real (⋃ A ∈ heavyAtoms mu P c, A)ᶜ ≤ partitionEntropy mu P / c := by
  classical
  let H := heavyAtoms mu P c
  let L := lightAtoms mu P c
  have hsubset :
      (⋃ A ∈ H, A)ᶜ ⊆ (⋃ A ∈ L, A) ∪ (⋃ A ∈ P, A)ᶜ := by
    intro x hx
    by_cases hxP : x ∈ ⋃ A ∈ P, A
    · rcases Set.mem_iUnion.mp hxP with ⟨A, hxP⟩
      rcases Set.mem_iUnion.mp hxP with ⟨hAP, hxA⟩
      by_cases hA_light : mu.real A < Real.exp (-c)
      · apply Or.inl
        apply Set.mem_iUnion_of_mem A
        exact Set.mem_iUnion_of_mem
          (Finset.mem_filter.mpr ⟨hAP, hA_light⟩) hxA
      · have hAH : A ∈ H :=
          Finset.mem_filter.mpr ⟨hAP, le_of_not_gt hA_light⟩
        exact (hx (Set.mem_iUnion_of_mem A (Set.mem_iUnion_of_mem hAH hxA))).elim
    · exact Or.inr hxP
  have hpairwise : Set.Pairwise (L : Set (Set M)) fun A B => AEDisjoint mu A B := by
    intro A hAL B hBL hAB
    exact hP.disjoint A (Finset.mem_filter.mp hAL).1
      B (Finset.mem_filter.mp hBL).1 hAB
  have hL_measure :
      mu.real (⋃ A ∈ L, A) = ∑ A ∈ L, mu.real A := by
    exact measureReal_biUnion_finset₀ hpairwise
      (fun A hAL =>
        (hP.measurable A (Finset.mem_filter.mp hAL).1).nullMeasurableSet)
  have hP_compl_zero : mu.real (⋃ A ∈ P, A)ᶜ = 0 :=
    (measureReal_eq_zero_iff).2 hP.cover
  calc
    mu.real (⋃ A ∈ H, A)ᶜ ≤
        mu.real ((⋃ A ∈ L, A) ∪ (⋃ A ∈ P, A)ᶜ) := measureReal_mono hsubset
    _ ≤ mu.real (⋃ A ∈ L, A) + mu.real (⋃ A ∈ P, A)ᶜ :=
      measureReal_union_le _ _
    _ = ∑ A ∈ L, mu.real A := by rw [hP_compl_zero, add_zero, hL_measure]
    _ ≤ partitionEntropy mu P / c := by
      simpa [L] using sum_measureReal_lightAtoms_le_partitionEntropy_div mu P hc

lemma exists_partition_subfamily_cover_of_entropy
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ Q : Finset (Set M), Q ⊆ P ∧
      (Q.card : ℝ) ≤ Real.exp (partitionEntropy mu P / delta + 1) ∧
      mu.real (⋃ A ∈ Q, A)ᶜ ≤ delta := by
  let c := partitionEntropy mu P / delta + 1
  have hentropy : 0 ≤ partitionEntropy mu P := partitionEntropy_nonneg mu P
  have hc : 0 < c := by
    exact add_pos_of_nonneg_of_pos (div_nonneg hentropy hdelta.le) zero_lt_one
  have hratio : partitionEntropy mu P / c ≤ delta := by
    apply (div_le_iff₀ hc).2
    calc
      partitionEntropy mu P ≤ partitionEntropy mu P + delta :=
        le_add_of_nonneg_right hdelta.le
      _ = delta * c := by
        dsimp [c]
        field_simp
  refine ⟨heavyAtoms mu P c, Finset.filter_subset _ _, ?_, ?_⟩
  · exact card_heavyAtoms_le_exp mu hP c
  · exact (measureReal_compl_iUnion_heavyAtoms_le_partitionEntropy_div
      mu hP hc).trans hratio

lemma exists_partition_subfamily_liminf_full_measure
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (P : ℕ → Finset (Set M))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta_sum : (∑' n, ENNReal.ofReal (delta n)) ≠ ⊤) :
    ∃ Q : ℕ → Finset (Set M),
      (∀ n, Q n ⊆ P n) ∧
      (∀ n, ((Q n).card : ℝ) ≤
        Real.exp (partitionEntropy mu (P n) / delta n + 1)) ∧
      (∀ n, mu.real (⋃ A ∈ Q n, A)ᶜ ≤ delta n) ∧
      MeasurableSet
        (Filter.liminf (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ∧
      mu (Filter.liminf (fun n => ⋃ A ∈ Q n, A) Filter.atTop)ᶜ = 0 := by
  classical
  choose Q hQ using fun n =>
    exists_partition_subfamily_cover_of_entropy mu (hP n) (hdelta n)
  have hQ_subset : ∀ n, Q n ⊆ P n := fun n => (hQ n).1
  have hQ_card : ∀ n, ((Q n).card : ℝ) ≤
      Real.exp (partitionEntropy mu (P n) / delta n + 1) :=
    fun n => (hQ n).2.1
  have hQ_cover : ∀ n, mu.real (⋃ A ∈ Q n, A)ᶜ ≤ delta n :=
    fun n => (hQ n).2.2
  have hU_measurable : ∀ n, MeasurableSet (⋃ A ∈ Q n, A) := by
    intro n
    exact Finset.measurableSet_biUnion (Q n) fun A hAQ =>
      (hP n).measurable A (hQ_subset n hAQ)
  have hliminf_measurable :
      MeasurableSet (Filter.liminf (fun n => ⋃ A ∈ Q n, A) Filter.atTop) := by
    exact MeasurableSet.measurableSet_liminf hU_measurable
  have hmeasure : ∀ n,
      mu (⋃ A ∈ Q n, A)ᶜ ≤ ENNReal.ofReal (delta n) := by
    intro n
    calc
      mu (⋃ A ∈ Q n, A)ᶜ =
          ENNReal.ofReal (mu.real (⋃ A ∈ Q n, A)ᶜ) :=
        (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (delta n) := ENNReal.ofReal_le_ofReal (hQ_cover n)
  have hsum_measure : (∑' n, mu (⋃ A ∈ Q n, A)ᶜ) ≠ ⊤ :=
    ne_top_of_le_ne_top hdelta_sum (ENNReal.tsum_le_tsum hmeasure)
  have hfull :
      mu (Filter.liminf (fun n => ⋃ A ∈ Q n, A) Filter.atTop)ᶜ = 0 := by
    rw [Filter.liminf_compl]
    simpa [Function.comp_def] using measure_limsup_atTop_eq_zero hsum_measure
  exact ⟨Q, hQ_subset, hQ_card, hQ_cover, hliminf_measurable, hfull⟩

lemma measure_limsup_ne_zero_of_compl_measureReal_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    {delta : ℝ} (hdelta_lt : delta < 1)
    (hmeasure : ∀ n, mu.real (U n)ᶜ ≤ delta) :
    mu (Filter.limsup U Filter.atTop) ≠ 0 := by
  let V : ℕ → Set M := fun N => ⋂ i : ℕ, ⋂ (_hi : i ≥ N), (U i)ᶜ
  have hV_mono : Monotone V := by
    intro N N' hNN' x hx
    simp only [V, Set.mem_iInter] at hx ⊢
    intro i hi
    exact hx i (hNN'.trans hi)
  have hV_measure (N : ℕ) : mu (V N) ≤ ENNReal.ofReal delta := by
    calc
      mu (V N) ≤ mu (U N)ᶜ := measure_mono (by
        intro x hx
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hx N) le_rfl)
      _ = ENNReal.ofReal (mu.real (U N)ᶜ) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal delta := ENNReal.ofReal_le_ofReal (hmeasure N)
  have hcomp_le :
      mu (Filter.limsup U Filter.atTop)ᶜ ≤ ENNReal.ofReal delta := by
    rw [Filter.limsup_compl, Filter.liminf_eq_iSup_iInf_of_nat]
    change mu (⋃ N, V N) ≤ _
    rw [hV_mono.measure_iUnion]
    exact iSup_le hV_measure
  have hcomp_lt : mu (Filter.limsup U Filter.atTop)ᶜ < 1 :=
    hcomp_le.trans_lt (ENNReal.ofReal_lt_one.2 hdelta_lt)
  intro hzero
  have hS_measurable : MeasurableSet (Filter.limsup U Filter.atTop) :=
    MeasurableSet.measurableSet_limsup hU
  have hcomp_eq : mu (Filter.limsup U Filter.atTop)ᶜ = 1 := by
    rw [measure_compl hS_measurable (by finiteness), hzero, measure_univ]
    simp
  rw [hcomp_eq] at hcomp_lt
  exact lt_irrefl 1 hcomp_lt

lemma exists_partition_subfamily_limsup_ne_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (P : ℕ → Finset (Set M))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1) :
    ∃ Q : ℕ → Finset (Set M),
      (∀ n, Q n ⊆ P n) ∧
      (∀ n, ((Q n).card : ℝ) ≤
        Real.exp (partitionEntropy mu (P n) / delta + 1)) ∧
      (∀ n, mu.real (⋃ A ∈ Q n, A)ᶜ ≤ delta) ∧
      MeasurableSet
        (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ∧
      mu (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ≠ 0 := by
  classical
  choose Q hQ using fun n =>
    exists_partition_subfamily_cover_of_entropy mu (hP n) hdelta_pos
  have hQ_subset : ∀ n, Q n ⊆ P n := fun n => (hQ n).1
  have hQ_card : ∀ n, ((Q n).card : ℝ) ≤
      Real.exp (partitionEntropy mu (P n) / delta + 1) :=
    fun n => (hQ n).2.1
  have hQ_cover : ∀ n, mu.real (⋃ A ∈ Q n, A)ᶜ ≤ delta :=
    fun n => (hQ n).2.2
  have hU_measurable : ∀ n, MeasurableSet (⋃ A ∈ Q n, A) := by
    intro n
    exact Finset.measurableSet_biUnion (Q n) fun A hAQ =>
      (hP n).measurable A (hQ_subset n hAQ)
  exact ⟨Q, hQ_subset, hQ_card, hQ_cover,
    MeasurableSet.measurableSet_limsup hU_measurable,
    measure_limsup_ne_zero_of_compl_measureReal_le
      mu (fun n => ⋃ A ∈ Q n, A) hU_measurable hdelta_lt hQ_cover⟩

end Submission.Helpers
