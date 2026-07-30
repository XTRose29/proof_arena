import Submission.EntropyTypical

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology
open scoped ENNReal

lemma dimH_le_of_finset_covers
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : Set X) (Q : ℕ → Finset (Set X))
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ᶠ n in atTop, ∀ A ∈ Q n, Metric.ediam A ≤ r n)
    (hcover : ∀ᶠ n in atTop, s ⊆ ⋃ A ∈ Q n, A)
    (d : NNReal)
    (hsum :
      liminf
          (fun n => ∑ A ∈ Q n, Metric.ediam A ^ (d : ℝ))
          atTop ≠ ⊤) :
    dimH s ≤ d := by
  let t : ∀ n, ↥(Q n) → Set X := fun _n A => A.1
  have hdiam' : ∀ᶠ n in atTop, ∀ A : ↥(Q n), Metric.ediam (t n A) ≤ r n := by
    filter_upwards [hdiam] with n hn
    intro A
    exact hn A.1 A.2
  have hcover' : ∀ᶠ n in atTop, s ⊆ ⋃ A : ↥(Q n), t n A := by
    filter_upwards [hcover] with n hn
    intro x hx
    rcases Set.mem_iUnion.mp (hn hx) with ⟨A, hxA⟩
    rcases Set.mem_iUnion.mp hxA with ⟨hAQ, hxA⟩
    exact Set.mem_iUnion_of_mem ⟨A, hAQ⟩ hxA
  have hmeasure := Measure.mkMetric_le_liminf_sum s r hr t hdiam' hcover'
    (fun z => z ^ (d : ℝ))
  have hsum_eq :
      (fun n => ∑ A : ↥(Q n), Metric.ediam (t n A) ^ (d : ℝ)) =
        fun n => ∑ A ∈ Q n, Metric.ediam A ^ (d : ℝ) := by
    funext n
    change (∑ A ∈ (Q n).attach, Metric.ediam (A : Set X) ^ (d : ℝ)) = _
    exact Finset.sum_attach (Q n) fun A => Metric.ediam A ^ (d : ℝ)
  rw [hsum_eq] at hmeasure
  have hmeasure' :
      Measure.hausdorffMeasure (d : ℝ) s ≤
        liminf (fun n => ∑ A ∈ Q n, Metric.ediam A ^ (d : ℝ)) atTop := by
    simpa [Measure.hausdorffMeasure] using hmeasure
  exact dimH_le_of_hausdorffMeasure_ne_top
    (ne_top_of_le_ne_top hsum hmeasure')

lemma dimH_le_of_finset_covers_card_mul_rpow
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : Set X) (Q : ℕ → Finset (Set X))
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ᶠ n in atTop, ∀ A ∈ Q n, Metric.ediam A ≤ r n)
    (hcover : ∀ᶠ n in atTop, s ⊆ ⋃ A ∈ Q n, A)
    (d : NNReal)
    (hcard :
      liminf
          (fun n => ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ))
          atTop ≠ ⊤) :
    dimH s ≤ d := by
  have hsum_le : ∀ᶠ n in atTop,
      (∑ A ∈ Q n, Metric.ediam A ^ (d : ℝ)) ≤
        ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ) := by
    filter_upwards [hdiam] with n hn
    calc
      (∑ A ∈ Q n, Metric.ediam A ^ (d : ℝ)) ≤
          ∑ _A ∈ Q n, r n ^ (d : ℝ) := by
        apply Finset.sum_le_sum
        intro A hA
        exact ENNReal.rpow_le_rpow (hn A hA) d.coe_nonneg
      _ = ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ) := by simp
  apply dimH_le_of_finset_covers s Q r hr hdiam hcover d
  exact ne_top_of_le_ne_top hcard (Filter.liminf_le_liminf hsum_le)

lemma dimH_liminf_iUnion_finset_le_of_card_mul_rpow
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Q : ℕ → Finset (Set X))
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ᶠ n in atTop, ∀ A ∈ Q n, Metric.ediam A ≤ r n)
    (d : NNReal)
    (hcard :
      liminf
          (fun n => ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ))
          atTop ≠ ⊤) :
    dimH
        (liminf (fun n => ⋃ A ∈ Q n, A) atTop) ≤ d := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  change dimH (⋃ N : ℕ, ⋂ i : ℕ, ⋂ (_hi : i ≥ N), ⋃ A ∈ Q i, A) ≤ d
  rw [dimH_iUnion]
  apply iSup_le
  intro N
  apply dimH_le_of_finset_covers_card_mul_rpow
    (⋂ i : ℕ, ⋂ (_hi : i ≥ N), ⋃ A ∈ Q i, A) Q r hr hdiam _ d hcard
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro x hx
  exact Set.mem_iInter.mp (Set.mem_iInter.mp hx n) hn

lemma dimH_limsup_iUnion_finset_le_of_tail_cost
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Q : ℕ → Finset (Set X))
    (r : ℕ → ℝ≥0∞) (hr_mono : Antitone r)
    (hr : Tendsto r atTop (nhds 0))
    (hdiam : ∀ n, ∀ A ∈ Q n, Metric.ediam A ≤ r n)
    (d : NNReal) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hcost : ∀ N,
      (∑' n : {n : ℕ // N ≤ n},
        ((Q n.1).card : ℝ≥0∞) * r n.1 ^ (d : ℝ)) ≤ C) :
    dimH (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ≤ d := by
  let I (N : ℕ) := Σ n : {n : ℕ // N ≤ n}, ↥(Q n.1)
  let t (N : ℕ) (i : I N) : Set X := i.2.1
  have ht : ∀ N, ∀ i : I N, Metric.ediam (t N i) ≤ r N := by
    intro N i
    exact (hdiam i.1.1 i.2.1 i.2.2).trans (hr_mono i.1.2)
  have hcover : ∀ N,
      Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop ⊆ ⋃ i : I N, t N i := by
    intro N x hx
    rw [Filter.limsup_eq_iInf_iSup_of_nat] at hx
    change x ∈ ⋂ N, ⋃ i, ⋃ (_hi : i ≥ N), ⋃ A ∈ Q i, A at hx
    have hxN := Set.mem_iInter.mp hx N
    rcases Set.mem_iUnion.mp hxN with ⟨n, hxn⟩
    rcases Set.mem_iUnion.mp hxn with ⟨hn, hxn⟩
    rcases Set.mem_iUnion.mp hxn with ⟨A, hxn⟩
    rcases Set.mem_iUnion.mp hxn with ⟨hAQ, hxA⟩
    exact Set.mem_iUnion_of_mem ⟨⟨n, hn⟩, ⟨A, hAQ⟩⟩ hxA
  have hinner (n : ℕ) :
      (∑' A : ↥(Q n), Metric.ediam (A : Set X) ^ (d : ℝ)) ≤
        ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ) := by
    rw [tsum_fintype]
    calc
      (∑ A : ↥(Q n), Metric.ediam (A : Set X) ^ (d : ℝ)) ≤
          ∑ _A : ↥(Q n), r n ^ (d : ℝ) := by
        apply Finset.sum_le_sum
        intro A _hA
        exact ENNReal.rpow_le_rpow (hdiam n A.1 A.2) d.coe_nonneg
      _ = ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ) := by simp
  have htail (N : ℕ) :
      (∑' i : I N, Metric.ediam (t N i) ^ (d : ℝ)) ≤ C := by
    simp only [I, t]
    calc
      (∑' i : Σ n : {n : ℕ // N ≤ n}, ↥(Q n.1),
          Metric.ediam (i.2.1 : Set X) ^ (d : ℝ)) =
          ∑' n : {n : ℕ // N ≤ n},
            ∑' A : ↥(Q n.1), Metric.ediam (A : Set X) ^ (d : ℝ) :=
        ENNReal.tsum_sigma fun (n : {n : ℕ // N ≤ n})
          (A : ↥(Q n.1)) => Metric.ediam (A : Set X) ^ (d : ℝ)
      _ ≤ ∑' n : {n : ℕ // N ≤ n},
          ((Q n.1).card : ℝ≥0∞) * r n.1 ^ (d : ℝ) :=
        ENNReal.tsum_le_tsum fun n => hinner n.1
      _ ≤ C := hcost N
  have hmeasure := Measure.mkMetric_le_liminf_tsum
    (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop)
    r hr t (Filter.Eventually.of_forall ht)
      (Filter.Eventually.of_forall hcover) (fun z => z ^ (d : ℝ))
  have hliminf :
      Filter.liminf
          (fun N => ∑' i : I N, Metric.ediam (t N i) ^ (d : ℝ))
          Filter.atTop ≤ C :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall htail)
  have hmeasure' :
      Measure.hausdorffMeasure (d : ℝ)
          (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ≤ C := by
    have hmeasure'' :
        Measure.hausdorffMeasure (d : ℝ)
            (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ≤
          Filter.liminf
            (fun N => ∑' i : I N, Metric.ediam (t N i) ^ (d : ℝ))
            Filter.atTop := by
      simpa [Measure.hausdorffMeasure] using hmeasure
    exact hmeasure''.trans hliminf
  exact dimH_le_of_hausdorffMeasure_ne_top
    (ne_top_of_le_ne_top hC hmeasure')

lemma dimMeasure_le_of_partition_entropy_limsup_covers
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    (P : ℕ → Finset (Set EucPlane))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (r : ℕ → ℝ≥0∞) (hr_mono : Antitone r)
    (hr : Tendsto r atTop (nhds 0))
    (hdiam : ∀ n, ∀ A ∈ P n, Metric.ediam A ≤ r n)
    (d : NNReal) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hgrowth : ∀ N,
      (∑' n : {n : ℕ // N ≤ n},
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
          r n.1 ^ (d : ℝ)) ≤ C) :
    dimMeasure mu ≤ d := by
  obtain ⟨Q, hQ_subset, hQ_card, _hQ_cover, hS_measurable, hS_ne_zero⟩ :=
    exists_partition_subfamily_limsup_ne_zero
      mu P hP hdelta_pos hdelta_lt
  have hQ_diam : ∀ n, ∀ A ∈ Q n, Metric.ediam A ≤ r n := by
    intro n A hAQ
    exact hdiam n A (hQ_subset n hAQ)
  have hQ_card_ennreal (n : ℕ) :
      ((Q n).card : ℝ≥0∞) ≤
        ENNReal.ofReal
          (Real.exp (partitionEntropy mu (P n) / delta + 1)) := by
    have h := ENNReal.ofReal_le_ofReal (hQ_card n)
    simpa using h
  have hQ_cost (N : ℕ) :
      (∑' n : {n : ℕ // N ≤ n},
        ((Q n.1).card : ℝ≥0∞) * r n.1 ^ (d : ℝ)) ≤ C := by
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans (hgrowth N)
    exact mul_le_mul_left (hQ_card_ennreal n.1) _
  have hS_dim :
      dimH (Filter.limsup (fun n => ⋃ A ∈ Q n, A) Filter.atTop) ≤ d :=
    dimH_limsup_iUnion_finset_le_of_tail_cost
      Q r hr_mono hr hQ_diam d C hC hQ_cost
  exact (dimMeasure_le_dimH_of_measure_ne_zero_ergodic
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hmu_erg
      hS_measurable hS_ne_zero).trans hS_dim

lemma dimMeasure_le_of_partition_entropy_covers
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (P : ℕ → Finset (Set EucPlane))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta_sum : (∑' n, ENNReal.ofReal (delta n)) ≠ ⊤)
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ᶠ n in atTop, ∀ A ∈ P n, Metric.ediam A ≤ r n)
    (d : NNReal)
    (hgrowth :
      liminf
          (fun n =>
            ENNReal.ofReal
                (Real.exp (partitionEntropy mu (P n) / delta n + 1)) *
              r n ^ (d : ℝ))
          atTop ≠ ⊤) :
    dimMeasure mu ≤ d := by
  obtain ⟨Q, hQ_subset, hQ_card, _hQ_cover, hS_measurable, hS_full⟩ :=
    exists_partition_subfamily_liminf_full_measure
      mu P hP delta hdelta hdelta_sum
  have hQ_diam : ∀ᶠ n in atTop, ∀ A ∈ Q n, Metric.ediam A ≤ r n := by
    filter_upwards [hdiam] with n hn
    intro A hAQ
    exact hn A (hQ_subset n hAQ)
  have hQ_growth_le : ∀ᶠ n in atTop,
      ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ) ≤
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n) / delta n + 1)) *
          r n ^ (d : ℝ) := by
    exact Filter.Eventually.of_forall fun n =>
      mul_le_mul_left (by
        have h := ENNReal.ofReal_le_ofReal (hQ_card n)
        simpa using h) _
  have hQ_growth :
      liminf
          (fun n => ((Q n).card : ℝ≥0∞) * r n ^ (d : ℝ))
          atTop ≠ ⊤ :=
    ne_top_of_le_ne_top hgrowth (Filter.liminf_le_liminf hQ_growth_le)
  have hS_dim :
      dimH (liminf (fun n => ⋃ A ∈ Q n, A) atTop) ≤ d :=
    dimH_liminf_iUnion_finset_le_of_card_mul_rpow Q r hr hQ_diam d hQ_growth
  exact (dimMeasure_le_dimH_of_full_measure mu hS_measurable hS_full).trans hS_dim

end Submission.Helpers
