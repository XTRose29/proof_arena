import Submission.HausdorffCovers

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma dimMeasure_le_of_partition_entropy_covers_on_goodSets
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (P : ℕ → Finset (Set EucPlane))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta_sum : (∑' n, ENNReal.ofReal (delta n)) ≠ ⊤)
    (good : ℕ → Set EucPlane) (hgood_measurable : ∀ n, MeasurableSet (good n))
    (hgood_full : mu (liminf good atTop)ᶜ = 0)
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (nhds 0))
    (hdiam : ∀ᶠ n in atTop, ∀ A ∈ P n,
      Metric.ediam (A ∩ good n) ≤ r n)
    (d : NNReal)
    (hgrowth :
      liminf
          (fun n =>
            ENNReal.ofReal
                (Real.exp (partitionEntropy mu (P n) / delta n + 1)) *
              r n ^ (d : ℝ))
          atTop ≠ ⊤) :
    dimMeasure mu ≤ d := by
  classical
  obtain ⟨Q, hQ_subset, hQ_card, _hQ_cover, hQlim_measurable, hQlim_full⟩ :=
    exists_partition_subfamily_liminf_full_measure
      mu P hP delta hdelta hdelta_sum
  let R : ℕ → Finset (Set EucPlane) := fun n =>
    (Q n).image fun A => A ∩ good n
  have hR_diam : ∀ᶠ n in atTop, ∀ B ∈ R n, Metric.ediam B ≤ r n := by
    filter_upwards [hdiam] with n hn
    intro B hB
    obtain ⟨A, hAQ, rfl⟩ := Finset.mem_image.mp hB
    exact hn A (hQ_subset n hAQ)
  have hR_card (n : ℕ) : (R n).card ≤ (Q n).card := by
    exact Finset.card_image_le
  have hR_growth_le : ∀ᶠ n in atTop,
      ((R n).card : ℝ≥0∞) * r n ^ (d : ℝ) ≤
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n) / delta n + 1)) *
          r n ^ (d : ℝ) := by
    exact Eventually.of_forall fun n => mul_le_mul_left (by
      calc
        ((R n).card : ℝ≥0∞) ≤ ((Q n).card : ℝ≥0∞) := by exact_mod_cast hR_card n
        _ ≤ ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n) / delta n + 1)) := by
          have h := ENNReal.ofReal_le_ofReal (hQ_card n)
          simpa using h) _
  have hR_growth :
      liminf (fun n => ((R n).card : ℝ≥0∞) * r n ^ (d : ℝ)) atTop ≠ ⊤ :=
    ne_top_of_le_ne_top hgrowth (Filter.liminf_le_liminf hR_growth_le)
  have hR_dim : dimH (liminf (fun n => ⋃ B ∈ R n, B) atTop) ≤ d :=
    dimH_liminf_iUnion_finset_le_of_card_mul_rpow
      R r hr hR_diam d hR_growth
  let UQ : ℕ → Set EucPlane := fun n => ⋃ A ∈ Q n, A
  let S := liminf UQ atTop ∩ liminf good atTop
  have hS_measurable : MeasurableSet S := by
    exact hQlim_measurable.inter
      (MeasurableSet.measurableSet_liminf hgood_measurable)
  have hS_full : mu Sᶜ = 0 := by
    dsimp [S]
    rw [Set.compl_inter]
    exact measure_union_null (by simpa [UQ] using hQlim_full) hgood_full
  have hS_subset : S ⊆ liminf (fun n => ⋃ B ∈ R n, B) atTop := by
    intro x hx
    dsimp [S] at hx
    have hxQ := hx.1
    have hxG := hx.2
    rw [Filter.liminf_eq_iSup_iInf_of_nat] at hxQ hxG ⊢
    obtain ⟨NQ, hxQ⟩ := Set.mem_iUnion.mp hxQ
    obtain ⟨NG, hxG⟩ := Set.mem_iUnion.mp hxG
    apply Set.mem_iUnion_of_mem (max NQ NG)
    apply Set.mem_iInter.mpr
    intro n
    apply Set.mem_iInter.mpr
    intro hn
    have hxQn := Set.mem_iInter.mp (Set.mem_iInter.mp hxQ n)
      ((le_max_left NQ NG).trans hn)
    have hxGn := Set.mem_iInter.mp (Set.mem_iInter.mp hxG n)
      ((le_max_right NQ NG).trans hn)
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxQn
    obtain ⟨hAQ, hxA⟩ := Set.mem_iUnion.mp hxA
    have hAR : A ∩ good n ∈ R n := by
      exact Finset.mem_image.mpr ⟨A, hAQ, rfl⟩
    exact Set.mem_iUnion_of_mem (A ∩ good n)
      (Set.mem_iUnion_of_mem hAR ⟨hxA, hxGn⟩)
  calc
    dimMeasure mu ≤ dimH S :=
      dimMeasure_le_dimH_of_full_measure mu hS_measurable hS_full
    _ ≤ dimH (liminf (fun n => ⋃ B ∈ R n, B) atTop) := dimH_mono hS_subset
    _ ≤ d := hR_dim

lemma dimMeasure_le_of_partition_entropy_limsup_covers_on_goodSets
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
    (good : ℕ → Set EucPlane) (hgood_measurable : ∀ n, MeasurableSet (good n))
    (hgood_full : mu (liminf good atTop)ᶜ = 0)
    (r : ℕ → ℝ≥0∞) (hr_mono : Antitone r)
    (hr : Tendsto r atTop (nhds 0))
    (hdiam : ∀ n, ∀ A ∈ P n, Metric.ediam (A ∩ good n) ≤ r n)
    (d : NNReal) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hgrowth : ∀ N,
      (∑' n : {n : ℕ // N ≤ n},
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
          r n.1 ^ (d : ℝ)) ≤ C) :
    dimMeasure mu ≤ d := by
  classical
  obtain ⟨Q, hQ_subset, hQ_card, _hQ_cover, hQlim_measurable, hQlim_ne_zero⟩ :=
    exists_partition_subfamily_limsup_ne_zero
      mu P hP hdelta_pos hdelta_lt
  let R : ℕ → Finset (Set EucPlane) := fun n =>
    (Q n).image fun A => A ∩ good n
  have hR_diam : ∀ n, ∀ B ∈ R n, Metric.ediam B ≤ r n := by
    intro n B hB
    obtain ⟨A, hAQ, rfl⟩ := Finset.mem_image.mp hB
    exact hdiam n A (hQ_subset n hAQ)
  have hR_card (n : ℕ) : (R n).card ≤ (Q n).card := Finset.card_image_le
  have hR_card_ennreal (n : ℕ) :
      ((R n).card : ℝ≥0∞) ≤
        ENNReal.ofReal
          (Real.exp (partitionEntropy mu (P n) / delta + 1)) := by
    calc
      ((R n).card : ℝ≥0∞) ≤ ((Q n).card : ℝ≥0∞) := by exact_mod_cast hR_card n
      _ ≤ ENNReal.ofReal
          (Real.exp (partitionEntropy mu (P n) / delta + 1)) := by
        have h := ENNReal.ofReal_le_ofReal (hQ_card n)
        simpa using h
  have hR_cost (N : ℕ) :
      (∑' n : {n : ℕ // N ≤ n},
        ((R n.1).card : ℝ≥0∞) * r n.1 ^ (d : ℝ)) ≤ C := by
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans (hgrowth N)
    exact mul_le_mul_left (hR_card_ennreal n.1) _
  have hR_dim : dimH (limsup (fun n => ⋃ B ∈ R n, B) atTop) ≤ d :=
    dimH_limsup_iUnion_finset_le_of_tail_cost
      R r hr_mono hr hR_diam d C hC hR_cost
  let UQ : ℕ → Set EucPlane := fun n => ⋃ A ∈ Q n, A
  let G := liminf good atTop
  let S := limsup UQ atTop ∩ G
  have hG_measurable : MeasurableSet G :=
    MeasurableSet.measurableSet_liminf hgood_measurable
  have hS_measurable : MeasurableSet S := by
    exact hQlim_measurable.inter hG_measurable
  have hS_ne_zero : mu S ≠ 0 := by
    have hEq : mu (limsup UQ atTop ∩ G) = mu (limsup UQ atTop) :=
      measure_inter_eq_of_compl_eq_zero mu (by simpa [G] using hgood_full) _
    dsimp [S]
    rw [hEq]
    simpa [UQ] using hQlim_ne_zero
  have hS_subset : S ⊆ limsup (fun n => ⋃ B ∈ R n, B) atTop := by
    intro x hx
    dsimp [S, G] at hx
    have hxQ := hx.1
    have hxG := hx.2
    rw [Filter.limsup_eq_iInf_iSup_of_nat] at hxQ ⊢
    rw [Filter.liminf_eq_iSup_iInf_of_nat] at hxG
    obtain ⟨NG, hxG⟩ := Set.mem_iUnion.mp hxG
    apply Set.mem_iInter.mpr
    intro N
    have hxQtail := Set.mem_iInter.mp hxQ (max N NG)
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxQtail
    obtain ⟨hn, hxUn⟩ := Set.mem_iUnion.mp hxn
    have hxGn := Set.mem_iInter.mp (Set.mem_iInter.mp hxG n)
      ((le_max_right N NG).trans hn)
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxUn
    obtain ⟨hAQ, hxA⟩ := Set.mem_iUnion.mp hxA
    apply Set.mem_iUnion_of_mem n
    apply Set.mem_iUnion_of_mem ((le_max_left N NG).trans hn)
    have hAR : A ∩ good n ∈ R n :=
      Finset.mem_image.mpr ⟨A, hAQ, rfl⟩
    exact Set.mem_iUnion_of_mem (A ∩ good n)
      (Set.mem_iUnion_of_mem hAR ⟨hxA, hxGn⟩)
  have hR_union_measurable (n : ℕ) : MeasurableSet (⋃ B ∈ R n, B) := by
    apply Finset.measurableSet_biUnion
    intro B hBR
    obtain ⟨A, hAQ, rfl⟩ := Finset.mem_image.mp hBR
    exact ((hP n).measurable A (hQ_subset n hAQ)).inter (hgood_measurable n)
  have hRlim_measurable :
      MeasurableSet (limsup (fun n => ⋃ B ∈ R n, B) atTop) :=
    MeasurableSet.measurableSet_limsup hR_union_measurable
  have hRlim_ne_zero : mu (limsup (fun n => ⋃ B ∈ R n, B) atTop) ≠ 0 := by
    intro hzero
    apply hS_ne_zero
    exact measure_mono_null hS_subset hzero
  exact (dimMeasure_le_dimH_of_measure_ne_zero_ergodic
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hmu_erg
      hRlim_measurable hRlim_ne_zero).trans hR_dim

end Submission.Helpers
