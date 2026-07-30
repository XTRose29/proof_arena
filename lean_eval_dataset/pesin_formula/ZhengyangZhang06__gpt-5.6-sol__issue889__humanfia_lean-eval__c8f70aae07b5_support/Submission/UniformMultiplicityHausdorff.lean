import Submission.MultiplicityHausdorff
import Submission.UniformGoodSetHausdorff

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

/-- The entropy/Hausdorff covering argument with both a uniformly large good
set and finitely many small pieces per partition atom. -/
lemma dimMeasure_le_of_partition_entropy_limsup_piece_covers_on_uniform_goodSets
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    (P : ℕ → Finset (Set EucPlane))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    {delta gamma : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_gamma : delta + gamma < 1)
    (good : ℕ → Set EucPlane)
    (_hgood_measurable : ∀ n, MeasurableSet (good n))
    (hgood_compl : ∀ n, mu.real (good n)ᶜ ≤ gamma)
    (pieces : ℕ → Set EucPlane → Finset (Set EucPlane))
    (M : ℕ → ℕ)
    (hpieces_card : ∀ n A, A ∈ P n → (pieces n A).card ≤ M n)
    (hpieces_measurable : ∀ n A, A ∈ P n →
      ∀ B ∈ pieces n A, MeasurableSet B)
    (hpieces_cover : ∀ n A, A ∈ P n →
      A ∩ good n ⊆ ⋃ B ∈ pieces n A, B)
    (r : ℕ → ℝ≥0∞) (hr_mono : Antitone r)
    (hr : Tendsto r atTop (nhds 0))
    (hdiam : ∀ n A, A ∈ P n →
      ∀ B ∈ pieces n A, Metric.ediam B ≤ r n)
    (d : NNReal) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hgrowth : ∀ N,
      (∑' n : {n : ℕ // N ≤ n},
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
          (M n.1 : ℝ≥0∞) * r n.1 ^ (d : ℝ)) ≤ C) :
    dimMeasure mu ≤ d := by
  classical
  obtain ⟨Q, hQ_subset, hQ_card, hQ_cover, _hQlim_measurable,
      _hQlim_ne_zero⟩ :=
    exists_partition_subfamily_limsup_ne_zero
      mu P hP hdelta_pos (by
        have hgamma_nonneg : 0 ≤ gamma :=
          (measureReal_nonneg.trans (hgood_compl 0))
        linarith)
  let R : ℕ → Finset (Set EucPlane) := fun n =>
    (Q n).biUnion (pieces n)
  have hR_diam (n : ℕ) (B : Set EucPlane) (hBR : B ∈ R n) :
      Metric.ediam B ≤ r n := by
    obtain ⟨A, hAQ, hB⟩ := Finset.mem_biUnion.mp hBR
    exact hdiam n A (hQ_subset n hAQ) B hB
  have hR_measurable (n : ℕ) : MeasurableSet (⋃ B ∈ R n, B) := by
    apply Finset.measurableSet_biUnion
    intro B hBR
    obtain ⟨A, hAQ, hB⟩ := Finset.mem_biUnion.mp hBR
    exact hpieces_measurable n A (hQ_subset n hAQ) B hB
  have hR_card (n : ℕ) : (R n).card ≤ (Q n).card * M n := by
    calc
      (R n).card ≤ ∑ A ∈ Q n, (pieces n A).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ Q n, M n := by
        apply Finset.sum_le_sum
        intro A hAQ
        exact hpieces_card n A (hQ_subset n hAQ)
      _ = (Q n).card * M n := by simp
  have hR_card_ennreal (n : ℕ) :
      ((R n).card : ℝ≥0∞) ≤
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n) / delta + 1)) *
          (M n : ℝ≥0∞) := by
    calc
      ((R n).card : ℝ≥0∞) ≤ ((Q n).card : ℝ≥0∞) * (M n : ℝ≥0∞) := by
        exact_mod_cast hR_card n
      _ ≤ ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n) / delta + 1)) *
          (M n : ℝ≥0∞) := by
        gcongr
        have h := ENNReal.ofReal_le_ofReal (hQ_card n)
        simpa using h
  have hR_cost (N : ℕ) :
      (∑' n : {n : ℕ // N ≤ n},
        ((R n.1).card : ℝ≥0∞) * r n.1 ^ (d : ℝ)) ≤ C := by
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans (hgrowth N)
    calc
      ((R n.1).card : ℝ≥0∞) * r n.1 ^ (d : ℝ) ≤
          (ENNReal.ofReal
              (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
            (M n.1 : ℝ≥0∞)) * r n.1 ^ (d : ℝ) := by
        exact mul_le_mul_left (hR_card_ennreal n.1) _
      _ = ENNReal.ofReal
              (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
            (M n.1 : ℝ≥0∞) * r n.1 ^ (d : ℝ) := by ring
  have hR_dim :
      dimH (limsup (fun n => ⋃ B ∈ R n, B) atTop) ≤ d :=
    dimH_limsup_iUnion_finset_le_of_tail_cost
      R r hr_mono hr hR_diam d C hC hR_cost
  let UQ : ℕ → Set EucPlane := fun n => ⋃ A ∈ Q n, A
  have hR_cover (n : ℕ) :
      mu.real (⋃ B ∈ R n, B)ᶜ ≤ delta + gamma := by
    have hsubset : UQ n ∩ good n ⊆ ⋃ B ∈ R n, B := by
      rintro x ⟨hxQ, hxgood⟩
      change x ∈ ⋃ A ∈ Q n, A at hxQ
      simp only [Set.mem_iUnion] at hxQ
      obtain ⟨A, hAQ, hxA⟩ := hxQ
      have hxpieces := hpieces_cover n A (hQ_subset n hAQ) ⟨hxA, hxgood⟩
      simp only [Set.mem_iUnion] at hxpieces
      obtain ⟨B, hB, hxB⟩ := hxpieces
      exact Set.mem_iUnion_of_mem B (Set.mem_iUnion_of_mem
        (Finset.mem_biUnion.mpr ⟨A, hAQ, hB⟩) hxB)
    have hcompl : (⋃ B ∈ R n, B)ᶜ ⊆ (UQ n)ᶜ ∪ (good n)ᶜ := by
      rw [← Set.compl_inter]
      exact Set.compl_subset_compl.mpr hsubset
    calc
      mu.real (⋃ B ∈ R n, B)ᶜ ≤
          mu.real ((UQ n)ᶜ ∪ (good n)ᶜ) := measureReal_mono hcompl
      _ ≤ mu.real (UQ n)ᶜ + mu.real (good n)ᶜ :=
        measureReal_union_le _ _
      _ ≤ delta + gamma := add_le_add (by
        simpa [UQ] using hQ_cover n) (hgood_compl n)
  have hRlim_measurable :
      MeasurableSet (limsup (fun n => ⋃ B ∈ R n, B) atTop) :=
    MeasurableSet.measurableSet_limsup hR_measurable
  have hRlim_ne_zero :
      mu (limsup (fun n => ⋃ B ∈ R n, B) atTop) ≠ 0 :=
    measure_limsup_ne_zero_of_compl_measureReal_le
      mu (fun n => ⋃ B ∈ R n, B) hR_measurable
        hdelta_gamma hR_cover
  exact (dimMeasure_le_dimH_of_measure_ne_zero_ergodic
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hmu_erg
      hRlim_measurable hRlim_ne_zero).trans hR_dim

/-- The balanced centered specialization of the uniform-good-set piece-cover
criterion.  The exponential growth of the number of pieces contributes
additively to the entropy rate. -/
lemma dimMeasure_le_of_balanced_centered_uniform_good_piece_covers
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (good : ℕ → Set EucPlane)
    (hgood_measurable : ∀ L, MeasurableSet (good L))
    {gamma : ℝ} (hgood_compl : ∀ L, mu.real (good L)ᶜ ≤ gamma)
    (pieces : ℕ → Set EucPlane → Finset (Set EucPlane))
    (M : ℕ → ℕ) {kappa R delta : ℝ}
    (hM : ∀ L, (M L : ℝ) ≤ Real.exp (kappa * L))
    (hpieces_card : ∀ L A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L) →
        (pieces L A).card ≤ M L)
    (hpieces_measurable : ∀ L A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L) →
        ∀ B ∈ pieces L A, MeasurableSet B)
    (hpieces_cover : ∀ L A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L) →
        A ∩ good L ⊆ ⋃ B ∈ pieces L A, B)
    (hdiam : ∀ L A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L) →
        ∀ B ∈ pieces L A,
          Metric.ediam B ≤ ENNReal.ofReal (Real.exp (-R * L)))
    (hR : 0 < R) (hdelta_pos : 0 < delta)
    (hdelta_gamma : delta + gamma < 1)
    (d : NNReal)
    (hrate : entropyW mu T P / delta + kappa < R * (d : ℝ)) :
    dimMeasure mu ≤ d := by
  let Q : ℕ → Finset (Set EucPlane) := fun L => centeredJoin T T_inv P
    (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L)
  let r : ℕ → ℝ≥0∞ := fun L => ENNReal.ofReal (Real.exp (-R * L))
  have hQ (L : ℕ) : IsMeasurablePartition mu (Q L) :=
    isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP _ _
  have hr_mono : Antitone r := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hab_real : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hexponent : Tendsto (fun L : ℕ => -R * (L : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (neg_neg_of_pos hR)
  have hr : Tendsto r atTop (nhds 0) := by
    have hexp := Real.tendsto_exp_atBot.comp hexponent
    simpa [r] using ENNReal.tendsto_ofReal hexp
  let u : ℕ → ℝ := fun L =>
    partitionEntropy mu (iteratedJoin T P L) + delta * kappa * L
  have hu_base : Tendsto
      (fun L => partitionEntropy mu (iteratedJoin T P L) / L)
      atTop (nhds (entropyW mu T P)) :=
    tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT P hP
  have hlinear : Tendsto (fun L : ℕ => (delta * kappa * L) / L)
      atTop (nhds (delta * kappa)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    field_simp
  have hu : Tendsto (fun L => u L / L)
      atTop (nhds (entropyW mu T P + delta * kappa)) := by
    convert hu_base.add hlinear using 1
    funext L
    dsimp [u]
    ring
  have hrate' :
      (entropyW mu T P + delta * kappa) / delta < R * (d : ℝ) := by
    calc
      (entropyW mu T P + delta * kappa) / delta =
          entropyW mu T P / delta + kappa := by
        field_simp [hdelta_pos.ne']
      _ < R * (d : ℝ) := hrate
  obtain ⟨C, hC, hcost⟩ := exists_exponential_entropy_tail_bound
    u hu hdelta_pos d hrate'
  apply dimMeasure_le_of_partition_entropy_limsup_piece_covers_on_uniform_goodSets
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hErg
      Q hQ hdelta_pos hdelta_gamma good hgood_measurable hgood_compl
      pieces M (fun L A hA => hpieces_card L A hA)
      (fun L A hA => hpieces_measurable L A hA)
      (fun L A hA => hpieces_cover L A hA)
      r hr_mono hr (fun L A hA => hdiam L A hA) d C hC
  intro N
  refine (ENNReal.tsum_le_tsum fun L => ?_).trans (hcost N)
  have hM_ennreal : (M L.1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (kappa * L.1)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (hM L.1)
  have hrewrite :
      ENNReal.ofReal
            (Real.exp (partitionEntropy mu (Q L.1) / delta + 1)) *
          (M L.1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (u L.1 / delta + 1)) := by
    calc
      ENNReal.ofReal
            (Real.exp (partitionEntropy mu (Q L.1) / delta + 1)) *
          (M L.1 : ℝ≥0∞) ≤
          ENNReal.ofReal
              (Real.exp (partitionEntropy mu (Q L.1) / delta + 1)) *
            ENNReal.ofReal (Real.exp (kappa * L.1)) := by
        gcongr
      _ = ENNReal.ofReal (Real.exp (u L.1 / delta + 1)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        rw [← Real.exp_add]
        apply congrArg ENNReal.ofReal
        apply congrArg Real.exp
        have hentropy : partitionEntropy mu (Q L.1) =
            partitionEntropy mu (iteratedJoin T P L.1) := by
          rw [partitionEntropy_centeredJoin
            mu T T_inv hT_left hT hT_inv P hP]
          rw [balancedBackward_add_balancedForward hlam1 hlam2]
        rw [hentropy]
        dsimp [u]
        field_simp [hdelta_pos.ne']
        ring
  exact mul_le_mul_left hrewrite _

end Submission.Helpers
