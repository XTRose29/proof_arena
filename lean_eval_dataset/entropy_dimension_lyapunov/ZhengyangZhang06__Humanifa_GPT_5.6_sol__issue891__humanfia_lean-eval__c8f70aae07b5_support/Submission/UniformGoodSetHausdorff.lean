import Submission.CenteredGoodSetHausdorff

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma dimMeasure_le_of_partition_entropy_limsup_covers_on_uniform_goodSets
    (T T_inv : EucPlane -> EucPlane)
    (hT_smooth : ContDiff Real 2 T)
    (hT_inv_smooth : ContDiff Real 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    (P : Nat -> Finset (Set EucPlane))
    (hP : ∀ n, IsMeasurablePartition mu (P n))
    {delta gamma : Real} (hdelta_pos : 0 < delta)
    (hdelta_gamma : delta + gamma < 1)
    (good : Nat -> Set EucPlane)
    (hgood_measurable : ∀ n, MeasurableSet (good n))
    (hgood_compl : ∀ n, mu.real (good n)ᶜ <= gamma)
    (r : Nat -> ENNReal) (hr_mono : Antitone r)
    (hr : Tendsto r atTop (nhds 0))
    (hdiam : ∀ n, ∀ A ∈ P n,
      Metric.ediam (A ∩ good n) <= r n)
    (d : NNReal) (C : ENNReal) (hC : C ≠ ⊤)
    (hgrowth : ∀ N,
      (∑' n : {n : Nat // N <= n},
        ENNReal.ofReal
            (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
          r n.1 ^ (d : Real)) <= C) :
    dimMeasure mu <= d := by
  classical
  have hdelta_lt : delta < 1 := by
    have hgamma_nonneg : 0 <= gamma := by
      exact (measureReal_nonneg.trans (hgood_compl 0))
    linarith
  obtain ⟨Q, hQ_subset, hQ_card, hQ_cover, _hQlim_measurable,
      _hQlim_ne_zero⟩ :=
    exists_partition_subfamily_limsup_ne_zero
      mu P hP hdelta_pos hdelta_lt
  let R : Nat -> Finset (Set EucPlane) := fun n =>
    (Q n).image fun A => A ∩ good n
  have hR_diam : ∀ n, ∀ B ∈ R n, Metric.ediam B <= r n := by
    intro n B hB
    obtain ⟨A, hAQ, rfl⟩ := Finset.mem_image.mp hB
    exact hdiam n A (hQ_subset n hAQ)
  have hR_card (n : Nat) : (R n).card <= (Q n).card :=
    Finset.card_image_le
  have hR_card_ennreal (n : Nat) :
      ((R n).card : ENNReal) <=
        ENNReal.ofReal
          (Real.exp (partitionEntropy mu (P n) / delta + 1)) := by
    calc
      ((R n).card : ENNReal) <= ((Q n).card : ENNReal) := by
        exact_mod_cast hR_card n
      _ <= ENNReal.ofReal
          (Real.exp (partitionEntropy mu (P n) / delta + 1)) := by
        have h := ENNReal.ofReal_le_ofReal (hQ_card n)
        simpa using h
  have hR_cost (N : Nat) :
      (∑' n : {n : Nat // N <= n},
        ((R n.1).card : ENNReal) * r n.1 ^ (d : Real)) <= C := by
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans (hgrowth N)
    exact mul_le_mul_left (hR_card_ennreal n.1) _
  have hR_dim : dimH (limsup (fun n => ⋃ B ∈ R n, B) atTop) <= d :=
    dimH_limsup_iUnion_finset_le_of_tail_cost
      R r hr_mono hr hR_diam d C hC hR_cost
  have hR_union_measurable (n : Nat) :
      MeasurableSet (⋃ B ∈ R n, B) := by
    apply Finset.measurableSet_biUnion
    intro B hBR
    obtain ⟨A, hAQ, rfl⟩ := Finset.mem_image.mp hBR
    exact ((hP n).measurable A (hQ_subset n hAQ)).inter
      (hgood_measurable n)
  have hR_cover (n : Nat) :
      mu.real (⋃ B ∈ R n, B)ᶜ <= delta + gamma := by
    let U := ⋃ A ∈ Q n, A
    have hR_eq : (⋃ B ∈ R n, B) = U ∩ good n := by
      ext x
      simp only [R, U, Set.mem_iUnion, Finset.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨B, ⟨hBR, hxB⟩⟩
        obtain ⟨A, hAQ, rfl⟩ := hBR
        exact ⟨⟨A, ⟨hAQ, hxB.1⟩⟩, hxB.2⟩
      · rintro ⟨⟨A, hAQ, hxA⟩, hxgood⟩
        exact ⟨A ∩ good n, ⟨⟨A, hAQ, rfl⟩, hxA, hxgood⟩⟩
    rw [hR_eq, Set.compl_inter]
    calc
      mu.real (Uᶜ ∪ (good n)ᶜ) <=
          mu.real Uᶜ + mu.real (good n)ᶜ := measureReal_union_le _ _
      _ <= delta + gamma := add_le_add (by simpa [U] using hQ_cover n)
        (hgood_compl n)
  have hRlim_measurable :
      MeasurableSet (limsup (fun n => ⋃ B ∈ R n, B) atTop) :=
    MeasurableSet.measurableSet_limsup hR_union_measurable
  have hRlim_ne_zero :
      mu (limsup (fun n => ⋃ B ∈ R n, B) atTop) ≠ 0 :=
    measure_limsup_ne_zero_of_compl_measureReal_le
      mu (fun n => ⋃ B ∈ R n, B) hR_union_measurable
        hdelta_gamma hR_cover
  exact (dimMeasure_le_dimH_of_measure_ne_zero_ergodic
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hmu_erg
      hRlim_measurable hRlim_ne_zero).trans hR_dim

lemma dimMeasure_le_of_balanced_centered_uniform_good_diameter
    (T T_inv : EucPlane -> EucPlane)
    (hT_smooth : ContDiff Real 2 T)
    (hT_inv_smooth : ContDiff Real 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {lam1 lam2 : Real} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (good : Nat -> Set EucPlane)
    (hgood_measurable : ∀ L, MeasurableSet (good L))
    {gamma : Real} (hgood_compl : ∀ L, mu.real (good L)ᶜ <= gamma)
    {R delta : Real} (hR : 0 < R) (hdelta_pos : 0 < delta)
    (hdelta_gamma : delta + gamma < 1)
    (d : NNReal)
    (hrate : entropyW mu T P / delta < R * (d : Real))
    (hdiam : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      Metric.ediam (A ∩ good L) <=
        ENNReal.ofReal (Real.exp (-R * L))) :
    dimMeasure mu <= d := by
  let Q : Nat -> Finset (Set EucPlane) := fun L => centeredJoin T T_inv P
    (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L)
  let r : Nat -> ENNReal := fun L => ENNReal.ofReal (Real.exp (-R * L))
  have hQ (L : Nat) : IsMeasurablePartition mu (Q L) := by
    exact isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP _ _
  have hr_mono : Antitone r := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hab_real : (a : Real) <= b := by exact_mod_cast hab
    nlinarith
  have hexponent : Tendsto (fun L : Nat => -R * (L : Real)) atTop atBot := by
    exact (tendsto_natCast_atTop_atTop (R := Real)).const_mul_atTop_of_neg
      (neg_neg_of_pos hR)
  have hr : Tendsto r atTop (nhds 0) := by
    have hexp := Real.tendsto_exp_atBot.comp hexponent
    have hofReal := ENNReal.tendsto_ofReal hexp
    simpa [r] using hofReal
  let u : Nat -> Real := fun L => partitionEntropy mu (iteratedJoin T P L)
  have hu : Tendsto (fun L => u L / L) atTop (nhds (entropyW mu T P)) := by
    simpa [u] using tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT P hP
  obtain ⟨C, hC, hcost⟩ := exists_exponential_entropy_tail_bound
    u hu hdelta_pos d hrate
  apply dimMeasure_le_of_partition_entropy_limsup_covers_on_uniform_goodSets
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hErg
      Q hQ hdelta_pos hdelta_gamma good hgood_measurable hgood_compl
      r hr_mono hr (fun L A hA => hdiam L A hA) d C hC
  intro N
  have hentropy (L : Nat) : partitionEntropy mu (Q L) = u L := by
    rw [partitionEntropy_centeredJoin mu T T_inv hT_left hT hT_inv P hP]
    rw [balancedBackward_add_balancedForward hlam1 hlam2]
  simpa [r, hentropy] using hcost N

end Submission.Helpers
