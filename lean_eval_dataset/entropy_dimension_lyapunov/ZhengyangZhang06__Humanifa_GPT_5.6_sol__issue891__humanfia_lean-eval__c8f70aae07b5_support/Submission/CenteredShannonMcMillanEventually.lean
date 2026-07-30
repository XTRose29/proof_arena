import Submission.CenteredShannonMcMillan

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma birkhoffAverage_centered_eq_weighted
    {M : Type*} (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (f : M → ℝ) {m n : ℕ} (hmn : 0 < m + n) (x : M) :
    birkhoffAverage ℝ T f (m + n) (T_inv^[m] x) =
      (m : ℝ) / (m + n : ℕ) *
          birkhoffAverage ℝ T_inv f m (T_inv x) +
        (n : ℝ) / (m + n : ℕ) * birkhoffAverage ℝ T f n x := by
  rw [birkhoffAverage, birkhoffAverage, birkhoffAverage]
  rw [birkhoffSum_centered_eq_backward_add_forward
    T T_inv hT_right f m n x]
  simp only [smul_eq_mul]
  have hmn0 : ((m + n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmn.ne'
  by_cases hm : m = 0
  · subst m
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp [hn0]
  by_cases hn : n = 0
  · subst n
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    simp [hm0]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hmn0, hm0, hn0]

lemma ae_tendsto_birkhoffAverage_centered
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    (m n : ℕ → ℕ) (hm_top : Tendsto m atTop atTop)
    (hn_top : Tendsto n atTop atTop)
    {a b : ℝ}
    (hm_ratio : Tendsto
      (fun L => (m L : ℝ) / (m L + n L : ℕ)) atTop (nhds a))
    (hn_ratio : Tendsto
      (fun L => (n L : ℝ) / (m L + n L : ℕ)) atTop (nhds b))
    (hab : a + b = 1) :
    ∀ᵐ x ∂mu, Tendsto
      (fun L => birkhoffAverage ℝ T f (m L + n L) (T_inv^[m L] x))
      atTop (nhds (∫ y, f y ∂mu)) := by
  have hforward := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg f hf_measurable hf
  have hbackward := ae_tendsto_birkhoffAverage_integral
    mu T_inv hT_inv hErg_inv f hf_measurable hf
  have hbackward_shift := hT_inv.quasiMeasurePreserving.tendsto_ae hbackward
  filter_upwards [hforward, hbackward_shift] with x hxforward hxbackward
  have hxforward' : Tendsto
      (fun L => birkhoffAverage ℝ T f (n L) x)
      atTop (nhds (∫ y, f y ∂mu)) := by
    simpa [Function.comp_def] using hxforward.comp hn_top
  have hxbackward' : Tendsto
      (fun L => birkhoffAverage ℝ T_inv f (m L) (T_inv x))
      atTop (nhds (∫ y, f y ∂mu)) := by
    simpa [Function.comp_def] using hxbackward.comp hm_top
  have hweighted := (hm_ratio.mul hxbackward').add (hn_ratio.mul hxforward')
  have hweighted' : Tendsto
      (fun L =>
        (m L : ℝ) / (m L + n L : ℕ) *
            birkhoffAverage ℝ T_inv f (m L) (T_inv x) +
          (n L : ℝ) / (m L + n L : ℕ) *
            birkhoffAverage ℝ T f (n L) x)
      atTop (nhds (∫ y, f y ∂mu)) := by
    convert hweighted using 1
    rw [← add_mul, hab, one_mul]
  apply hweighted'.congr'
  filter_upwards [hm_top.eventually (eventually_gt_atTop 0)] with L hmL
  exact (birkhoffAverage_centered_eq_weighted
    T T_inv hT_right f (Nat.add_pos_left hmL (n L)) x).symm

lemma tendsto_nat_sub_div_sub
    (u : ℕ → ℕ) (hu_top : Tendsto u atTop atTop)
    {a : ℝ}
    (hu_ratio : Tendsto (fun L => (u L : ℝ) / L) atTop (nhds a))
    (C D : ℕ) :
    Tendsto (fun L => ((u L - C : ℕ) : ℝ) / (L - D : ℕ))
      atTop (nhds a) := by
  have hCdiv : Tendsto (fun L : ℕ => (C : ℝ) / L) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)
  have hDdiv : Tendsto (fun L : ℕ => (D : ℝ) / L) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (D : ℝ)
  have hformula : Tendsto
      (fun L : ℕ =>
        (((u L : ℝ) / L) - (C : ℝ) / L) /
          (1 - (D : ℝ) / L))
      atTop (nhds a) := by
    have hnum := hu_ratio.sub hCdiv
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hden := hone.sub hDdiv
    have hquot := hnum.div hden (by norm_num)
    have hquot' : Tendsto
        (fun L : ℕ =>
          (((u L : ℝ) / L) - (C : ℝ) / L) /
            (1 - (D : ℝ) / L))
        atTop (nhds ((a - 0) / (1 - 0))) := by
      apply hquot.congr'
      exact Eventually.of_forall fun _ => rfl
    simpa using hquot'
  apply hformula.congr'
  filter_upwards
      [hu_top.eventually (eventually_ge_atTop C), eventually_gt_atTop D]
      with L huC hDL
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hDL).ne'
  have hLD : D ≤ L := hDL.le
  rw [Nat.cast_sub huC, Nat.cast_sub hLD]
  have hLD0 : (L : ℝ) - D ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hDL.ne')
  field_simp [hL0, hLD0]

noncomputable def trimmedBalancedBackward
    (lam1 lam2 : ℝ) (C L : ℕ) : ℕ :=
  balancedBackward lam1 lam2 L - C

noncomputable def trimmedBalancedForward
    (lam1 lam2 : ℝ) (C L : ℕ) : ℕ :=
  balancedForward lam1 lam2 L - C

lemma tendsto_trimmedBalancedBackward_atTop
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (C : ℕ) :
    Tendsto (trimmedBalancedBackward lam1 lam2 C) atTop atTop := by
  change Tendsto (fun L => balancedBackward lam1 lam2 L - C) atTop atTop
  simpa [Function.comp_def] using
    (Filter.tendsto_sub_atTop_nat C).comp
      (tendsto_balancedBackward_atTop hlam1 hlam2)

lemma tendsto_trimmedBalancedForward_atTop
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (C : ℕ) :
    Tendsto (trimmedBalancedForward lam1 lam2 C) atTop atTop := by
  change Tendsto (fun L => balancedForward lam1 lam2 L - C) atTop atTop
  simpa [Function.comp_def] using
    (Filter.tendsto_sub_atTop_nat C).comp
      (tendsto_balancedForward_atTop hlam1 hlam2)

lemma eventually_trimmedBalanced_add
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (C : ℕ) :
    ∀ᶠ L in atTop,
      trimmedBalancedBackward lam1 lam2 C L +
          trimmedBalancedForward lam1 lam2 C L =
        L - 2 * C := by
  have hback := (tendsto_balancedBackward_atTop hlam1 hlam2).eventually
    (eventually_ge_atTop C)
  have hforward := (tendsto_balancedForward_atTop hlam1 hlam2).eventually
    (eventually_ge_atTop C)
  filter_upwards [hback, hforward] with L hCLback hCLforward
  dsimp [trimmedBalancedBackward, trimmedBalancedForward]
  have hsplit := balancedBackward_add_balancedForward hlam1 hlam2 L
  omega

lemma tendsto_trimmedBalancedBackward_ratio
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (C : ℕ) :
    Tendsto
      (fun L =>
        (trimmedBalancedBackward lam1 lam2 C L : ℝ) /
          (trimmedBalancedBackward lam1 lam2 C L +
            trimmedBalancedForward lam1 lam2 C L : ℕ))
      atTop (nhds (lam1 / (lam1 - lam2))) := by
  have hraw := tendsto_nat_sub_div_sub
    (balancedBackward lam1 lam2)
    (tendsto_balancedBackward_atTop hlam1 hlam2)
    (tendsto_balancedBackward_div hlam1 hlam2) C (2 * C)
  apply hraw.congr'
  filter_upwards [eventually_trimmedBalanced_add hlam1 hlam2 C] with L hsum
  rw [← hsum]
  rfl

lemma tendsto_trimmedBalancedForward_ratio
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (C : ℕ) :
    Tendsto
      (fun L =>
        (trimmedBalancedForward lam1 lam2 C L : ℝ) /
          (trimmedBalancedBackward lam1 lam2 C L +
            trimmedBalancedForward lam1 lam2 C L : ℕ))
      atTop (nhds ((-lam2) / (lam1 - lam2))) := by
  have hraw := tendsto_nat_sub_div_sub
    (balancedForward lam1 lam2)
    (tendsto_balancedForward_atTop hlam1 hlam2)
    (tendsto_balancedForward_div hlam1 hlam2) C (2 * C)
  apply hraw.congr'
  filter_upwards [eventually_trimmedBalanced_add hlam1 hlam2 C] with L hsum
  rw [← hsum]
  rfl

lemma ae_tendsto_birkhoffAverage_balanced_trimmed
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (f : M → ℝ) (hf_measurable : Measurable f) (hf : Integrable f mu)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (C : ℕ) :
    ∀ᵐ x ∂mu, Tendsto
      (fun L => birkhoffAverage ℝ T f
        (trimmedBalancedBackward lam1 lam2 C L +
          trimmedBalancedForward lam1 lam2 C L)
        (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x))
      atTop (nhds (∫ y, f y ∂mu)) := by
  have hdenom : lam1 - lam2 ≠ 0 :=
    (sub_pos.mpr (hlam2.trans hlam1)).ne'
  apply ae_tendsto_birkhoffAverage_centered
    mu T T_inv hT_right hT hT_inv hErg hErg_inv f hf_measurable hf
      (trimmedBalancedBackward lam1 lam2 C)
      (trimmedBalancedForward lam1 lam2 C)
      (tendsto_trimmedBalancedBackward_atTop hlam1 hlam2 C)
      (tendsto_trimmedBalancedForward_atTop hlam1 hlam2 C)
      (tendsto_trimmedBalancedBackward_ratio hlam1 hlam2 C)
      (tendsto_trimmedBalancedForward_ratio hlam1 hlam2 C)
  field_simp [hdenom]
  ring

lemma partitionInformation_lower_centeredBirkhoffAverage
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (P : Finset (Set M))
    (hT : Measurable T) (hP : ∀ A ∈ P, MeasurableSet A)
    {x : M}
    (hchain : ∀ k n,
      partitionInformation mu (iteratedJoin T P (n + 2)) (T^[k] x) =
        futureConditionalInformation mu T P n (T^[k] x) +
          partitionInformation mu (iteratedJoin T P (n + 1)) (T^[k + 1] x))
    {delta : ℝ} (hdelta : 0 ≤ delta) (N0 : ℕ)
    {L : ℕ} (hL : 0 < L) :
    ((L : ℝ) / (L + 2 * (N0 + 1) : ℕ)) *
        (birkhoffAverage ℝ T
            (futureConditionalInformationLimit mu T hT P hP) L
              (T^[N0 + 1] x) - delta -
          birkhoffAverage ℝ T
            ((futureInformationBadSet mu T P hT hP delta N0).indicator
              (futureConditionalInformationLimit mu T hT P hP)) L
              (T^[N0 + 1] x)) ≤
      partitionInformation mu
          (iteratedJoin T P (L + 2 * (N0 + 1))) x /
        (L + 2 * (N0 + 1) : ℕ) := by
  let cInf := futureConditionalInformationLimit mu T hT P hP
  let badInfo :=
    (futureInformationBadSet mu T P hT hP delta N0).indicator cInf
  let C := N0 + 1
  let J := L + 2 * C
  let N := J - 1
  have hC : 0 < C := by simp [C]
  have hJ : 0 < J := by omega
  have hN : N + 1 = J := by
    dsimp [N]
    omega
  have hindex (j : ℕ) (hj : j ∈ Finset.Ico C (C + L)) :
      N0 ≤ N - 1 - j := by
    have hj' := Finset.mem_Ico.mp hj
    dsimp [N, J, C] at hj' ⊢
    omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico C (C + L)) :
      cInf (T^[j] x) - delta - badInfo (T^[j] x) ≤
        futureConditionalInformation mu T P (N - 1 - j) (T^[j] x) := by
    exact futureConditionalInformation_lower_bound_badSet
      mu T P hT hP hdelta (hindex j hj) (T^[j] x)
  have hsubset : Finset.Ico C (C + L) ⊆ Finset.range N := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    apply Finset.mem_range.mpr
    dsimp [N, J]
    omega
  have hsum_le :
      (∑ j ∈ Finset.Ico C (C + L),
          (cInf (T^[j] x) - delta - badInfo (T^[j] x))) ≤
        partitionInformation mu (iteratedJoin T P J) x := by
    calc
      (∑ j ∈ Finset.Ico C (C + L),
          (cInf (T^[j] x) - delta - badInfo (T^[j] x))) ≤
          ∑ j ∈ Finset.Ico C (C + L),
            futureConditionalInformation mu T P (N - 1 - j) (T^[j] x) :=
        Finset.sum_le_sum hterm
      _ ≤ ∑ j ∈ Finset.range N,
            futureConditionalInformation mu T P (N - 1 - j) (T^[j] x) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro j _hj _hjIco
        exact futureConditionalInformation_nonneg
          mu T P (N - 1 - j) (T^[j] x)
      _ ≤ (∑ j ∈ Finset.range N,
            futureConditionalInformation mu T P (N - 1 - j) (T^[j] x)) +
          partitionInformation mu (iteratedJoin T P 1) (T^[N] x) :=
        le_add_of_nonneg_right
          (partitionInformation_nonneg mu (iteratedJoin T P 1) (T^[N] x))
      _ = partitionInformation mu (iteratedJoin T P J) x := by
        rw [← hN]
        simpa using (partitionInformation_chain_sum mu T P hchain 0 N).symm
  have hsum_eq :
      (L : ℝ) *
          (birkhoffAverage ℝ T cInf L (T^[C] x) - delta -
            birkhoffAverage ℝ T badInfo L (T^[C] x)) =
        ∑ j ∈ Finset.Ico C (C + L),
          (cInf (T^[j] x) - delta - badInfo (T^[j] x)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum]
    simp only [smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp [hL0]
    rw [show C + L - C = L by omega]
    have hcInfSum :
        (∑ j ∈ Finset.range L, cInf (T^[j] (T^[C] x))) =
          ∑ j ∈ Finset.range L, cInf (T^[C + j] x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply congrArg cInf
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have hbadSum :
        (∑ j ∈ Finset.range L, badInfo (T^[j] (T^[C] x))) =
          ∑ j ∈ Finset.range L, badInfo (T^[C + j] x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply congrArg badInfo
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [hcInfSum, hbadSum]
    ring
  have hdenom : (0 : ℝ) < (L + 2 * (N0 + 1) : ℕ) := by positivity
  change ((L : ℝ) / (L + 2 * (N0 + 1) : ℕ)) *
      (birkhoffAverage ℝ T cInf L (T^[C] x) - delta -
        birkhoffAverage ℝ T badInfo L (T^[C] x)) ≤
    partitionInformation mu (iteratedJoin T P J) x /
      (L + 2 * (N0 + 1) : ℕ)
  rw [show ((L : ℝ) / (L + 2 * (N0 + 1) : ℕ)) *
      (birkhoffAverage ℝ T cInf L (T^[C] x) - delta -
        birkhoffAverage ℝ T badInfo L (T^[C] x)) =
      ((L : ℝ) *
        (birkhoffAverage ℝ T cInf L (T^[C] x) - delta -
          birkhoffAverage ℝ T badInfo L (T^[C] x))) /
        (L + 2 * (N0 + 1) : ℕ) by ring]
  apply (div_le_div_iff_of_pos_right hdenom).2
  rw [hsum_eq]
  simpa [J, C] using hsum_le

lemma ae_eventually_balanced_centeredInformation_div_gt_entropy_sub
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ L in atTop,
      entropyW mu T P - epsilon <
        partitionInformation mu
            (centeredJoin T T_inv P
              (balancedBackward lam1 lam2 L)
              (balancedForward lam1 lam2 L)) x / L := by
  let delta : ℝ := epsilon / 8
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  have hbadTend := tendsto_integral_futureInformationBadSet
    mu T hT.measurable P hP.measurable hdelta
  have hbadEventually : ∀ᶠ N in atTop,
      (∫ x,
        (futureInformationBadSet mu T P hT.measurable hP.measurable delta N).indicator
          (futureConditionalInformationLimit
            mu T hT.measurable P hP.measurable) x ∂mu) < delta :=
    (tendsto_order.1 hbadTend).2 delta hdelta
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hbadEventually
  let C := N0 + 1
  let cInf := futureConditionalInformationLimit mu T hT.measurable P hP.measurable
  let badSet := futureInformationBadSet
    mu T P hT.measurable hP.measurable delta N0
  let badInfo := badSet.indicator cInf
  have hbadIntegral : (∫ x, badInfo x ∂mu) < delta := hN0 N0 le_rfl
  have hcMeas : Measurable cInf :=
    measurable_futureConditionalInformationLimit
      mu T hT.measurable P hP.measurable
  have hcInt : Integrable cInf mu :=
    integrable_futureConditionalInformationLimit
      mu T hT.measurable P hP.measurable
  have hbadMeas : MeasurableSet badSet :=
    measurableSet_futureInformationBadSet
      mu T P hT.measurable hP.measurable delta N0
  have hbadInfoMeas : Measurable badInfo := hcMeas.indicator hbadMeas
  have hbadInfoInt : Integrable badInfo mu := hcInt.indicator hbadMeas
  have hcAverage := ae_tendsto_birkhoffAverage_balanced_trimmed
    mu T T_inv hT_right hT hT_inv hErg hErg_inv cInf hcMeas hcInt
      hlam1 hlam2 C
  have hbadAverage := ae_tendsto_birkhoffAverage_balanced_trimmed
    mu T T_inv hT_right hT hT_inv hErg hErg_inv
      badInfo hbadInfoMeas hbadInfoInt hlam1 hlam2 C
  have hchain := ae_all_partitionInformation_succ_chain_iterate
    mu T hT P hP
  have hchainBackward : ∀ᵐ x ∂mu, ∀ m k n,
      partitionInformation mu (iteratedJoin T P (n + 2))
          (T^[k] (T_inv^[m] x)) =
        futureConditionalInformation mu T P n (T^[k] (T_inv^[m] x)) +
          partitionInformation mu (iteratedJoin T P (n + 1))
            (T^[k + 1] (T_inv^[m] x)) := by
    rw [ae_all_iff]
    intro m
    exact (hT_inv.iterate m).quasiMeasurePreserving.tendsto_ae hchain
  filter_upwards [hcAverage, hbadAverage, hchainBackward] with
      x hcx hbadx hxchain
  have hCpos : 0 < C := by simp [C]
  have hCdiv : Tendsto (fun L : ℕ => ((2 * C : ℕ) : ℝ) / L)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat ((2 * C : ℕ) : ℝ)
  have hratioBase : Tendsto
      (fun L : ℕ => 1 - ((2 * C : ℕ) : ℝ) / L)
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.sub hCdiv
  have hratio : Tendsto
      (fun L : ℕ => ((L - 2 * C : ℕ) : ℝ) / L)
      atTop (nhds 1) := by
    apply hratioBase.congr'
    filter_upwards [eventually_gt_atTop (2 * C)] with L hLC
    rw [Nat.cast_sub hLC.le]
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hLC).ne'
    field_simp [hL0]
  have hinside : Tendsto
      (fun L =>
        birkhoffAverage ℝ T cInf
            (trimmedBalancedBackward lam1 lam2 C L +
              trimmedBalancedForward lam1 lam2 C L)
            (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x) - delta -
          birkhoffAverage ℝ T badInfo
            (trimmedBalancedBackward lam1 lam2 C L +
              trimmedBalancedForward lam1 lam2 C L)
            (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x))
      atTop (nhds ((∫ y, cInf y ∂mu) - delta - ∫ y, badInfo y ∂mu)) :=
    hcx.sub tendsto_const_nhds |>.sub hbadx
  have hrhs : Tendsto
      (fun L : ℕ => ((L - 2 * C : ℕ) : ℝ) / L *
        (birkhoffAverage ℝ T cInf
            (trimmedBalancedBackward lam1 lam2 C L +
              trimmedBalancedForward lam1 lam2 C L)
            (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x) - delta -
          birkhoffAverage ℝ T badInfo
            (trimmedBalancedBackward lam1 lam2 C L +
              trimmedBalancedForward lam1 lam2 C L)
            (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x)))
      atTop
      (nhds (1 * ((∫ y, cInf y ∂mu) - delta - ∫ y, badInfo y ∂mu))) :=
    hratio.mul hinside
  have hcIntegral : (∫ y, cInf y ∂mu) = entropyW mu T P :=
    integral_futureConditionalInformationLimit_eq_entropyW
      mu T T_inv hT_right hT P hP
  have hlimitLower : entropyW mu T P - epsilon <
      1 * ((∫ y, cInf y ∂mu) - delta - ∫ y, badInfo y ∂mu) := by
    rw [hcIntegral]
    dsimp [delta] at hbadIntegral ⊢
    linarith
  have hrhsEventually : ∀ᶠ L : ℕ in atTop,
      entropyW mu T P - epsilon <
        ((L - 2 * C : ℕ) : ℝ) / L *
          (birkhoffAverage ℝ T cInf
              (trimmedBalancedBackward lam1 lam2 C L +
                trimmedBalancedForward lam1 lam2 C L)
              (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x) - delta -
            birkhoffAverage ℝ T badInfo
              (trimmedBalancedBackward lam1 lam2 C L +
                trimmedBalancedForward lam1 lam2 C L)
              (T_inv^[trimmedBalancedBackward lam1 lam2 C L] x)) :=
    (tendsto_order.1 hrhs).1 _ hlimitLower
  have hbackLarge := (tendsto_balancedBackward_atTop hlam1 hlam2).eventually
    (eventually_ge_atTop C)
  have hforwardLarge := (tendsto_balancedForward_atTop hlam1 hlam2).eventually
    (eventually_ge_atTop C)
  filter_upwards
      [hrhsEventually, hbackLarge, hforwardLarge,
        eventually_gt_atTop (2 * C)] with L hrhsLower hCback hCforward hLC
  let m := balancedBackward lam1 lam2 L
  let n := balancedForward lam1 lam2 L
  let inner := L - 2 * C
  have hsplit : m + n = L := balancedBackward_add_balancedForward hlam1 hlam2 L
  have hinnerSplit : (m - C) + (n - C) = inner := by
    dsimp [m, n, inner]
    omega
  have hinnerPos : 0 < inner := by
    dsimp [inner]
    omega
  let y := T_inv^[m] x
  have hychain : ∀ k r,
      partitionInformation mu (iteratedJoin T P (r + 2)) (T^[k] y) =
        futureConditionalInformation mu T P r (T^[k] y) +
          partitionInformation mu (iteratedJoin T P (r + 1))
            (T^[k + 1] y) := by
    intro k r
    exact hxchain m k r
  have hgeom := partitionInformation_lower_centeredBirkhoffAverage
    mu T P hT.measurable hP.measurable hychain hdelta.le N0 hinnerPos
  have hbase : T^[C] y = T_inv^[m - C] x := by
    exact iterate_before_inverse_cancel hT_right hCback x
  have hjoinLength : inner + 2 * (N0 + 1) = L := by
    dsimp [inner, C]
    omega
  have hgeom' :
      ((inner : ℝ) / L) *
          (birkhoffAverage ℝ T cInf inner (T_inv^[m - C] x) - delta -
            birkhoffAverage ℝ T badInfo inner (T_inv^[m - C] x)) ≤
        partitionInformation mu (iteratedJoin T P L) y / L := by
    simpa [cInf, badInfo, badSet, C, y, hbase, hjoinLength] using hgeom
  have hrhsLower' : entropyW mu T P - epsilon <
      ((inner : ℝ) / L) *
        (birkhoffAverage ℝ T cInf inner (T_inv^[m - C] x) - delta -
          birkhoffAverage ℝ T badInfo inner (T_inv^[m - C] x)) := by
    simpa [trimmedBalancedBackward, trimmedBalancedForward,
      m, n, inner, hinnerSplit] using hrhsLower
  have hfinal := hrhsLower'.trans_le hgeom'
  rw [partitionInformation_centeredJoin
    mu T T_inv hT_left hT hT_inv P hP m n x]
  simpa [hsplit, y] using hfinal

lemma ae_eventually_mem_balanced_centered_entropy_lightAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hepsilon : 0 < epsilon) :
    ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      x ∈ ⋃ A ∈ lightAtoms mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L))
          ((entropyW mu T P - epsilon) * L), A := by
  have hlower := ae_eventually_balanced_centeredInformation_div_gt_entropy_sub
    mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv P hP
      hlam1 hlam2 hepsilon
  have hthreshold : ∀ᵐ x ∂mu, ∀ L : ℕ,
      (x ∈ ⋃ A ∈ lightAtoms mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L))
          ((entropyW mu T P - epsilon) * L), A ↔
        (entropyW mu T P - epsilon) * L <
          partitionInformation mu
            (centeredJoin T T_inv P
              (balancedBackward lam1 lam2 L)
              (balancedForward lam1 lam2 L)) x) := by
    apply ae_all_iff.2
    intro L
    exact mem_iUnion_lightAtoms_iff_information_gt_ae
      mu
      (centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L)
        (balancedForward lam1 lam2 L))
      (isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP
        (balancedBackward lam1 lam2 L)
        (balancedForward lam1 lam2 L))
      ((entropyW mu T P - epsilon) * L)
  filter_upwards [hlower, hthreshold] with x hxlower hxthreshold
  filter_upwards [hxlower, eventually_gt_atTop 0] with L hL hLpos
  apply (hxthreshold L).2
  have hLposReal : (0 : ℝ) < L := by exact_mod_cast hLpos
  exact (lt_div_iff₀ hLposReal).mp hL

end Submission.Helpers
