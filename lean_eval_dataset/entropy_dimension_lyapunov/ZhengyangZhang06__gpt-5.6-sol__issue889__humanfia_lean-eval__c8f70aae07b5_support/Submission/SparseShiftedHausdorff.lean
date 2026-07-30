import Submission.SparseUniformCover

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

/-- A shifted version of the balanced multiplicity covering criterion.  The
shift lets all quantitative estimates start beyond one common finite
threshold without changing their asymptotic entropy rate. -/
lemma dimMeasure_le_of_shifted_balanced_uniform_piece_covers
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
    (L0 : ℕ)
    (good : ℕ → Set EucPlane)
    (hgood_measurable : ∀ n, MeasurableSet (good n))
    {gamma : ℝ} (hgood_compl : ∀ n, mu.real (good n)ᶜ ≤ gamma)
    (pieces : ℕ → Set EucPlane → Finset (Set EucPlane))
    (M : ℕ → ℕ) {kappa R delta : ℝ}
    (hM : ∀ n, (M n : ℝ) ≤ Real.exp (kappa * (n + L0)))
    (hpieces_card : ∀ n A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 (n + L0))
          (balancedForward lam1 lam2 (n + L0)) →
        (pieces n A).card ≤ M n)
    (hpieces_measurable : ∀ n A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 (n + L0))
          (balancedForward lam1 lam2 (n + L0)) →
        ∀ B ∈ pieces n A, MeasurableSet B)
    (hpieces_cover : ∀ n A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 (n + L0))
          (balancedForward lam1 lam2 (n + L0)) →
        A ∩ good n ⊆ ⋃ B ∈ pieces n A, B)
    (hdiam : ∀ n A,
      A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 (n + L0))
          (balancedForward lam1 lam2 (n + L0)) →
        ∀ B ∈ pieces n A,
          Metric.ediam B ≤ ENNReal.ofReal (Real.exp (-R * n)))
    (hR : 0 < R) (hdelta_pos : 0 < delta)
    (hdelta_gamma : delta + gamma < 1)
    (d : NNReal)
    (hrate : entropyW mu T P / delta + kappa < R * (d : ℝ)) :
    dimMeasure mu ≤ d := by
  let Q : ℕ → Finset (Set EucPlane) := fun n =>
    centeredJoin T T_inv P
      (balancedBackward lam1 lam2 (n + L0))
      (balancedForward lam1 lam2 (n + L0))
  let r : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (-R * n))
  have hQ (n : ℕ) : IsMeasurablePartition mu (Q n) :=
    isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP _ _
  have hr_mono : Antitone r := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hab_real : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hexponent : Tendsto (fun n : ℕ => -R * (n : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (neg_neg_of_pos hR)
  have hr : Tendsto r atTop (nhds 0) := by
    have hexp := Real.tendsto_exp_atBot.comp hexponent
    simpa [r] using ENNReal.tendsto_ofReal hexp
  let u : ℕ → ℝ := fun n =>
    partitionEntropy mu (iteratedJoin T P (n + L0)) +
      delta * kappa * (n + L0)
  have hshift : Tendsto (fun n : ℕ => n + L0) atTop atTop :=
    Filter.tendsto_add_atTop_nat L0
  have hbase : Tendsto
      (fun n =>
        partitionEntropy mu (iteratedJoin T P (n + L0)) / (n + L0))
      atTop (nhds (entropyW mu T P)) := by
    simpa [Function.comp_def] using
      (tendsto_partitionEntropy_iteratedJoin_div_entropyW
        mu T T_inv hT_right hT P hP).comp hshift
  have hratio : Tendsto
      (fun n : ℕ => ((n + L0 : ℕ) : ℝ) / n)
      atTop (nhds 1) := by
    have hzero := tendsto_const_div_atTop_nhds_zero_nat (L0 : ℝ)
    have hadd : Tendsto
        (fun n : ℕ => (1 : ℝ) + (L0 : ℝ) / n)
        atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add hzero
    have hadd' : Tendsto
        (fun n : ℕ => (1 : ℝ) + (L0 : ℝ) / n)
        atTop (nhds 1) := by
      simpa using hadd
    apply hadd'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have hpart : Tendsto
      (fun n => partitionEntropy mu (iteratedJoin T P (n + L0)) / n)
      atTop (nhds (entropyW mu T P)) := by
    have hmul := hbase.mul hratio
    have hmul' : Tendsto
        (fun n =>
          (partitionEntropy mu (iteratedJoin T P (n + L0)) /
            (n + L0)) * (((n + L0 : ℕ) : ℝ) / n))
        atTop (nhds (entropyW mu T P)) := by
      simpa using hmul
    apply hmul'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnL0 : (0 : ℝ) < (n + L0 : ℕ) := by positivity
    push_cast
    field_simp [hn0, hnL0.ne']
  have hlinear : Tendsto
      (fun n : ℕ => (delta * kappa * (n + L0)) / n)
      atTop (nhds (delta * kappa)) := by
    have hconst : Tendsto (fun _ : ℕ => delta * kappa)
        atTop (nhds (delta * kappa)) :=
      tendsto_const_nhds
    have hmul := hconst.mul hratio
    have hmul' : Tendsto
        (fun n : ℕ => (delta * kappa) *
          (((n + L0 : ℕ) : ℝ) / n))
        atTop (nhds (delta * kappa)) := by
      simpa using hmul
    apply hmul'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have hu : Tendsto (fun n => u n / n)
      atTop (nhds (entropyW mu T P + delta * kappa)) := by
    apply (hpart.add hlinear).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp [u]
    field_simp [hn0]
  have hrate' :
      (entropyW mu T P + delta * kappa) / delta <
        R * (d : ℝ) := by
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
      pieces M (fun n A hA => hpieces_card n A hA)
      (fun n A hA => hpieces_measurable n A hA)
      (fun n A hA => hpieces_cover n A hA)
      r hr_mono hr (fun n A hA => hdiam n A hA) d C hC
  intro N
  refine (ENNReal.tsum_le_tsum fun n => ?_).trans (hcost N)
  have hM_ennreal : (M n.1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (kappa * (n.1 + L0))) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (hM n.1)
  have hentropy :
      partitionEntropy mu (Q n.1) =
        partitionEntropy mu (iteratedJoin T P (n.1 + L0)) := by
    rw [partitionEntropy_centeredJoin
      mu T T_inv hT_left hT hT_inv P hP]
    rw [balancedBackward_add_balancedForward hlam1 hlam2]
  have hrewrite :
      ENNReal.ofReal
            (Real.exp (partitionEntropy mu (Q n.1) / delta + 1)) *
          (M n.1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (u n.1 / delta + 1)) := by
    calc
      ENNReal.ofReal
            (Real.exp (partitionEntropy mu (Q n.1) / delta + 1)) *
          (M n.1 : ℝ≥0∞) ≤
          ENNReal.ofReal
              (Real.exp (partitionEntropy mu (Q n.1) / delta + 1)) *
            ENNReal.ofReal
              (Real.exp (kappa * (n.1 + L0))) := by
        gcongr
      _ = ENNReal.ofReal (Real.exp (u n.1 / delta + 1)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        rw [← Real.exp_add]
        apply congrArg ENNReal.ofReal
        apply congrArg Real.exp
        rw [hentropy]
        dsimp [u]
        field_simp [hdelta_pos.ne']
        ring
  exact mul_le_mul_left hrewrite _

lemma card_gridPatterns_le_exp
    {H L : ℕ} (hH : 0 < H) (hHL : H ≤ L) :
    ((gridPatterns H L).card : ℝ) ≤
      Real.exp ((2 * Real.log 2 / H) * L) := by
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hHLreal : (H : ℝ) ≤ L := by exact_mod_cast hHL
  have hratio_one : (1 : ℝ) ≤ (L : ℝ) / H :=
    (le_div_iff₀ hHreal).2 (by simpa using hHLreal)
  have hgrid :
      ((gridIndexSet H L).card : ℝ) ≤ 2 * (L : ℝ) / H := by
    calc
      ((gridIndexSet H L).card : ℝ) ≤ (L / H + 1 : ℕ) := by
        exact_mod_cast card_gridIndexSet_le_div_add_one hH
      _ = ((L / H : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ (L : ℝ) / H + 1 := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ 2 * (L : ℝ) / H := by
        rw [show 2 * (L : ℝ) / H = 2 * ((L : ℝ) / H) by ring]
        linarith
  have hlog_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [card_gridPatterns, Nat.cast_pow]
  calc
    (2 : ℝ) ^ (gridIndexSet H L).card =
        (Real.exp (Real.log 2)) ^ (gridIndexSet H L).card := by
      congr 1
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp
        ((gridIndexSet H L).card * Real.log 2) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp
        (Real.log 2 * (gridIndexSet H L).card) := by
      congr 1
      ring
    _ ≤ Real.exp (Real.log 2 * (2 * (L : ℝ) / H)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hgrid hlog_nonneg
    _ = Real.exp ((2 * Real.log 2 / H) * L) := by
      congr 1
      field_simp

lemma pow_sparseBadBudget_le_exp
    {Fcard H D L : ℕ} {q : ℝ}
    (hH : 0 < H) (hFcard : 0 < Fcard) (hq : 0 < q)
    (habsorb : (H : ℝ) * (q + 1) ≤ q * L) :
    ((Fcard ^ (4 * D * H * sparseBadBudget q H L) : ℕ) : ℝ) ≤
      Real.exp ((8 * D * q * Real.log Fcard) * L) := by
  have hq_nonneg : 0 ≤ q := hq.le
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hdiv :
      (H : ℝ) * ((L / H : ℕ) : ℝ) ≤ L := by
    exact_mod_cast Nat.mul_div_le L H
  have hdivq :
      q * ((H : ℝ) * ((L / H : ℕ) : ℝ)) ≤ q * L :=
    mul_le_mul_of_nonneg_left hdiv hq_nonneg
  have hbudget :
      (H : ℝ) * (sparseBadBudget q H L : ℕ) ≤ 2 * q * L := by
    have hceil := Nat.ceil_lt_add_one
      (mul_nonneg hq_nonneg (by positivity) :
        0 ≤ q * ((((L / H + 1 : ℕ) : ℝ))))
    apply le_of_lt
    calc
      (H : ℝ) * (sparseBadBudget q H L : ℕ) <
          (H : ℝ) *
            (q * ((((L / H + 1 : ℕ) : ℝ))) + 1) := by
        apply mul_lt_mul_of_pos_left _ hHreal
        simpa [sparseBadBudget] using hceil
      _ = q * ((H : ℝ) * ((L / H : ℕ) : ℝ)) +
          (H : ℝ) * (q + 1) := by
        push_cast
        ring
      _ ≤ q * L + q * L := add_le_add hdivq habsorb
      _ = 2 * q * L := by ring
  have hexponent :
      (4 : ℝ) * D * H * sparseBadBudget q H L ≤
        8 * D * q * L := by
    calc
      (4 : ℝ) * D * H * sparseBadBudget q H L =
          (4 * D) * ((H : ℝ) *
            (sparseBadBudget q H L : ℕ)) := by
        ring
      _ ≤ (4 * D) * (2 * q * L) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = 8 * D * q * L := by ring
  have hFreal : (0 : ℝ) < Fcard := by exact_mod_cast hFcard
  have hlog_nonneg : 0 ≤ Real.log Fcard :=
    Real.log_nonneg (by exact_mod_cast hFcard)
  rw [Nat.cast_pow]
  calc
    (Fcard : ℝ) ^ (4 * D * H * sparseBadBudget q H L) =
        (Real.exp (Real.log Fcard)) ^
          (4 * D * H * sparseBadBudget q H L) := by
      congr 1
      rw [Real.exp_log hFreal]
    _ = Real.exp
        ((4 * D * H * sparseBadBudget q H L) *
          Real.log Fcard) := by
      rw [← Real.exp_nat_mul]
      push_cast
      rfl
    _ = Real.exp (Real.log Fcard *
        (4 * D * H * sparseBadBudget q H L)) := by
      congr 1
      ring
    _ ≤ Real.exp (Real.log Fcard * (8 * D * q * L)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hexponent hlog_nonneg
    _ = Real.exp ((8 * D * q * Real.log Fcard) * L) := by
      congr 1
      ring

lemma sparsePieceMultiplicity_le_exp
    {Fcard H D L : ℕ} {q : ℝ}
    (hH : 0 < H) (hHL : H ≤ L)
    (hFcard : 0 < Fcard) (hq : 0 < q)
    (habsorb : (H : ℝ) * (q + 1) ≤ q * L) :
    (sparsePieceMultiplicity Fcard H D q L : ℝ) ≤
      Real.exp
        ((2 * Real.log 2 / H +
          8 * D * q * Real.log Fcard) * L) := by
  have hpatterns := card_gridPatterns_le_exp hH hHL
  have hlabels := pow_sparseBadBudget_le_exp
    (Fcard := Fcard) (H := H) (D := D) (L := L)
      hH hFcard hq habsorb
  calc
    (sparsePieceMultiplicity Fcard H D q L : ℝ) =
        ((gridPatterns H L).card : ℝ) *
          ((Fcard ^ (4 * D * H * sparseBadBudget q H L) : ℕ) : ℝ) := by
      simp [sparsePieceMultiplicity, Nat.cast_mul]
    _ ≤ Real.exp ((2 * Real.log 2 / H) * L) *
        Real.exp ((8 * D * q * Real.log Fcard) * L) := by
      gcongr
    _ = Real.exp
        ((2 * Real.log 2 / H +
          8 * D * q * Real.log Fcard) * L) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Submission.Helpers
