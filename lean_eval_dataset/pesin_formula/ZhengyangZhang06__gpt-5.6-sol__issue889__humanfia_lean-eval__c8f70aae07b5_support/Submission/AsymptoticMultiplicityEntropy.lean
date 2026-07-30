import Submission.UniformMultiplicityHausdorff

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

/-- Uniform good-set covers whose multiplicity has logarithmic rate `kappa`
force the entropy-plus-multiplicity lower bound.  This version accepts an
arbitrary sequence of measurable partitions, which permits discarding a
finite initial range of orbit lengths. -/
lemma dimMeasure_mul_rate_le_entropy_add_of_asymptotic_piece_covers
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    (hdim_top : dimMeasure mu ≠ ⊤)
    {entropy kappa R : ℝ} (hkappa : 0 ≤ kappa) (hR : 0 < R)
    (hdata : ∀ gamma : ℝ, 0 < gamma →
      ∃ P : ℕ → Finset (Set EucPlane),
      ∃ good : ℕ → Set EucPlane,
      ∃ pieces : ℕ → Set EucPlane → Finset (Set EucPlane),
      ∃ M : ℕ → ℕ,
      ∃ growth : ℕ → ℝ,
      ∃ partitionRate : ℝ,
        (∀ n, IsMeasurablePartition mu (P n)) ∧
        Tendsto
          (fun n : ℕ => partitionEntropy mu (P n) / n)
          atTop (nhds partitionRate) ∧
        partitionRate ≤ entropy ∧
        (∀ n, MeasurableSet (good n)) ∧
        (∀ n, mu.real (good n)ᶜ ≤ gamma) ∧
        (∀ n A, A ∈ P n → (pieces n A).card ≤ M n) ∧
        (∀ n A, A ∈ P n →
          ∀ B ∈ pieces n A, MeasurableSet B) ∧
        (∀ n A, A ∈ P n →
          A ∩ good n ⊆ ⋃ B ∈ pieces n A, B) ∧
        (∀ n A, A ∈ P n →
          ∀ B ∈ pieces n A,
            Metric.ediam B ≤
              ENNReal.ofReal (Real.exp (-R * n))) ∧
        (∀ n, (M n : ℝ) ≤ Real.exp (growth n)) ∧
        Tendsto (fun n : ℕ => growth n / n) atTop (nhds kappa)) :
    (dimMeasure mu).toReal * R ≤ entropy + kappa := by
  let D := (dimMeasure mu).toReal
  have hD_nonneg : 0 ≤ D := ENNReal.toReal_nonneg
  apply le_of_not_gt
  intro hcontra
  have hsum_lt : entropy + kappa < D * R := by
    simpa [D] using hcontra
  have hD_pos : 0 < D := by
    apply lt_of_le_of_ne hD_nonneg
    intro hDzero
    have hDzero' : D = 0 := hDzero.symm
    rw [hDzero', zero_mul] at hsum_lt
    have hentropy_nonneg : 0 ≤ entropy := by
      obtain ⟨P, _good, _pieces, _M, _growth, partitionRate,
          _hP, hpartitionRate, hpartitionRate_le, _rest⟩ :=
        hdata (1 / 2) (by norm_num)
      exact (ge_of_tendsto' hpartitionRate (fun n =>
        div_nonneg (partitionEntropy_nonneg mu _) (Nat.cast_nonneg n))).trans
          hpartitionRate_le
    linarith
  have hR_nonneg : 0 ≤ R := hR.le
  have hbase_lt : (entropy + kappa) / R < D :=
    (div_lt_iff₀ hR).2 (by simpa [mul_comm] using hsum_lt)
  let dReal := ((entropy + kappa) / R + D) / 2
  have hdReal_nonneg : 0 ≤ dReal := by
    have hentropy_nonneg : 0 ≤ entropy := by
      obtain ⟨P, _good, _pieces, _M, _growth, partitionRate,
          _hP, hpartitionRate, hpartitionRate_le, _rest⟩ :=
        hdata (1 / 2) (by norm_num)
      exact (ge_of_tendsto' hpartitionRate (fun n =>
        div_nonneg (partitionEntropy_nonneg mu _) (Nat.cast_nonneg n))).trans
          hpartitionRate_le
    dsimp [dReal]
    have : 0 ≤ (entropy + kappa) / R :=
      div_nonneg (add_nonneg hentropy_nonneg hkappa) hR_nonneg
    linarith
  let d : NNReal := ⟨dReal, hdReal_nonneg⟩
  have hd_lt_D : (d : ℝ) < D := by
    change dReal < D
    dsimp [dReal]
    linarith
  have hgap : 0 < R * (d : ℝ) - kappa - entropy := by
    have hmid : (entropy + kappa) / R < (d : ℝ) := by
      change (entropy + kappa) / R < dReal
      dsimp [dReal]
      linarith
    have := mul_lt_mul_of_pos_left hmid hR
    field_simp [hR.ne'] at this
    linarith
  let gap := R * (d : ℝ) - kappa - entropy
  let delta : ℝ :=
    if entropy = 0 then 1 / 2 else entropy / (entropy + gap / 2)
  have hentropy_nonneg : 0 ≤ entropy := by
    obtain ⟨P, _good, _pieces, _M, _growth, partitionRate,
        _hP, hpartitionRate, hpartitionRate_le, _rest⟩ :=
      hdata (1 / 2) (by norm_num)
    exact (ge_of_tendsto' hpartitionRate (fun n =>
      div_nonneg (partitionEntropy_nonneg mu _) (Nat.cast_nonneg n))).trans
        hpartitionRate_le
  have hdelta_pos : 0 < delta := by
    by_cases he : entropy = 0
    · simp [delta, he]
    · dsimp [delta]
      rw [if_neg he]
      exact div_pos (lt_of_le_of_ne hentropy_nonneg (Ne.symm he))
        (add_pos_of_nonneg_of_pos hentropy_nonneg
          (half_pos (by simpa [gap] using hgap)))
  have hdelta_lt : delta < 1 := by
    by_cases he : entropy = 0
    · norm_num [delta, he]
    · dsimp [delta]
      rw [if_neg he]
      apply (div_lt_one
        (add_pos_of_nonneg_of_pos hentropy_nonneg
          (half_pos (by simpa [gap] using hgap)))).2
      have : 0 < gap / 2 := half_pos (by simpa [gap] using hgap)
      linarith
  have hrate : entropy / delta + kappa < R * (d : ℝ) := by
    by_cases he : entropy = 0
    · simp [delta, he]
      simpa [gap, he] using hgap
    · have hdelta :
          delta = entropy / (entropy + gap / 2) := by
        simp [delta, he]
      have hepos : 0 < entropy :=
        lt_of_le_of_ne hentropy_nonneg (Ne.symm he)
      rw [hdelta]
      field_simp [he]
      dsimp [gap]
      linarith
  let gamma := (1 - delta) / 2
  have hgamma_pos : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hdelta_gamma : delta + gamma < 1 := by
    dsimp [gamma]
    linarith
  obtain ⟨P, good, pieces, M, growth, partitionRate, hP, hPentropy,
      hpartitionRate_le,
      hgood_measurable, hgood_compl, hpieces_card,
      hpieces_measurable, hpieces_cover, hdiam, hM, hgrowth⟩ :=
    hdata gamma hgamma_pos
  let r : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (-R * n))
  have hr_mono : Antitone r := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hab_real : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hexponent :
      Tendsto (fun n : ℕ => -R * (n : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (neg_neg_of_pos hR)
  have hr : Tendsto r atTop (nhds 0) := by
    have hexp := Real.tendsto_exp_atBot.comp hexponent
    simpa [r] using ENNReal.tendsto_ofReal hexp
  let u : ℕ → ℝ := fun n =>
    partitionEntropy mu (P n) + delta * growth n
  have hu : Tendsto (fun n : ℕ => u n / n)
      atTop (nhds (partitionRate + delta * kappa)) := by
    convert hPentropy.add (tendsto_const_nhds.mul hgrowth) using 1
    funext n
    dsimp [u]
    ring
  have hrate' :
      (partitionRate + delta * kappa) / delta < R * (d : ℝ) := by
    calc
      (partitionRate + delta * kappa) / delta =
          partitionRate / delta + kappa := by
        field_simp [hdelta_pos.ne']
      _ ≤ entropy / delta + kappa := by
        gcongr
      _ < R * (d : ℝ) := hrate
  obtain ⟨Ccost, hCcost, hcost⟩ :=
    exists_exponential_entropy_tail_bound u hu hdelta_pos d hrate'
  have hd_le : dimMeasure mu ≤ d := by
    apply
      dimMeasure_le_of_partition_entropy_limsup_piece_covers_on_uniform_goodSets
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          mu hmu_erg P hP hdelta_pos hdelta_gamma
          good hgood_measurable hgood_compl pieces M
          hpieces_card hpieces_measurable hpieces_cover
          r hr_mono hr
          (fun n A hA B hB => by simpa [r] using hdiam n A hA B hB)
          d Ccost hCcost
    intro N
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans (hcost N)
    have hM_ennreal : (M n.1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (growth n.1)) := by
      exact_mod_cast ENNReal.ofReal_le_ofReal (hM n.1)
    have hrewrite :
        ENNReal.ofReal
              (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
            (M n.1 : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.exp (u n.1 / delta + 1)) := by
      calc
        ENNReal.ofReal
              (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
            (M n.1 : ℝ≥0∞) ≤
            ENNReal.ofReal
                (Real.exp (partitionEntropy mu (P n.1) / delta + 1)) *
              ENNReal.ofReal (Real.exp (growth n.1)) := by
          gcongr
        _ = ENNReal.ofReal (Real.exp (u n.1 / delta + 1)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          rw [← Real.exp_add]
          apply congrArg ENNReal.ofReal
          apply congrArg Real.exp
          dsimp [u]
          field_simp [hdelta_pos.ne']
          ring
    exact mul_le_mul_left hrewrite _
  have hD_le_d : D ≤ (d : ℝ) := by
    have := (ENNReal.toReal_le_toReal hdim_top ENNReal.coe_ne_top).2 hd_le
    simpa [D] using this
  exact (not_lt_of_ge hD_le_d) hd_lt_D

end Submission.Helpers
