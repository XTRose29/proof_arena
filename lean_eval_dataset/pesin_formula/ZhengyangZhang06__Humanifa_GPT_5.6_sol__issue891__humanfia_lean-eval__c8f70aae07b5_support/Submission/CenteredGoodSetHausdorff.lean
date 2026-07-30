import Submission.EntropyRateTail
import Submission.CenteredShannonMcMillanEventually

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma dimMeasure_le_of_balanced_centered_good_diameter
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
    (good : ℕ → Set EucPlane) (hgood_measurable : ∀ L, MeasurableSet (good L))
    (hgood_full : mu (liminf good atTop)ᶜ = 0)
    {R delta : ℝ} (hR : 0 < R) (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (d : NNReal)
    (hrate : entropyW mu T P / delta < R * (d : ℝ))
    (hdiam : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      Metric.ediam (A ∩ good L) ≤ ENNReal.ofReal (Real.exp (-R * L))) :
    dimMeasure mu ≤ d := by
  let Q : ℕ → Finset (Set EucPlane) := fun L => centeredJoin T T_inv P
    (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L)
  let r : ℕ → ℝ≥0∞ := fun L => ENNReal.ofReal (Real.exp (-R * L))
  have hQ (L : ℕ) : IsMeasurablePartition mu (Q L) := by
    exact isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP _ _
  have hr_mono : Antitone r := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hab_real : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hexponent : Tendsto (fun L : ℕ => -R * (L : ℝ)) atTop atBot := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (neg_neg_of_pos hR)
  have hr : Tendsto r atTop (nhds 0) := by
    have hexp := Real.tendsto_exp_atBot.comp hexponent
    have hofReal := ENNReal.tendsto_ofReal hexp
    simpa [r] using hofReal
  let u : ℕ → ℝ := fun L => partitionEntropy mu (iteratedJoin T P L)
  have hu : Tendsto (fun L => u L / L) atTop (nhds (entropyW mu T P)) := by
    simpa [u] using tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT P hP
  obtain ⟨C, hC, hcost⟩ := exists_exponential_entropy_tail_bound
    u hu hdelta_pos d hrate
  apply dimMeasure_le_of_partition_entropy_limsup_covers_on_goodSets
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hErg
      Q hQ hdelta_pos hdelta_lt good hgood_measurable hgood_full
      r hr_mono hr (fun L A hA => hdiam L A hA) d C hC
  intro N
  have hentropy (L : ℕ) : partitionEntropy mu (Q L) = u L := by
    rw [partitionEntropy_centeredJoin mu T T_inv hT_left hT hT_inv P hP]
    rw [balancedBackward_add_balancedForward hlam1 hlam2]
  simpa [r, hentropy] using hcost N

lemma dimMeasure_mul_rate_le_entropyW_of_balanced_centered_good_diameter
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
    (hdim_top : dimMeasure mu ≠ ⊤)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (good : ℕ → Set EucPlane) (hgood_measurable : ∀ L, MeasurableSet (good L))
    (hgood_full : mu (liminf good atTop)ᶜ = 0)
    {R : ℝ} (hR : 0 < R)
    (hdiam : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      Metric.ediam (A ∩ good L) ≤ ENNReal.ofReal (Real.exp (-R * L))) :
    (dimMeasure mu).toReal * R ≤ entropyW mu T P := by
  have hu := tendsto_partitionEntropy_iteratedJoin_div_entropyW
    mu T T_inv hT_right hT P hP
  have hentropy_nonneg : 0 ≤ entropyW mu T P := by
    apply ge_of_tendsto' hu
    intro n
    exact div_nonneg (partitionEntropy_nonneg mu _) (Nat.cast_nonneg n)
  apply le_of_not_gt
  intro hlt
  let D := (dimMeasure mu).toReal
  let h := entropyW mu T P
  have hlt' : h < D * R := by simpa [h, D] using hlt
  have hD_nonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hD_pos : 0 < D := by
    apply lt_of_le_of_ne hD_nonneg
    intro hDzero
    have hDzero' : D = 0 := hDzero.symm
    rw [hDzero', zero_mul] at hlt'
    exact (not_lt_of_ge hentropy_nonneg) hlt'
  have hDR_pos : 0 < D * R := mul_pos hD_pos hR
  let ratio := h / (D * R)
  have hratio_nonneg : 0 ≤ ratio := div_nonneg hentropy_nonneg hDR_pos.le
  have hratio_lt_one : ratio < 1 := (div_lt_one hDR_pos).2 (by
    simpa [D, h] using hlt)
  let delta := (ratio + 1) / 2
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    linarith
  have hdelta_lt : delta < 1 := by
    dsimp [delta]
    linarith
  have hratio_delta : ratio < delta := by
    dsimp [delta]
    linarith
  have hh_delta : h / delta < D * R := by
    have hmul : h < delta * (D * R) := by
      have := mul_lt_mul_of_pos_right hratio_delta hDR_pos
      dsimp [ratio] at this
      exact (div_mul_cancel₀ h hDR_pos.ne').symm ▸ this
    exact (div_lt_iff₀ hdelta_pos).2 (by simpa [mul_comm] using hmul)
  let q := h / (delta * R)
  have hq_lt_D : q < D := by
    apply (div_lt_iff₀ (mul_pos hdelta_pos hR)).2
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using
      (div_lt_iff₀ hdelta_pos).mp hh_delta
  have hq_nonneg : 0 ≤ q := div_nonneg hentropy_nonneg
    (mul_nonneg hdelta_pos.le hR.le)
  let dReal := (q + D) / 2
  have hdReal_nonneg : 0 ≤ dReal := by
    dsimp [dReal]
    linarith
  let d : NNReal := ⟨dReal, hdReal_nonneg⟩
  have hd_coe : (d : ℝ) = dReal := rfl
  have hdReal_lt_D : (d : ℝ) < D := by
    rw [hd_coe]
    dsimp [dReal]
    linarith
  have hrate : entropyW mu T P / delta < R * (d : ℝ) := by
    change h / delta < R * (d : ℝ)
    have hq_lt_d : q < (d : ℝ) := by
      rw [hd_coe]
      dsimp [dReal]
      linarith
    have := mul_lt_mul_of_pos_left hq_lt_d hR
    dsimp [q] at this
    field_simp [hR.ne', hdelta_pos.ne'] at this ⊢
    nlinarith
  have hd_le := dimMeasure_le_of_balanced_centered_good_diameter
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hT hT_inv hErg
      P hP hlam1 hlam2 good hgood_measurable hgood_full hR
      hdelta_pos hdelta_lt d hrate hdiam
  have hD_le_d : D ≤ (d : ℝ) := by
    have := (ENNReal.toReal_le_toReal hdim_top ENNReal.coe_ne_top).2 hd_le
    simpa [D] using this
  exact (not_lt_of_ge hD_le_d) hdReal_lt_D

end Submission.Helpers
