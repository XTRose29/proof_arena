import Submission.UniformGoodSetHausdorff
import Submission.CenteredDiameterBridge

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

/-- Uniformly high-measure good sets are enough for the centered entropy lower
bound; a single full-measure liminf set is not required. -/
lemma dimMeasure_mul_rate_le_entropyW_of_uniform_centered_pairwise_close
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
    {R : ℝ} (hR : 0 < R)
    (hgood : ∀ gamma : ℝ, 0 < gamma →
      ∃ good : ℕ → Set EucPlane,
        (∀ L, MeasurableSet (good L)) ∧
        (∀ L, mu.real (good L)ᶜ ≤ gamma) ∧
        ∀ L, ∀ A ∈ centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L),
          ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
            dist x y ≤ Real.exp (-R * L)) :
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
  have hratio_nonneg : 0 ≤ ratio :=
    div_nonneg hentropy_nonneg hDR_pos.le
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
  let gamma := (1 - delta) / 2
  have hgamma_pos : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hdelta_gamma : delta + gamma < 1 := by
    dsimp [gamma]
    linarith
  obtain ⟨good, hgood_measurable, hgood_compl, hpair⟩ :=
    hgood gamma hgamma_pos
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
    have hmul := mul_lt_mul_of_pos_left hq_lt_d hR
    dsimp [q] at hmul
    field_simp [hR.ne', hdelta_pos.ne'] at hmul ⊢
    nlinarith
  have hdiam :
      ∀ L, ∀ A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 L)
          (balancedForward lam1 lam2 L),
        Metric.ediam (A ∩ good L) ≤
          ENNReal.ofReal (Real.exp (-R * L)) := by
    intro L A hA
    exact ediam_inter_le_of_pairwise_dist_le (hpair L A hA)
  have hd_le := dimMeasure_le_of_balanced_centered_uniform_good_diameter
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      mu hT hT_inv hErg P hP hlam1 hlam2
      good hgood_measurable hgood_compl hR hdelta_pos hdelta_gamma
      d hrate hdiam
  have hD_le_d : D ≤ (d : ℝ) := by
    have := (ENNReal.toReal_le_toReal hdim_top ENNReal.coe_ne_top).2 hd_le
    simpa [D] using this
  exact (not_lt_of_ge hD_le_d) hdReal_lt_D

/-- A partition may depend on the requested exceptional-measure tolerance when
the final target is Kolmogorov--Sinai entropy. -/
lemma dimMeasure_mul_rate_le_kolmogorovSinaiEntropy_of_uniform_centered_pairwise_close
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu)
    (hdim_top : dimMeasure mu ≠ ⊤)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    {R : ℝ} (hR : 0 < R)
    (hgood : ∀ gamma : ℝ, 0 < gamma →
      ∃ P : Finset (Set EucPlane), ∃ good : ℕ → Set EucPlane,
        IsMeasurablePartition mu P ∧
        (∀ L, MeasurableSet (good L)) ∧
        (∀ L, mu.real (good L)ᶜ ≤ gamma) ∧
        (∀ L, ∀ A ∈ centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L),
          ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
            dist x y ≤ Real.exp (-R * L)) ∧
        entropyW mu T P ≤ kolmogorovSinaiEntropy mu T) :
    (dimMeasure mu).toReal * R ≤ kolmogorovSinaiEntropy mu T := by
  let D := (dimMeasure mu).toReal
  let h := kolmogorovSinaiEntropy mu T
  have hh_nonneg : 0 ≤ h := kolmogorovSinaiEntropy_nonneg mu T
  apply le_of_not_gt
  intro hlt
  have hlt' : h < D * R := by simpa [h, D] using hlt
  have hD_nonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hD_pos : 0 < D := by
    apply lt_of_le_of_ne hD_nonneg
    intro hDzero
    have hDzero' : D = 0 := hDzero.symm
    rw [hDzero', zero_mul] at hlt'
    exact (not_lt_of_ge hh_nonneg) hlt'
  have hDR_pos : 0 < D * R := mul_pos hD_pos hR
  let ratio := h / (D * R)
  have hratio_nonneg : 0 ≤ ratio := div_nonneg hh_nonneg hDR_pos.le
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
  let gamma := (1 - delta) / 2
  have hgamma_pos : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hdelta_gamma : delta + gamma < 1 := by
    dsimp [gamma]
    linarith
  obtain ⟨P, good, hP, hgood_measurable, hgood_compl,
      hpair, hP_entropy⟩ := hgood gamma hgamma_pos
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
  have hq_nonneg : 0 ≤ q :=
    div_nonneg hh_nonneg (mul_nonneg hdelta_pos.le hR.le)
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
  have hrate_h : h / delta < R * (d : ℝ) := by
    have hq_lt_d : q < (d : ℝ) := by
      rw [hd_coe]
      dsimp [dReal]
      linarith
    have hmul := mul_lt_mul_of_pos_left hq_lt_d hR
    dsimp [q] at hmul
    field_simp [hR.ne', hdelta_pos.ne'] at hmul ⊢
    nlinarith
  have hrate :
      entropyW mu T P / delta < R * (d : ℝ) := by
    exact ((div_le_div_iff_of_pos_right hdelta_pos).2 hP_entropy).trans_lt
      hrate_h
  have hdiam :
      ∀ L, ∀ A ∈ centeredJoin T T_inv P
          (balancedBackward lam1 lam2 L)
          (balancedForward lam1 lam2 L),
        Metric.ediam (A ∩ good L) ≤
          ENNReal.ofReal (Real.exp (-R * L)) := by
    intro L A hA
    exact ediam_inter_le_of_pairwise_dist_le (hpair L A hA)
  have hd_le := dimMeasure_le_of_balanced_centered_uniform_good_diameter
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      mu hT hT_inv hErg P hP hlam1 hlam2
      good hgood_measurable hgood_compl hR hdelta_pos hdelta_gamma
      d hrate hdiam
  have hD_le_d : D ≤ (d : ℝ) := by
    have := (ENNReal.toReal_le_toReal hdim_top ENNReal.coe_ne_top).2 hd_le
    simpa [D] using this
  exact (not_lt_of_ge hD_le_d) hdReal_lt_D

end Submission.Helpers
