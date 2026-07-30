import Submission.Endpoint
import Submission.FejerLaplace
import Submission.Oscillation
import Submission.ResidueCertificate

open Complex Filter MeasureTheory Metric Real Set Topology

namespace Submission.BoundaryOscillation

open Submission.Analytic Submission.Endpoint Submission.FejerLaplace
open Submission.Helpers Submission.Oscillation Submission.PrimeSeries
open Submission.ResidueCertificate Submission.SignChange
open Submission.ZeroDensity Submission.ZeroMass

noncomputable def boundaryWeight (R gamma : ℝ) : ℝ :=
  max 0 (1 - |gamma| / (2 * R))

lemma boundaryWeight_nonneg (R gamma : ℝ) : 0 ≤ boundaryWeight R gamma := by
  exact le_max_left _ _

lemma boundaryWeight_le_one {R gamma : ℝ} (hR : 0 < R) :
    boundaryWeight R gamma ≤ 1 := by
  unfold boundaryWeight
  rw [max_le_iff]
  exact ⟨zero_le_one, sub_le_self _ (div_nonneg (abs_nonneg _) (by positivity))⟩

lemma boundaryWeight_eq_zero {R gamma : ℝ} (hR : 0 < R)
    (hgamma : 2 * R ≤ |gamma|) :
    boundaryWeight R gamma = 0 := by
  unfold boundaryWeight
  rw [max_eq_left]
  rw [sub_nonpos, one_le_div₀ (by positivity)]
  exact hgamma

lemma boundaryWeight_ge_half {R gamma : ℝ} (hR : 0 < R)
    (hgamma : |gamma| ≤ R) :
    (1 / 2 : ℝ) ≤ boundaryWeight R gamma := by
  unfold boundaryWeight
  apply le_max_of_le_right
  have hdiv : |gamma| / (2 * R) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * R)).2
    linarith
  linarith

lemma shifted_invSq_sum_le
    {r Q : ℝ} (hr : 1 ≤ r) (hrQ : r < Q) :
    ∑ u ∈ (shiftedZeroDivisor_support_finite Q).toFinset with r ≤ ‖u‖,
        (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤
      5 * shiftedZeroJensenConstant / Real.sqrt r := by
  let S := (shiftedZeroDivisor_support_finite Q).toFinset
  let T := S.filter fun u => r ≤ ‖u‖
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hQ : 0 < Q := hr0.trans hrQ
  have hraw :
      ∑ u ∈ T, (shiftedZeroDivisor Q u : ℝ) * (r ^ 2 / ‖u‖ ^ 2) ≤
        5 * shiftedZeroJensenConstant * r ^ 2 / Real.sqrt r := by
    apply weighted_invSq_tail_le_threeHalves T norm
      (fun u => (shiftedZeroDivisor Q u : ℝ)) hr0 hrQ.le
      shiftedZeroJensenConstant_nonneg
    · intro u hu
      exact (Finset.mem_filter.mp hu).2
    · intro u hu
      have hdiv : shiftedZeroDivisor Q u ≠ 0 :=
        (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp
          (Finset.mem_filter.mp hu).1
      have huBall := (shiftedZeroDivisor Q).supportWithinDomain hdiv
      have huNorm : ‖u‖ < Q := by
        simpa [mem_ball_iff_norm] using huBall
      exact huNorm.le
    · intro t ht
      let U := S.filter fun u => ‖u‖ < t
      have hsub : T.filter (fun u => ‖u‖ < t) ⊆ U := by
        intro u hu
        have hu' := Finset.mem_filter.mp hu
        have huT := Finset.mem_filter.mp hu'.1
        exact Finset.mem_filter.mpr ⟨huT.1, hu'.2⟩
      calc
        ∑ u ∈ T with ‖u‖ < t, (shiftedZeroDivisor Q u : ℝ) ≤
            ∑ u ∈ U, (shiftedZeroDivisor Q u : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro u huU huT
          exact_mod_cast shiftedZeroDivisor_nonneg Q u
        _ = shiftedZeroCount t := by
          dsimp [U, S]
          exact sum_shiftedZeroDivisor_filter_norm_lt ht.2
        _ ≤ shiftedZeroJensenConstant * t * Real.sqrt t :=
          shiftedZeroCount_le_cubicRootBound
            ((hr.trans (le_of_lt ht.1)))
    · calc
        ∑ u ∈ T, (shiftedZeroDivisor Q u : ℝ) ≤
            ∑ u ∈ S, (shiftedZeroDivisor Q u : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro u huS huT
          exact_mod_cast shiftedZeroDivisor_nonneg Q u
        _ = shiftedZeroCount Q := by
          dsimp [S]
          exact sum_shiftedZeroDivisor_eq_count Q
        _ ≤ shiftedZeroJensenConstant * Q * Real.sqrt Q :=
          shiftedZeroCount_le_cubicRootBound (hr.trans hrQ.le)
  change ∑ u ∈ T, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤ _
  have hrSq : 0 < r ^ 2 := sq_pos_of_pos hr0
  calc
    ∑ u ∈ T, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 =
        (∑ u ∈ T,
          (shiftedZeroDivisor Q u : ℝ) * (r ^ 2 / ‖u‖ ^ 2)) / r ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      field_simp [hr0.ne']
    _ ≤ (5 * shiftedZeroJensenConstant * r ^ 2 /
          Real.sqrt r) / r ^ 2 :=
      div_le_div_of_nonneg_right hraw hrSq.le
    _ = 5 * shiftedZeroJensenConstant / Real.sqrt r := by
      field_simp [hr0.ne']

noncomputable def boundaryZeroTerm (Q R x : ℝ) (u : ℂ) : ℂ :=
  (shiftedZeroDivisor Q u : ℂ) * boundaryWeight R u.im /
      (1 / 2 + u) * Complex.exp (u * (x : ℂ))

noncomputable def boundaryPolynomial (Q R x : ℝ) : ℂ :=
  1 + ∑ u ∈ (shiftedZeroDivisor_support_finite Q).toFinset,
    boundaryZeroTerm Q R x u

noncomputable def boundaryRealTerm (Q R x : ℝ) (u : ℂ) : ℝ :=
  (shiftedZeroDivisor Q u : ℝ) * boundaryWeight R u.im *
    ((1 / 2 : ℝ) * Real.cos (u.im * x) + u.im * Real.sin (u.im * x)) /
    ((1 / 2 : ℝ) ^ 2 + u.im ^ 2)

noncomputable def boundaryPolynomialRe (Q R x : ℝ) : ℝ :=
  1 + ∑ u ∈ (shiftedZeroDivisor_support_finite Q).toFinset,
    boundaryRealTerm Q R x u

private lemma eq_im_mul_I {u : ℂ} (hu : u.re = 0) :
    u = (u.im : ℂ) * I := by
  apply Complex.ext
  · simp [hu]
  · simp

lemma norm_eq_abs_im {u : ℂ} (hu : u.re = 0) : ‖u‖ = |u.im| := by
  rw [eq_im_mul_I hu, norm_mul]
  simp

private lemma gamma_mul_sin_nonneg {R gamma : ℝ} (hR : 0 < R)
    (hgamma : |gamma| ≤ 2 * R) :
    0 ≤ gamma * Real.sin (gamma / R) := by
  have htheta : |gamma / R| ≤ 2 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_iff₀ hR).2 hgamma
  by_cases hgamma0 : 0 ≤ gamma
  · exact mul_nonneg hgamma0 <| Real.sin_nonneg_of_nonneg_of_le_pi
      (div_nonneg hgamma0 hR.le)
      ((le_abs_self _).trans (htheta.trans (by linarith [Real.pi_gt_three])))
  · have hgammaNeg : gamma ≤ 0 := le_of_not_ge hgamma0
    have hnegTheta : 0 ≤ -gamma / R := div_nonneg (neg_nonneg.mpr hgammaNeg) hR.le
    have hnegThetaPi : -gamma / R ≤ Real.pi := by
      have habs : |-gamma / R| ≤ 2 := by
        rw [abs_div, abs_neg, abs_of_pos hR]
        exact (div_le_iff₀ hR).2 hgamma
      exact (le_abs_self _).trans (habs.trans (by linarith [Real.pi_gt_three]))
    have hsin : 0 ≤ Real.sin (-gamma / R) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hnegTheta hnegThetaPi
    rw [show -gamma / R = -(gamma / R) by ring, Real.sin_neg] at hsin
    exact mul_nonneg_of_nonpos_of_nonpos hgammaNeg (by linarith)

private lemma gamma_mul_sin_lower {R gamma : ℝ} (hR : 0 < R)
    (hgamma : |gamma| ≤ R) :
    gamma ^ 2 / (2 * R) ≤ gamma * Real.sin (gamma / R) := by
  have htheta : |gamma / R| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos hR]
    have hleOne : |gamma| / R ≤ 1 := (div_le_one hR).2 hgamma
    exact hleOne.trans (by linarith [Real.two_le_pi])
  have hsin := Real.mul_abs_le_abs_sin htheta
  have hprod : 0 ≤ gamma * Real.sin (gamma / R) :=
    gamma_mul_sin_nonneg hR (hgamma.trans (by linarith))
  have habsProd : gamma * Real.sin (gamma / R) =
      |gamma| * |Real.sin (gamma / R)| := by
    rw [← abs_mul, abs_of_nonneg hprod]
  rw [habsProd]
  have hmul := mul_le_mul_of_nonneg_left hsin (abs_nonneg gamma)
  have hpi : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_le_four]
  have hthetaAbs : |gamma / R| = |gamma| / R := by
    rw [abs_div, abs_of_pos hR]
  rw [hthetaAbs] at hmul
  calc
    gamma ^ 2 / (2 * R) = |gamma| * ((1 / 2 : ℝ) * (|gamma| / R)) := by
      rw [← sq_abs gamma]
      field_simp [hR.ne']
    _ ≤ |gamma| * ((2 / Real.pi) * (|gamma| / R)) := by
      gcongr
    _ ≤ |gamma| * |Real.sin (gamma / R)| := hmul

private lemma oscillatory_ratio_le_invSq {R gamma : ℝ} (hR : 0 < R)
    (hgamma0 : gamma ≠ 0) :
    boundaryWeight R gamma *
        ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
        ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) ≤
      1 / (2 * gamma ^ 2) := by
  by_cases hsupport : 2 * R ≤ |gamma|
  · rw [boundaryWeight_eq_zero hR hsupport]
    simp only [zero_mul, zero_div]
    exact (one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_ne_zero hgamma0))).le
  · have hgamma : |gamma| ≤ 2 * R := le_of_not_ge hsupport
    have hsin : 0 ≤ gamma * Real.sin (gamma / R) :=
      gamma_mul_sin_nonneg hR hgamma
    have hnum :
        (1 / 2 : ℝ) * Real.cos (-gamma / R) +
            gamma * Real.sin (-gamma / R) ≤ 1 / 2 := by
      rw [show -gamma / R = -(gamma / R) by ring, Real.cos_neg, Real.sin_neg]
      nlinarith [Real.cos_le_one (gamma / R)]
    have hw0 := boundaryWeight_nonneg R gamma
    have hw1 := boundaryWeight_le_one (gamma := gamma) hR
    have hden : 0 < (1 / 2 : ℝ) ^ 2 + gamma ^ 2 := by positivity
    have hgammaSq : 0 < gamma ^ 2 := sq_pos_of_ne_zero hgamma0
    by_cases hnum0 : 0 ≤ (1 / 2 : ℝ) * Real.cos (-gamma / R) +
        gamma * Real.sin (-gamma / R)
    · apply (div_le_iff₀ hden).2
      calc
        boundaryWeight R gamma *
            ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
              gamma * Real.sin (-gamma / R)) ≤ 1 * (1 / 2) := by
          exact mul_le_mul hw1 hnum hnum0 zero_le_one
        _ ≤ (1 / (2 * gamma ^ 2)) *
            ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) := by
          have heq : (1 / (2 * gamma ^ 2)) *
              ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) =
                1 / 2 + 1 / (8 * gamma ^ 2) := by
            field_simp [hgamma0]
            ring
          rw [heq]
          have hpos : 0 < 1 / (8 * gamma ^ 2) := by positivity
          linarith
    · have hleft : boundaryWeight R gamma *
          ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
            gamma * Real.sin (-gamma / R)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hw0 (le_of_not_ge hnum0)
      exact (div_nonpos_of_nonpos_of_nonneg hleft hden.le).trans (by positivity)

private lemma oscillatory_ratio_high_le {R gamma : ℝ} (hR : 1 ≤ R)
    (hlow : 2 * Real.sqrt R ≤ |gamma|) (hhigh : |gamma| ≤ R) :
    boundaryWeight R gamma *
        ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
        ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) ≤
      -1 / (10 * R) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hgammaSqLow : 4 * R ≤ gamma ^ 2 := by
    have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt R)
      (abs_nonneg gamma)).2 hlow
    rw [sq_abs, mul_pow, Real.sq_sqrt hR0.le] at hsquare
    nlinarith
  have hsin : gamma ^ 2 / (2 * R) ≤
      gamma * Real.sin (gamma / R) :=
    gamma_mul_sin_lower hR0 hhigh
  have hnum :
      (1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R) ≤ -gamma ^ 2 / (4 * R) := by
    rw [show -gamma / R = -(gamma / R) by ring, Real.cos_neg, Real.sin_neg]
    have hcos := Real.cos_le_one (gamma / R)
    have hquarter : (1 / 2 : ℝ) ≤ gamma ^ 2 / (4 * R) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * R)).2
      nlinarith
    have hhalf : gamma ^ 2 / (2 * R) = 2 * (gamma ^ 2 / (4 * R)) := by ring
    calc
      (1 / 2 : ℝ) * Real.cos (gamma / R) + gamma * -Real.sin (gamma / R) =
          (1 / 2 : ℝ) * Real.cos (gamma / R) -
            gamma * Real.sin (gamma / R) := by ring
      _ ≤ 1 / 2 - gamma * Real.sin (gamma / R) := by
        have hcosHalf : (1 / 2 : ℝ) * Real.cos (gamma / R) ≤ 1 / 2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hcos
            (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        exact sub_le_sub_right hcosHalf _
      _ ≤ 1 / 2 - gamma ^ 2 / (2 * R) := sub_le_sub_left hsin _
      _ ≤ -gamma ^ 2 / (4 * R) := by
        rw [hhalf]
        calc
          (1 / 2 : ℝ) - 2 * (gamma ^ 2 / (4 * R)) ≤
              gamma ^ 2 / (4 * R) - 2 * (gamma ^ 2 / (4 * R)) :=
            sub_le_sub_right hquarter _
          _ = -gamma ^ 2 / (4 * R) := by ring
  have hgammaSqPos : 0 < gamma ^ 2 := by nlinarith
  have hdenPos : 0 < (1 / 2 : ℝ) ^ 2 + gamma ^ 2 := by positivity
  have hdenUpper : (1 / 2 : ℝ) ^ 2 + gamma ^ 2 ≤
      5 / 4 * gamma ^ 2 := by nlinarith
  have hratio :
      ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
          ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) ≤ -1 / (5 * R) := by
    apply (div_le_iff₀ hdenPos).2
    calc
      (1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R) ≤ -gamma ^ 2 / (4 * R) := hnum
      _ ≤ (-1 / (5 * R)) * ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) := by
        have hneg : -1 / (5 * R) < 0 := by
          exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
        calc
          -gamma ^ 2 / (4 * R) = (-1 / (5 * R)) * (5 / 4 * gamma ^ 2) := by ring
          _ ≤ (-1 / (5 * R)) * ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) :=
            mul_le_mul_of_nonpos_left hdenUpper hneg.le
  have hw := boundaryWeight_ge_half hR0 hhigh
  have hw0 := boundaryWeight_nonneg R gamma
  have hratioNeg :
      ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
          ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) ≤ 0 :=
    hratio.trans (by
      exact (div_neg_of_neg_of_pos (by norm_num) (by positivity : 0 < 5 * R)).le)
  calc
    boundaryWeight R gamma *
        ((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
        ((1 / 2 : ℝ) ^ 2 + gamma ^ 2) =
      boundaryWeight R gamma *
        (((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
        ((1 / 2 : ℝ) ^ 2 + gamma ^ 2)) := by ring
    _ ≤ (1 / 2 : ℝ) *
        (((1 / 2 : ℝ) * Real.cos (-gamma / R) +
          gamma * Real.sin (-gamma / R)) /
        ((1 / 2 : ℝ) ^ 2 + gamma ^ 2)) :=
      mul_le_mul_of_nonpos_right hw hratioNeg
    _ ≤ (1 / 2 : ℝ) * (-1 / (5 * R)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = -1 / (10 * R) := by ring

lemma boundaryRealTerm_le_invSq
    {C Q R : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (hR : 0 < R) {u : ℂ} (hu : shiftedZeroDivisor Q u ≠ 0) :
    boundaryRealTerm Q R (-1 / R) u ≤
      (shiftedZeroDivisor Q u : ℝ) / (2 * ‖u‖ ^ 2) := by
  have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hu
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    exact hu (shiftedZeroDivisor_zero (by
      have huBall := (shiftedZeroDivisor Q).supportWithinDomain hu
      simpa [mem_ball_iff_norm] using huBall))
  have him0 : u.im ≠ 0 := by
    intro h
    apply hu0
    apply Complex.ext
    · simp [hure]
    · simp [h]
  unfold boundaryRealTerm
  rw [show u.im * (-1 / R) = -u.im / R by ring]
  have hratio := oscillatory_ratio_le_invSq hR him0
  have hm : 0 ≤ (shiftedZeroDivisor Q u : ℝ) := by
    exact_mod_cast shiftedZeroDivisor_nonneg Q u
  have hmul := mul_le_mul_of_nonneg_left hratio hm
  rw [mul_div_assoc] at hmul
  rw [norm_eq_abs_im hure, sq_abs]
  calc
    (shiftedZeroDivisor Q u : ℝ) * boundaryWeight R u.im *
        ((1 / 2 : ℝ) * Real.cos (-u.im / R) + u.im * Real.sin (-u.im / R)) /
        ((1 / 2 : ℝ) ^ 2 + u.im ^ 2) =
      (shiftedZeroDivisor Q u : ℝ) *
        (boundaryWeight R u.im *
          (((1 / 2 : ℝ) * Real.cos (-u.im / R) + u.im * Real.sin (-u.im / R)) /
          ((1 / 2 : ℝ) ^ 2 + u.im ^ 2))) := by ring
    _ ≤ (shiftedZeroDivisor Q u : ℝ) * (1 / (2 * u.im ^ 2)) := hmul
    _ = (shiftedZeroDivisor Q u : ℝ) / (2 * u.im ^ 2) := by ring

lemma boundaryRealTerm_high_le
    {C Q R : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (hR : 1 ≤ R) {u : ℂ} (hu : shiftedZeroDivisor Q u ≠ 0)
    (hlow : 2 * Real.sqrt R ≤ ‖u‖) (hhigh : ‖u‖ ≤ R) :
    boundaryRealTerm Q R (-1 / R) u ≤
      -(shiftedZeroDivisor Q u : ℝ) / (10 * R) := by
  have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hu
  unfold boundaryRealTerm
  rw [show u.im * (-1 / R) = -u.im / R by ring]
  rw [norm_eq_abs_im hure] at hlow hhigh
  have hratio := oscillatory_ratio_high_le hR hlow hhigh
  have hm : 0 ≤ (shiftedZeroDivisor Q u : ℝ) := by
    exact_mod_cast shiftedZeroDivisor_nonneg Q u
  have hmul := mul_le_mul_of_nonneg_left hratio hm
  rw [mul_div_assoc] at hmul
  calc
    (shiftedZeroDivisor Q u : ℝ) * boundaryWeight R u.im *
        ((1 / 2 : ℝ) * Real.cos (-u.im / R) + u.im * Real.sin (-u.im / R)) /
        ((1 / 2 : ℝ) ^ 2 + u.im ^ 2) =
      (shiftedZeroDivisor Q u : ℝ) *
        (boundaryWeight R u.im *
          (((1 / 2 : ℝ) * Real.cos (-u.im / R) + u.im * Real.sin (-u.im / R)) /
          ((1 / 2 : ℝ) ^ 2 + u.im ^ 2))) := by ring
    _ ≤ (shiftedZeroDivisor Q u : ℝ) * (-1 / (10 * R)) := hmul
    _ = -(shiftedZeroDivisor Q u : ℝ) / (10 * R) := by ring

lemma shifted_invSq_sum_all_le
    {delta Q : ℝ} (hdelta : 0 < delta)
    (hfree : ∀ u ∈ ball (0 : ℂ) delta, shiftedChiFourXi u ≠ 0)
    (hQ : 1 < Q) :
    ∑ u ∈ (shiftedZeroDivisor_support_finite Q).toFinset,
        (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤
      shiftedZeroCount 1 / delta ^ 2 + 5 * shiftedZeroJensenConstant := by
  let S := (shiftedZeroDivisor_support_finite Q).toFinset
  let I := S.filter fun u => ‖u‖ < 1
  let O := S.filter fun u => 1 ≤ ‖u‖
  have hinner :
      ∑ u ∈ I, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤
        shiftedZeroCount 1 / delta ^ 2 := by
    have hsum : ∑ u ∈ I, (shiftedZeroDivisor Q u : ℝ) =
        shiftedZeroCount 1 := by
      dsimp [I, S]
      exact sum_shiftedZeroDivisor_filter_norm_lt hQ
    calc
      ∑ u ∈ I, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤
          ∑ u ∈ I, (shiftedZeroDivisor Q u : ℝ) / delta ^ 2 := by
        apply Finset.sum_le_sum
        intro u hu
        have hdiv : shiftedZeroDivisor Q u ≠ 0 :=
          (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp
            (Finset.mem_filter.mp hu).1
        have hnorm : delta ≤ ‖u‖ := by
          by_contra h
          have huBall : u ∈ ball (0 : ℂ) delta := by
            simpa [mem_ball_iff_norm] using lt_of_not_ge h
          exact hdiv (shiftedZeroDivisor_eq_zero_of_ne_zero
            (ball_subset_closedBall <|
              (shiftedZeroDivisor Q).supportWithinDomain hdiv)
            (hfree u huBall))
        have hm : 0 ≤ (shiftedZeroDivisor Q u : ℝ) := by
          exact_mod_cast shiftedZeroDivisor_nonneg Q u
        exact div_le_div_of_nonneg_left hm (sq_pos_of_pos hdelta)
          ((sq_le_sq₀ hdelta.le (norm_nonneg u)).2 hnorm)
      _ = shiftedZeroCount 1 / delta ^ 2 := by rw [← Finset.sum_div, hsum]
  have houter :
      ∑ u ∈ O, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤
        5 * shiftedZeroJensenConstant := by
    dsimp [O, S]
    simpa using shifted_invSq_sum_le (r := (1 : ℝ)) (Q := Q) (by norm_num) hQ
  have hpartition : S = I ∪ O := by
    ext u
    simp only [I, O, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      by_cases h : ‖u‖ < 1
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, le_of_not_gt h⟩
    · exact fun h => h.elim And.left And.left
  have hdisjoint : Disjoint I O := by
    rw [Finset.disjoint_left]
    intro u huI huO
    exact (not_lt_of_ge (Finset.mem_filter.mp huO).2)
      (Finset.mem_filter.mp huI).2
  change ∑ u ∈ S, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤ _
  rw [hpartition, Finset.sum_union hdisjoint]
  exact add_le_add hinner houter

theorem exists_boundaryPolynomial_re_neg
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) :
    ∃ Q R : ℝ, 4 < R ∧ 2 * R < Q ∧
      (∀ u ∈ sphere (0 : ℂ) Q, shiftedChiFourXi u ≠ 0) ∧
      boundaryPolynomialRe Q R (-1 / R) < 0 := by
  obtain ⟨delta, hdelta, hfree⟩ := exists_shiftedZero_free_radius
  let P : ℝ := shiftedZeroCount 1 / delta ^ 2 +
    5 * shiftedZeroJensenConstant
  let threshold : ℝ := max
    (max (16 * shiftedZeroJensenConstant)
      (shiftedZeroCount 4 / delta + 1))
    (20 * (1 + P) + 1)
  obtain ⟨Bnat, hBnat⟩ := exists_nat_gt threshold
  let B : ℝ := Bnat
  have hB16 : 16 * shiftedZeroJensenConstant < B :=
    (le_max_left _ _ |>.trans (le_max_left _ _)).trans_lt hBnat
  have hBcount : shiftedZeroCount 4 / delta + 1 < B :=
    (le_max_right _ _ |>.trans (le_max_left _ _)).trans_lt hBnat
  have hBpoly : 20 * (1 + P) + 1 < B :=
    (le_max_right _ _).trans_lt hBnat
  have hPnonneg : 0 ≤ P := by
    dsimp [P]
    exact add_nonneg
      (div_nonneg (shiftedZeroCount_nonneg 1) (sq_nonneg delta))
      (mul_nonneg (by norm_num) shiftedZeroJensenConstant_nonneg)
  have hBpos : 0 < B := by
    linarith
  obtain ⟨R, hR0, hRcount⟩ := shiftedZeroCount_div_unbounded B
  have hRdelta : delta < R := by
    by_contra h
    have hcountZero := shiftedZeroCount_eq_zero_of_le_free_radius hR0
      (le_of_not_gt h) hfree
    rw [hcountZero] at hRcount
    exact (not_lt_of_ge (mul_nonneg hBpos.le hR0.le)) hRcount
  have hRfour : 4 < R := by
    by_contra h
    have hmono := shiftedZeroCount_mono hR0.le (le_of_not_gt h)
    have hBdelta : shiftedZeroCount 4 < B * delta := by
      have hdiv : shiftedZeroCount 4 / delta < B := by linarith
      exact (div_lt_iff₀ hdelta).1 hdiv
    have : B * delta < shiftedZeroCount R := by
      exact (mul_lt_mul_of_pos_left hRdelta hBpos).trans hRcount
    linarith
  have hRone : 1 ≤ R := by linarith
  have hroot : 16 * shiftedZeroJensenConstant ≤
      B * Real.sqrt (Real.sqrt R) := by
    have hsqrt : 1 ≤ Real.sqrt (Real.sqrt R) := by
      exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hRone)
    exact hB16.le.trans (by
      calc
        B ≤ B * Real.sqrt (Real.sqrt R) :=
          le_mul_of_one_le_right hBpos.le hsqrt
        _ = _ := rfl)
  have hsmall := shiftedZeroCount_two_sqrt_le_quarter hRone hroot
  obtain ⟨Q, hQint, hQfree⟩ :=
    exists_shiftedChiFourXi_zero_free_radius (2 * R)
  have hQ : 2 * R < Q := hQint.1
  let S := (shiftedZeroDivisor_support_finite Q).toFinset
  let H := S.filter fun u => 2 * Real.sqrt R ≤ ‖u‖ ∧ ‖u‖ < R
  let O := S.filter fun u => ¬(2 * Real.sqrt R ≤ ‖u‖ ∧ ‖u‖ < R)
  have hhighMass : 3 * B * R / 4 <
      ∑ u ∈ H, (shiftedZeroDivisor Q u : ℝ) := by
    have htwoR : 2 * Real.sqrt R < R := by
      have hsqrtSq := Real.sq_sqrt (show 0 ≤ R by positivity)
      nlinarith [Real.sqrt_nonneg R]
    have hRltQ : R < Q := (by linarith : R < 2 * R).trans hQ
    have htwoLtQ := htwoR.trans hRltQ
    have hpartition :
        S.filter (fun u => ‖u‖ < R) =
          (S.filter fun u => ‖u‖ < 2 * Real.sqrt R) ∪ H := by
      ext u
      simp only [H, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hu
        by_cases h : ‖u‖ < 2 * Real.sqrt R
        · exact Or.inl ⟨hu.1, h⟩
        · exact Or.inr ⟨hu.1, le_of_not_gt h, hu.2⟩
      · intro hu
        exact hu.elim (fun h => ⟨h.1, h.2.trans htwoR⟩)
          (fun h => ⟨h.1, h.2.2⟩)
    have hdisjoint : Disjoint (S.filter fun u => ‖u‖ < 2 * Real.sqrt R) H := by
      rw [Finset.disjoint_left]
      intro u huI huH
      exact (not_lt_of_ge (Finset.mem_filter.mp huH).2.1)
        (Finset.mem_filter.mp huI).2
    have hmassEq :
        ∑ u ∈ H, (shiftedZeroDivisor Q u : ℝ) =
          shiftedZeroCount R - shiftedZeroCount (2 * Real.sqrt R) := by
      have hRsum := sum_shiftedZeroDivisor_filter_norm_lt (R := Q) hRltQ
      have hsmallSum := sum_shiftedZeroDivisor_filter_norm_lt (R := Q) htwoLtQ
      rw [hpartition, Finset.sum_union hdisjoint] at hRsum
      linarith
    rw [hmassEq]
    linarith
  have hsumAll :
      ∑ u ∈ S, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2 ≤ P := by
    dsimp [P, S]
    exact shifted_invSq_sum_all_le hdelta hfree (by linarith)
  have hhighTerms :
      ∑ u ∈ H, boundaryRealTerm Q R (-1 / R) u <
        -3 * B / 40 := by
    have hterm : ∀ u ∈ H,
        boundaryRealTerm Q R (-1 / R) u ≤
          -(shiftedZeroDivisor Q u : ℝ) / (10 * R) := by
      intro u hu
      have huS := (Finset.mem_filter.mp hu).1
      have hdiv := (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp huS
      have huRange := (Finset.mem_filter.mp hu).2
      exact boundaryRealTerm_high_le hone hRone hdiv huRange.1 huRange.2.le
    calc
      ∑ u ∈ H, boundaryRealTerm Q R (-1 / R) u ≤
          ∑ u ∈ H, (-(shiftedZeroDivisor Q u : ℝ) / (10 * R)) :=
        Finset.sum_le_sum hterm
      _ = -(∑ u ∈ H, (shiftedZeroDivisor Q u : ℝ)) / (10 * R) := by
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
      _ < -3 * B / 40 := by
        field_simp [hR0.ne']
        nlinarith [hhighMass]
  have hotherTerms :
      ∑ u ∈ O, boundaryRealTerm Q R (-1 / R) u ≤ P / 2 := by
    calc
      ∑ u ∈ O, boundaryRealTerm Q R (-1 / R) u ≤
          ∑ u ∈ O, (shiftedZeroDivisor Q u : ℝ) / (2 * ‖u‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro u hu
        have huS := (Finset.mem_filter.mp hu).1
        exact boundaryRealTerm_le_invSq hone (by positivity)
          ((shiftedZeroDivisor_support_finite Q).mem_toFinset.mp huS)
      _ ≤ (∑ u ∈ S, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2) / 2 := by
        have hre : ∑ u ∈ O, (shiftedZeroDivisor Q u : ℝ) / (2 * ‖u‖ ^ 2) =
            (∑ u ∈ O, (shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2) / 2 := by
          calc
            ∑ u ∈ O, (shiftedZeroDivisor Q u : ℝ) / (2 * ‖u‖ ^ 2) =
                ∑ u ∈ O, ((shiftedZeroDivisor Q u : ℝ) / ‖u‖ ^ 2) / 2 := by
              apply Finset.sum_congr rfl
              intro u hu
              ring
            _ = _ := by rw [Finset.sum_div]
        rw [hre]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u huS huO
        exact div_nonneg (by exact_mod_cast shiftedZeroDivisor_nonneg Q u) (sq_nonneg _)
      _ ≤ P / 2 := div_le_div_of_nonneg_right hsumAll (by norm_num)
  have hpartition : S = H ∪ O := by
    ext u
    simp only [H, O, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisjoint : Disjoint H O := by
    rw [Finset.disjoint_left]
    intro u huH huO
    exact (Finset.mem_filter.mp huO).2 (Finset.mem_filter.mp huH).2
  refine ⟨Q, R, hRfour, hQ, ?_, ?_⟩
  · exact hQfree
  · unfold boundaryPolynomialRe
    change 1 + ∑ u ∈ S, boundaryRealTerm Q R (-1 / R) u < 0
    rw [hpartition, Finset.sum_union hdisjoint]
    have hBlarge : 20 * (1 + P) < B := by linarith
    nlinarith

end Submission.BoundaryOscillation
