import Mathlib
import Submission.Helpers

open MeromorphicOn
open Complex Function Metric Set

namespace Submission

theorem rouche_zero_count_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
  let CB : Set ℂ := closedBall 0 R
  have hgNhd : AnalyticOnNhd ℂ g univ :=
    isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg
  have hgCB : AnalyticOnNhd ℂ g CB := hgNhd.mono (fun _ _ ↦ mem_univ _)
  have hfBoundary (z : ℂ) (hz : z ∈ sphere 0 R) :
      AnalyticAt ℂ f z ∧ f z ≠ 0 := by
    have hzNorm : ‖z‖ = R := by
      simpa [mem_sphere] using hz
    have hf_ne : f z ≠ 0 := by
      intro hf_zero
      have h := hbound z hzNorm
      rw [hf_zero, norm_zero] at h
      exact (not_lt_of_ge (norm_nonneg (g z))) h
    have hfNF : MeromorphicNFAt f z := hf (mem_univ z)
    have horder : meromorphicOrderAt f z = 0 :=
      hfNF.meromorphicOrderAt_eq_zero_iff.2 hf_ne
    exact
      ⟨hfNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (by rw [horder]), hf_ne⟩
  have hsumBoundary (z : ℂ) (hz : z ∈ sphere 0 R) :
      AnalyticAt ℂ (f + g) z ∧ (f + g) z ≠ 0 := by
    have hf_data := hfBoundary z hz
    have hg_analytic : AnalyticAt ℂ g z := hgNhd z (mem_univ z)
    have hzNorm : ‖z‖ = R := by
      simpa [mem_sphere] using hz
    have hsum_ne : (f + g) z ≠ 0 := by
      intro hsum_zero
      have hsum_zero' : f z + g z = 0 := by
        simpa only [Pi.add_apply] using hsum_zero
      have hf_eq : f z = -g z := by
        calc
          f z = f z + g z - g z := by ring
          _ = -g z := by rw [hsum_zero']; simp
      have h := hbound z hzNorm
      rw [hf_eq, norm_neg] at h
      exact (lt_irrefl _ h)
    exact ⟨hf_data.1.add hg_analytic, hsum_ne⟩
  let q : ℂ → ℂ := (f + g) / f
  have hqAnalytic (z : ℂ) (hz : z ∈ sphere 0 R) : AnalyticAt ℂ q z := by
    have hf_data := hfBoundary z hz
    have hsum_data := hsumBoundary z hz
    simpa only [q] using
      hsum_data.1.div hf_data.1 hf_data.2
  have hqSlit (z : ℂ) (hz : z ∈ sphere 0 R) : q z ∈ slitPlane := by
    have hf_data := hfBoundary z hz
    have hzNorm : ‖z‖ = R := by
      simpa [mem_sphere] using hz
    have hratio : ‖g z / f z‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one (norm_pos_iff.mpr hf_data.2)).2 (hbound z hzNorm)
    have hmem := Complex.mem_slitPlane_of_norm_lt_one hratio
    have hq_eq : q z = 1 + g z / f z := by
      dsimp only [q, Pi.add_apply, Pi.div_apply]
      field_simp [hf_data.2]
    rwa [hq_eq]
  have hqLogDeriv (z : ℂ) (hz : z ∈ sphere 0 R) :
      logDeriv q z = logDeriv (f + g) z - logDeriv f z := by
    have hf_data := hfBoundary z hz
    have hsum_data := hsumBoundary z hz
    change
      logDeriv (fun w ↦ (f + g) w / f w) z =
        logDeriv (f + g) z - logDeriv f z
    exact
      logDeriv_div z hsum_data.2 hf_data.2 hsum_data.1.differentiableAt
        hf_data.1.differentiableAt
  have hqIntegral : (∮ z in C(0, R), logDeriv q z) = 0 := by
    calc
      (∮ z in C(0, R), logDeriv q z) =
          ∮ z in C(0, R), deriv (Complex.log ∘ q) z := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        exact
          (Complex.deriv_log_comp_eq_logDeriv
            (hqAnalytic z hz).differentiableAt (hqSlit z hz)).symm
      _ = 0 := by
        apply Helpers.circleIntegral_deriv_eq_zero
        intro z hz
        rw [abs_of_pos hR] at hz
        exact (hqAnalytic z hz).clog (hqSlit z hz)
  have hlogFAnalytic (z : ℂ) (hz : z ∈ sphere 0 R) :
      AnalyticAt ℂ (logDeriv f) z := by
    have h := hfBoundary z hz
    simpa only [logDeriv] using h.1.deriv.div h.1 h.2
  have hlogSumAnalytic (z : ℂ) (hz : z ∈ sphere 0 R) :
      AnalyticAt ℂ (logDeriv (f + g)) z := by
    have h := hsumBoundary z hz
    simpa only [logDeriv] using h.1.deriv.div h.1 h.2
  have hlogFIntegrable : CircleIntegrable (logDeriv f) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hlogFAnalytic z hz).continuousAt.continuousWithinAt
  have hlogSumIntegrable : CircleIntegrable (logDeriv (f + g)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hlogSumAnalytic z hz).continuousAt.continuousWithinAt
  have hintegral :
      (∮ z in C(0, R), logDeriv (f + g) z) =
        ∮ z in C(0, R), logDeriv f z := by
    apply sub_eq_zero.mp
    rw [← circleIntegral.integral_sub hlogSumIntegrable hlogFIntegrable]
    rw [← circleIntegral.integral_congr hR.le hqLogDeriv]
    exact hqIntegral
  have hfMeromorphic : MeromorphicOn f CB := fun z _ ↦
    hf.meromorphicOn z (mem_univ z)
  have hsumMeromorphic : MeromorphicOn (f + g) CB :=
    hfMeromorphic.add hgCB.meromorphicOn
  have hargF :=
    Helpers.circleIntegral_logDeriv_eq_finsum_divisor hR hfMeromorphic hfBoundary
  have hargSum :=
    Helpers.circleIntegral_logDeriv_eq_finsum_divisor hR hsumMeromorphic hsumBoundary
  have htotalCast :
      (((∑ᶠ z, (divisor (f + g) CB) z) : ℤ) : ℂ) =
        (((∑ᶠ z, (divisor f CB) z) : ℤ) : ℂ) := by
    apply
      mul_right_cancel₀
        (show (2 * Real.pi * I : ℂ) ≠ 0 by norm_num [Real.pi_ne_zero])
    rw [← hargSum, ← hargF]
    exact hintegral
  have htotal :
      (∑ᶠ z, (divisor (f + g) CB) z) =
        ∑ᶠ z, (divisor f CB) z := by
    exact_mod_cast htotalCast
  have hneg :
      (divisor (f + g) CB)⁻ = (divisor f CB)⁻ :=
    hfMeromorphic.negPart_divisor_add_of_analyticNhdOn_right hgCB
  have finsum_pos_eq (D : Function.locallyFinsuppWithin CB ℤ) :
      (∑ᶠ z, (D⁺) z) = (∑ᶠ z, D z) + ∑ᶠ z, (D⁻) z := by
    have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
    have hDneg : (D⁻).support.Finite := (D⁻).finiteSupport (isCompact_closedBall 0 R)
    calc
      (∑ᶠ z, (D⁺) z) = ∑ᶠ z, (D z + (D⁻) z) := by
        apply finsum_congr
        intro z
        change (D z)⁺ = D z + (D z)⁻
        have h := posPart_sub_negPart (D z)
        omega
      _ = (∑ᶠ z, D z) + ∑ᶠ z, (D⁻) z :=
        finsum_add_distrib hD hDneg
  calc
    (∑ᶠ z, ((divisor (f + g) (closedBall 0 R))⁺) z) =
        (∑ᶠ z, (divisor (f + g) CB) z) +
          ∑ᶠ z, ((divisor (f + g) CB)⁻) z := by
      simpa only [CB] using finsum_pos_eq (divisor (f + g) CB)
    _ = (∑ᶠ z, (divisor f CB) z) + ∑ᶠ z, ((divisor f CB)⁻) z := by
      rw [htotal, hneg]
    _ = ∑ᶠ z, ((divisor f (closedBall 0 R))⁺) z := by
      simpa only [CB] using (finsum_pos_eq (divisor f CB)).symm

end Submission
