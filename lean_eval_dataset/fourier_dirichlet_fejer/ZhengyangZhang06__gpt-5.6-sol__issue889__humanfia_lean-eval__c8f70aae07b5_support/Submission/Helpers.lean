import Mathlib
import ChallengeDeps
import Submission.Fejer

namespace Submission.Helpers

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def periodicContinuous (f : ℝ → ℂ) (hperiod : Function.Periodic f (2 * Real.pi))
    (hcont : Continuous f) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨hperiod.lift, continuous_coinduced_dom.mpr hcont⟩

@[simp]
theorem periodicContinuous_apply (f : ℝ → ℂ)
    (hperiod : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f) (x : ℝ) :
    periodicContinuous f hperiod hcont (x : AddCircle (2 * Real.pi)) = f x := by
  exact hperiod.lift_coe x

theorem fourierCoeff_periodicContinuous (f : ℝ → ℂ)
    (hperiod : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f) (n : ℤ) :
    fourierCoeff (periodicContinuous f hperiod hcont) n =
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [fourierCoeff_eq_intervalIntegral (a := 0)]
  rw [fourierCoeffOn_eq_integral]
  simp only [periodicContinuous_apply, zero_add, sub_zero]
  rw [show 2 * Real.pi - 0 = 2 * Real.pi by ring]

theorem fourier_two_pi_apply (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 * Real.pi)) =
      Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem circlePartialSum_periodicContinuous (f : ℝ → ℂ)
    (hperiod : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f)
    (N : ℕ) (x : ℝ) :
    Submission.Fejer.circlePartialSum (periodicContinuous f hperiod hcont) N
        (x : AddCircle (2 * Real.pi)) =
      LeanEval.Analysis.fourierPartialSum f N x := by
  simp only [Submission.Fejer.circlePartialSum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, fourierCoeff_periodicContinuous, smul_eq_mul,
    LeanEval.Analysis.fourierPartialSum]
  apply Finset.sum_congr rfl
  intro n _
  rw [fourier_two_pi_apply]

theorem circleCesaroMean_periodicContinuous (f : ℝ → ℂ)
    (hperiod : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f)
    (N : ℕ) (x : ℝ) :
    Submission.Fejer.circleCesaroMean (periodicContinuous f hperiod hcont) N
        (x : AddCircle (2 * Real.pi)) =
      LeanEval.Analysis.fourierCesaroMean f N x := by
  simp only [Submission.Fejer.circleCesaroMean, ContinuousMap.smul_apply,
    ContinuousMap.sum_apply, circlePartialSum_periodicContinuous,
    LeanEval.Analysis.fourierCesaroMean]
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem continuous_deriv_of_contDiff_one {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (deriv f) := by
  change Continuous (fun x => (fderiv ℝ f x) 1)
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem fourierCoeffOn_eq_deriv_div {f : ℝ → ℂ}
    (hperiod : Function.Periodic f (2 * Real.pi)) (hC1 : ContDiff ℝ 1 f)
    {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn Real.two_pi_pos f n =
      fourierCoeffOn Real.two_pi_pos (deriv f) n / (Complex.I * (n : ℂ)) := by
  rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn
    (fun x _ => (hC1.differentiable (by norm_num) x).hasDerivAt)
    ((continuous_deriv_of_contDiff_one hC1).intervalIntegrable 0 (2 * Real.pi))]
  have hfper : f (2 * Real.pi) = f 0 := by
    simpa using hperiod 0
  simp [hfper]
  field_simp [Real.pi_ne_zero, hn]
  simp [Complex.I_sq]

theorem summable_fourierCoeffOn_of_contDiff_one_periodic {f : ℝ → ℂ}
    (hperiod : Function.Periodic f (2 * Real.pi)) (hC1 : ContDiff ℝ 1 f) :
    Summable (fourierCoeffOn Real.two_pi_pos f) := by
  let f' : ℝ → ℂ := deriv f
  have hf'cont : Continuous f' := continuous_deriv_of_contDiff_one hC1
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).exists_bound_of_continuousOn
      hf'cont.continuousOn
  have hf'L2 : MemLp f' 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
    apply MemLp.of_bound hf'cont.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x ⟨hx.1.le, hx.2⟩
  have hcoeffSq : Summable (fun n : ℤ =>
      ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn Real.two_pi_pos hf'L2).summable
  have hcoeffRpow : Summable (fun n : ℤ =>
      ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using hcoeffSq
  have hinvRpow : Summable (fun n : ℤ =>
      (1 / |(n : ℝ)|) ^ (2 : ℝ)) := by
    have h := (Real.summable_one_div_int_add_rpow 0 2).2 (by norm_num)
    simpa only [add_zero, Real.div_rpow zero_le_one (abs_nonneg _) 2,
      Real.one_rpow] using h
  have hprod : Summable (fun n : ℤ =>
      ‖fourierCoeffOn Real.two_pi_pos f' n‖ * (1 / |(n : ℝ)|)) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
      (fun _ => norm_nonneg _) (fun _ => by positivity) hcoeffRpow hinvRpow
  have htail : Summable (fun n : ℤ =>
      if n = 0 then 0 else ‖fourierCoeffOn Real.two_pi_pos f n‖) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hprod
    intro n
    split_ifs with hn
    · positivity
    · rw [fourierCoeffOn_eq_deriv_div hperiod hC1 hn]
      simp only [f', div_eq_mul_inv]
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]
      simp
  have hnorm : Summable (fun n : ℤ => ‖fourierCoeffOn Real.two_pi_pos f n‖) :=
    htail.congr_cofinite <| (Filter.eventually_cofinite_ne 0).mono fun n hn => by simp [hn]
  exact summable_norm_iff.mp hnorm

end

end Submission.Helpers
