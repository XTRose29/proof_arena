import ChallengeDeps

open LeanEval.Analysis.NyquistShannon
open scoped FourierTransform SchwartzMap
open Set MeasureTheory TopologicalSpace

namespace Submission.Helpers

noncomputable section

lemma sinc_eq_real_sinc (x : ℝ) : sinc x = (Real.sinc x : ℂ) := by
  simp only [sinc, Real.sinc_apply]
  split_ifs <;> simp

lemma norm_sinc_le_one (x : ℝ) : ‖sinc x‖ ≤ 1 := by
  rw [sinc_eq_real_sinc, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sinc_le_one x

lemma sinc_neg (x : ℝ) : sinc (-x) = sinc x := by
  rw [sinc_eq_real_sinc, sinc_eq_real_sinc, Real.sinc_neg]

lemma summable_int_eval_norm (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ ↦ ‖f (n : ℝ)‖) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
  exact
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto
      Int.tendsto_coe_cofinite).norm_left

lemma fourier_fourier_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (𝓕 f)) x = f (-x) := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) ↦ g (-x))
    (@FourierTransform.fourierInv_fourier_eq
      (𝓢(ℝ, ℂ)) (𝓢(ℝ, ℂ)) _ _ _ f)
  change (𝓕 (𝓕 f)) (-(-x)) = f (-x) at h
  simpa using h

lemma band_fourier_series (f : 𝓢(ℝ, ℂ))
    (hf : FourierSupportedInNyquist f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    (𝓕 f) x =
      ∑' n : ℤ, f (n : ℝ) *
        Complex.exp ((-2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I) := by
  have hshift (k : ℤ) (hk : k ≠ 0) :
      (𝓕 f) (x + (k : ℝ)) = 0 := by
    apply hf
    intro hmem
    have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hk' with hk' | hk'
    · have hk'' : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
      linarith [hx.2, hmem.1]
    · have hk'' : (1 : ℝ) ≤ k := by exact_mod_cast hk'
      linarith [hx.1, hmem.2]
  calc
    (𝓕 f) x = ∑' k : ℤ, (𝓕 f) (x + (k : ℝ)) := by
      rw [tsum_eq_single 0]
      · simp
      · exact hshift
    _ = ∑' k : ℤ,
        (𝓕 (𝓕 f)) (k : ℝ) * fourier k (x : UnitAddCircle) :=
      SchwartzMap.tsum_eq_tsum_fourier (𝓕 f) x
    _ = ∑' k : ℤ, f (-(k : ℝ)) * fourier k (x : UnitAddCircle) := by
      apply tsum_congr
      intro k
      rw [fourier_fourier_apply]
    _ = ∑' n : ℤ, f (n : ℝ) * fourier (-n) (x : UnitAddCircle) := by
      rw [← (Equiv.neg ℤ).tsum_eq]
      simp
    _ = ∑' n : ℤ, f (n : ℝ) *
        Complex.exp ((-2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I) := by
      apply tsum_congr
      intro n
      rw [fourier_coe_apply]
      congr 2
      push_cast
      ring

lemma integral_exp_band_eq_sinc (a : ℝ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      Complex.exp ((2 * Real.pi * a * x : ℝ) * Complex.I)) =
        sinc (Real.pi * a) := by
  by_cases ha : a = 0
  · subst a
    norm_num [sinc]
  have hpa : Real.pi * a ≠ 0 := mul_ne_zero Real.pi_ne_zero ha
  let c : ℂ := (2 * Real.pi * a : ℝ) * Complex.I
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ha
    · exact Complex.I_ne_zero
  have hfun :
      (fun x : ℝ ↦ Complex.exp ((2 * Real.pi * a * x : ℝ) * Complex.I)) =
        fun x : ℝ ↦ Complex.exp (c * x) := by
    funext x
    congr 1
    simp only [c]
    push_cast
    ring
  have hright : c * (1 / 2 : ℝ) = (Real.pi * a : ℝ) * Complex.I := by
    simp only [c]
    push_cast
    ring
  have hleft : c * (↑(-(1 / 2 : ℝ)) : ℂ) =
      (-(Real.pi * a) : ℝ) * Complex.I := by
    simp only [c]
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc, hright, hleft,
    Complex.exp_mul_I, Complex.exp_mul_I, sinc_eq_real_sinc,
    Real.sinc_of_ne_zero hpa]
  simp only [c]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  field_simp [hc, hpa]
  ring

lemma fourier_inversion_band (f : 𝓢(ℝ, ℂ))
    (hf : FourierSupportedInNyquist f) (t : ℝ) :
    f t =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I) * (𝓕 f) x := by
  calc
    f t = (𝓕⁻ (𝓕 f)) t := by
      exact congrArg (fun g : 𝓢(ℝ, ℂ) ↦ g t)
        (@FourierTransform.fourierInv_fourier_eq
          (𝓢(ℝ, ℂ)) (𝓢(ℝ, ℂ)) _ _ _ f).symm
    _ = ∫ x : ℝ,
        Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I) * (𝓕 f) x := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      simp only [smul_eq_mul, Real.inner_apply]
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      push_cast
      ring
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc,
        ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hf x hx, mul_zero]

lemma cardinal_series_summable (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Summable (fun n : ℤ ↦
      f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))) := by
  apply (summable_int_eval_norm f).of_norm_bounded
  intro n
  rw [norm_mul]
  calc
    ‖f (n : ℝ)‖ * ‖sinc (Real.pi * ((n : ℝ) - t))‖
        ≤ ‖f (n : ℝ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_sinc_le_one _) (norm_nonneg _)
    _ = ‖f (n : ℝ)‖ := mul_one _

lemma sampling_identity (f : 𝓢(ℝ, ℂ))
    (hf : FourierSupportedInNyquist f) (t : ℝ) :
    f t =
      ∑' n : ℤ, f (n : ℝ) *
        sinc (Real.pi * ((n : ℝ) - t)) := by
  let F : ℤ → C(ℝ, ℂ) := fun n ↦
    ⟨fun x ↦ f (n : ℝ) *
        Complex.exp ((2 * Real.pi * (t - (n : ℝ)) * x : ℝ) * Complex.I),
      by fun_prop⟩
  have hF_norm :
      Summable fun n : ℤ ↦
        ‖(F n).restrict
          (⟨uIcc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), isCompact_uIcc⟩ :
            Compacts ℝ)‖ := by
    apply (summable_int_eval_norm f).of_norm_bounded
    intro n
    rw [norm_norm, ContinuousMap.norm_le _ (norm_nonneg _)]
    rintro ⟨x, _⟩
    simp [F, Complex.norm_exp]
  calc
    f t = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I) * (𝓕 f) x :=
      fourier_inversion_band f hf t
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ∑' n : ℤ, F n x := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      change
        Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I) * (𝓕 f) x =
          ∑' n : ℤ, F n x
      rw [band_fourier_series f hf hx, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [F, ContinuousMap.coe_mk]
      calc
        Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I) *
              (f (n : ℝ) *
                Complex.exp ((-2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I)) =
            f (n : ℝ) *
              (Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I) *
                Complex.exp ((-2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I)) := by
          ring
        _ = f (n : ℝ) *
            Complex.exp
              (((2 * Real.pi * x * t : ℝ) * Complex.I) +
                ((-2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I)) := by
          rw [Complex.exp_add]
        _ = f (n : ℝ) *
            Complex.exp
              ((2 * Real.pi * (t - (n : ℝ)) * x : ℝ) * Complex.I) := by
          congr 2
          push_cast
          ring
    _ = ∑' n : ℤ,
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F n x :=
      (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hF_norm).symm
    _ = ∑' n : ℤ, f (n : ℝ) *
        sinc (Real.pi * ((n : ℝ) - t)) := by
      apply tsum_congr
      intro n
      simp only [F, ContinuousMap.coe_mk]
      rw [intervalIntegral.integral_const_mul,
        integral_exp_band_eq_sinc]
      congr 1
      rw [show Real.pi * (t - (n : ℝ)) =
        -(Real.pi * ((n : ℝ) - t)) by ring, sinc_neg]

end

end Submission.Helpers
