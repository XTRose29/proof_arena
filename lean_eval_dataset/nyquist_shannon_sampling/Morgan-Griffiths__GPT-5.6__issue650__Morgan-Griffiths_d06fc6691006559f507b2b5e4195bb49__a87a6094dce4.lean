import Mathlib

namespace Submission

namespace LeanEval.Analysis.NyquistShannon

/-!
# Nyquist–Shannon sampling theorem

`nyquist_shannon_sampling`: a Schwartz function whose Fourier transform is
supported in the Nyquist band `[-1/2, 1/2]` (mathlib's `e^{-2π i x ξ}`
convention) is reconstructed from its integer samples by the Whittaker–Shannon
cardinal series `f(t) = ∑_{n : ℤ} f(n) * sinc(π(n - t))`. Trusted helpers
(`sinc`, `FourierSupportedInNyquist`) are non-holes. Mathlib has Schwartz space,
the Fourier transform, inversion, Plancherel and Poisson summation, but not the
sampling theorem. Category-(b) candidate from §179 of the Knill survey.
-/

open scoped FourierTransform SchwartzMap
open Set

/-- The unnormalised cardinal sine, with the removable singularity filled by
the standard value `1`.  Knill writes `sinc x = sin x / x`; the reconstruction
formula evaluates this at `0` when `t` is an integer, so the total version is
the faithful formal spelling. -/
noncomputable def sinc (x : ℝ) : ℂ :=
  if x = 0 then 1 else ((Real.sin x / x : ℝ) : ℂ)

/-- The Fourier transform of `f` is supported in the Nyquist band for
mathlib's `e^{-2π i x ξ}` Fourier convention, namely `[-1/2, 1/2]`. -/
def FourierSupportedInNyquist (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) → 𝓕 f ξ = 0



end LeanEval.Analysis.NyquistShannon

open LeanEval.Analysis.NyquistShannon
open scoped FourierTransform SchwartzMap
open Set
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open MeasureTheory Filter Asymptotics Complex

lemma norm_sinc_le_one (x : ℝ) : ‖sinc x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [sinc, hx]
  · rw [sinc, if_neg hx, Complex.norm_real, Real.norm_eq_abs, abs_div]
    exact (div_le_one (abs_pos.mpr hx)).2 (Real.abs_sin_le_abs (x := x))

lemma summable_schwartz_int (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  have h := (f.isBigO_cocompact_rpow (-2 : ℝ)).comp_tendsto
    Int.tendsto_coe_cofinite
  -- the scalar majorant `|n|⁻²`
  have hb : (1:ℝ) < 2 := by norm_num
  exact summable_of_isBigO (Real.summable_abs_int_rpow hb) (by
    simpa only [Function.comp_def, Real.norm_eq_abs] using h)

lemma summable_sample_sinc (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Summable (fun n : ℤ => f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))) := by
  have hf0 := summable_schwartz_int f
  have hf_norm : Summable (fun n : ℤ => ‖f (n : ℝ)‖) :=
    (summable_norm_iff).2 hf0
  refine Summable.of_norm_bounded hf_norm ?_
  intro n
  calc
    ‖f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))‖ =
        ‖f (n : ℝ)‖ * ‖sinc (Real.pi * ((n : ℝ) - t))‖ := norm_mul _ _
    _ ≤ ‖f (n : ℝ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_sinc_le_one _) (norm_nonneg _)
    _ = ‖f (n : ℝ)‖ := by ring


lemma integral_band_exp (a : ℝ) :
    (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
      Complex.exp (((2 * Real.pi * a * x : ℝ) : ℂ) * Complex.I)) =
      sinc (Real.pi * a) := by
  -- Work with interval integrals to use the elementary antiderivative of an exponential.
  have hab : (-(1/2:ℝ)) ≤ (1/2:ℝ) := by norm_num
  have hset : (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
          Complex.exp (((2 * Real.pi * a * x : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ in (-(1/2:ℝ))..(1/2:ℝ),
          Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I * (x:ℂ)) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hab,
        one_smul, Set.uIoc_of_le hab]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    congr 1 with x
    push_cast
    congr 1
    ring
  rw [hset]
  by_cases ha : a = 0
  · subst a
    simp [sinc]
    norm_num
  · have hc : ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I ≠ 0 := by
      have hp : (2 * Real.pi * a : ℝ) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) ha
      exact mul_ne_zero (by exact_mod_cast hp) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    rw [sinc, if_neg (mul_ne_zero (ne_of_gt Real.pi_pos) ha)]
    have hp1 :
        (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I * ((1/2:ℝ):ℂ))
          = ((Real.pi * a : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hp1]
    have hp2 :
        (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I * (((-(1/2)):ℝ):ℂ))
          = - ((Real.pi * a : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hp2]
    rw [Complex.exp_ofReal_mul_I]
    rw [show -((Real.pi*a:ℝ):ℂ) * Complex.I = ((-(Real.pi*a):ℝ):ℂ) * Complex.I by
          push_cast; ring,
        Complex.exp_ofReal_mul_I]
    push_cast
    -- the cosine terms cancel and the sine terms give `2 i sin`
    simp [Real.cos_neg, Real.sin_neg]
    have hpa : (Real.pi * a : ℝ) ≠ 0 :=
      mul_ne_zero (ne_of_gt Real.pi_pos) ha
    -- all remaining arithmetic is in the field `ℂ`
    field_simp
    <;> ring


lemma fourier_twice_apply_int (f : 𝓢(ℝ, ℂ)) (n : ℤ) :
    (𝓕 (𝓕 f)) (n : ℝ) = f (-(n : ℝ)) := by
  -- inverse Fourier is Fourier with the argument negated
  have h := congrArg (fun h : 𝓢(ℝ, ℂ) => h (-(n:ℝ)))
    (FourierPair.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) f)
  rw [SchwartzMap.fourierInv_apply_eq] at h
  change (𝓕 (𝓕 f)) (- (-(n:ℝ))) = f (-(n:ℝ)) at h
  simpa using h


lemma band_fourier_series (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f)
    {x : ℝ} (hx : x ∈ Ioo (-(1/2:ℝ)) (1/2:ℝ)) :
    (𝓕 f) x = ∑' n : ℤ, f (-(n:ℝ)) * fourier n (x : UnitAddCircle) := by
  have hone : (∑' k : ℤ, (𝓕 f) (x + (k:ℝ))) = (𝓕 f) x := by
    have hz : ∀ k : ℤ, k ≠ 0 → (𝓕 f) (x + (k:ℝ)) = 0 := by
      intro k hk
      apply hf (x + (k:ℝ))
      intro hmem
      rcases hmem with ⟨hlo, hhi⟩
      have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hk' with hk' | hk'
      · have hh : (k:ℝ) ≤ -1 := by exact_mod_cast hk'
        linarith [hx.2]
      · have hh : (1:ℝ) ≤ k := by exact_mod_cast hk'
        linarith [hx.1]
    calc
      (∑' k : ℤ, (𝓕 f) (x + (k:ℝ))) = (𝓕 f) (x + (0:ℝ)) :=
        by simpa using (tsum_eq_single (L := SummationFilter.unconditional ℤ) 0 hz)
      _ = (𝓕 f) x := by norm_num
  have hpoi := SchwartzMap.tsum_eq_tsum_fourier (𝓕 f) x
  rw [hone] at hpoi
  -- replace the double Fourier transform by reflection
  simpa [fourier_twice_apply_int] using hpoi


lemma interior_mul_series (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f)
    (t : ℝ) {x : ℝ} (hx : x ∈ Ioo (-(1/2:ℝ)) (1/2:ℝ)) :
    (𝓕 f) x * Complex.exp (((2*Real.pi*t*x:ℝ):ℂ) * Complex.I) =
      ∑' n : ℤ, f (-(n:ℝ)) *
        Complex.exp (((2*Real.pi*((n:ℝ)+t)*x:ℝ):ℂ) * Complex.I) := by
  rw [band_fourier_series f hf hx, ← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [fourier_coe_apply]
  push_cast
  -- the product of the two phases combines their real arguments
  rw [div_one, mul_assoc, ← Complex.exp_add]
  congr 1
  ring


lemma integral_norm_term (c : ℂ) (a : ℝ) :
    (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
      ‖c * Complex.exp (((2*Real.pi*a*x:ℝ):ℂ) * Complex.I)‖) = ‖c‖ := by
  have he (x : ℝ) :
      ‖c * Complex.exp (((2*Real.pi*a*x:ℝ):ℂ) * Complex.I)‖ = ‖c‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  simp_rw [he]
  -- the band has length one
  rw [MeasureTheory.setIntegral_const]
  simp [Real.volume_Icc]
  <;> ring

lemma integrable_term_band (c : ℂ) (a : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => c * Complex.exp (((2*Real.pi*a*x:ℝ):ℂ) * Complex.I))
      (MeasureTheory.volume.restrict (Icc (-(1/2:ℝ)) (1/2:ℝ))) := by
  apply ContinuousOn.integrableOn_Icc
  fun_prop


lemma ae_interior_band :
    ∀ᵐ x : ℝ ∂(MeasureTheory.volume.restrict (Icc (-(1/2:ℝ)) (1/2:ℝ))),
      x ∈ Ioo (-(1/2:ℝ)) (1/2:ℝ) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  -- the two endpoints are null
  have h₁ : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ (-(1/2:ℝ)) := by
    rw [MeasureTheory.ae_iff]
    convert Real.volume_singleton (a := (-(1/2:ℝ)))
    ext x
    simp
  have h₂ : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ (1/2:ℝ) := by
    rw [MeasureTheory.ae_iff]
    convert Real.volume_singleton (a := (1/2:ℝ))
    ext x
    simp
  filter_upwards [h₁, h₂] with x hx1 hx2 hx
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx1), lt_of_le_of_ne hx.2 hx2⟩

lemma band_integral_series (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f) (t : ℝ) :
    (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
       (𝓕 f) x * Complex.exp (((2*Real.pi*t*x:ℝ):ℂ)*Complex.I)) =
      ∑' n : ℤ, f (-(n:ℝ)) * sinc (Real.pi * ((n:ℝ)+t)) := by
  let F : ℤ → ℝ → ℂ := fun n x => f (-(n:ℝ)) *
        Complex.exp (((2*Real.pi*((n:ℝ)+t)*x:ℝ):ℂ)*Complex.I)
  have hi : ∀ n : ℤ, MeasureTheory.Integrable (F n)
        (MeasureTheory.volume.restrict (Icc (-(1/2:ℝ)) (1/2:ℝ))) := by
    intro n
    exact integrable_term_band _ _
  have hn : Summable (fun n : ℤ =>
        ∫ x : ℝ, ‖F n x‖ ∂(MeasureTheory.volume.restrict (Icc (-(1/2:ℝ)) (1/2:ℝ)))) := by
    have hs : Summable (fun n : ℤ => f (-(n:ℝ))) := by
      have h0 := summable_schwartz_int f
      have hcomp := (Equiv.neg ℤ).summable_iff.mpr h0
      simpa [Function.comp_def] using hcomp
    have hs' : Summable (fun n : ℤ => ‖f (-(n:ℝ))‖) := (summable_norm_iff).2 hs
    have hnn (n : ℤ) :
        (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ), ‖F n x‖) = ‖f (-(n:ℝ))‖ := by
      simpa [F] using (integral_norm_term (f (-(n:ℝ))) ((n:ℝ)+t))
    simpa only [hnn] using hs'
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hi hn
  -- identify the a.e. pointwise sum using the Fourier series
  have hpoint :
      (∫ x : ℝ, (𝓕 f) x * Complex.exp (((2*Real.pi*t*x:ℝ):ℂ)*Complex.I) ∂(MeasureTheory.volume.restrict (Icc (-(1/2:ℝ)) (1/2:ℝ))))
       = ∫ x : ℝ, (∑' n : ℤ, F n x) ∂(MeasureTheory.volume.restrict (Icc (-(1/2:ℝ)) (1/2:ℝ))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_interior_band] with x hx
      exact interior_mul_series f hf t hx
  rw [hpoint]
  rw [← hswap]
  apply tsum_congr
  intro n
  change (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
      f (-(n:ℝ)) *
       Complex.exp (((2*Real.pi*((n:ℝ)+t)*x:ℝ):ℂ)*Complex.I)) = _
  rw [MeasureTheory.integral_const_mul]
  rw [integral_band_exp]


lemma inversion_integral_band (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f) (t : ℝ) :
    f t = (∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
       (𝓕 f) x * Complex.exp (((2*Real.pi*t*x:ℝ):ℂ)*Complex.I)) := by
  have hinv := congrArg (fun h : 𝓢(ℝ, ℂ) => h t)
    (FourierPair.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) f)
  rw [SchwartzMap.fourierInv_apply_eq] at hinv
  change (𝓕 (𝓕 f)) (-t) = f t at hinv
  have hform := Real.fourier_real_eq_integral_exp_smul
     (fun x : ℝ => (𝓕 f) x) (-t)
  have hall : f t = ∫ x : ℝ,
       (𝓕 f) x * Complex.exp (((2*Real.pi*t*x:ℝ):ℂ)*Complex.I) := by
    rw [← hinv]
    rw [SchwartzMap.fourier_coe] -- expression as integral
    rw [hform]
    congr 1 with x
    -- smul on `ℂ` is multiplication, and the phase simplifies
    simp [smul_eq_mul]
    push_cast
    ring
  rw [hall]
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [hf x hx, zero_mul]


lemma sinc_neg (x : ℝ) : sinc (-x) = sinc x := by
  by_cases hx : x = 0
  · simp [hx, sinc]
  · have hn : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [sinc, if_neg hn, sinc, if_neg hx]
    norm_cast
    rw [Real.sin_neg]
    ring

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem nyquist_shannon_sampling (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f) :
    ∀ t : ℝ,
      Summable (fun n : ℤ ↦ f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))) ∧
        f t =
          ∑' n : ℤ, f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t)) :=
/-ResultProofBegin-/by
  intro t
  refine ⟨summable_sample_sinc f t, ?_⟩
  calc
    f t = ∫ x : ℝ in Icc (-(1/2:ℝ)) (1/2:ℝ),
       (𝓕 f) x * Complex.exp (((2*Real.pi*t*x:ℝ):ℂ)*Complex.I) :=
         inversion_integral_band f hf t
    _ = ∑' n : ℤ, f (-(n:ℝ)) * sinc (Real.pi * ((n:ℝ)+t)) :=
         band_integral_series f hf t
    _ = ∑' n : ℤ, f (n:ℝ) * sinc (Real.pi * ((n:ℝ)-t)) := by
      rw [← (Equiv.neg ℤ).tsum_eq
        (fun n : ℤ => f (-(n:ℝ)) * sinc (Real.pi * ((n:ℝ)+t)))]
      apply tsum_congr
      intro n
      congr 1
      · congr 1 <;> simp
      have harg : Real.pi * ((-(n:ℝ)) + t) = -(Real.pi * ((n:ℝ)-t)) := by ring
      simp only [Equiv.neg_apply, Int.cast_neg]
      rw [harg, sinc_neg]
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
