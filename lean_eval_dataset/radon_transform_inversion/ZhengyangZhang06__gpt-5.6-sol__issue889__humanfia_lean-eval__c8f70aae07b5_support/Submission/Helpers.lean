import ChallengeDeps

open LeanEval.Analysis.RadonTransform
open MeasureTheory Real Complex
open scoped FourierTransform RealInnerProductSpace

namespace Submission.Helpers

lemma fourier2_eq_complex_fourier (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    fourier2 f q =
      𝓕 (fun z : ℂ => f (z.re, z.im)) (q.1 + q.2 * Complex.I) := by
  rw [Real.fourier_eq']
  unfold fourier2
  rw [← Complex.volume_preserving_equiv_real_prod.integral_comp']
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Complex.measurableEquivRealProd_apply, Complex.inner, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.mul_I_im, neg_mul, smul_eq_mul]
  congr 2
  push_cast
  ring

lemma fourier_marginal (Φ : SchwartzMap ℂ ℂ) (k : ℝ) :
    fourier1 (fun p => ∫ t : ℝ, Φ (p + t * Complex.I)) k =
      𝓕 (Φ : ℂ → ℂ) (k : ℂ) := by
  let H : ℂ → ℂ := fun z => 𝐞 (-⟪z, (k : ℂ)⟫) • Φ z
  let F : ℝ × ℝ → ℂ := fun q =>
    Complex.exp (-(2 * Real.pi * q.1 * k) * Complex.I) *
      Φ (q.1 + q.2 * Complex.I)
  have hH : Integrable H :=
    (Real.fourierIntegral_convergent_iff
      (f := (Φ : ℂ → ℂ)) (k : ℂ)).2 Φ.integrable
  have hFH : F = H ∘ Complex.measurableEquivRealProd.symm := by
    funext q
    simp only [F, H, Function.comp_apply, Complex.measurableEquivRealProd_symm_apply,
      Circle.smul_def, Real.fourierChar_apply, Complex.inner, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, neg_mul,
      smul_eq_mul]
    congr 2
    · push_cast
      ring
    · exact (Complex.mk_eq_add_mul_I q.1 q.2).symm
  have hF : Integrable F := by
    rw [hFH]
    exact Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hH
  calc
    fourier1 (fun p => ∫ t : ℝ, Φ (p + t * Complex.I)) k =
        ∫ p : ℝ, ∫ t : ℝ, F (p, t) := by
          unfold fourier1
          simp only [F]
          simp_rw [← MeasureTheory.integral_const_mul]
    _ = ∫ q : ℝ × ℝ, F q := (MeasureTheory.integral_prod F hF).symm
    _ = ∫ z : ℂ, H z := by
      rw [hFH]
      exact Complex.volume_preserving_equiv_real_prod.symm.integral_comp' H
    _ = 𝓕 (Φ : ℂ → ℂ) (k : ℂ) := (Real.fourier_eq _ _).symm

lemma fourier_slice (φ : SchwartzMap (ℝ × ℝ) ℂ) (θ k : ℝ) :
    fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
      fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ) := by
  let Φ : SchwartzMap ℂ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Complex.equivRealProdCLM φ
  let A : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp θ)
  let Ψ : SchwartzMap ℂ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv Φ
  have hradon :
      (fun p : ℝ => radon (φ : ℝ × ℝ → ℂ) (p, θ)) =
        fun p : ℝ => ∫ t : ℝ, Ψ (p + t * Complex.I) := by
    funext p
    unfold radon
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Ψ, Φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, Complex.equivRealProdCLM, Complex.equivRealProdLm,
      Complex.equivRealProdAddHom, Complex.equivRealProd, A]
    congr 2 <;> simp [_root_.rotation_apply, Circle.coe_exp] <;> ring
  rw [hradon, fourier_marginal]
  rw [show 𝓕 (Ψ : ℂ → ℂ) (k : ℂ) = 𝓕 (Φ : ℂ → ℂ) (A (k : ℂ)) by
    exact Real.fourier_comp_linearIsometry A (Φ : ℂ → ℂ) (k : ℂ)]
  have hΦfun : (Φ : ℂ → ℂ) = fun z => φ (z.re, z.im) := by
    funext z
    rfl
  have hA :
      A (k : ℂ) =
        ((k * Real.cos θ : ℝ) : ℂ) +
          ((k * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    simp only [A]
    rw [_root_.rotation_apply, Circle.coe_exp, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  rw [fourier2_eq_complex_fourier, hΦfun]
  rw [hA]

lemma fourier2_injective
    (φ ψ : SchwartzMap (ℝ × ℝ) ℂ)
    (h : ∀ q : ℝ × ℝ,
      fourier2 (φ : ℝ × ℝ → ℂ) q = fourier2 (ψ : ℝ × ℝ → ℂ) q) :
    (φ : ℝ × ℝ → ℂ) = (ψ : ℝ × ℝ → ℂ) := by
  let Φ : SchwartzMap ℂ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Complex.equivRealProdCLM φ
  let Ψ : SchwartzMap ℂ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Complex.equivRealProdCLM ψ
  have hΦfun : (Φ : ℂ → ℂ) = fun z => φ (z.re, z.im) := by
    funext z
    rfl
  have hΨfun : (Ψ : ℂ → ℂ) = fun z => ψ (z.re, z.im) := by
    funext z
    rfl
  have hfourier : 𝓕 Φ = 𝓕 Ψ := by
    ext z
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hΦfun, hΨfun]
    simpa only [fourier2_eq_complex_fourier, Complex.re_add_im] using h (z.re, z.im)
  have hΦ : Φ = Ψ :=
    (FourierTransform.fourierCLE ℂ (SchwartzMap ℂ ℂ)).injective hfourier
  funext q
  have hq := congrArg
    (fun f : SchwartzMap ℂ ℂ => f (Complex.equivRealProdCLM.symm q)) hΦ
  simpa only [Φ, Ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hq

lemma radon_injective
    (φ ψ : SchwartzMap (ℝ × ℝ) ℂ)
    (h : radon (φ : ℝ × ℝ → ℂ) = radon (ψ : ℝ × ℝ → ℂ)) :
    (φ : ℝ × ℝ → ℂ) = (ψ : ℝ × ℝ → ℂ) := by
  apply fourier2_injective φ ψ
  intro q
  let z : ℂ := q.1 + q.2 * Complex.I
  have hq :
      (‖z‖ * Real.cos z.arg, ‖z‖ * Real.sin z.arg) = q := by
    apply Prod.ext
    · simp [Complex.norm_mul_cos_arg, z]
    · simp [Complex.norm_mul_sin_arg, z]
  rw [← hq, ← fourier_slice, ← fourier_slice]
  congr 2
  funext p
  exact congrFun h (p, z.arg)

end Submission.Helpers
