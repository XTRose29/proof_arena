import Submission.BoundaryOscillation

open Complex Filter MeasureTheory Metric Real Set Topology

namespace Submission.BoundaryFinal

open Submission.Analytic Submission.BoundaryOscillation Submission.Endpoint
open Submission.FejerLaplace Submission.Helpers Submission.Oscillation
open Submission.PrimeSeries Submission.ResidueCertificate Submission.SignChange
open Submission.ZeroMass

private lemma boundaryZeroTerm_re_eq
    {C Q R x : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    {u : ℂ} (hu : shiftedZeroDivisor Q u ≠ 0) :
    (boundaryZeroTerm Q R x u).re = boundaryRealTerm Q R x u := by
  have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hu
  have hueq : u = (u.im : ℂ) * I := by
    apply Complex.ext
    · simp [hure]
    · simp
  unfold boundaryZeroTerm boundaryRealTerm
  have hexpArg : Complex.exp (u * (x : ℂ)) =
      Complex.exp (((u.im * x : ℝ) : ℂ) * I) := by
    congr 1
    calc
      u * (x : ℂ) = ((u.im : ℂ) * I) * (x : ℂ) :=
        congrArg (fun z : ℂ => z * (x : ℂ)) hueq
      _ = ((u.im * x : ℝ) : ℂ) * I := by
        push_cast
        ring
  have hexpRe : (Complex.exp (u * (x : ℂ))).re = Real.cos (u.im * x) := by
    rw [hexpArg, Complex.exp_ofReal_mul_I_re]
  have hexpIm : (Complex.exp (u * (x : ℂ))).im = Real.sin (u.im * x) := by
    rw [hexpArg, Complex.exp_ofReal_mul_I_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.normSq_apply, hure, hexpRe, hexpIm]
  ring

lemma boundaryPolynomial_re_eq
    {C Q R x : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) :
    (boundaryPolynomial Q R x).re = boundaryPolynomialRe Q R x := by
  unfold boundaryPolynomial boundaryPolynomialRe
  rw [Complex.add_re, Complex.one_re]
  congr 1
  change Complex.reCLM
      (∑ u ∈ (shiftedZeroDivisor_support_finite Q).toFinset,
        boundaryZeroTerm Q R x u) = _
  rw [map_sum]
  simp only [Complex.reCLM_apply]
  apply Finset.sum_congr rfl
  intro u hu
  have hdiv : shiftedZeroDivisor Q u ≠ 0 :=
    (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp hu
  exact boundaryZeroTerm_re_eq hone hdiv

private lemma boundaryPolynomial_eq_finiteExponentialSum
    {C Q R : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) (x : ℝ) :
    let S := (shiftedZeroDivisor_support_finite Q).toFinset
    let c : ↥S → ℂ := fun u =>
      (shiftedZeroDivisor Q u : ℂ) * boundaryWeight R u.1.im / (1 / 2 + u.1)
    let gamma : ↥S → ℝ := fun u => u.1.im
    boundaryPolynomial Q R x = 1 + finiteExponentialSum c gamma x := by
  dsimp only
  unfold boundaryPolynomial finiteExponentialSum boundaryZeroTerm
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply congrArg (fun z : ℂ => 1 + z)
  apply Finset.sum_congr rfl
  intro u _hu
  have hdiv : shiftedZeroDivisor Q u.1 ≠ 0 :=
    (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp u.2
  have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hdiv
  have hueq : u.1 = (u.1.im : ℂ) * I := by
    apply Complex.ext
    · simp [hure]
    · simp
  congr 1
  rw [hueq]
  congr 1
  push_cast
  ring

lemma exists_large_boundaryPolynomialRe_neg
    {C Q R x₀ : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (hneg : boundaryPolynomialRe Q R x₀ < 0) (N : ℝ) :
    ∃ x > N, boundaryPolynomialRe Q R x < 0 := by
  let S := (shiftedZeroDivisor_support_finite Q).toFinset
  let c : ↥S → ℂ := fun u =>
    (shiftedZeroDivisor Q u : ℂ) * boundaryWeight R u.1.im / (1 / 2 + u.1)
  let gamma : ↥S → ℝ := fun u => u.1.im
  let epsilon : ℝ := -boundaryPolynomialRe Q R x₀ / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  obtain ⟨x, hxN, hxclose⟩ :=
    exists_large_real_finiteExponentialSum_close c gamma hepsilon x₀ N
  refine ⟨x, hxN, ?_⟩
  have hpoly (y : ℝ) :
      boundaryPolynomial Q R y = 1 + finiteExponentialSum c gamma y := by
    simpa only [S, c, gamma] using
      (boundaryPolynomial_eq_finiteExponentialSum hone y)
  have hreClose :
      |boundaryPolynomialRe Q R x - boundaryPolynomialRe Q R x₀| < epsilon := by
    rw [← boundaryPolynomial_re_eq hone, ← boundaryPolynomial_re_eq hone,
      hpoly x, hpoly x₀]
    calc
      |(1 + finiteExponentialSum c gamma x).re -
          (1 + finiteExponentialSum c gamma x₀).re| =
          |(finiteExponentialSum c gamma x -
            finiteExponentialSum c gamma x₀).re| := by
        simp only [Complex.add_re, Complex.one_re, Complex.sub_re]
        congr 1
        ring
      _ ≤ ‖finiteExponentialSum c gamma x -
          finiteExponentialSum c gamma x₀‖ := Complex.abs_re_le_norm _
      _ < epsilon := hxclose
  dsimp [epsilon] at hreClose
  linarith [lt_of_abs_lt hreClose]

end Submission.BoundaryFinal
