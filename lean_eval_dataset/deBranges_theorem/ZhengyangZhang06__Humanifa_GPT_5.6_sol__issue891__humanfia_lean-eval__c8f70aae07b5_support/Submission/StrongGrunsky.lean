import Submission.GrunskyFourier

open Metric Set MeasureTheory

open scoped ENNReal Topology

namespace Submission

open HahnSeries LaurentSeries

noncomputable def polynomialDerivativeWeight (P : Polynomial ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖P.derivative.eval z‖ ^ 2

noncomputable def finiteFaberPolynomial (L : ℂ → ℂ) (c : ℕ → ℂ) (N : ℕ) :
    Polynomial ℂ :=
  ∑ k ∈ Finset.range N,
    Polynomial.C (c (k + 1)) *
      faberPolynomial (exteriorFactorPowerSeries L) (k + 1)

noncomputable def finiteFaberLaurent (L : ℂ → ℂ) (c : ℕ → ℂ) (N : ℕ) :
    ℂ⸨X⸩ :=
  ∑ k ∈ Finset.range N,
    c (k + 1) • faberLaurent (exteriorFactorPowerSeries L) (k + 1)

noncomputable def finiteGrunskyCombination
    (L : ℂ → ℂ) (c : ℕ → ℂ) (N m : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    c (k + 1) * ((k + 1 : ℕ) : ℂ) * grunskyCoeff L (k + 1) m

noncomputable def finiteFaberShiftFunction
    (L : ℂ → ℂ) (c : ℕ → ℂ) (N : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N,
    c (k + 1) *
      (w ^ (N - (k + 1)) * faberShiftFunction L (k + 1) w)

lemma faberShiftFunction_differentiableOn {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) (n : ℕ) :
    DifferentiableOn ℂ (faberShiftFunction L n) (ball 0 R) := by
  have hE := exteriorAnalyticFactor_differentiableOn hL
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  unfold faberShiftFunction
  apply DifferentiableAt.fun_sum
  intro i hi
  exact (differentiableAt_const _).mul
    ((differentiableAt_id.pow _).mul
      ((hE.differentiableAt (isOpen_ball.mem_nhds hw)).pow _))

lemma finiteFaberShiftFunction_differentiableOn {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) (c : ℕ → ℂ) (N : ℕ) :
    DifferentiableOn ℂ (finiteFaberShiftFunction L c N) (ball 0 R) := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  unfold finiteFaberShiftFunction
  apply DifferentiableAt.fun_sum
  intro k hk
  exact (differentiableAt_const _).mul
    ((differentiableAt_id.pow _).mul
      ((faberShiftFunction_differentiableOn hL (k + 1)).differentiableAt
        (isOpen_ball.mem_nhds hw)))

lemma finiteFaberShiftFunction_eq_eval {L : ℂ → ℂ} (c : ℕ → ℂ) (N : ℕ)
    {w : ℂ} (hw : w ≠ 0) :
    finiteFaberShiftFunction L c N w =
      w ^ N * (finiteFaberPolynomial L c N).eval
        (w⁻¹ * exteriorAnalyticFactor L w) := by
  unfold finiteFaberShiftFunction finiteFaberPolynomial
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    faberShiftFunction_eq_eval hw]
  have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
  have hpow : w ^ (N - (k + 1)) * w ^ (k + 1) = w ^ N := by
    rw [← _root_.pow_add, Nat.sub_add_cancel hkN]
  rw [show w ^ (N - (k + 1)) *
      (w ^ (k + 1) *
        (faberPolynomial (exteriorFactorPowerSeries L) (k + 1)).eval
          (w⁻¹ * exteriorAnalyticFactor L w)) =
      (w ^ (N - (k + 1)) * w ^ (k + 1)) *
        (faberPolynomial (exteriorFactorPowerSeries L) (k + 1)).eval
          (w⁻¹ * exteriorAnalyticFactor L w) by ring,
    hpow]
  ring

lemma taylorCoeff_finiteFaberShiftFunction {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (c : ℕ → ℂ) (N j : ℕ) :
    taylorCoeff (finiteFaberShiftFunction L c N) j =
      (finiteFaberLaurent L c N).coeff ((j : ℤ) - (N : ℤ)) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hterms : ∀ k ∈ Finset.range N, ContDiffAt ℂ j
      (fun w => c (k + 1) *
        (w ^ (N - (k + 1)) * faberShiftFunction L (k + 1) w)) 0 := by
    intro k hk
    have hshift : ContDiffAt ℂ j (faberShiftFunction L (k + 1)) 0 :=
      ((faberShiftFunction_differentiableOn hL (k + 1)).contDiffOn isOpen_ball).contDiffAt
        (isOpen_ball.mem_nhds hzero)
    fun_prop
  change taylorCoeff (fun w => ∑ k ∈ Finset.range N,
    c (k + 1) *
      (w ^ (N - (k + 1)) * faberShiftFunction L (k + 1) w)) j = _
  rw [taylorCoeff_finset_sum hterms]
  unfold finiteFaberLaurent
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [taylorCoeff_const_mul_function, HahnSeries.coeff_smul, smul_eq_mul]
  let d := N - (k + 1)
  have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
  rw [taylorCoeff_pow_mul hR
    (faberShiftFunction_differentiableOn hL (k + 1)) d j]
  by_cases hdj : d ≤ j
  · rw [if_pos hdj, taylorCoeff_faberShiftFunction hR hL]
    congr 2
    dsimp only [d]
    omega
  · rw [if_neg hdj]
    have hindex : (j : ℤ) - (N : ℤ) = -((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : j ≤ N)]
      ring
    rw [hindex]
    have hlt : k + 1 < N - j := by
      dsimp only [d] at hdj
      omega
    rw [coeff_faberLaurent_neg_eq_zero_of_lt
      (exteriorFactorPowerSeries L) (k + 1) (N - j) hlt]

lemma finiteFaberPolynomial_eval_exteriorTransform
    {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (c : ℕ → ℂ) (N : ℕ) {z : ℂ} (hz : z ∈ exteriorDisk R) :
    (finiteFaberPolynomial L c N).eval (exteriorTransform f z) =
      z ^ N * finiteFaberShiftFunction L c N z⁻¹ := by
  have hz0 := ne_zero_of_mem_exteriorDisk hR hz
  have hshift := finiteFaberShiftFunction_eq_eval (L := L) c N (inv_ne_zero hz0)
  have harg : (z⁻¹)⁻¹ * exteriorAnalyticFactor L z⁻¹ = exteriorTransform f z := by
    rw [inv_inv, exteriorTransform_eq_mul_exp_neg hR hf hexp hz]
    rfl
  rw [hshift, harg]
  rw [← mul_assoc, ← _root_.mul_pow]
  simp [hz0]

noncomputable def shiftedAnalyticCircle
    (H : ℂ → ℂ) (N : ℕ) (r theta : ℝ) : ℂ :=
  circleMap 0 r theta ^ N * H (circleMap 0 r theta)⁻¹

lemma hasDerivAt_shiftedAnalyticCircle {H : ℂ → ℂ} {N : ℕ} {r theta : ℝ}
    (hr : r ≠ 0) (hH : DifferentiableAt ℂ H (circleMap 0 r theta)⁻¹) :
    HasDerivAt (shiftedAnalyticCircle H N r)
      (Complex.I * (circleMap 0 r theta ^ N *
        ((N : ℂ) * H (circleMap 0 r theta)⁻¹ -
          (circleMap 0 r theta)⁻¹ * deriv H (circleMap 0 r theta)⁻¹))) theta := by
  let z := circleMap 0 r theta
  have hz0 : z ≠ 0 := by
    intro hzero
    have hnorm : ‖z‖ = |r| := norm_circleMap_zero r theta
    rw [hzero, norm_zero] at hnorm
    exact hr (abs_eq_zero.mp hnorm.symm)
  have hz : HasDerivAt (circleMap 0 r) (z * Complex.I) theta := by
    simpa only [z] using hasDerivAt_circleMap 0 r theta
  have hzinvComplex := (hasDerivAt_inv hz0).complexToReal_fderiv
  have hzinvRaw := (hzinvComplex.comp theta hz.hasFDerivAt).hasDerivAt
  change HasDerivAt (fun u => (circleMap 0 r u)⁻¹) _ theta at hzinvRaw
  have hzinv : HasDerivAt (fun u => (circleMap 0 r u)⁻¹)
      (-Complex.I * z⁻¹) theta := by
    apply hzinvRaw.congr_deriv
    simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.toSpanSingleton_apply_one]
    field_simp [hz0]
    simp
  have hcomp := hH.hasDerivAt.comp theta hzinv
  have hprod := (hz.pow N).mul hcomp
  unfold shiftedAnalyticCircle
  change HasDerivAt (fun u => circleMap 0 r u ^ N * H (circleMap 0 r u)⁻¹) _ theta
  change HasDerivAt (fun u => circleMap 0 r u ^ N * H (circleMap 0 r u)⁻¹) _ theta at hprod
  apply hprod.congr_deriv
  change (N : ℂ) * z ^ (N - 1) * (z * Complex.I) * H z⁻¹ +
      z ^ N * (deriv H z⁻¹ * (-Complex.I * z⁻¹)) =
    Complex.I * (z ^ N * ((N : ℂ) * H z⁻¹ - z⁻¹ * deriv H z⁻¹))
  cases N with
  | zero =>
      simp
      ring_nf
  | succ N =>
      simp only [Nat.cast_add, Nat.cast_one,
        show N + 1 - 1 = N by omega]
      rw [pow_succ]
      field_simp [hz0]
      ring

noncomputable def shiftedAnalyticCircleFlux
    (H : ℂ → ℂ) (N : ℕ) (r theta : ℝ) : ℝ :=
  (1 / 2 : ℝ) * signedCross (shiftedAnalyticCircle H N r theta)
    (deriv (shiftedAnalyticCircle H N r) theta)

lemma shiftedAnalyticCircleFlux_eq {H : ℂ → ℂ} {N : ℕ} {r theta : ℝ}
    (hr : 0 < r) (hH : DifferentiableAt ℂ H (circleMap 0 r theta)⁻¹) :
    shiftedAnalyticCircleFlux H N r theta =
      (1 / 2 : ℝ) * r ^ (2 * N) *
        ((N : ℝ) * ‖H (circleMap 0 r theta)⁻¹‖ ^ 2 -
          signedCross (H (circleMap 0 r theta)⁻¹)
            (Complex.I * ((circleMap 0 r theta)⁻¹ *
              deriv H (circleMap 0 r theta)⁻¹))) := by
  have hd := hasDerivAt_shiftedAnalyticCircle (N := N) hr.ne' hH
  unfold shiftedAnalyticCircleFlux
  rw [hd.deriv]
  unfold shiftedAnalyticCircle
  rw [show Complex.I * (circleMap 0 r theta ^ N *
      ((N : ℂ) * H (circleMap 0 r theta)⁻¹ -
        (circleMap 0 r theta)⁻¹ * deriv H (circleMap 0 r theta)⁻¹)) =
    circleMap 0 r theta ^ N *
      (Complex.I * ((N : ℂ) * H (circleMap 0 r theta)⁻¹ -
        (circleMap 0 r theta)⁻¹ * deriv H (circleMap 0 r theta)⁻¹)) by ring]
  rw [signedCross_mul_left]
  have hnorm : ‖circleMap 0 r theta ^ N‖ ^ 2 = r ^ (2 * N) := by
    rw [norm_pow, norm_circleMap_zero, abs_of_pos hr]
    ring
  rw [hnorm]
  rw [show signedCross (H (circleMap 0 r theta)⁻¹)
      (Complex.I * ((N : ℂ) * H (circleMap 0 r theta)⁻¹ -
        (circleMap 0 r theta)⁻¹ * deriv H (circleMap 0 r theta)⁻¹)) =
    (N : ℝ) * ‖H (circleMap 0 r theta)⁻¹‖ ^ 2 -
      signedCross (H (circleMap 0 r theta)⁻¹)
        (Complex.I * ((circleMap 0 r theta)⁻¹ *
          deriv H (circleMap 0 r theta)⁻¹)) by
    rw [mul_sub]
    unfold signedCross
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring]
  ring

lemma inv_circleMap_zero (r theta : ℝ) :
    (circleMap 0 r theta)⁻¹ = circleMap 0 (1 / r) (-theta) := by
  rw [circleMap, circleMap]
  simp only [zero_add, Complex.ofReal_div, Complex.ofReal_one, mul_inv_rev]
  rw [← Complex.exp_neg]
  have harg : -((theta : ℂ) * Complex.I) = ((-theta : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, div_eq_mul_inv]
  ring

lemma integral_circleMap_eq_circleAverage (F : ℂ → ℝ) (r : ℝ) :
    (∫ theta in -Real.pi..Real.pi, F (circleMap 0 r theta)) =
      2 * Real.pi * Real.circleAverage F 0 r := by
  simpa [circleMap, ← Complex.cos_add_sin_I] using
    integral_polarAngle_eq_circleAverage F r

lemma integral_shiftedAnalyticCircleFlux_eq {H : ℂ → ℂ} {R r : ℝ}
    (hH : DifferentiableOn ℂ H (ball 0 R)) (hr : 0 < r) (hsR : 1 / r < R)
    (N : ℕ) :
    (∫ theta in -Real.pi..Real.pi, shiftedAnalyticCircleFlux H N r theta) =
      Real.pi * r ^ (2 * N) *
        ((N : ℝ) * Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 (1 / r) -
          analyticCircleFlux H (1 / r)) := by
  let s : ℝ := 1 / r
  let normEnergy : ℂ → ℝ := fun w => ‖H w‖ ^ 2
  let eulerFlux : ℂ → ℝ := fun w =>
    signedCross (H w) (Complex.I * (w * deriv H w))
  let energyDifference : ℂ → ℝ := fun w =>
    (N : ℝ) * normEnergy w - eulerFlux w
  have hs : 0 < s := by dsimp only [s]; exact one_div_pos.mpr hr
  have hsphere : sphere (0 : ℂ) s ⊆ ball 0 R := by
    intro w hw
    rw [mem_sphere, dist_zero_right] at hw
    rw [mem_ball_zero_iff, hw]
    exact hsR
  have hnormCont : ContinuousOn normEnergy (sphere (0 : ℂ) s) := by
    exact (hH.continuousOn.norm.pow 2).mono hsphere
  have hderiv : DifferentiableOn ℂ (deriv H) (ball 0 R) := hH.deriv isOpen_ball
  have heulerCont : ContinuousOn eulerFlux (sphere (0 : ℂ) s) := by
    intro w hw
    have hwR := hsphere hw
    have hHAt := hH.differentiableAt (isOpen_ball.mem_nhds hwR)
    have hdAt := hderiv.differentiableAt (isOpen_ball.mem_nhds hwR)
    dsimp only [eulerFlux]
    unfold signedCross
    have hconj : ContinuousAt (fun z => starRingEnd ℂ (H z)) w :=
      Complex.conjCLE.continuous.continuousAt.comp hHAt.continuousAt
    have hright : ContinuousAt
        (fun z => Complex.I * (z * deriv H z)) w :=
      continuousAt_const.mul (continuousAt_id.mul hdAt.continuousAt)
    exact (Complex.imCLM.continuous.continuousAt.comp
      (hconj.mul hright)).continuousWithinAt
  have hnormInt : CircleIntegrable normEnergy 0 s :=
    hnormCont.circleIntegrable hs.le
  have heulerInt : CircleIntegrable eulerFlux 0 s :=
    heulerCont.circleIntegrable hs.le
  have havg : Real.circleAverage energyDifference 0 s =
      (N : ℝ) * Real.circleAverage normEnergy 0 s - analyticCircleFlux H s := by
    have hscalar : Real.circleAverage (fun w => (N : ℝ) * normEnergy w) 0 s =
        (N : ℝ) * Real.circleAverage normEnergy 0 s := by
      rw [show (fun w => (N : ℝ) * normEnergy w) =
        fun w => (N : ℝ) • normEnergy w by funext w; simp]
      rw [Real.circleAverage_fun_smul]
      rfl
    have heuler : Real.circleAverage eulerFlux 0 s = analyticCircleFlux H s := by
      simpa only [analyticCircleFlux, eulerFlux] using
        (circleAverage_comp_mul eulerFlux s).symm
    rw [show energyDifference =
      (fun w => (N : ℝ) * normEnergy w) - eulerFlux by rfl]
    rw [Real.circleAverage_sub (by
      exact hnormInt.const_mul N) heulerInt, hscalar, heuler]
  have hpoint : (fun theta => shiftedAnalyticCircleFlux H N r theta) =
      fun theta => (1 / 2 : ℝ) * r ^ (2 * N) *
        energyDifference (circleMap 0 r theta)⁻¹ := by
    funext theta
    have hinvR : (circleMap 0 r theta)⁻¹ ∈ ball (0 : ℂ) R := by
      rw [inv_circleMap_zero, mem_ball_zero_iff, norm_circleMap_zero,
        abs_of_pos hs]
      exact hsR
    rw [shiftedAnalyticCircleFlux_eq hr
      (hH.differentiableAt (isOpen_ball.mem_nhds hinvR))]
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hinverse : (fun theta => energyDifference (circleMap 0 r theta)⁻¹) =
      fun theta => energyDifference (circleMap 0 s (-theta)) := by
    funext theta
    rw [inv_circleMap_zero]
  rw [hinverse]
  have hneg :
      (∫ theta in -Real.pi..Real.pi,
        energyDifference (circleMap 0 s (-theta))) =
      ∫ theta in -Real.pi..Real.pi,
        energyDifference (circleMap 0 s theta) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun theta => energyDifference (circleMap 0 s theta))
      (a := -Real.pi) (b := Real.pi))
  rw [hneg]
  rw [integral_circleMap_eq_circleAverage, havg]
  dsimp only [s, normEnergy]
  ring

lemma taylorCoeff_sq_tendsto_circleAverage {H : ℂ → ℂ} {R s : ℝ}
    (hH : DifferentiableOn ℂ H (ball 0 R)) (hs : 0 ≤ s) (hsR : s < R) :
    Filter.Tendsto
      (fun K => ∑ j ∈ Finset.range K,
        ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j))
      Filter.atTop
      (nhds (Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 s)) := by
  let Ufin : ℕ → ℂ → ℂ := fun K => finitePositiveFourier
    (fun j => taylorCoeff H j * (s : ℂ) ^ j) K
  let U : ℂ → ℂ := fun z => H ((s : ℂ) * z)
  have hU : TendstoUniformlyOn Ufin U Filter.atTop (sphere (0 : ℂ) 1) := by
    simpa only [Ufin, U] using
      tendstoUniformlyOn_finitePositiveFourier_taylor hH hs hsR
  have hUcont : ContinuousOn U (sphere (0 : ℂ) 1) := by
    intro z hz
    have hznorm : ‖z‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hsz : (s : ℂ) * z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs, hznorm, mul_one]
      exact hsR
    exact (hH.differentiableAt (isOpen_ball.mem_nhds hsz)).continuousAt.comp
      (by fun_prop) |>.continuousWithinAt
  have hUfinCont : ∀ K, ContinuousOn (Ufin K) (sphere (0 : ℂ) 1) := by
    intro K
    exact (continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial
        (fun j => taylorCoeff H j * (s : ℂ) ^ j) K).hasDerivAt z).continuousAt).continuousOn
  have havg := tendsto_circleAverage_norm_sq_of_tendstoUniformlyOn
    hUfinCont hUcont hU
  have hfinite (K : ℕ) :
      Real.circleAverage (fun z => ‖Ufin K z‖ ^ 2) 0 1 =
        ∑ j ∈ Finset.range K, ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j) := by
    rw [show Real.circleAverage (fun z => ‖Ufin K z‖ ^ 2) 0 1 =
        ∑ j ∈ Finset.range K,
          ‖taylorCoeff H j * (s : ℂ) ^ j‖ ^ 2 by
      simpa only [Ufin, finitePositiveFourier] using
        (truncatedPowerPolynomial_parseval
          (fun j => taylorCoeff H j * (s : ℂ) ^ j) K).symm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs]
    ring
  have hlimit : Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 =
      Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 s := by
    simpa only [U] using
      circleAverage_comp_mul (fun w => ‖H w‖ ^ 2) s
  simpa only [hfinite, hlimit] using havg

lemma shiftedTaylorEnergy_tendsto {H : ℂ → ℂ} {R s : ℝ}
    (hR : 0 < R) (hH : DifferentiableOn ℂ H (ball 0 R))
    (hs : 0 ≤ s) (hsR : s < R) (N : ℕ) :
    Filter.Tendsto
      (fun K => ∑ j ∈ Finset.range K,
        ((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j))
      Filter.atTop
      (nhds ((N : ℝ) * Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 s -
        analyticCircleFlux H s)) := by
  have hnorm := (taylorCoeff_sq_tendsto_circleAverage hH hs hsR).const_mul (N : ℝ)
  have hflux := analyticCircleFlux_tendsto hR hH hs hsR
  have hterm (K : ℕ) :
      (N : ℝ) * (∑ j ∈ Finset.range K,
          ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j)) -
        (∑ j ∈ Finset.range K,
          (j : ℝ) * ‖taylorCoeff H j * (s : ℂ) ^ j‖ ^ 2) =
      ∑ j ∈ Finset.range K,
        ((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs]
    ring
  have hlim := hnorm.sub hflux
  simpa only [hterm] using hlim

lemma shiftedTaylorEnergy_nonneg {H : ℂ → ℂ} {R s : ℝ}
    (hR : 0 < R) (hH : DifferentiableOn ℂ H (ball 0 R))
    (hs : 0 ≤ s) (hsR : s < R) (N K : ℕ) (hNK : N ≤ K)
    (hlimit : 0 ≤ (N : ℝ) * Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 s -
      analyticCircleFlux H s) :
    0 ≤ ∑ j ∈ Finset.range K,
      ((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j) := by
  have htend := shiftedTaylorEnergy_tendsto hR hH hs hsR N
  have hle :
      (N : ℝ) * Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 s -
          analyticCircleFlux H s ≤
        ∑ j ∈ Finset.range K,
          ((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j) := by
    apply le_of_tendsto htend
    filter_upwards [Filter.eventually_ge_atTop K] with J hKJ
    have hneg := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun j => -(((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j)))
      (Finset.range_mono hKJ) (by
        intro j hjJ hjK
        have hKj : K ≤ j := by
          simpa only [Finset.mem_range, not_lt] using hjK
        have hNj : (N : ℝ) ≤ j := by exact_mod_cast hNK.trans hKj
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hNj) (sq_nonneg _))
          (by positivity)) )
    have hneg' :
        -(∑ j ∈ Finset.range K,
            ((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j)) ≤
          -(∑ j ∈ Finset.range J,
            ((N : ℝ) - j) * ‖taylorCoeff H j‖ ^ 2 * s ^ (2 * j)) := by
      simpa only [← Finset.sum_neg_distrib] using hneg
    exact neg_le_neg_iff.mp hneg'
  exact hlimit.trans hle

lemma finiteFaberLaurent_coeff_neg {L : ℂ → ℂ} (hL0 : L 0 = 0)
    (c : ℕ → ℂ) (N q : ℕ) (hq0 : 0 < q) :
    (finiteFaberLaurent L c N).coeff (-(q : ℤ)) =
      if q ≤ N then c q else 0 := by
  unfold finiteFaberLaurent
  rw [HahnSeries.coeff_sum]
  by_cases hqN : q ≤ N
  · rw [if_pos hqN]
    let qIndex : ℕ := q - 1
    have hqIndex : qIndex ∈ Finset.range N := by
      rw [Finset.mem_range]
      dsimp only [qIndex]
      omega
    rw [Finset.sum_eq_single qIndex]
    · rw [HahnSeries.coeff_smul]
      have hindex : qIndex + 1 = q := by dsimp only [qIndex]; omega
      rw [hindex, (logarithmicFaber_principal_part hL0 q).1, smul_eq_mul, mul_one]
    · intro k hk hkq
      rw [HahnSeries.coeff_smul]
      have hkNe : (k : ℕ) + 1 ≠ q := by
        intro heq
        apply hkq
        dsimp only [qIndex]
        omega
      by_cases hqlt : q < (k : ℕ) + 1
      · rw [(logarithmicFaber_principal_part hL0 ((k : ℕ) + 1)).2 q]
        · simp
        · exact hqlt
      · have hklt : (k : ℕ) + 1 < q := by omega
        rw [coeff_faberLaurent_neg_eq_zero_of_lt
          (exteriorFactorPowerSeries L) ((k : ℕ) + 1) q hklt]
        simp
    · intro hnot
      exact (hnot hqIndex).elim
  · rw [if_neg hqN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [HahnSeries.coeff_smul]
    have hkN : (k : ℕ) + 1 ≤ N := Finset.mem_range.mp hk
    have hkltq : (k : ℕ) + 1 < q := by omega
    rw [coeff_faberLaurent_neg_eq_zero_of_lt
      (exteriorFactorPowerSeries L) ((k : ℕ) + 1) q hkltq]
    simp

lemma finiteFaberLaurent_coeff_nonneg (L : ℂ → ℂ) (c : ℕ → ℂ)
    (N m : ℕ) :
    (finiteFaberLaurent L c N).coeff (m : ℤ) =
      finiteGrunskyCombination L c N m := by
  unfold finiteFaberLaurent finiteGrunskyCombination
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  unfold grunskyCoeff
  have hk0 : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk0]

lemma taylorCoeff_finiteFaberShiftFunction_principal
    {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (c : ℕ → ℂ) (N q : ℕ) (hq0 : 0 < q) (hqN : q ≤ N) :
    taylorCoeff (finiteFaberShiftFunction L c N) (N - q) = c q := by
  rw [taylorCoeff_finiteFaberShiftFunction hR hL]
  have hindex : (((N - q : ℕ) : ℤ) - (N : ℤ)) = -(q : ℤ) := by
    rw [Nat.cast_sub hqN]
    ring
  rw [hindex, finiteFaberLaurent_coeff_neg hL0 c N q hq0, if_pos hqN]

lemma taylorCoeff_finiteFaberShiftFunction_tail
    {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R))
    (c : ℕ → ℂ) (N m : ℕ) :
    taylorCoeff (finiteFaberShiftFunction L c N) (N + m) =
      finiteGrunskyCombination L c N m := by
  rw [taylorCoeff_finiteFaberShiftFunction hR hL]
  have hindex : (((N + m : ℕ) : ℤ) - (N : ℤ)) = (m : ℤ) := by omega
  rw [hindex, finiteFaberLaurent_coeff_nonneg]

lemma lintegral_closedBall_eq_polar {g : ℂ → ℝ≥0∞} {A : ℝ} :
    (∫⁻ z in closedBall (0 : ℂ) A, g z) =
      ∫⁻ p in Ioc (0 : ℝ) A ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) := by
  have hpolar := Complex.lintegral_comp_polarCoord_symm
    ((closedBall (0 : ℂ) A).indicator g)
  rw [polarCoord_target] at hpolar
  rw [← lintegral_indicator (measurableSet_closedBall :
    MeasurableSet (closedBall (0 : ℂ) A))]
  rw [← hpolar]
  have hsubset : Ioc (0 : ℝ) A ×ˢ Ioo (-Real.pi) Real.pi ⊆
      Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
    rintro ⟨r, theta⟩ ⟨hr, htheta⟩
    exact ⟨hr.1, htheta⟩
  rw [← inter_eq_left.mpr hsubset]
  rw [← setLIntegral_indicator
    (measurableSet_Ioc.prod (measurableSet_Ioo :
      MeasurableSet (Ioo (-Real.pi) Real.pi)))
    (t := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)]
  apply setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ioo :
      MeasurableSet (Ioo (-Real.pi) Real.pi)))
  intro p hp
  change ENNReal.ofReal p.1 • (closedBall (0 : ℂ) A).indicator g
      (Complex.polarCoord.symm p) = _
  have hp0 : 0 < p.1 := hp.1
  have hball : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) A ↔
      p.1 ∈ Ioc (0 : ℝ) A := by
    rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp0]
    exact ⟨fun h => ⟨hp0, h⟩, fun h => h.2⟩
  by_cases hpA : p.1 ∈ Ioc (0 : ℝ) A
  · rw [Set.indicator_of_mem (hball.mpr hpA),
      Set.indicator_of_mem
        (show p ∈ Ioc (0 : ℝ) A ×ˢ Ioo (-Real.pi) Real.pi from ⟨hpA, hp.2⟩)]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hpA (hball.mp h)),
      Set.indicator_of_notMem
        (show p ∉ Ioc (0 : ℝ) A ×ˢ Ioo (-Real.pi) Real.pi by
          intro h
          exact hpA h.1)]
    simp

noncomputable def exteriorPolynomialPolar (f : ℂ → ℂ) (P : Polynomial ℂ) :
    ℝ × ℝ → ℂ :=
  (fun w => P.eval w) ∘ exteriorTransform f ∘ Complex.polarCoord.symm

lemma hasFDerivAt_exteriorPolynomialPolar {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R) (P : Polynomial ℂ)
    {p : ℝ × ℝ} (hp : Complex.polarCoord.symm p ∈ exteriorDisk R) :
    HasFDerivAt (exteriorPolynomialPolar f P)
      (((P.derivative.eval
          (exteriorTransform f (Complex.polarCoord.symm p)) •
          (1 : ℂ →L[ℝ] ℂ)).comp
        ((deriv (exteriorTransform f) (Complex.polarCoord.symm p) •
          (1 : ℂ →L[ℝ] ℂ)).comp (polarComplexFDeriv p)))) p := by
  have hpolar := hasFDerivAt_complex_polarCoord_symm p
  have hF := (exteriorTransform_differentiableAt hR hf hp).hasDerivAt.complexToReal_fderiv
  have hpoly := (P.hasDerivAt
    (exteriorTransform f (Complex.polarCoord.symm p))).complexToReal_fderiv
  simpa only [exteriorPolynomialPolar] using hpoly.comp p (hF.comp p hpolar)

lemma finiteFaberPolynomial_radialAreaFlux_eq_shiftedAnalyticCircleFlux
    {f L : ℂ → ℂ} {R r : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (c : ℕ → ℂ) (N : ℕ) (theta : ℝ) :
    radialAreaFlux
        (exteriorPolynomialPolar f (finiteFaberPolynomial L c N)) (r, theta) =
      shiftedAnalyticCircleFlux (finiteFaberShiftFunction L c N) N r theta := by
  have hr0 : 0 < r := (one_div_pos.mpr hR).trans hr
  have hpolar (t : ℝ) : Complex.polarCoord.symm (r, t) = circleMap 0 r t := by
    simp [circleMap, ← Complex.cos_add_sin_I]
  have hzExt (t : ℝ) : Complex.polarCoord.symm (r, t) ∈ exteriorDisk R := by
    rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm, abs_of_pos hr0]
    exact hr
  have hslice :
      (fun t => exteriorPolynomialPolar f (finiteFaberPolynomial L c N) (r, t)) =
        shiftedAnalyticCircle (finiteFaberShiftFunction L c N) N r := by
    funext t
    unfold exteriorPolynomialPolar shiftedAnalyticCircle
    simp only [Function.comp_apply]
    have hzCircle := hzExt t
    rw [hpolar] at hzCircle
    rw [hpolar]
    exact finiteFaberPolynomial_eval_exteriorTransform hR hf hexp c N hzCircle
  have hd := hasFDerivAt_exteriorPolynomialPolar hR hf
    (finiteFaberPolynomial L c N) (hzExt theta)
  have hsliceDeriv : HasDerivAt
      (fun t => exteriorPolynomialPolar f (finiteFaberPolynomial L c N) (r, t))
      (fderiv ℝ (exteriorPolynomialPolar f (finiteFaberPolynomial L c N))
        (r, theta) (0, 1)) theta := by
    have h := (hd.comp theta (hasFDerivAt_prodMk_right r theta)).hasDerivAt
    change HasDerivAt
      (fun t => exteriorPolynomialPolar f (finiteFaberPolynomial L c N) (r, t)) _ theta at h
    rw [hd.fderiv]
    exact h
  have hderiv := congrArg (fun F : ℝ → ℂ => deriv F theta) hslice
  unfold radialAreaFlux shiftedAnalyticCircleFlux
  rw [← hsliceDeriv.deriv, hderiv, congrFun hslice theta]

lemma exteriorPolynomialPolar_contDiffAt {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R) (P : Polynomial ℂ)
    {p : ℝ × ℝ} (hp : Complex.polarCoord.symm p ∈ exteriorDisk R) :
    ContDiffAt ℝ 2 (exteriorPolynomialPolar f P) p := by
  let z : ℂ := Complex.polarCoord.symm p
  have hFdiff : DifferentiableOn ℂ (exteriorTransform f) (exteriorDisk R) :=
    fun w hw => (exteriorTransform_differentiableAt hR hf hw).differentiableWithinAt
  have hF : ContDiffAt ℂ ⊤ (exteriorTransform f) z :=
    (hFdiff.contDiffOn (isOpen_exteriorDisk R)).contDiffAt
      ((isOpen_exteriorDisk R).mem_nhds hp)
  have hpolar : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Complex.polarCoord.symm q) p := by
    have hpair : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => (q.1 * Real.cos q.2, q.1 * Real.sin q.2)) p := by
      fun_prop
    simpa [Complex.polarCoord, Function.comp_def] using
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp p hpair
  have hpoly : ContDiffAt ℝ 2 (fun w : ℂ => P.eval w) (exteriorTransform f z) := by
    have hc : ContDiffAt ℂ 2 (fun w : ℂ => P.eval w) (exteriorTransform f z) := by
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ => simpa using hP.add hQ
      | monomial n a =>
          simpa [Polynomial.eval_monomial] using
            (contDiffAt_const.mul (contDiffAt_id.pow n))
    exact hc.restrict_scalars ℝ
  unfold exteriorPolynomialPolar
  exact hpoly.comp p (((hF.restrict_scalars ℝ).of_le (by norm_num)).comp p hpolar)

lemma exteriorPolynomialPolar_polarJacobian {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R) (P : Polynomial ℂ)
    {p : ℝ × ℝ} (hp : Complex.polarCoord.symm p ∈ exteriorDisk R) :
    polarJacobian (exteriorPolynomialPolar f P) p =
      p.1 * ‖deriv (exteriorTransform f) (Complex.polarCoord.symm p)‖ ^ 2 *
        ‖P.derivative.eval (exteriorTransform f (Complex.polarCoord.symm p))‖ ^ 2 := by
  have hd := hasFDerivAt_exteriorPolynomialPolar hR hf P hp
  unfold polarJacobian
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
  change signedCross
      (P.derivative.eval (exteriorTransform f (Complex.polarCoord.symm p)) *
        (deriv (exteriorTransform f) (Complex.polarCoord.symm p) *
          polarComplexFDeriv p (1, 0)))
      (P.derivative.eval (exteriorTransform f (Complex.polarCoord.symm p)) *
        (deriv (exteriorTransform f) (Complex.polarCoord.symm p) *
          polarComplexFDeriv p (0, 1))) = _
  rw [signedCross_mul_left, signedCross_mul_left, signedCross_polar]
  ring

lemma exteriorPolynomialPolar_polarJacobian_nonneg {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R) (P : Polynomial ℂ)
    {p : ℝ × ℝ} (hp0 : 0 ≤ p.1)
    (hp : Complex.polarCoord.symm p ∈ exteriorDisk R) :
    0 ≤ polarJacobian (exteriorPolynomialPolar f P) p := by
  rw [exteriorPolynomialPolar_polarJacobian hR hf P hp]
  positivity

lemma exteriorPolynomialPolar_angularAreaFlux_periodic {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R) (P : Polynomial ℂ)
    {r : ℝ} (hr : 1 / R < r) :
    angularAreaFlux (exteriorPolynomialPolar f P) (r, Real.pi) =
      angularAreaFlux (exteriorPolynomialPolar f P) (r, -Real.pi) := by
  have hr0 : 0 < r := (one_div_pos.mpr hR).trans hr
  have hzplus : Complex.polarCoord.symm (r, Real.pi) ∈ exteriorDisk R := by
    rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm, abs_of_pos hr0]
    exact hr
  have hzminus : Complex.polarCoord.symm (r, -Real.pi) ∈ exteriorDisk R := by
    rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm, abs_of_pos hr0]
    exact hr
  have hdplus := hasFDerivAt_exteriorPolynomialPolar hR hf P hzplus
  have hdminus := hasFDerivAt_exteriorPolynomialPolar hR hf P hzminus
  have hzEq : Complex.polarCoord.symm (r, Real.pi) =
      Complex.polarCoord.symm (r, -Real.pi) := by
    simp [Complex.polarCoord_symm_apply]
  have hval : exteriorPolynomialPolar f P (r, Real.pi) =
      exteriorPolynomialPolar f P (r, -Real.pi) := by
    simp only [exteriorPolynomialPolar, Function.comp_apply]
    rw [hzEq]
  have hderiv : fderiv ℝ (exteriorPolynomialPolar f P) (r, Real.pi) (1, 0) =
      fderiv ℝ (exteriorPolynomialPolar f P) (r, -Real.pi) (1, 0) := by
    rw [hdplus.fderiv, hdminus.fderiv]
    change P.derivative.eval (exteriorTransform f _) *
        (deriv (exteriorTransform f) _ * polarComplexFDeriv (r, Real.pi) (1, 0)) =
      P.derivative.eval (exteriorTransform f _) *
        (deriv (exteriorTransform f) _ * polarComplexFDeriv (r, -Real.pi) (1, 0))
    rw [hzEq, polarComplexFDeriv_radial, polarComplexFDeriv_radial]
    simp
  unfold angularAreaFlux
  rw [hval, hderiv]

lemma exteriorWeightedIntegral_eq_polarJacobian {f : ℂ → ℂ} {R r A : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hr : 1 / R < r) (P : Polynomial ℂ) :
    (∫⁻ z in closedAnnulus r A,
        ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2) *
          polynomialDerivativeWeight P (exteriorTransform f z)) =
      ∫⁻ p in Icc r A ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (polarJacobian (exteriorPolynomialPolar f P) p) := by
  have hr0 : 0 < r := (one_div_pos.mpr hR).trans hr
  rw [lintegral_closedAnnulus_eq_polar hr0]
  apply setLIntegral_congr_fun
    (measurableSet_Icc.prod (measurableSet_Ioo :
      MeasurableSet (Ioo (-Real.pi) Real.pi)))
  intro p hp
  have hp0 : 0 < p.1 := hr0.trans_le hp.1.1
  have hpExt : Complex.polarCoord.symm p ∈ exteriorDisk R := by
    rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm, abs_of_pos hp0]
    exact hr.trans_le hp.1.1
  change ENNReal.ofReal p.1 *
      (ENNReal.ofReal (‖deriv (exteriorTransform f) (Complex.polarCoord.symm p)‖ ^ 2) *
        polynomialDerivativeWeight P
          (exteriorTransform f (Complex.polarCoord.symm p))) =
    ENNReal.ofReal (polarJacobian (exteriorPolynomialPolar f P) p)
  rw [exteriorPolynomialPolar_polarJacobian hR hf P hpExt]
  unfold polynomialDerivativeWeight
  rw [ENNReal.ofReal_mul (mul_nonneg hp0.le (sq_nonneg _)),
    ENNReal.ofReal_mul hp0.le]
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
  ring

lemma fillWeightedIntegral_eq_polarJacobian {L : ℂ → ℂ} {R A ρ : ℝ}
    {M : NNReal} (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (P : Polynomial ℂ) :
    (∫⁻ z in closedBall (0 : ℂ) A,
        ENNReal.ofReal |(harmonicFillFDeriv L A z).det| *
          polynomialDerivativeWeight P (exteriorHarmonicFill L A z)) =
      ∫⁻ p in Icc (0 : ℝ) A ×ˢ Icc (-Real.pi) Real.pi,
        ENNReal.ofReal (polarJacobian (faberFillPolar L A P) p) := by
  rw [lintegral_closedBall_eq_polar]
  calc
    (∫⁻ p in Ioc (0 : ℝ) A ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 *
          (ENNReal.ofReal |(harmonicFillFDeriv L A
              (Complex.polarCoord.symm p)).det| *
            polynomialDerivativeWeight P
              (exteriorHarmonicFill L A (Complex.polarCoord.symm p)))) =
        ∫⁻ p in Icc (0 : ℝ) A ×ˢ Icc (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 *
            (ENNReal.ofReal |(harmonicFillFDeriv L A
                (Complex.polarCoord.symm p)).det| *
              polynomialDerivativeWeight P
                (exteriorHarmonicFill L A (Complex.polarCoord.symm p))) := by
      exact setLIntegral_congr
        (Measure.set_prod_ae_eq (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))
          (Ioo_ae_eq_Icc (α := ℝ) (μ := volume)))
    _ = ∫⁻ p in Icc (0 : ℝ) A ×ˢ Icc (-Real.pi) Real.pi,
          ENNReal.ofReal (polarJacobian (faberFillPolar L A P) p) := by
      apply setLIntegral_congr_fun
        (measurableSet_Icc.prod (measurableSet_Icc :
          MeasurableSet (Icc (-Real.pi) Real.pi)))
      intro p hp
      have hp0 : 0 ≤ p.1 := hp.1.1
      have hpA : p.1 ≤ A := hp.1.2
      have hzA : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) A := by
        rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm,
          abs_of_nonneg hp0]
        exact hpA
      have hfactor := harmonicFactor_nonneg hA hAρ hP hK hzA
      have hdet : |(harmonicFillFDeriv L A (Complex.polarCoord.symm p)).det| =
          1 - (‖deriv (exteriorAnalyticSlope L)
            (interiorReflection A (Complex.polarCoord.symm p))‖ / A ^ 2) ^ 2 := by
        rw [det_harmonicFillFDeriv]
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hA.le]
        exact abs_of_nonneg hfactor
      change ENNReal.ofReal p.1 *
          (ENNReal.ofReal |(harmonicFillFDeriv L A
              (Complex.polarCoord.symm p)).det| *
            polynomialDerivativeWeight P
              (exteriorHarmonicFill L A (Complex.polarCoord.symm p))) =
        ENNReal.ofReal (polarJacobian (faberFillPolar L A P) p)
      rw [faberFillPolar_polarJacobian hR hL hA (hAρ.trans hρR) P hp0 hpA]
      unfold polynomialDerivativeWeight
      rw [hdet]
      rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
      rw [← ENNReal.ofReal_mul hfactor, ← ENNReal.ofReal_mul hp0]
      congr 1
      ring

lemma exteriorPolarJacobian_lintegral_eq_ofReal_integral
    {f : ℂ → ℂ} {R r A : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hr : 1 / R < r)
    (P : Polynomial ℂ) :
    (∫⁻ p in Icc r A ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (polarJacobian (exteriorPolynomialPolar f P) p)) =
      ENNReal.ofReal
        (∫ p in Icc (r, -Real.pi) (A, Real.pi),
          polarJacobian (exteriorPolynomialPolar f P) p) := by
  have hr0 : 0 < r := (one_div_pos.mpr hR).trans hr
  calc
    (∫⁻ p in Icc r A ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (polarJacobian (exteriorPolynomialPolar f P) p)) =
        ∫⁻ p in Icc r A ×ˢ Icc (-Real.pi) Real.pi,
          ENNReal.ofReal (polarJacobian (exteriorPolynomialPolar f P) p) := by
      exact setLIntegral_congr
        (Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
          (Ioo_ae_eq_Icc (α := ℝ) (μ := volume)))
    _ = ∫⁻ p in Icc (r, -Real.pi) (A, Real.pi),
          ENNReal.ofReal (polarJacobian (exteriorPolynomialPolar f P) p) := by
      rw [Icc_prod_Icc]
    _ = ENNReal.ofReal
        (∫ p in Icc (r, -Real.pi) (A, Real.pi),
          polarJacobian (exteriorPolynomialPolar f P) p) := by
      symm
      apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      · apply ContinuousOn.integrableOn_Icc
        intro p hp
        have hp0 : 0 < p.1 := hr0.trans_le hp.1.1
        have hpExt : Complex.polarCoord.symm p ∈ exteriorDisk R := by
          rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm,
            abs_of_pos hp0]
          exact hr.trans_le hp.1.1
        exact (polarJacobian_contDiffAt
          (exteriorPolynomialPolar_contDiffAt hR hf P hpExt)).continuousAt
            |>.continuousWithinAt
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
        have hp0 : 0 < p.1 := hr0.trans_le hp.1.1
        have hpExt : Complex.polarCoord.symm p ∈ exteriorDisk R := by
          rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm,
            abs_of_pos hp0]
          exact hr.trans_le hp.1.1
        exact exteriorPolynomialPolar_polarJacobian_nonneg hR hf P hp0.le hpExt

lemma fillPolarJacobian_lintegral_eq_ofReal_integral
    {L : ℂ → ℂ} {R A ρ : ℝ} {M : NNReal}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (P : Polynomial ℂ) :
    (∫⁻ p in Icc (0 : ℝ) A ×ˢ Icc (-Real.pi) Real.pi,
        ENNReal.ofReal (polarJacobian (faberFillPolar L A P) p)) =
      ENNReal.ofReal
        (∫ p in Icc ((0 : ℝ), -Real.pi) (A, Real.pi),
          polarJacobian (faberFillPolar L A P) p) := by
  rw [Icc_prod_Icc]
  symm
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
  · apply ContinuousOn.integrableOn_Icc
    intro p hp
    exact (polarJacobian_contDiffAt
      (faberFillPolar_contDiffAt hR hL hA (hAρ.trans hρR) P hp.1.1 hp.2.1)).continuousAt
        |>.continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    rw [faberFillPolar_polarJacobian hR hL hA (hAρ.trans hρR) P hp.1.1 hp.2.1]
    have hzA : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) A := by
      rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm,
        abs_of_nonneg hp.1.1]
      exact hp.2.1
    exact mul_nonneg (mul_nonneg hp.1.1 (sq_nonneg _))
      (harmonicFactor_nonneg hA hAρ hP hK hzA)

lemma faberFillPolar_radialAreaFlux_eq_exteriorPolynomialPolar
    {f L : ℂ → ℂ} {R A : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hA : 0 < A) (hRA : 1 / R < A) (P : Polynomial ℂ) (theta : ℝ) :
    radialAreaFlux (faberFillPolar L A P) (A, theta) =
      radialAreaFlux (exteriorPolynomialPolar f P) (A, theta) := by
  have hAR : 1 / A < R := (one_div_lt hR hA).mp hRA
  have hzSphere (t : ℝ) : Complex.polarCoord.symm (A, t) ∈ sphere (0 : ℂ) A := by
    rw [mem_sphere, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hA]
  have hzBall : Complex.polarCoord.symm (A, theta) ∈ closedBall (0 : ℂ) A := by
    rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hA]
  have hzExt : Complex.polarCoord.symm (A, theta) ∈ exteriorDisk R := by
    rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm, abs_of_pos hA]
    exact hRA
  have hboundary := exteriorHarmonicFill_eq_exteriorTransform_on_sphere
    hR hA hRA hf hL0 hexp
  have hslice : (fun t => faberFillPolar L A P (A, t)) =
      fun t => exteriorPolynomialPolar f P (A, t) := by
    funext t
    unfold faberFillPolar exteriorPolynomialPolar
    exact congrArg P.eval (hboundary (hzSphere t))
  have hdFill := hasFDerivAt_faberFillPolar hR hL hA hAR P hzBall
  have hdExt := hasFDerivAt_exteriorPolynomialPolar hR hf P hzExt
  have hfillSlice : HasDerivAt (fun t => faberFillPolar L A P (A, t))
      (fderiv ℝ (faberFillPolar L A P) (A, theta) (0, 1)) theta := by
    have h := (hdFill.comp theta (hasFDerivAt_prodMk_right A theta)).hasDerivAt
    change HasDerivAt (fun t : ℝ => faberFillPolar L A P (A, t)) _ theta at h
    rw [hdFill.fderiv]
    exact h
  have hextSlice : HasDerivAt (fun t => exteriorPolynomialPolar f P (A, t))
      (fderiv ℝ (exteriorPolynomialPolar f P) (A, theta) (0, 1)) theta := by
    have h := (hdExt.comp theta (hasFDerivAt_prodMk_right A theta)).hasDerivAt
    change HasDerivAt (fun t : ℝ => exteriorPolynomialPolar f P (A, t)) _ theta at h
    rw [hdExt.fderiv]
    exact h
  have hderiv : fderiv ℝ (faberFillPolar L A P) (A, theta) (0, 1) =
      fderiv ℝ (exteriorPolynomialPolar f P) (A, theta) (0, 1) := by
    rw [← hfillSlice.deriv, ← hextSlice.deriv]
    exact congrArg (fun F : ℝ → ℂ => deriv F theta) hslice
  have hval : faberFillPolar L A P (A, theta) =
      exteriorPolynomialPolar f P (A, theta) := congrFun hslice theta
  unfold radialAreaFlux
  rw [hval, hderiv]

lemma polynomialDerivativeWeight_image_mono {f L : ℂ → ℂ} {R r A ρ : ℝ}
    {M : NNReal} (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (hrA : r ≤ A) (hA : 0 < A)
    (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (P : Polynomial ℂ) :
    (∫⁻ z in closedAnnulus r A,
        ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2) *
          polynomialDerivativeWeight P (exteriorTransform f z)) ≤
      ∫⁻ z in closedBall (0 : ℂ) A,
        ENNReal.ofReal |(harmonicFillFDeriv L A z).det| *
          polynomialDerivativeWeight P (exteriorHarmonicFill L A z) := by
  have hRA : 1 / R < A := hr.trans_le hrA
  rcases exists_exteriorGluedMap_homeomorph hA hAρ.le hP hK with ⟨e, he⟩
  have hfill : Set.EqOn (exteriorHarmonicFill L A) e (closedBall (0 : ℂ) A) := by
    intro z hz
    rw [he, exteriorGluedMap_eq_fill hz]
  have hinjFill : (closedBall (0 : ℂ) A).InjOn (exteriorHarmonicFill L A) := by
    intro x hx y hy hxy
    apply e.injective
    rw [← hfill hx, ← hfill hy]
    exact hxy
  have himage := exteriorTransform_image_closedAnnulus_subset_fill_image
    hR hRA hf hL0 hexp hr he
  calc
    (∫⁻ z in closedAnnulus r A,
        ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2) *
          polynomialDerivativeWeight P (exteriorTransform f z)) =
        ∫⁻ w in exteriorTransform f '' closedAnnulus r A,
          polynomialDerivativeWeight P w := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume)
        (measurableSet_closedAnnulus r A)
        (fun z hz => (exteriorTransform_differentiableAt hR hf
          (closedAnnulus_subset_exteriorDisk hr hz)).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt)
        ((exteriorTransform_injOn hR hf).mono
          (closedAnnulus_subset_exteriorDisk hr))]
      apply MeasureTheory.setLIntegral_congr_fun (measurableSet_closedAnnulus r A)
      intro z hz
      dsimp only
      rw [det_complex_smul_one, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ∫⁻ w in exteriorHarmonicFill L A '' closedBall (0 : ℂ) A,
          polynomialDerivativeWeight P w :=
      lintegral_mono' (Measure.restrict_mono himage le_rfl) le_rfl
    _ = ∫⁻ z in closedBall (0 : ℂ) A,
        ENNReal.ofReal |(harmonicFillFDeriv L A z).det| *
          polynomialDerivativeWeight P (exteriorHarmonicFill L A z) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume)
        (measurableSet_closedBall : MeasurableSet (closedBall (0 : ℂ) A))
        (fun z hz => (hasFDerivAt_exteriorHarmonicFill hR hL hA
          (hAρ.trans hρR) hz).hasFDerivWithinAt) hinjFill]

lemma exteriorPolynomialPolar_radialAreaFlux_nonneg_of_fill
    {f L : ℂ → ℂ} {R r A ρ : ℝ} {M : NNReal}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (hrA : r ≤ A) (hA : 0 < A)
    (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (P : Polynomial ℂ) :
    0 ≤ ∫ theta in -Real.pi..Real.pi,
      radialAreaFlux (exteriorPolynomialPolar f P) (r, theta) := by
  have hRA : 1 / R < A := hr.trans_le hrA
  have hmono := polynomialDerivativeWeight_image_mono hR hf hL hL0 hexp
    hr hrA hA hAρ hρR hP hK P
  rw [exteriorWeightedIntegral_eq_polarJacobian hR hf hr P,
    fillWeightedIntegral_eq_polarJacobian hR hL hA hAρ hρR hP hK P,
    exteriorPolarJacobian_lintegral_eq_ofReal_integral hR hf hr P,
    fillPolarJacobian_lintegral_eq_ofReal_integral
      hR hL hA hAρ hρR hP hK P] at hmono
  have hfillIntegralNonneg :
      0 ≤ ∫ p in Icc ((0 : ℝ), -Real.pi) (A, Real.pi),
        polarJacobian (faberFillPolar L A P) p := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    rw [faberFillPolar_polarJacobian hR hL hA (hAρ.trans hρR) P hp.1.1 hp.2.1]
    have hzA : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) A := by
      rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm,
        abs_of_nonneg hp.1.1]
      exact hp.2.1
    exact mul_nonneg (mul_nonneg hp.1.1 (sq_nonneg _))
      (harmonicFactor_nonneg hA hAρ hP hK hzA)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hfillIntegralNonneg).mp hmono
  have hextGreen := integral_polarJacobian_eq_radialAreaFlux_sub hrA
    (phi := exteriorPolynomialPolar f P)
    (fun p hp => by
      have hp0 : 0 < p.1 := ((one_div_pos.mpr hR).trans hr).trans_le hp.1.1
      have hpExt : Complex.polarCoord.symm p ∈ exteriorDisk R := by
        rw [exteriorDisk, mem_setOf_eq, Complex.norm_polarCoord_symm,
          abs_of_pos hp0]
        exact hr.trans_le hp.1.1
      exact exteriorPolynomialPolar_contDiffAt hR hf P hpExt)
    (fun s hs => exteriorPolynomialPolar_angularAreaFlux_periodic hR hf P
      (hr.trans_le hs.1))
  have hfillGreen := integral_polarJacobian_eq_radialAreaFlux_sub hA.le
    (phi := faberFillPolar L A P)
    (fun p hp => faberFillPolar_contDiffAt hR hL hA (hAρ.trans hρR) P
      hp.1.1 hp.2.1)
    (fun s hs => faberFillPolar_angularAreaFlux_periodic hR hL hA
      (hAρ.trans hρR) P hs.1 hs.2)
  have hfillZero :
      (∫ theta in -Real.pi..Real.pi,
        radialAreaFlux (faberFillPolar L A P) (0, theta)) = 0 := by
    calc
      (∫ theta in -Real.pi..Real.pi,
          radialAreaFlux (faberFillPolar L A P) (0, theta)) =
          ∫ _theta in -Real.pi..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        intro theta _
        exact faberFillPolar_radialAreaFlux_zero hR hL hA
          (hAρ.trans hρR) P theta
      _ = 0 := by simp
  have houter :
      (∫ theta in -Real.pi..Real.pi,
        radialAreaFlux (faberFillPolar L A P) (A, theta)) =
      ∫ theta in -Real.pi..Real.pi,
        radialAreaFlux (exteriorPolynomialPolar f P) (A, theta) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    intro theta _
    exact faberFillPolar_radialAreaFlux_eq_exteriorPolynomialPolar
      hR hf hL hL0 hexp hA hRA P theta
  rw [hfillZero, sub_zero, houter] at hfillGreen
  rw [hextGreen, hfillGreen] at hreal
  linarith

lemma exteriorPolynomialPolar_radialAreaFlux_nonneg
    {f L : ℂ → ℂ} {R r : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (P : Polynomial ℂ) :
    0 ≤ ∫ theta in -Real.pi..Real.pi,
      radialAreaFlux (exteriorPolynomialPolar f P) (r, theta) := by
  rcases exists_exteriorAnalyticSlope_lipschitzOn hR hL with
    ⟨rho, hrho, hrhoR, M, hM⟩
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (max r (max (1 / rho) ((M : ℝ) + 1)))
  let A : ℝ := N
  have hrA : r ≤ A := (le_max_left _ _).trans hN.le
  have hinner : max (1 / rho) ((M : ℝ) + 1) < A :=
    (le_max_right r _).trans_lt hN
  have hArho' : 1 / rho < A := (le_max_left _ _).trans_lt hinner
  have hMA : (M : ℝ) + 1 < A := (le_max_right _ _).trans_lt hinner
  have hr0 : 0 < r := (one_div_pos.mpr hR).trans hr
  have hA : 0 < A := hr0.trans_le hrA
  have hArho : 1 / A < rho := (one_div_lt hrho hA).mp hArho'
  have hAone : 1 < A := by
    have hM0 : 0 ≤ (M : ℝ) := NNReal.coe_nonneg M
    linarith
  have hMAsq : (M : ℝ) < A ^ 2 := by
    nlinarith
  have hK : M * interiorReflectionLipschitzConstant A < 1 := by
    apply NNReal.coe_lt_coe.mp
    change (M : ℝ) * (1 / A ^ 2) < 1
    rw [mul_one_div]
    exact (div_lt_one (sq_pos_of_pos hA)).2 hMAsq
  exact exteriorPolynomialPolar_radialAreaFlux_nonneg_of_fill
    hR hf hL hL0 hexp hr hrA hA hArho hrhoR hM hK P

lemma finiteFaberShiftFunction_shiftedTaylorEnergy_nonneg
    {f L : ℂ → ℂ} {R r : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (c : ℕ → ℂ) (N K : ℕ) (hNK : N ≤ K) :
    0 ≤ ∑ j ∈ Finset.range K,
      ((N : ℝ) - j) *
        ‖taylorCoeff (finiteFaberShiftFunction L c N) j‖ ^ 2 *
          (1 / r) ^ (2 * j) := by
  let H := finiteFaberShiftFunction L c N
  let P := finiteFaberPolynomial L c N
  have hr0 : 0 < r := (one_div_pos.mpr hR).trans hr
  have hrR : 1 / r < R := (one_div_lt hR hr0).mp hr
  have hH : DifferentiableOn ℂ H (ball 0 R) := by
    exact finiteFaberShiftFunction_differentiableOn hL c N
  have hflux := exteriorPolynomialPolar_radialAreaFlux_nonneg
    hR hf hL hL0 hexp hr P
  have hfluxEq :
      (∫ theta in -Real.pi..Real.pi,
        radialAreaFlux (exteriorPolynomialPolar f P) (r, theta)) =
      ∫ theta in -Real.pi..Real.pi, shiftedAnalyticCircleFlux H N r theta := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    intro theta htheta
    exact finiteFaberPolynomial_radialAreaFlux_eq_shiftedAnalyticCircleFlux
      hR hf hexp hr c N theta
  rw [hfluxEq, integral_shiftedAnalyticCircleFlux_eq hH hr0 hrR N] at hflux
  have hfactor : 0 < Real.pi * r ^ (2 * N) :=
    mul_pos Real.pi_pos (pow_pos hr0 _)
  have hlimit : 0 ≤
      (N : ℝ) * Real.circleAverage (fun w => ‖H w‖ ^ 2) 0 (1 / r) -
        analyticCircleFlux H (1 / r) :=
    nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hflux) hfactor
  exact shiftedTaylorEnergy_nonneg hR hH (one_div_nonneg.mpr hr0.le) hrR
    N K hNK hlimit

lemma finiteGrunskyCombination_norm_sq_le
    {f L : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (c : ℕ → ℂ) (N M : ℕ) :
    (∑ m ∈ Finset.range M,
        (m : ℝ) * ‖finiteGrunskyCombination L c N m‖ ^ 2) ≤
      ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * ‖c (k + 1)‖ ^ 2 := by
  have hR : 0 < R := zero_lt_one.trans hR1
  have hr : 1 / R < (1 : ℝ) := by
    simpa using one_div_lt_one_div_of_lt one_pos hR1
  have henergy := finiteFaberShiftFunction_shiftedTaylorEnergy_nonneg
    hR hf hL hL0 hexp hr c N (N + M) (by omega)
  simp only [one_div, inv_one, one_pow, mul_one] at henergy
  rw [Finset.sum_range_add] at henergy
  have hprincipal :
      (∑ j ∈ Finset.range N,
          ((N : ℝ) - j) *
            ‖taylorCoeff (finiteFaberShiftFunction L c N) j‖ ^ 2) =
        ∑ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) * ‖c (k + 1)‖ ^ 2 := by
    let a : ℕ → ℝ := fun j =>
      ((N : ℝ) - j) *
        ‖taylorCoeff (finiteFaberShiftFunction L c N) j‖ ^ 2
    change (∑ j ∈ Finset.range N, a j) = _
    calc
      (∑ j ∈ Finset.range N, a j) =
          ∑ k ∈ Finset.range N, a (N - 1 - k) :=
        (Finset.sum_range_reflect a N).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkN : k + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
        dsimp only [a]
        rw [show N - 1 - k = N - (k + 1) by omega]
        rw [taylorCoeff_finiteFaberShiftFunction_principal
          hR hL hL0 c N (k + 1) (by omega) hkN]
        rw [Nat.cast_sub hkN]
        push_cast
        ring
  have htail :
      (∑ m ∈ Finset.range M,
          ((N : ℝ) - ((N + m : ℕ) : ℝ)) *
            ‖taylorCoeff (finiteFaberShiftFunction L c N) (N + m)‖ ^ 2) =
        -(∑ m ∈ Finset.range M,
          (m : ℝ) * ‖finiteGrunskyCombination L c N m‖ ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [taylorCoeff_finiteFaberShiftFunction_tail hR hL]
    push_cast
    ring
  rw [hprincipal, htail] at henergy
  linarith

end Submission
