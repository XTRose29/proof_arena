import Submission.GrunskyInequality

open Metric Set

noncomputable section

namespace Submission

noncomputable def finitePositiveFourier (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (truncatedPowerPolynomial a N).eval z

noncomputable def finiteEulerFourier (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (truncatedPowerPolynomial (fun n => (n : ℂ) * a n) N).eval z

lemma signedCross_mul_I (u v : ℂ) :
    signedCross u (Complex.I * v) = (starRingEnd ℂ u * v).re := by
  simp [signedCross, Complex.mul_re, Complex.mul_im]

lemma two_mul_signedCross_mul_I (u v : ℂ) :
    2 * signedCross u (Complex.I * v) =
      ‖u + v‖ ^ 2 - ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  rw [signedCross_mul_I, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

lemma finitePositiveFourier_add_euler (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    finitePositiveFourier a N z + finiteEulerFourier a N z =
      finitePositiveFourier (fun n => ((n + 1 : ℕ) : ℂ) * a n) N z := by
  simp only [finitePositiveFourier, finiteEulerFourier,
    eval_truncatedPowerPolynomial]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

lemma circleAverage_signedCross_mul_I_eq_norms {U D : ℂ → ℂ}
    (hUSq : CircleIntegrable (fun z => ‖U z‖ ^ 2) 0 1)
    (hDSq : CircleIntegrable (fun z => ‖D z‖ ^ 2) 0 1)
    (hSumSq : CircleIntegrable (fun z => ‖U z + D z‖ ^ 2) 0 1) :
    Real.circleAverage (fun z => signedCross (U z) (Complex.I * D z)) 0 1 =
      (1 / 2 : ℝ) *
        (Real.circleAverage (fun z => ‖U z + D z‖ ^ 2) 0 1 -
          Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 -
          Real.circleAverage (fun z => ‖D z‖ ^ 2) 0 1) := by
  have hpoint : (fun z => signedCross (U z) (Complex.I * D z)) =
      fun z => (1 / 2 : ℝ) * (‖U z + D z‖ ^ 2 - ‖U z‖ ^ 2 - ‖D z‖ ^ 2) := by
    funext z
    nlinarith [two_mul_signedCross_mul_I (U z) (D z)]
  rw [hpoint]
  rw [show (fun z => (1 / 2 : ℝ) *
      (‖U z + D z‖ ^ 2 - ‖U z‖ ^ 2 - ‖D z‖ ^ 2)) =
    fun z => (1 / 2 : ℝ) •
      (((fun w => ‖U w + D w‖ ^ 2) - (fun w => ‖U w‖ ^ 2)) z -
        (fun w => ‖D w‖ ^ 2) z) by
      funext z
      simp]
  rw [Real.circleAverage_fun_smul]
  change (1 / 2 : ℝ) • Real.circleAverage
    (((fun z => ‖U z + D z‖ ^ 2) - (fun z => ‖U z‖ ^ 2)) -
      (fun z => ‖D z‖ ^ 2)) 0 1 = _
  rw [Real.circleAverage_sub (hSumSq.sub hUSq) hDSq,
    Real.circleAverage_sub hSumSq hUSq]
  simp

lemma finitePositiveFourier_flux_parseval (a : ℕ → ℂ) (N : ℕ) :
    Real.circleAverage
        (fun z => signedCross (finitePositiveFourier a N z)
          (Complex.I * finiteEulerFourier a N z)) 0 1 =
      ∑ n ∈ Finset.range N, (n : ℝ) * ‖a n‖ ^ 2 := by
  let U : ℂ → ℂ := finitePositiveFourier a N
  let D : ℂ → ℂ := finiteEulerFourier a N
  have hU : Continuous U := by
    dsimp only [U, finitePositiveFourier]
    exact continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial a N).hasDerivAt z).continuousAt
  have hD : Continuous D := by
    dsimp only [D, finiteEulerFourier]
    exact continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial (fun n => (n : ℂ) * a n) N).hasDerivAt z).continuousAt
  have hUSq : CircleIntegrable (fun z => ‖U z‖ ^ 2) 0 1 :=
    (hU.norm.pow 2).continuousOn.circleIntegrable (by norm_num)
  have hDSq : CircleIntegrable (fun z => ‖D z‖ ^ 2) 0 1 :=
    (hD.norm.pow 2).continuousOn.circleIntegrable (by norm_num)
  have hSumSq : CircleIntegrable (fun z => ‖U z + D z‖ ^ 2) 0 1 :=
    ((hU.add hD).norm.pow 2).continuousOn.circleIntegrable (by norm_num)
  have hpoint : (fun z => signedCross (U z) (Complex.I * D z)) =
      fun z => (1 / 2 : ℝ) * (‖U z + D z‖ ^ 2 - ‖U z‖ ^ 2 - ‖D z‖ ^ 2) := by
    funext z
    nlinarith [two_mul_signedCross_mul_I (U z) (D z)]
  change Real.circleAverage (fun z => signedCross (U z) (Complex.I * D z)) 0 1 = _
  rw [hpoint]
  have hlinear :
      Real.circleAverage
          (fun z => (1 / 2 : ℝ) * (‖U z + D z‖ ^ 2 - ‖U z‖ ^ 2 - ‖D z‖ ^ 2)) 0 1 =
        (1 / 2 : ℝ) *
          (Real.circleAverage (fun z => ‖U z + D z‖ ^ 2) 0 1 -
            Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 -
            Real.circleAverage (fun z => ‖D z‖ ^ 2) 0 1) := by
    rw [show (fun z => (1 / 2 : ℝ) *
        (‖U z + D z‖ ^ 2 - ‖U z‖ ^ 2 - ‖D z‖ ^ 2)) =
      fun z => (1 / 2 : ℝ) •
        ((fun w => ‖U w + D w‖ ^ 2) z -
          (fun w => ‖U w‖ ^ 2) z - (fun w => ‖D w‖ ^ 2) z) by
        funext z
        simp]
    rw [Real.circleAverage_fun_smul]
    change (1 / 2 : ℝ) • Real.circleAverage
      (((fun z => ‖U z + D z‖ ^ 2) - (fun z => ‖U z‖ ^ 2)) -
        (fun z => ‖D z‖ ^ 2)) 0 1 = _
    rw [Real.circleAverage_sub (hSumSq.sub hUSq) hDSq,
      Real.circleAverage_sub hSumSq hUSq]
    simp
  rw [hlinear]
  have hparseU : Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
    simpa [U, finitePositiveFourier] using
      (truncatedPowerPolynomial_parseval a N).symm
  have hparseD : Real.circleAverage (fun z => ‖D z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖(n : ℂ) * a n‖ ^ 2 := by
    simpa [D, finiteEulerFourier] using
      (truncatedPowerPolynomial_parseval (fun n => (n : ℂ) * a n) N).symm
  have hparseSum : Real.circleAverage (fun z => ‖U z + D z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖((n + 1 : ℕ) : ℂ) * a n‖ ^ 2 := by
    have hfun : (fun z => U z + D z) =
        finitePositiveFourier (fun n => ((n + 1 : ℕ) : ℂ) * a n) N := by
      funext z
      exact finitePositiveFourier_add_euler a N z
    rw [show (fun z => ‖U z + D z‖ ^ 2) =
        fun z => ‖finitePositiveFourier
          (fun n => ((n + 1 : ℕ) : ℂ) * a n) N z‖ ^ 2 by
      funext z
      rw [congrFun hfun z]]
    simpa [finitePositiveFourier] using
      (truncatedPowerPolynomial_parseval
        (fun n => ((n + 1 : ℕ) : ℂ) * a n) N).symm
  rw [hparseSum, hparseU, hparseD]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [norm_mul, Complex.norm_natCast]
  push_cast
  ring

lemma tendstoUniformlyOn_finitePositiveFourier_taylor {H : ℂ → ℂ} {R r : ℝ}
    (hH : DifferentiableOn ℂ H (ball 0 R)) (hr : 0 ≤ r) (hrR : r < R) :
    TendstoUniformlyOn
      (fun N z => finitePositiveFourier
        (fun n => taylorCoeff H n * (r : ℂ) ^ n) N z)
      (fun z => H ((r : ℂ) * z)) Filter.atTop (sphere (0 : ℂ) 1) := by
  let P : ℕ → ℂ → ℂ := fun N z =>
    ∑ n ∈ Finset.range N, (taylorCoeff H n * (r : ℂ) ^ n) * z ^ n
  let fsum : ℂ → ℂ := fun z =>
    ∑' n, (taylorCoeff H n * (r : ℂ) ^ n) * z ^ n
  have hsummable : Summable (fun n => ‖taylorCoeff H n‖ * r ^ n) :=
    summable_norm_taylorCoeff_mul_pow hH hr hrR
  have huniformSum : TendstoUniformlyOn P fsum Filter.atTop (sphere (0 : ℂ) 1) := by
    apply tendstoUniformlyOn_tsum_nat hsummable
    intro n z hz
    have hznorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr, hznorm]
    simp
  have hEq : Set.EqOn fsum (fun z => H ((r : ℂ) * z)) (sphere (0 : ℂ) 1) := by
    intro z hz
    have hznorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
        hznorm, mul_one]
      exact hrR
    have hsum := Complex.hasSum_taylorSeries_on_ball hH hrz
    change (∑' n, (taylorCoeff H n * (r : ℂ) ^ n) * z ^ n) = H ((r : ℂ) * z)
    rw [← hsum.tsum_eq]
    apply tsum_congr
    intro n
    simp only [taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv]
    rw [mul_pow]
    ring
  have h := huniformSum.congr_right hEq
  simpa only [P, finitePositiveFourier, eval_truncatedPowerPolynomial] using h

noncomputable def analyticCircleFlux (H : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage
    (fun z => signedCross (H ((r : ℂ) * z))
      (Complex.I * (((r : ℂ) * z) * deriv H ((r : ℂ) * z)))) 0 1

lemma analyticCircleFlux_tendsto {H : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hH : DifferentiableOn ℂ H (ball 0 R))
    (hr : 0 ≤ r) (hrR : r < R) :
    Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N,
        (n : ℝ) * ‖taylorCoeff H n * (r : ℂ) ^ n‖ ^ 2)
      Filter.atTop (nhds (analyticCircleFlux H r)) := by
  let U : ℂ → ℂ := fun z => H ((r : ℂ) * z)
  let D : ℂ → ℂ := fun z => ((r : ℂ) * z) * deriv H ((r : ℂ) * z)
  let Ufin : ℕ → ℂ → ℂ := fun N => finitePositiveFourier
    (fun n => taylorCoeff H n * (r : ℂ) ^ n) N
  let Dfin : ℕ → ℂ → ℂ := fun N => finiteEulerFourier
    (fun n => taylorCoeff H n * (r : ℂ) ^ n) N
  have hU : TendstoUniformlyOn Ufin U Filter.atTop (sphere (0 : ℂ) 1) := by
    simpa only [Ufin, U] using tendstoUniformlyOn_finitePositiveFourier_taylor hH hr hrR
  have hDfunc : DifferentiableOn ℂ (id * deriv H) (ball 0 R) :=
    differentiableOn_id.mul (hH.deriv isOpen_ball)
  have hD : TendstoUniformlyOn Dfin D Filter.atTop (sphere (0 : ℂ) 1) := by
    have hbase := tendstoUniformlyOn_finitePositiveFourier_taylor hDfunc hr hrR
    have hcoeff (n : ℕ) : taylorCoeff (id * deriv H) n =
        (n : ℂ) * taylorCoeff H n := by
      simpa using taylorCoeff_id_mul_deriv hR hH n
    convert hbase using 1
    · ext N z
      simp only [Dfin, finiteEulerFourier, finitePositiveFourier, hcoeff]
      apply congrArg (fun a : ℕ → ℂ => (truncatedPowerPolynomial a N).eval z)
      funext n
      ring
    · ext z
      simp only [D, Pi.mul_apply, id_eq]
  have hUcont : ContinuousOn U (sphere (0 : ℂ) 1) := by
    intro z hz
    have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) R := by
      have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
        hznorm, mul_one]
      exact hrR
    exact (hH.differentiableAt (isOpen_ball.mem_nhds hrz)).continuousAt.comp
      (by fun_prop) |>.continuousWithinAt
  have hDcont : ContinuousOn D (sphere (0 : ℂ) 1) := by
    intro z hz
    have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) R := by
      have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
        hznorm, mul_one]
      exact hrR
    exact (hDfunc.differentiableAt (isOpen_ball.mem_nhds hrz)).continuousAt.comp
      (by fun_prop) |>.continuousWithinAt
  have hUfinCont : ∀ N, ContinuousOn (Ufin N) (sphere (0 : ℂ) 1) := by
    intro N
    exact (continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial
        (fun n => taylorCoeff H n * (r : ℂ) ^ n) N).hasDerivAt z).continuousAt).continuousOn
  have hDfinCont : ∀ N, ContinuousOn (Dfin N) (sphere (0 : ℂ) 1) := by
    intro N
    exact (continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial
        (fun n => (n : ℂ) * (taylorCoeff H n * (r : ℂ) ^ n)) N).hasDerivAt z).continuousAt).continuousOn
  have hUSq := tendsto_circleAverage_norm_sq_of_tendstoUniformlyOn hUfinCont hUcont hU
  have hDSq := tendsto_circleAverage_norm_sq_of_tendstoUniformlyOn hDfinCont hDcont hD
  have hSumSq := tendsto_circleAverage_norm_sq_of_tendstoUniformlyOn
    (fun N => (hUfinCont N).add (hDfinCont N)) (hUcont.add hDcont) (hU.add hD)
  have hflux : Filter.Tendsto
      (fun N => Real.circleAverage
        (fun z => signedCross (Ufin N z) (Complex.I * Dfin N z)) 0 1)
      Filter.atTop
      (nhds (Real.circleAverage
        (fun z => signedCross (U z) (Complex.I * D z)) 0 1)) := by
    have hcomb := ((hSumSq.sub hUSq).sub hDSq).const_mul (1 / 2 : ℝ)
    have hfinEq (N : ℕ) : Real.circleAverage
        (fun z => signedCross (Ufin N z) (Complex.I * Dfin N z)) 0 1 =
        (1 / 2 : ℝ) *
          (Real.circleAverage (fun z => ‖Ufin N z + Dfin N z‖ ^ 2) 0 1 -
            Real.circleAverage (fun z => ‖Ufin N z‖ ^ 2) 0 1 -
            Real.circleAverage (fun z => ‖Dfin N z‖ ^ 2) 0 1) :=
      circleAverage_signedCross_mul_I_eq_norms
        ((hUfinCont N).norm.pow 2 |>.circleIntegrable (by norm_num))
        ((hDfinCont N).norm.pow 2 |>.circleIntegrable (by norm_num))
        (((hUfinCont N).add (hDfinCont N)).norm.pow 2 |>.circleIntegrable (by norm_num))
    have hlimEq : Real.circleAverage
        (fun z => signedCross (U z) (Complex.I * D z)) 0 1 =
        (1 / 2 : ℝ) *
          (Real.circleAverage (fun z => ‖U z + D z‖ ^ 2) 0 1 -
            Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 -
            Real.circleAverage (fun z => ‖D z‖ ^ 2) 0 1) :=
      circleAverage_signedCross_mul_I_eq_norms
        (hUcont.norm.pow 2 |>.circleIntegrable (by norm_num))
        (hDcont.norm.pow 2 |>.circleIntegrable (by norm_num))
        ((hUcont.add hDcont).norm.pow 2 |>.circleIntegrable (by norm_num))
    convert hcomb using 1
    · funext N
      exact hfinEq N
    · exact congrArg nhds hlimEq
  have hfinite (N : ℕ) : Real.circleAverage
      (fun z => signedCross (Ufin N z) (Complex.I * Dfin N z)) 0 1 =
      ∑ n ∈ Finset.range N,
        (n : ℝ) * ‖taylorCoeff H n * (r : ℂ) ^ n‖ ^ 2 := by
    exact finitePositiveFourier_flux_parseval
      (fun n => taylorCoeff H n * (r : ℂ) ^ n) N
  simpa only [hfinite, U, D, analyticCircleFlux] using hflux

lemma finite_taylorCircleFlux_le {H : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hH : DifferentiableOn ℂ H (ball 0 R))
    (hr : 0 ≤ r) (hrR : r < R) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (n : ℝ) * ‖taylorCoeff H n‖ ^ 2 * r ^ (2 * n)) ≤
      analyticCircleFlux H r := by
  have hlim := analyticCircleFlux_tendsto hR hH hr hrR
  have hterm (n : ℕ) :
      (n : ℝ) * ‖taylorCoeff H n * (r : ℂ) ^ n‖ ^ 2 =
        (n : ℝ) * ‖taylorCoeff H n‖ ^ 2 * r ^ (2 * n) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr]
    ring
  simp_rw [hterm] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [Filter.eventually_ge_atTop N] with K hNK
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
  intro n hnK hnN
  positivity

noncomputable def finiteLaurentFourier (a : ℕ → ℂ) (shift N : ℕ) (z : ℂ) : ℂ :=
  z ^ (-(shift : ℤ)) * finitePositiveFourier a N z

noncomputable def finiteLaurentEuler (a : ℕ → ℂ) (shift N : ℕ) (z : ℂ) : ℂ :=
  z ^ (-(shift : ℤ)) *
    (finiteEulerFourier a N z - (shift : ℂ) * finitePositiveFourier a N z)

lemma signedCross_mul_I_sub_nat (u v : ℂ) (k : ℕ) :
    signedCross u (Complex.I * (v - (k : ℂ) * u)) =
      signedCross u (Complex.I * v) - (k : ℝ) * ‖u‖ ^ 2 := by
  rw [signedCross_mul_I, signedCross_mul_I, mul_sub, Complex.sub_re]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

lemma finiteLaurentFourier_flux_parseval (a : ℕ → ℂ) (shift N : ℕ) :
    Real.circleAverage
        (fun z => signedCross (finiteLaurentFourier a shift N z)
          (Complex.I * finiteLaurentEuler a shift N z)) 0 1 =
      ∑ n ∈ Finset.range N, ((n : ℝ) - shift) * ‖a n‖ ^ 2 := by
  let U : ℂ → ℂ := finitePositiveFourier a N
  let D : ℂ → ℂ := finiteEulerFourier a N
  have hU : Continuous U := by
    dsimp only [U, finitePositiveFourier]
    exact continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial a N).hasDerivAt z).continuousAt
  have hD : Continuous D := by
    dsimp only [D, finiteEulerFourier]
    exact continuous_iff_continuousAt.mpr fun z =>
      ((truncatedPowerPolynomial (fun n => (n : ℂ) * a n) N).hasDerivAt z).continuousAt
  have hpoint : Set.EqOn
      (fun z => signedCross (finiteLaurentFourier a shift N z)
        (Complex.I * finiteLaurentEuler a shift N z))
      (fun z => signedCross (U z) (Complex.I * D z) -
        (shift : ℝ) * ‖U z‖ ^ 2) (sphere (0 : ℂ) 1) := by
    intro z hz
    have hzNorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hpowNorm : ‖z ^ (-(shift : ℤ))‖ ^ 2 = 1 := by
      rw [norm_zpow, hzNorm, one_zpow, one_pow]
    unfold finiteLaurentFourier finiteLaurentEuler
    change signedCross (z ^ (-(shift : ℤ)) * U z)
        (Complex.I * (z ^ (-(shift : ℤ)) *
          (D z - (shift : ℂ) * U z))) = _
    rw [show Complex.I * (z ^ (-(shift : ℤ)) *
        (D z - (shift : ℂ) * U z)) =
      z ^ (-(shift : ℤ)) * (Complex.I *
        (D z - (shift : ℂ) * U z)) by ring]
    rw [signedCross_mul_left, hpowNorm, one_mul,
      signedCross_mul_I_sub_nat]
  have havg : Real.circleAverage
      (fun z => signedCross (finiteLaurentFourier a shift N z)
        (Complex.I * finiteLaurentEuler a shift N z)) 0 1 =
      Real.circleAverage (fun z => signedCross (U z) (Complex.I * D z) -
        (shift : ℝ) * ‖U z‖ ^ 2) 0 1 :=
    Real.circleAverage_congr_sphere (by simpa using hpoint)
  rw [havg]
  have hfluxInt : CircleIntegrable
      (fun z => signedCross (U z) (Complex.I * D z)) 0 1 := by
    have hcont : Continuous (fun z => signedCross (U z) (Complex.I * D z)) := by
      unfold signedCross
      fun_prop
    exact hcont.continuousOn.circleIntegrable (by norm_num)
  have hnormInt : CircleIntegrable (fun z => (shift : ℝ) * ‖U z‖ ^ 2) 0 1 :=
    (hU.norm.pow 2).const_mul shift |>.continuousOn.circleIntegrable (by norm_num)
  rw [show (fun z => signedCross (U z) (Complex.I * D z) -
      (shift : ℝ) * ‖U z‖ ^ 2) =
    (fun z => signedCross (U z) (Complex.I * D z)) -
      (fun z => (shift : ℝ) * ‖U z‖ ^ 2) by rfl]
  rw [Real.circleAverage_sub hfluxInt hnormInt]
  rw [show Real.circleAverage (fun z => signedCross (U z) (Complex.I * D z)) 0 1 =
      ∑ n ∈ Finset.range N, (n : ℝ) * ‖a n‖ ^ 2 by
    simpa only [U, D] using finitePositiveFourier_flux_parseval a N]
  rw [show Real.circleAverage (fun z => (shift : ℝ) * ‖U z‖ ^ 2) 0 1 =
      (shift : ℝ) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 by
    rw [show (fun z => (shift : ℝ) * ‖U z‖ ^ 2) =
      fun z => (shift : ℝ) • ‖U z‖ ^ 2 by funext z; simp]
    rw [Real.circleAverage_fun_smul]
    change (shift : ℝ) * Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 = _
    rw [show Real.circleAverage (fun z => ‖U z‖ ^ 2) 0 1 =
        ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 by
      simpa only [U, finitePositiveFourier] using
        (truncatedPowerPolynomial_parseval a N).symm]]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end Submission
