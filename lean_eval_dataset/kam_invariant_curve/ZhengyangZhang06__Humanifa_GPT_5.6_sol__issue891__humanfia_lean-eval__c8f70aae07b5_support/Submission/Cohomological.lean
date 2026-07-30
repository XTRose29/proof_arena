import Submission.Helpers

open LeanEval.Dynamics
open scoped ContDiff

namespace Submission.Cohomological

noncomputable section

/-- The real Fourier symbol of the second difference at frequency `n`. -/
def laplacianSymbol (α : ℝ) (n : ℤ) : ℝ :=
  2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2

/-- Fourier coefficients on the unit period, with real values embedded in `ℂ`. -/
def realFourierCoeff (g : ℝ → ℝ) (n : ℤ) : ℂ :=
  fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
    (fun x => Complex.ofReal (g x)) n

/-- The coefficient obtained by dividing a nonzero Fourier mode by the
second-difference symbol.  The zero mode is normalized to zero. -/
def inverseFourierCoeff (α : ℝ) (g : ℝ → ℝ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else
    (laplacianSymbol α n : ℂ)⁻¹ * realFourierCoeff g n

/-- The real part of a unit-period Fourier mode with complex coefficient `a`. -/
def mode (a : ℂ) (n : ℤ) (t : ℝ) : ℝ :=
  a.re * Real.cos (2 * Real.pi * (n : ℝ) * t) -
    a.im * Real.sin (2 * Real.pi * (n : ℝ) * t)

theorem laplacianSymbol_ne_zero {α : ℝ} (hα : IsDiophantine α)
    (n : ℤ) (hn : n ≠ 0) : laplacianSymbol α n ≠ 0 := by
  exact Helpers.isDiophantine_cos_symbol_ne_zero hα n hn

theorem mode_periodic (a : ℂ) (n : ℤ) :
    Function.Periodic (mode a n) 1 := by
  intro t
  simp only [mode]
  rw [show 2 * Real.pi * (n : ℝ) * (t + 1) =
      2 * Real.pi * (n : ℝ) * t + n * (2 * Real.pi) by ring]
  rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem mode_contDiff (a : ℂ) (n : ℤ) : ContDiff ℝ ∞ (mode a n) := by
  unfold mode
  fun_prop

theorem iteratedDeriv_mode (a : ℂ) (n : ℤ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (mode a n) t =
      a.re * ((2 * Real.pi * (n : ℝ)) ^ k *
        iteratedDeriv k Real.cos (2 * Real.pi * (n : ℝ) * t)) -
      a.im * ((2 * Real.pi * (n : ℝ)) ^ k *
        iteratedDeriv k Real.sin (2 * Real.pi * (n : ℝ) * t)) := by
  let b : ℝ := 2 * Real.pi * (n : ℝ)
  have hcos : ContDiffAt ℝ k (fun x : ℝ => a.re * Real.cos (b * x)) t := by
    fun_prop
  have hsin : ContDiffAt ℝ k (fun x : ℝ => a.im * Real.sin (b * x)) t := by
    fun_prop
  have hcosk : ContDiff ℝ k Real.cos := Real.contDiff_cos.of_le le_top
  have hsink : ContDiff ℝ k Real.sin := Real.contDiff_sin.of_le le_top
  change iteratedDeriv k
      ((fun x : ℝ => a.re * Real.cos (b * x)) -
        (fun x : ℝ => a.im * Real.sin (b * x))) t = _
  rw [iteratedDeriv_sub hcos hsin]
  simp only [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_mul hcosk b,
    iteratedDeriv_comp_const_mul hsink b]

theorem norm_iteratedFDeriv_mode_le (a : ℂ) (n : ℤ) (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (mode a n) t‖ ≤
      2 * |2 * Real.pi * (n : ℝ)| ^ k * ‖a‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    iteratedDeriv_mode]
  let X := a.re * ((2 * Real.pi * (n : ℝ)) ^ k *
    iteratedDeriv k Real.cos (2 * Real.pi * (n : ℝ) * t))
  let Y := a.im * ((2 * Real.pi * (n : ℝ)) ^ k *
    iteratedDeriv k Real.sin (2 * Real.pi * (n : ℝ) * t))
  calc
    |a.re * ((2 * Real.pi * (n : ℝ)) ^ k *
          iteratedDeriv k Real.cos (2 * Real.pi * (n : ℝ) * t)) -
        a.im * ((2 * Real.pi * (n : ℝ)) ^ k *
          iteratedDeriv k Real.sin (2 * Real.pi * (n : ℝ) * t))| ≤ |X| + |Y| :=
      abs_sub X Y
    _ ≤
        |a.re| * (|2 * Real.pi * (n : ℝ)| ^ k * 1) +
          |a.im| * (|2 * Real.pi * (n : ℝ)| ^ k * 1) := by
      dsimp only [X, Y]
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      simp only [abs_pow]
      gcongr
      · exact Real.abs_iteratedDeriv_cos_le_one k _
      · exact Real.abs_iteratedDeriv_sin_le_one k _
    _ ≤ ‖a‖ * (|2 * Real.pi * (n : ℝ)| ^ k * 1) +
          ‖a‖ * (|2 * Real.pi * (n : ℝ)| ^ k * 1) := by
      gcongr
      · exact Complex.abs_re_le_norm a
      · exact Complex.abs_im_le_norm a
    _ = 2 * |2 * Real.pi * (n : ℝ)| ^ k * ‖a‖ := by ring

/-- Smoothness gives arbitrary polynomial decay of the real Fourier
coefficients.  The harmless factor `2π` is discarded to make subsequent
small-divisor estimates easier to combine. -/
theorem exists_realFourierCoeff_decay {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℤ, n ≠ 0 →
      ‖realFourierCoeff g n‖ ≤ (1 / |(n : ℝ)|) ^ m * B := by
  have hcont : Continuous (iteratedDeriv m g) :=
    hg.continuous_iteratedDeriv m
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m).le
  obtain ⟨B, hB, hbound⟩ :=
    Helpers.exists_fourierCoeffOn_norm_bound hcont
  refine ⟨B, hB, ?_⟩
  intro n hn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habspos : 0 < |(n : ℝ)| := abs_pos.mpr hnreal
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiv : ‖Helpers.fourierDerivativeDivisor n‖ ≤ 1 / |(n : ℝ)| := by
    rw [Helpers.norm_fourierDerivativeDivisor]
    apply one_div_le_one_div_of_le habspos
    nlinarith
  have hpow : ‖Helpers.fourierDerivativeDivisor n‖ ^ m ≤
      (1 / |(n : ℝ)|) ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) hdiv m
  rw [realFourierCoeff,
    Helpers.fourierCoeffOn_iteratedDeriv_iterate hg hper m n hn,
    norm_mul, norm_pow]
  calc
    ‖Helpers.fourierDerivativeDivisor n‖ ^ m *
        ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun x => Complex.ofReal (iteratedDeriv m g x)) n‖ ≤
        ‖Helpers.fourierDerivativeDivisor n‖ ^ m * B :=
      mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (norm_nonneg _) _)
    _ ≤ (1 / |(n : ℝ)|) ^ m * B :=
      mul_le_mul_of_nonneg_right hpow hB

/-- Dividing by a Diophantine second-difference symbol costs at most two
powers of the Fourier frequency. -/
theorem norm_inverseFourierCoeff_le {α : ℝ} (g : ℝ → ℝ)
    (C : ℝ) (hC : 0 < C)
    (hsymbol : ∀ n : ℤ, n ≠ 0 →
      (C / |(n : ℝ)|) ^ 2 ≤ |laplacianSymbol α n|)
    (n : ℤ) (hn : n ≠ 0) :
    ‖inverseFourierCoeff α g n‖ ≤
      (|(n : ℝ)| / C) ^ 2 * ‖realFourierCoeff g n‖ := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habspos : 0 < |(n : ℝ)| := abs_pos.mpr hnreal
  have hlower : 0 < (C / |(n : ℝ)|) ^ 2 := by positivity
  have hsymbolpos : 0 < |laplacianSymbol α n| :=
    hlower.trans_le (hsymbol n hn)
  have hinv : |laplacianSymbol α n|⁻¹ ≤
      ((C / |(n : ℝ)|) ^ 2)⁻¹ :=
    (inv_le_inv₀ hsymbolpos hlower).2 (hsymbol n hn)
  have hnorm : ‖(laplacianSymbol α n : ℂ)⁻¹‖ ≤
      (|(n : ℝ)| / C) ^ 2 := by
    calc
      ‖(laplacianSymbol α n : ℂ)⁻¹‖ = |laplacianSymbol α n|⁻¹ := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ((C / |(n : ℝ)|) ^ 2)⁻¹ := hinv
      _ = (|(n : ℝ)| / C) ^ 2 := by
        field_simp [hC.ne', abs_ne_zero.mpr hnreal]
  rw [inverseFourierCoeff, if_neg hn, norm_mul]
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- A uniform bound for the `k`-th derivatives of the divided Fourier modes. -/
def modeDerivBound (α : ℝ) (g : ℝ → ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  2 * |2 * Real.pi * (n : ℝ)| ^ k * ‖inverseFourierCoeff α g n‖

/-- The loss of two derivatives in the small-divisor inverse is absorbed by
four additional integrations by parts, leaving a summable `1 / n²` tail. -/
theorem summable_modeDerivBound {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1)
    (k : ℕ) : Summable (modeDerivBound α g k) := by
  obtain ⟨C, hC, hsymbol'⟩ := Helpers.isDiophantine_cos_symbol_bound hα
  have hsymbol : ∀ n : ℤ, n ≠ 0 →
      (C / |(n : ℝ)|) ^ 2 ≤ |laplacianSymbol α n| := by
    simpa only [laplacianSymbol] using hsymbol'
  obtain ⟨B, hB, hdecay⟩ :=
    exists_realFourierCoeff_decay hg hper (k + 4)
  let D : ℝ := 2 * (2 * Real.pi) ^ k * B / C ^ 2
  have hD : 0 ≤ D := by positivity
  have href : Summable (fun n : ℤ => D * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left D
  apply href.of_nonneg_of_le
  · intro n
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))
      (norm_nonneg _)
  · intro n
    by_cases hn : n = 0
    · subst n
      simp [modeDerivBound, inverseFourierCoeff]
    · have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have habspos : 0 < |(n : ℝ)| := abs_pos.mpr hnreal
      calc
        modeDerivBound α g k n ≤
            2 * |2 * Real.pi * (n : ℝ)| ^ k *
              ((|(n : ℝ)| / C) ^ 2 * ‖realFourierCoeff g n‖) :=
          mul_le_mul_of_nonneg_left
            (norm_inverseFourierCoeff_le g C hC hsymbol n hn)
            (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))
        _ ≤ 2 * |2 * Real.pi * (n : ℝ)| ^ k *
              ((|(n : ℝ)| / C) ^ 2 *
                ((1 / |(n : ℝ)|) ^ (k + 4) * B)) := by
          gcongr
          exact hdecay n hn
        _ = D * (1 / (n : ℝ) ^ 2) := by
          rw [← sq_abs (n : ℝ)]
          simp only [D, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_pos Real.pi_pos, mul_pow, one_div, inv_pow, pow_add]
          field_simp [hC.ne', abs_ne_zero.mpr hnreal]

/-- The normalized smooth solution obtained by Fourier division. -/
def solve (α : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℤ, mode (inverseFourierCoeff α g n) n t

theorem solve_contDiff {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) :
    ContDiff ℝ ∞ (solve α g) := by
  apply contDiff_tsum (v := fun k n => modeDerivBound α g k n)
  · exact fun n => mode_contDiff _ n
  · intro k _
    exact summable_modeDerivBound hα hg hper k
  · intro k n t _
    exact norm_iteratedFDeriv_mode_le _ n k t

theorem solve_periodic (α : ℝ) (g : ℝ → ℝ) :
    Function.Periodic (solve α g) 1 := by
  intro t
  apply tsum_congr
  intro n
  exact mode_periodic (inverseFourierCoeff α g n) n t

theorem summable_realFourierCoeff {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) :
    Summable (realFourierCoeff g) := by
  obtain ⟨B, hB, hdecay⟩ := exists_realFourierCoeff_decay hg hper 2
  have htail : Summable (fun n : ℤ => (1 / (n : ℝ) ^ 2) * B) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_right B
  have hzero : Summable (fun n : ℤ =>
      if n = 0 then ‖realFourierCoeff g 0‖ else 0) := by
    exact (hasSum_ite_eq (0 : ℤ) ‖realFourierCoeff g 0‖).summable
  refine Summable.of_norm_bounded (htail.add hzero) ?_
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ↓reduceIte, add_zero]
    simpa only [div_pow, one_pow, sq_abs] using hdecay n hn

/-- A smooth periodic real function, viewed as a continuous complex-valued
function on the additive circle. -/
def periodicContinuousMap (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 1) : C(AddCircle (1 : ℝ), ℂ) where
  toFun := AddCircle.liftIoc (1 : ℝ) (0 : ℝ)
    (fun x => Complex.ofReal (g x))
  continuous_toFun := by
    apply AddCircle.liftIoc_continuous
    · simpa using congrArg Complex.ofReal (hper 0).symm
    · exact (Complex.continuous_ofReal.comp hg).continuousOn

theorem fourierCoeff_periodicContinuousMap (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 1) (n : ℤ) :
    fourierCoeff
        (periodicContinuousMap g hg hper : AddCircle (1 : ℝ) → ℂ) n =
      realFourierCoeff g n := by
  change fourierCoeff
      (AddCircle.liftIoc (1 : ℝ) (0 : ℝ)
        (fun x => Complex.ofReal (g x))) n = realFourierCoeff g n
  unfold realFourierCoeff
  rw [fourierCoeff_liftIoc_eq]
  congr
  norm_num

theorem periodicContinuousMap_coe (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 1) (t : ℝ) :
    periodicContinuousMap g hg hper (t : AddCircle (1 : ℝ)) =
      Complex.ofReal (g t) := by
  let gC : ℝ → ℂ := fun x => Complex.ofReal (g x)
  have hperC : Function.Periodic gC 1 := fun x => congrArg Complex.ofReal (hper x)
  have hlift : AddCircle.liftIoc (1 : ℝ) (0 : ℝ) gC = hperC.lift := by
    apply AddCircle.Ioc_ext (1 : ℝ) (0 : ℝ)
    intro x hx
    rw [AddCircle.liftIoc_coe_apply hx, hperC.lift_coe]
  change AddCircle.liftIoc (1 : ℝ) (0 : ℝ) gC
      (t : AddCircle (1 : ℝ)) = gC t
  rw [hlift, hperC.lift_coe]

theorem re_fourier_term (g : ℝ → ℝ) (n : ℤ) (t : ℝ) :
    (realFourierCoeff g n • (fourier n) (t : AddCircle (1 : ℝ))).re =
      mode (realFourierCoeff g n) n t := by
  rw [fourier_coe_apply]
  simp only [smul_eq_mul]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) =
      ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, div_one]
  rw [Complex.exp_ofReal_mul_I]
  simp only [mode, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one]

theorem hasSum_mode_realFourierCoeff {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) (t : ℝ) :
    HasSum (fun n : ℤ => mode (realFourierCoeff g n) n t) (g t) := by
  let G := periodicContinuousMap g hg.continuous hper
  have hcoeff : Summable
      (fourierCoeff (G : AddCircle (1 : ℝ) → ℂ)) := by
    apply (summable_realFourierCoeff hg hper).congr
    intro n
    exact (fourierCoeff_periodicContinuousMap g hg.continuous hper n).symm
  have hsum := has_pointwise_sum_fourier_series_of_summable hcoeff
    (t : AddCircle (1 : ℝ))
  have hG : G (t : AddCircle (1 : ℝ)) = Complex.ofReal (g t) :=
    periodicContinuousMap_coe g hg.continuous hper t
  have hterms : (fun n : ℤ => mode (realFourierCoeff g n) n t) =
      (fun n : ℤ =>
        (fourierCoeff (G : AddCircle (1 : ℝ) → ℂ) n •
          (fourier n) (t : AddCircle (1 : ℝ))).re) := by
    funext n
    rw [fourierCoeff_periodicContinuousMap]
    exact (re_fourier_term g n t).symm
  rw [hterms]
  simpa only [hG, Complex.ofReal_re] using Complex.hasSum_re hsum

theorem tsum_mode_realFourierCoeff {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) (t : ℝ) :
    ∑' n : ℤ, mode (realFourierCoeff g n) n t = g t :=
  (hasSum_mode_realFourierCoeff hg hper t).tsum_eq

theorem realFourierCoeff_zero_of_mean_zero {g : ℝ → ℝ}
    (hmean : ∫ x in (0 : ℝ)..1, g x = 0) :
    realFourierCoeff g 0 = 0 := by
  rw [realFourierCoeff, fourierCoeffOn_eq_integral]
  simp [fourier_apply]
  rw [intervalIntegral.integral_ofReal, hmean]
  norm_num

theorem discreteLaplacian_mode (α : ℝ) (a : ℂ) (n : ℤ) (t : ℝ) :
    Helpers.discreteLaplacian α (mode a n) t =
      laplacianSymbol α n * mode a n t := by
  rw [show Helpers.discreteLaplacian α (mode a n) t =
      a.re * Helpers.discreteLaplacian α
          (fun x => Real.cos (2 * Real.pi * (n : ℝ) * x)) t -
        a.im * Helpers.discreteLaplacian α
          (fun x => Real.sin (2 * Real.pi * (n : ℝ) * x)) t by
    simp only [Helpers.discreteLaplacian, mode]
    ring]
  rw [Helpers.discreteLaplacian_cos, Helpers.discreteLaplacian_sin]
  simp only [laplacianSymbol, mode]
  ring

theorem discreteLaplacian_inverse_mode {α : ℝ} (hα : IsDiophantine α)
    (g : ℝ → ℝ) (n : ℤ) (t : ℝ) :
    Helpers.discreteLaplacian α
        (mode (inverseFourierCoeff α g n) n) t =
      if n = 0 then 0 else mode (realFourierCoeff g n) n t := by
  by_cases hn : n = 0
  · subst n
    simp [inverseFourierCoeff, mode, Helpers.discreteLaplacian]
  · rw [if_neg hn, discreteLaplacian_mode]
    have hs : laplacianSymbol α n ≠ 0 := laplacianSymbol_ne_zero hα n hn
    have hcast : ((laplacianSymbol α n : ℂ)⁻¹) =
        (((laplacianSymbol α n)⁻¹ : ℝ) : ℂ) := by norm_cast
    rw [inverseFourierCoeff, if_neg hn, hcast]
    simp only [mode, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    field_simp [hs]

theorem norm_mode_le_modeDerivBound (α : ℝ) (g : ℝ → ℝ)
    (n : ℤ) (t : ℝ) :
    ‖mode (inverseFourierCoeff α g n) n t‖ ≤ modeDerivBound α g 0 n := by
  have h := norm_iteratedFDeriv_mode_le (inverseFourierCoeff α g n) n 0 t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  simpa only [modeDerivBound, pow_zero, mul_one, iteratedDeriv_zero] using h

theorem summable_mode_apply {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1)
    (t : ℝ) : Summable (fun n : ℤ => mode (inverseFourierCoeff α g n) n t) := by
  exact Summable.of_norm_bounded (summable_modeDerivBound hα hg hper 0)
    (fun n => norm_mode_le_modeDerivBound α g n t)

/-- Fourier division is a right inverse of the second difference on smooth,
unit-periodic functions whose zero Fourier mode vanishes. -/
theorem discreteLaplacian_solve {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g 1)
    (hmean : ∫ x in (0 : ℝ)..1, g x = 0) (t : ℝ) :
    Helpers.discreteLaplacian α (solve α g) t = g t := by
  let φ := fun n : ℤ => mode (inverseFourierCoeff α g n) n
  have hplus : Summable (fun n : ℤ => φ n (t + α)) :=
    summable_mode_apply hα hg hper (t + α)
  have hzero : Summable (fun n : ℤ => φ n t) :=
    summable_mode_apply hα hg hper t
  have hminus : Summable (fun n : ℤ => φ n (t - α)) :=
    summable_mode_apply hα hg hper (t - α)
  have hsumL : HasSum
      (fun n : ℤ => Helpers.discreteLaplacian α (φ n) t)
      (Helpers.discreteLaplacian α (solve α g) t) := by
    simpa only [Helpers.discreteLaplacian, solve, φ] using
      ((hplus.hasSum.sub (hzero.hasSum.mul_left 2)).add hminus.hasSum)
  have hcoeffZero : realFourierCoeff g 0 = 0 :=
    realFourierCoeff_zero_of_mean_zero hmean
  have hfiltered : HasSum
      (fun n : ℤ => if n = 0 then 0 else
        mode (realFourierCoeff g n) n t)
      (g t) := by
    apply (hasSum_mode_realFourierCoeff hg hper t).congr_fun
    intro n
    by_cases hn : n = 0
    · subst n
      simp [hcoeffZero, mode]
    · simp [hn]
  have hsumR : HasSum
      (fun n : ℤ => Helpers.discreteLaplacian α (φ n) t)
      (g t) := by
    apply hfiltered.congr_fun
    intro n
    exact discreteLaplacian_inverse_mode hα g n t
  exact hsumL.unique hsumR

end

end Submission.Cohomological
