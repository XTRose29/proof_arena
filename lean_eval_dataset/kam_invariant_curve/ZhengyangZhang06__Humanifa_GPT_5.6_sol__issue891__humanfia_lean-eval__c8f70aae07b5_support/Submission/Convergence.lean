import Submission.Budgets
import Mathlib.Analysis.Calculus.SmoothSeries

open LeanEval.Dynamics
open Filter
open scoped ContDiff Topology

namespace Submission.Majorant

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The power of the majorant base which bounds the `k`th derivative of the
`n`th Newton correction. -/
def smoothStepExponent (k n : ℕ) : ℕ :=
  lossExponent n * (k + 1) + (iterationOrder n + 2) * k ^ 2

/-- A uniform bound for the `k`th derivative of the `n`th Newton correction. -/
def smoothStepBound (B : ℝ) (k n : ℕ) : ℝ :=
  B ^ lossExponent n * errorBudget B n *
    weight (iterationOrder n + 2) k * (B ^ lossExponent n) ^ k

def growthConstant (k : ℕ) : ℕ :=
  500000 * (k + 1) + 7 * k ^ 2 + 1

theorem growthConstant_pos (k : ℕ) : 0 < growthConstant k := by
  unfold growthConstant
  omega

/-- All derivative losses at a fixed order grow at most quadratically in the
iteration index. -/
theorem smoothStepExponent_add_le_growthConstant_mul_sq
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    smoothStepExponent k n + n ≤ growthConstant k * n ^ 2 := by
  have hshift : n + 4 ≤ 5 * n := by omega
  have hshiftSq : (n + 4) ^ 2 ≤ (5 * n) ^ 2 := by gcongr
  have hloss : lossExponent n ≤ 500000 * n ^ 2 := by
    unfold lossExponent
    calc
      20000 * (n + 4) ^ 2 ≤ 20000 * (5 * n) ^ 2 :=
        Nat.mul_le_mul_left 20000 hshiftSq
      _ = 500000 * n ^ 2 := by ring
  have horder : iterationOrder n + 2 ≤ 7 * n := by
    unfold iterationOrder
    omega
  have hsq : n ≤ n ^ 2 := by
    simpa only [pow_two, one_mul] using Nat.mul_le_mul_right n hn
  have hfirst : lossExponent n * (k + 1) ≤
      (500000 * n ^ 2) * (k + 1) :=
    Nat.mul_le_mul_right (k + 1) hloss
  have hsecond : (iterationOrder n + 2) * k ^ 2 ≤
      (7 * n) * k ^ 2 := Nat.mul_le_mul_right (k ^ 2) horder
  have hsecond' : (7 * n) * k ^ 2 ≤ (7 * k ^ 2) * n ^ 2 := by
    calc
      (7 * n) * k ^ 2 = (7 * k ^ 2) * n := by ring
      _ ≤ (7 * k ^ 2) * n ^ 2 := Nat.mul_le_mul_left _ hsq
  unfold smoothStepExponent growthConstant
  calc
    lossExponent n * (k + 1) + (iterationOrder n + 2) * k ^ 2 + n ≤
        (500000 * n ^ 2) * (k + 1) + (7 * n) * k ^ 2 + n :=
      add_le_add (add_le_add hfirst hsecond) le_rfl
    _ ≤ (500000 * n ^ 2) * (k + 1) +
        (7 * k ^ 2) * n ^ 2 + n ^ 2 :=
      add_le_add (add_le_add le_rfl hsecond') hsq
    _ = (500000 * (k + 1) + 7 * k ^ 2 + 1) * n ^ 2 := by ring

/-- Exponential error decay eventually absorbs every fixed derivative loss. -/
theorem eventually_smoothStepExponent_add_le_errorExponent (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      smoothStepExponent k n + n ≤ errorExponent n := by
  let C := growthConstant k
  have hC : 0 < (C : ℝ) := by
    exact_mod_cast growthConstant_pos k
  have hsmall :=
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2
      (by norm_num : (1 : ℝ) < 2)).bound (inv_pos.mpr hC)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hsmalln
  have hpoly := smoothStepExponent_add_le_growthConstant_mul_sq k hn
  have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have htwoPow : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  have hsmalln' : (n : ℝ) ^ 2 ≤ (C : ℝ)⁻¹ * (2 : ℝ) ^ n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnSq,
      abs_of_nonneg htwoPow] using hsmalln
  have hdomReal : (C : ℝ) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
    calc
      (C : ℝ) * (n : ℝ) ^ 2 ≤
          (C : ℝ) * ((C : ℝ)⁻¹ * (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hsmalln' hC.le
      _ = (2 : ℝ) ^ n := by field_simp [hC.ne']
  have hdom : C * n ^ 2 ≤ 2 ^ n := by exact_mod_cast hdomReal
  calc
    smoothStepExponent k n + n ≤ C * n ^ 2 := hpoly
    _ ≤ 2 ^ n := hdom
    _ ≤ errorExponent n := by
      unfold errorExponent
      omega

theorem pow_mul_inv_pow_le_inv_pow {B : ℝ} (hB : 1 ≤ B)
    {a e n : ℕ} (h : a + n ≤ e) :
    B ^ a * B⁻¹ ^ e ≤ B⁻¹ ^ n := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hq0 : 0 ≤ B⁻¹ := inv_nonneg.mpr hBpos.le
  have hq1 : B⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hBpos]
    exact hB
  have he : e = a + (e - a) := by omega
  calc
    B ^ a * B⁻¹ ^ e =
        (B ^ a * B⁻¹ ^ a) * B⁻¹ ^ (e - a) := by
      conv_lhs => rw [he, pow_add]
      ring
    _ = B⁻¹ ^ (e - a) := by
      rw [← mul_pow, mul_inv_cancel₀ hBpos.ne', one_pow, one_mul]
    _ ≤ B⁻¹ ^ n := pow_le_pow_of_le_one hq0 hq1 (by omega)

theorem smoothStepBound_nonneg {B : ℝ} (hB : 0 ≤ B) (k n : ℕ) :
    0 ≤ smoothStepBound B k n := by
  unfold smoothStepBound
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (pow_nonneg hB _) (errorBudget_nonneg hB n))
      (weight_nonneg _ _))
    (pow_nonneg (pow_nonneg hB _) _)

/-- Increase both scalar parameters of a majorant in one abstract step.  This
keeps large Newton expressions opaque when both bounds change together. -/
theorem Majorized.amplitude_radius_mono {s : ℕ} {A A' R R' : ℝ}
    {g : ℝ → ℝ} (hg : Majorized s A R g) (hAA' : A ≤ A')
    (hA' : 0 ≤ A') (hR : 0 ≤ R) (hRR' : R ≤ R') :
    Majorized s A' R' g :=
  (hg.amplitude_mono hAA' hR).radius_mono hA' hR hRR'

theorem smoothStepBound_eventually_le_geometric {B : ℝ} (hB : 2 ≤ B)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, smoothStepBound B k n ≤ B⁻¹ ^ n := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have htwo : (2 : ℝ) ≤ B := hB
  filter_upwards [eventually_smoothStepExponent_add_le_errorExponent k]
    with n hn
  let w := (iterationOrder n + 2) * k ^ 2
  have hweight : weight (iterationOrder n + 2) k ≤ B ^ w := by
    unfold weight w
    exact pow_le_pow_left₀ (by norm_num) htwo _
  have hexp : lossExponent n + w + lossExponent n * k =
      smoothStepExponent k n := by
    unfold smoothStepExponent w
    ring
  have hpow : (B ^ lossExponent n) ^ k =
      B ^ (lossExponent n * k) := by
    rw [pow_mul]
  unfold smoothStepBound errorBudget
  calc
    B ^ lossExponent n * B⁻¹ ^ errorExponent n *
          weight (iterationOrder n + 2) k *
          (B ^ lossExponent n) ^ k ≤
        B ^ lossExponent n * B⁻¹ ^ errorExponent n * B ^ w *
          (B ^ lossExponent n) ^ k := by
      gcongr
    _ = B ^ smoothStepExponent k n * B⁻¹ ^ errorExponent n := by
      rw [hpow]
      calc
        B ^ lossExponent n * B⁻¹ ^ errorExponent n * B ^ w *
            B ^ (lossExponent n * k) =
            (B ^ lossExponent n * B ^ w *
              B ^ (lossExponent n * k)) * B⁻¹ ^ errorExponent n := by ring
        _ = B ^ (lossExponent n + w + lossExponent n * k) *
            B⁻¹ ^ errorExponent n := by rw [pow_mul_pow3]
        _ = B ^ smoothStepExponent k n * B⁻¹ ^ errorExponent n := by
          rw [hexp]
    _ ≤ B⁻¹ ^ n := pow_mul_inv_pow_le_inv_pow hB1 hn

theorem summable_smoothStepBound {B : ℝ} (hB : 2 ≤ B) (k : ℕ) :
    Summable (smoothStepBound B k) := by
  have hBpos : 0 < B := by linarith
  have hgeom : Summable (fun n : ℕ => B⁻¹ ^ n) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hBpos)]
      exact inv_lt_one_of_one_lt₀ (by linarith))
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [smoothStepBound_eventually_le_geometric hB k] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothStepBound_nonneg hBpos.le k n)]
  exact hn

def accumulatedIncrement (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, incrementBudget i

theorem accumulatedIncrement_nonneg (n : ℕ) :
    0 ≤ accumulatedIncrement n := by
  unfold accumulatedIncrement
  exact Finset.sum_nonneg fun i _ => incrementBudget_nonneg i

theorem accumulatedIncrement_le_eighth (n : ℕ) :
    accumulatedIncrement n ≤ (1 : ℝ) / 8 := by
  exact incrementBudget_partial_sum_le n

theorem accumulatedIncrement_succ (n : ℕ) :
    accumulatedIncrement (n + 1) =
      accumulatedIncrement n + incrementBudget n := by
  unfold accumulatedIncrement
  rw [Finset.sum_range_succ]

theorem incrementBudget_le_one (n : ℕ) : incrementBudget n ≤ 1 := by
  unfold incrementBudget
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem DerivativeMajorized.amplitude_mono {s : ℕ} {W W' R : ℝ}
    {g : ℝ → ℝ} (hg : DerivativeMajorized s W R g)
    (hWW' : W ≤ W') (hR : 0 ≤ R) :
    DerivativeMajorized s W' R g := by
  intro n hn t
  apply (hg n hn t).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hWW' (weight_nonneg s n))
    (pow_nonneg hR (n - 1))

theorem goodLift_of_deriv_bound {u : ℝ → ℝ}
    (hu : ∀ t, |deriv u t| ≤ (1 : ℝ) / 8) : Newton.GoodLift u := by
  intro t
  have hlo := neg_le_of_abs_le (hu t)
  have hhi := le_of_abs_le (hu t)
  constructor <;> simp only [Newton.liftDeriv] <;> linarith

theorem stepRadius_le_nextRadius (α : ℝ) (hα : IsDiophantine α)
    (sf s : ℕ) (RF W E R : ℝ) (hS : 0 ≤ stepRadius s W R) :
    stepRadius s W R ≤ nextRadius α hα sf s RF W E R := by
  unfold nextRadius taylorRemainderRadius
  let K := taylorKernelRadius sf RF (1 + W)
    (stepAmplitude α hα s W E R) (max 1 R) (stepRadius s W R)
  have hfour : stepRadius s W R ≤ 4 * stepRadius s W R := by linarith
  have hmax : 0 ≤ max (4 * stepRadius s W R) K :=
    (mul_nonneg (by norm_num) hS).trans (le_max_left _ _)
  calc
    stepRadius s W R ≤ 4 * stepRadius s W R := hfour
    _ ≤ max (4 * stepRadius s W R) K := le_max_left _ _
    _ ≤ 4 * max (4 * stepRadius s W R) K := by linarith
    _ ≤ max (defectRadius s W R)
        (4 * max (4 * stepRadius s W R) K) := le_max_right _ _

noncomputable def newtonIter (α c : ℝ) (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun t =>
      newtonIter α c f n t + Newton.step α c f (newtonIter α c f n) t

def newtonIncrement (α c : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  Newton.step α c f (newtonIter α c f n)

structure IterationInvariant (α c B : ℝ) (f : ℝ → ℝ) (n : ℕ) : Prop where
  smooth : ContDiff ℝ ∞ (newtonIter α c f n)
  periodic : Function.Periodic (newtonIter α c f n) 1
  deriv_bound : ∀ t,
    |deriv (newtonIter α c f n) t| ≤ accumulatedIncrement n
  derivative_majorized : DerivativeMajorized (iterationOrder n)
    (accumulatedIncrement n) (radiusBudget B n) (newtonIter α c f n)
  residual_majorized : Majorized (iterationOrder n) (errorBudget B n)
    (radiusBudget B n) (Newton.residual α c f (newtonIter α c f n))

theorem IterationInvariant.goodLift {α c B : ℝ} {f : ℝ → ℝ} {n : ℕ}
    (h : IterationInvariant α c B f n) :
    Newton.GoodLift (newtonIter α c f n) := by
  apply goodLift_of_deriv_bound
  intro t
  exact (h.deriv_bound t).trans (accumulatedIncrement_le_eighth n)

theorem initialIterationInvariant {α c B F RF : ℝ} {f : ℝ → ℝ}
    (hf : Majorized 1 F RF f) (hfs : ContDiff ℝ ∞ f)
    (hB : 1 ≤ B) (hRF0 : 0 ≤ RF) (hRF : RF ≤ B)
    (hc : |c| * F ≤ errorBudget B 0) :
    IterationInvariant α c B f 0 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hRFBudget : RF ≤ radiusBudget B 0 := by
    apply hRF.trans
    unfold radiusBudget
    simpa only [pow_one] using
      (pow_mono_exponent hB
        (show 1 ≤ radiusExponent 0 by norm_num [radiusExponent]))
  refine
    { smooth := by exact contDiff_const
      periodic := by intro t; simp [newtonIter]
      deriv_bound := by intro t; simp [newtonIter, accumulatedIncrement]
      derivative_majorized := by
        simpa [newtonIter, accumulatedIncrement, iterationOrder] using
          derivativeMajorized_zero 1 (radiusBudget B 0)
      residual_majorized := ?_ }
  have hscaled := hf.const_mul hfs (c := -c)
  have hamp : |-c| * F ≤ errorBudget B 0 := by simpa only [abs_neg] using hc
  have hscaled' := (hscaled.amplitude_mono hamp hRF0).radius_mono
    (errorBudget_nonneg hB0 0) hRF0 hRFBudget
  have hreszero : Newton.residual α c f (newtonIter α c f 0) =
      fun t => -(c * f t) := by
    funext t
    simp [Newton.residual, Helpers.discreteLaplacian, newtonIter]
  rw [show iterationOrder 0 = 1 by rfl, hreszero]
  simpa only [neg_mul] using hscaled'

theorem radiusBudget_one_le {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    1 ≤ radiusBudget B n := by
  unfold radiusBudget
  exact one_le_pow₀ hB

theorem radiusBudget_nonneg {B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ radiusBudget B n := by
  unfold radiusBudget
  positivity

theorem radiusBudget_mono {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    radiusBudget B n ≤ radiusBudget B (n + 1) := by
  unfold radiusBudget
  exact pow_mono_exponent hB (radiusExponent_mono n)

/-- The quantitative Newton invariants hold at every finite stage. -/
theorem iterationInvariant {α c B F RF : ℝ} {f : ℝ → ℝ}
    (hα : IsDiophantine α)
    (hf : Majorized 1 F RF f) (hfs : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hB : 64 ≤ B) (hsolve : solveConstant α hα ≤ B)
    (hF : 0 ≤ F) (hFB : F ≤ B) (hRF : 0 ≤ RF) (hRFB : RF ≤ B)
    (hc : |c| ≤ 1) (hinitial : |c| * F ≤ errorBudget B 0)
    (n : ℕ) : IterationInvariant α c B f n := by
  have hB2 : 2 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  induction n with
  | zero =>
      exact initialIterationInvariant hf hfs hB1 hRF hRFB hinitial
  | succ n ih =>
      have hW0 : 0 ≤ accumulatedIncrement n :=
        accumulatedIncrement_nonneg n
      have hW1 : accumulatedIncrement n ≤ 1 :=
        (accumulatedIncrement_le_eighth n).trans (by norm_num)
      have hE0 : 0 ≤ errorBudget B n := errorBudget_nonneg hB0 n
      have hE1 : errorBudget B n ≤ 1 := errorBudget_le_one hB1 n
      have hR0 : 0 ≤ radiusBudget B n := radiusBudget_nonneg hB0 n
      have hR1 : 1 ≤ radiusBudget B n := radiusBudget_one_le hB1 n
      have hsmall : B ^ lossExponent n * errorBudget B n ≤ 1 :=
        (loss_mul_errorBudget_le_incrementBudget hB2 n).trans
          (incrementBudget_le_one n)
      have hgood := ih.goodLift
      have hscalar := newton_scalar_bounds (α := α) hα
        (B := B) (F := F) (RF := RF)
        (W := accumulatedIncrement n) (E := errorBudget B n)
        (R := radiusBudget B n) (c := c) (n := n)
        hB hsolve hF hFB hRF hRFB hW0 hW1 hE0 hE1 hsmall
        hR1 le_rfl hc
      rcases hscalar with
        ⟨hstepA, hstepR, _hreducedA, _hreducedR, hnextR,
          hnextA, hstepProd, hstepDerivProd⟩
      have hsolve0 : 0 ≤ solveConstant α hα :=
        (solveConstant_pos α hα).le
      have hA0 : 0 ≤ stepAmplitude α hα (iterationOrder n)
          (accumulatedIncrement n) (errorBudget B n)
          (radiusBudget B n) := by
        have hLift : 0 ≤ stepLiftAmplitude (iterationOrder n)
            (accumulatedIncrement n) := by
          unfold stepLiftAmplitude
          positivity
        have hFirstRhs : 0 ≤ firstRhsAmplitude (iterationOrder n)
            (accumulatedIncrement n) (errorBudget B n) := by
          unfold firstRhsAmplitude
          exact mul_nonneg hLift hE0
        have hFirst : 0 ≤ firstSolutionAmplitude α hα (iterationOrder n)
            (accumulatedIncrement n) (errorBudget B n)
            (radiusBudget B n) := by
          unfold firstSolutionAmplitude
          positivity
        have hSecond : 0 ≤ secondRhsAmplitude α hα (iterationOrder n)
            (accumulatedIncrement n) (errorBudget B n)
            (radiusBudget B n) := by
          unfold secondRhsAmplitude
          exact mul_nonneg (by norm_num) hFirst
        have hReduced : 0 ≤ reducedAmplitude α hα (iterationOrder n)
            (accumulatedIncrement n) (errorBudget B n)
            (radiusBudget B n) := by
          unfold reducedAmplitude
          positivity
        unfold stepAmplitude
        exact mul_nonneg hLift hReduced
      have hS0 : 0 ≤ stepRadius (iterationOrder n)
          (accumulatedIncrement n) (radiusBudget B n) := by
        unfold stepRadius reducedRadius secondRhsRadius secondBaseRadius
          firstSolutionRadius inverseTwistRadius firstRhsRadius
          stepLiftRadius stepLiftAmplitude
        positivity
      have hstep := step_majorized hα c hfs hfper hfmean
        ih.smooth ih.periodic hgood ih.derivative_majorized
        ih.residual_majorized hW0 hE0 hR0
      have hstepSmooth := Newton.step_contDiff hα c hfs hfper
        ih.smooth ih.periodic hgood
      have hstepPeriodic := Newton.step_periodic α c (f := f) ih.periodic
      have hnextAmp0 : 0 ≤ nextAmplitude α hα c 1 (iterationOrder n)
          F RF (accumulatedIncrement n) (errorBudget B n)
          (radiusBudget B n) := by
        have hdefect : 0 ≤ defectAmplitude α hα (iterationOrder n)
            (accumulatedIncrement n) (errorBudget B n)
            (radiusBudget B n) := by
          unfold defectAmplitude reducedStepAmplitude
          apply mul_nonneg
          · exact mul_nonneg (mul_nonneg hE0 hR0)
              (pow_nonneg (by norm_num) _)
          · exact mul_nonneg (by norm_num) hA0
        have htaylor : 0 ≤ taylorRemainderAmplitude 1 F RF
            (stepAmplitude α hα (iterationOrder n)
              (accumulatedIncrement n) (errorBudget B n)
              (radiusBudget B n)) := by
          unfold taylorRemainderAmplitude secondDerivativeAmplitude
          positivity
        unfold nextAmplitude
        exact add_nonneg hdefect (mul_nonneg (abs_nonneg c) htaylor)
      have hnextRad0 : 0 ≤ nextRadius α hα 1 (iterationOrder n)
          RF (accumulatedIncrement n) (errorBudget B n)
          (radiusBudget B n) := by
        have hdefect : 0 ≤ defectRadius (iterationOrder n)
            (accumulatedIncrement n) (radiusBudget B n) := by
          unfold defectRadius reducedStepRadius stepRadius reducedRadius
            secondRhsRadius secondBaseRadius firstSolutionRadius
            inverseTwistRadius firstRhsRadius stepLiftRadius
            inverseLiftRadius stepLiftAmplitude
          positivity
        unfold nextRadius
        exact hdefect.trans (le_max_left _ _)
      have hresNext := residual_next_majorized hα c hf hfs hfper hfmean
        ih.smooth ih.periodic hgood ih.derivative_majorized
        ih.residual_majorized hF hRF hW0 hE0 hR0
      rw [nextExponent_iterationOrder n] at hresNext
      have hEnext0 : 0 ≤ errorBudget B (n + 1) :=
        errorBudget_nonneg hB0 (n + 1)
      have hnextA' : nextAmplitude α hα c 1 (iterationOrder n)
          F RF (accumulatedIncrement n) (errorBudget B n)
            (radiusBudget B n) ≤ errorBudget B (n + 1) :=
        hnextA.trans (errorBudget_contracts hB2 n)
      have hresNext' := hresNext.amplitude_radius_mono
        hnextA' hEnext0 hnextRad0 hnextR
      have hresFinal : Majorized (iterationOrder (n + 1))
          (errorBudget B (n + 1)) (radiusBudget B (n + 1))
          (Newton.residual α c f (newtonIter α c f (n + 1))) := by
        simpa only [newtonIter] using hresNext'
      have hRmono : radiusBudget B n ≤ radiusBudget B (n + 1) :=
        radiusBudget_mono hB1 n
      have huDerivative : DerivativeMajorized (iterationOrder (n + 1))
          (accumulatedIncrement n) (radiusBudget B (n + 1))
          (newtonIter α c f n) :=
        (ih.derivative_majorized.exponent_mono
          (by unfold iterationOrder; omega) hW0 hR0).radius_mono
          hW0 hR0 hRmono
      have hstepToNext : stepRadius (iterationOrder n)
          (accumulatedIncrement n) (radiusBudget B n) ≤
          radiusBudget B (n + 1) :=
        (stepRadius_le_nextRadius α hα 1 (iterationOrder n) RF
          (accumulatedIncrement n) (errorBudget B n)
          (radiusBudget B n) hS0).trans hnextR
      have hstepInc : stepAmplitude α hα (iterationOrder n)
          (accumulatedIncrement n) (errorBudget B n)
          (radiusBudget B n) *
          stepRadius (iterationOrder n) (accumulatedIncrement n)
            (radiusBudget B n) ≤ incrementBudget n :=
        hstepProd.trans (loss_mul_errorBudget_le_incrementBudget hB2 n)
      have hstepDerivative : DerivativeMajorized (iterationOrder (n + 1))
          (incrementBudget n) (radiusBudget B (n + 1))
          (Newton.step α c f (newtonIter α c f n)) :=
        ((hstep.derivativeMajorized.exponent_mono
          (by unfold iterationOrder; omega)
          (mul_nonneg hA0 hS0) hS0).amplitude_mono
          hstepInc hS0).radius_mono
          (incrementBudget_nonneg n) hS0 hstepToNext
      have hderivativeFinal : DerivativeMajorized (iterationOrder (n + 1))
          (accumulatedIncrement (n + 1)) (radiusBudget B (n + 1))
          (newtonIter α c f (n + 1)) := by
        have hadd := huDerivative.add hstepDerivative ih.smooth hstepSmooth
        simpa only [newtonIter, accumulatedIncrement_succ] using hadd
      have hpointDeriv (t : ℝ) :
          |deriv (newtonIncrement α c f n) t| ≤ incrementBudget n := by
        have hraw := hstep 1 t
        have hraw' : |deriv (newtonIncrement α c f n) t| ≤
            stepAmplitude α hα (iterationOrder n)
                (accumulatedIncrement n) (errorBudget B n)
                (radiusBudget B n) *
              weight (iterationOrder n + 2) 1 *
              stepRadius (iterationOrder n) (accumulatedIncrement n)
                (radiusBudget B n) := by
          simpa only [newtonIncrement,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
            Real.norm_eq_abs, pow_one] using hraw
        exact (hraw'.trans hstepDerivProd).trans
          (loss_mul_errorBudget_le_incrementBudget hB2 n)
      have hincSmooth : ContDiff ℝ ∞ (newtonIncrement α c f n) := by
        simpa only [newtonIncrement] using hstepSmooth
      have hderivFinal (t : ℝ) :
          |deriv (newtonIter α c f (n + 1)) t| ≤
            accumulatedIncrement (n + 1) := by
        have hdu : deriv (newtonIter α c f (n + 1)) t =
            deriv (newtonIter α c f n) t +
              deriv (newtonIncrement α c f n) t := by
          change deriv (newtonIter α c f n + newtonIncrement α c f n) t = _
          rw [deriv_add
            (ih.smooth.differentiable (by simp)).differentiableAt
            (hincSmooth.differentiable (by simp)).differentiableAt]
        rw [hdu]
        calc
          |deriv (newtonIter α c f n) t +
              deriv (newtonIncrement α c f n) t| ≤
              |deriv (newtonIter α c f n) t| +
                |deriv (newtonIncrement α c f n) t| := abs_add_le _ _
          _ ≤ accumulatedIncrement n + incrementBudget n :=
            add_le_add (ih.deriv_bound t) (hpointDeriv t)
          _ = accumulatedIncrement (n + 1) :=
            (accumulatedIncrement_succ n).symm
      refine
        { smooth := by
            change ContDiff ℝ ∞
              (newtonIter α c f n + Newton.step α c f (newtonIter α c f n))
            exact ih.smooth.add hstepSmooth
          periodic := by
            change Function.Periodic
              (newtonIter α c f n + Newton.step α c f (newtonIter α c f n)) 1
            exact ih.periodic.add hstepPeriodic
          deriv_bound := hderivFinal
          derivative_majorized := hderivativeFinal
          residual_majorized := hresFinal }

structure IterationSetup (α c B F RF : ℝ) (f : ℝ → ℝ) : Prop where
  diophantine : IsDiophantine α
  f_majorized : Majorized 1 F RF f
  f_smooth : ContDiff ℝ ∞ f
  f_periodic : Function.Periodic f 1
  f_mean : ∫ t in (0 : ℝ)..1, f t = 0
  base_large : 64 ≤ B
  solve_le : solveConstant α diophantine ≤ B
  f_nonneg : 0 ≤ F
  f_le : F ≤ B
  radius_nonneg : 0 ≤ RF
  radius_le : RF ≤ B
  coupling_le : |c| ≤ 1
  initial_error : |c| * F ≤ errorBudget B 0

theorem IterationSetup.invariant {α c B F RF : ℝ} {f : ℝ → ℝ}
    (h : IterationSetup α c B F RF f) (n : ℕ) :
    IterationInvariant α c B f n :=
  iterationInvariant h.diophantine h.f_majorized h.f_smooth h.f_periodic
    h.f_mean h.base_large h.solve_le h.f_nonneg h.f_le
    h.radius_nonneg h.radius_le h.coupling_le h.initial_error n

theorem IterationSetup.increment_smooth {α c B F RF : ℝ} {f : ℝ → ℝ}
    (h : IterationSetup α c B F RF f) (n : ℕ) :
    ContDiff ℝ ∞ (newtonIncrement α c f n) := by
  let hn := h.invariant n
  simpa only [newtonIncrement] using
    Newton.step_contDiff h.diophantine c h.f_smooth h.f_periodic
      hn.smooth hn.periodic hn.goodLift

theorem IterationSetup.increment_periodic {α c B F RF : ℝ} {f : ℝ → ℝ}
    (h : IterationSetup α c B F RF f) (n : ℕ) :
    Function.Periodic (newtonIncrement α c f n) 1 := by
  simpa only [newtonIncrement] using
    Newton.step_periodic α c (f := f) (h.invariant n).periodic

theorem IterationSetup.increment_majorized {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) (n : ℕ) :
    Majorized (iterationOrder n + 2)
      (B ^ lossExponent n * errorBudget B n) (B ^ lossExponent n)
      (newtonIncrement α c f n) := by
  let hn := h.invariant n
  have hB2 : 2 ≤ B := by linarith [h.base_large]
  have hB1 : 1 ≤ B := by linarith [h.base_large]
  have hB0 : 0 ≤ B := by linarith [h.base_large]
  have hW0 := accumulatedIncrement_nonneg n
  have hW1 : accumulatedIncrement n ≤ 1 :=
    (accumulatedIncrement_le_eighth n).trans (by norm_num)
  have hE0 := errorBudget_nonneg hB0 n
  have hE1 := errorBudget_le_one hB1 n
  have hR0 := radiusBudget_nonneg hB0 n
  have hR1 := radiusBudget_one_le hB1 n
  have hsmall : B ^ lossExponent n * errorBudget B n ≤ 1 :=
    (loss_mul_errorBudget_le_incrementBudget hB2 n).trans
      (incrementBudget_le_one n)
  have hscalar := newton_scalar_bounds h.diophantine
    (B := B) (F := F) (RF := RF)
    (W := accumulatedIncrement n) (E := errorBudget B n)
    (R := radiusBudget B n) (c := c) (n := n)
    h.base_large h.solve_le h.f_nonneg h.f_le h.radius_nonneg
    h.radius_le hW0 hW1 hE0 hE1 hsmall hR1 le_rfl h.coupling_le
  have hstep := step_majorized h.diophantine c h.f_smooth h.f_periodic
    h.f_mean hn.smooth hn.periodic hn.goodLift hn.derivative_majorized
    hn.residual_majorized hW0 hE0 hR0
  have hS0 : 0 ≤ stepRadius (iterationOrder n)
      (accumulatedIncrement n) (radiusBudget B n) := by
    unfold stepRadius reducedRadius secondRhsRadius secondBaseRadius
      firstSolutionRadius inverseTwistRadius firstRhsRadius
      stepLiftRadius stepLiftAmplitude
    positivity
  have htargetA : 0 ≤ B ^ lossExponent n * errorBudget B n :=
    mul_nonneg (pow_nonneg hB0 _) hE0
  rcases hscalar with ⟨hA, hR, _⟩
  have hp := (hstep.amplitude_mono hA hS0).radius_mono
    htargetA hS0 hR
  simpa only [newtonIncrement] using hp

theorem IterationSetup.increment_iteratedFDeriv_le {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f)
    (k n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (newtonIncrement α c f n) t‖ ≤
      smoothStepBound B k n := by
  have hm := h.increment_majorized n k t
  simpa only [smoothStepBound] using hm

theorem IterationSetup.increment_deriv_le {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f)
    (n : ℕ) (t : ℝ) :
    ‖deriv (newtonIncrement α c f n) t‖ ≤ incrementBudget n := by
  let hn := h.invariant n
  have hB2 : 2 ≤ B := by linarith [h.base_large]
  have hB1 : 1 ≤ B := by linarith [h.base_large]
  have hB0 : 0 ≤ B := by linarith [h.base_large]
  have hW0 := accumulatedIncrement_nonneg n
  have hW1 : accumulatedIncrement n ≤ 1 :=
    (accumulatedIncrement_le_eighth n).trans (by norm_num)
  have hE0 := errorBudget_nonneg hB0 n
  have hE1 := errorBudget_le_one hB1 n
  have hR0 := radiusBudget_nonneg hB0 n
  have hR1 := radiusBudget_one_le hB1 n
  have hsmall : B ^ lossExponent n * errorBudget B n ≤ 1 :=
    (loss_mul_errorBudget_le_incrementBudget hB2 n).trans
      (incrementBudget_le_one n)
  have hscalar := newton_scalar_bounds h.diophantine
    (B := B) (F := F) (RF := RF)
    (W := accumulatedIncrement n) (E := errorBudget B n)
    (R := radiusBudget B n) (c := c) (n := n)
    h.base_large h.solve_le h.f_nonneg h.f_le h.radius_nonneg
    h.radius_le hW0 hW1 hE0 hE1 hsmall hR1 le_rfl h.coupling_le
  have hstep := step_majorized h.diophantine c h.f_smooth h.f_periodic
    h.f_mean hn.smooth hn.periodic hn.goodLift hn.derivative_majorized
    hn.residual_majorized hW0 hE0 hR0
  have hraw := hstep 1 t
  have hraw' : ‖deriv (newtonIncrement α c f n) t‖ ≤
      stepAmplitude α h.diophantine (iterationOrder n)
          (accumulatedIncrement n) (errorBudget B n) (radiusBudget B n) *
        weight (iterationOrder n + 2) 1 *
        stepRadius (iterationOrder n) (accumulatedIncrement n)
          (radiusBudget B n) := by
    simpa only [newtonIncrement,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
      pow_one] using hraw
  rcases hscalar with ⟨_, _, _, _, _, _, _, hderiv⟩
  exact (hraw'.trans hderiv).trans
    (loss_mul_errorBudget_le_incrementBudget hB2 n)

theorem newtonIter_eq_sum_range (α c : ℝ) (f : ℝ → ℝ)
    (n : ℕ) (t : ℝ) :
    newtonIter α c f n t =
      ∑ i ∈ Finset.range n, newtonIncrement α c f i t := by
  induction n with
  | zero => simp [newtonIter]
  | succ n ih =>
      simp only [newtonIter, newtonIncrement, Finset.sum_range_succ, ih]

theorem errorBudget_le_geometric {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    errorBudget B n ≤ B⁻¹ ^ n := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hq0 : 0 ≤ B⁻¹ := inv_nonneg.mpr hBpos.le
  have hq1 : B⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hBpos]
    exact hB
  unfold errorBudget
  apply pow_le_pow_of_le_one hq0 hq1
  unfold errorExponent
  have hn := nat_succ_le_two_pow n
  omega

theorem tendsto_errorBudget_zero {B : ℝ} (hB : 1 < B) :
    Tendsto (errorBudget B) atTop (𝓝 0) := by
  have hq : |B⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans hB))]
    exact inv_lt_one_of_one_lt₀ hB
  apply squeeze_zero (fun n => errorBudget_nonneg (by linarith) n)
    (fun n => errorBudget_le_geometric hB.le n)
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq

def newtonLimit (α c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, newtonIncrement α c f n t

theorem IterationSetup.increment_summable {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) (t : ℝ) :
    Summable (fun n => newtonIncrement α c f n t) := by
  have hB2 : 2 ≤ B := by linarith [h.base_large]
  apply (summable_smoothStepBound hB2 0).of_norm_bounded
  intro n
  have hn := h.increment_iteratedFDeriv_le 0 n t
  simpa only [norm_iteratedFDeriv_zero] using hn

theorem IterationSetup.limit_smooth {α c B F RF : ℝ} {f : ℝ → ℝ}
    (h : IterationSetup α c B F RF f) :
    ContDiff ℝ ∞ (newtonLimit α c f) := by
  have hB2 : 2 ≤ B := by linarith [h.base_large]
  unfold newtonLimit
  apply contDiff_tsum (fun n => h.increment_smooth n)
    (fun k _ => summable_smoothStepBound hB2 k)
  intro k n t _
  exact h.increment_iteratedFDeriv_le k n t

theorem IterationSetup.limit_periodic {α c B F RF : ℝ} {f : ℝ → ℝ}
    (h : IterationSetup α c B F RF f) :
    Function.Periodic (newtonLimit α c f) 1 := by
  intro t
  unfold newtonLimit
  apply tsum_congr
  intro n
  exact h.increment_periodic n t

theorem IterationSetup.iter_tendsto_limit {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) (t : ℝ) :
    Tendsto (fun n => newtonIter α c f n t) atTop
      (𝓝 (newtonLimit α c f t)) := by
  unfold newtonLimit
  simpa only [newtonIter_eq_sum_range] using
    (h.increment_summable t).hasSum.tendsto_sum_nat

theorem summable_incrementBudget : Summable incrementBudget := by
  have hgeom : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hscaled := hgeom.mul_left (((1 : ℝ) / 2) ^ 4)
  change Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 4))
  simpa only [← pow_add, add_comm] using hscaled

theorem tsum_incrementBudget_le :
    (∑' n, incrementBudget n) ≤ (1 : ℝ) / 8 := by
  exact Real.tsum_le_of_sum_range_le incrementBudget_nonneg
    incrementBudget_partial_sum_le

theorem IterationSetup.limit_deriv_bound {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) (t : ℝ) :
    |deriv (newtonLimit α c f) t| ≤ (1 : ℝ) / 8 := by
  have hdiff (n : ℕ) : Differentiable ℝ (newtonIncrement α c f n) :=
    (h.increment_smooth n).differentiable (by simp)
  have hderivSummable :
      Summable (fun n => deriv (newtonIncrement α c f n) t) :=
    summable_incrementBudget.of_norm_bounded fun n => h.increment_deriv_le n t
  have hderivEq : deriv (newtonLimit α c f) t =
      ∑' n, deriv (newtonIncrement α c f n) t := by
    change deriv (fun z => ∑' n, newtonIncrement α c f n z) t = _
    exact deriv_tsum_apply summable_incrementBudget hdiff
      (fun n x => h.increment_deriv_le n x)
      (h.increment_summable 0) t
  rw [hderivEq, ← Real.norm_eq_abs]
  calc
    ‖∑' n, deriv (newtonIncrement α c f n) t‖ ≤
        ∑' n, ‖deriv (newtonIncrement α c f n) t‖ :=
      norm_tsum_le_tsum_norm hderivSummable.norm
    _ ≤ ∑' n, incrementBudget n :=
      hderivSummable.norm.tsum_le_tsum
        (fun n => h.increment_deriv_le n t) summable_incrementBudget
    _ ≤ (1 : ℝ) / 8 := tsum_incrementBudget_le

theorem IterationSetup.residual_norm_le {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f)
    (n : ℕ) (t : ℝ) :
    ‖Newton.residual α c f (newtonIter α c f n) t‖ ≤ errorBudget B n := by
  have hi : IterationInvariant α c B f n := h.invariant n
  have hn := hi.residual_majorized 0 t
  have hw : weight (iterationOrder n) 0 = 1 := by
    unfold weight
    norm_num
  rw [norm_iteratedFDeriv_zero, hw, pow_zero, mul_one, mul_one] at hn
  exact hn

theorem IterationSetup.residual_tendsto_zero {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) (t : ℝ) :
    Tendsto (fun n => Newton.residual α c f (newtonIter α c f n) t)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => h.residual_norm_le n t)
  exact tendsto_errorBudget_zero (by linarith [h.base_large])

theorem IterationSetup.limit_residual_eq_zero {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) (t : ℝ) :
    Newton.residual α c f (newtonLimit α c f) t = 0 := by
  have hplus := h.iter_tendsto_limit (t + α)
  have hcenter := h.iter_tendsto_limit t
  have hminus := h.iter_tendsto_limit (t - α)
  have harg : Tendsto (fun n => t + newtonIter α c f n t) atTop
      (𝓝 (t + newtonLimit α c f t)) := tendsto_const_nhds.add hcenter
  have hfval : Tendsto (fun n => f (t + newtonIter α c f n t)) atTop
      (𝓝 (f (t + newtonLimit α c f t))) :=
    (h.f_smooth.continuous.tendsto _).comp harg
  have hres : Tendsto
      (fun n => Newton.residual α c f (newtonIter α c f n) t) atTop
      (𝓝 (Newton.residual α c f (newtonLimit α c f) t)) := by
    simpa only [Newton.residual, Helpers.discreteLaplacian] using
      ((hplus.sub (hcenter.const_mul 2)).add hminus).sub (hfval.const_mul c)
  exact tendsto_nhds_unique hres (h.residual_tendsto_zero t)

/-- The Newton series converges to a smooth periodic solution, with a uniform
derivative bound strong enough to preserve strict monotonicity of the lift. -/
theorem IterationSetup.exists_limit_solution {α c B F RF : ℝ}
    {f : ℝ → ℝ} (h : IterationSetup α c B F RF f) :
    ∃ u : ℝ → ℝ,
      ContDiff ℝ ∞ u ∧ Function.Periodic u 1 ∧
      (∀ t, |deriv u t| ≤ (1 : ℝ) / 8) ∧
      ∀ t, Helpers.discreteLaplacian α u t = c * f (t + u t) := by
  refine ⟨newtonLimit α c f, h.limit_smooth, h.limit_periodic,
    h.limit_deriv_bound, ?_⟩
  intro t
  have hz := h.limit_residual_eq_zero t
  simpa only [Newton.residual, sub_eq_zero] using hz

/-- Quantitative KAM endpoint obtained from the analytic majorant and the
convergent Newton series. -/
theorem exists_invariant_curve_of_small_c
    (α : ℝ) (hα : IsDiophantine α) (f : ℝ → ℝ)
    (hfanalytic : AnalyticOnNhd ℝ f Set.univ)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, |c| < c₀ →
      ∃ q : ℝ → ℝ,
        ContDiff ℝ ∞ q ∧ StrictMono q ∧
        Function.Periodic (fun t => q t - t) 1 ∧
        ∀ t : ℝ,
          q (t + α) - 2 * q t + q (t - α) = c * f (q t) := by
  obtain ⟨F, RF, hF, hRF1, hf⟩ :=
    exists_periodic_analytic_majorant hfanalytic hfper
  have hfs : ContDiff ℝ ∞ f := Helpers.analyticOnNhd_contDiff_top hfanalytic
  let B := kamBase α hα F RF
  have hB64 : 64 ≤ B := kamBase_ge_sixty_four α hα F RF
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hsolve : solveConstant α hα ≤ B :=
    solveConstant_le_kamBase α hα F RF
  have hFB : F ≤ B := left_le_kamBase α hα F RF
  have hRFB : RF ≤ B := right_le_kamBase α hα F RF
  have hRF0 : 0 ≤ RF := zero_le_one.trans hRF1
  let D := max 1 F
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hFD : F ≤ D := le_max_right _ _
  have hEpos : 0 < errorBudget B 0 :=
    errorBudget_pos (by linarith) 0
  let c₀ := errorBudget B 0 / D
  refine ⟨c₀, div_pos hEpos hDpos, ?_⟩
  intro c hc
  have hcD : |c| * D < errorBudget B 0 := by
    apply (lt_div_iff₀ hDpos).mp
    simpa only [c₀] using hc
  have hinitial : |c| * F ≤ errorBudget B 0 := by
    exact le_of_lt <|
      (mul_le_mul_of_nonneg_left hFD (abs_nonneg c)).trans_lt hcD
  have hEle : errorBudget B 0 ≤ D :=
    (errorBudget_le_one hB1 0).trans hD1
  have hc₀le : c₀ ≤ 1 := by
    unfold c₀
    exact (div_le_one hDpos).2 hEle
  have hc1 : |c| ≤ 1 := (le_of_lt hc).trans hc₀le
  let setup : IterationSetup α c B F RF f :=
    { diophantine := hα
      f_majorized := hf
      f_smooth := hfs
      f_periodic := hfper
      f_mean := hfmean
      base_large := hB64
      solve_le := hsolve
      f_nonneg := hF
      f_le := hFB
      radius_nonneg := hRF0
      radius_le := hRFB
      coupling_le := hc1
      initial_error := hinitial }
  obtain ⟨u, hu, huper, hdu, heq⟩ := setup.exists_limit_solution
  let q := fun t : ℝ => t + u t
  have huDiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hqmono : StrictMono q := by
    apply strictMono_of_deriv_pos
    intro t
    have hlo := neg_le_of_abs_le (hdu t)
    dsimp only [q]
    change 0 < deriv (id + u) t
    rw [deriv_add differentiableAt_id huDiff.differentiableAt, deriv_id]
    linarith
  refine ⟨q, contDiff_id.add hu, hqmono, ?_, ?_⟩
  · intro t
    simpa only [q, add_sub_cancel_left] using huper t
  · intro t
    calc
      q (t + α) - 2 * q t + q (t - α) =
          Helpers.discreteLaplacian α u t := by
        simp only [q, Helpers.discreteLaplacian]
        ring
      _ = c * f (t + u t) := heq t
      _ = c * f (q t) := rfl

end

end Submission.Majorant
