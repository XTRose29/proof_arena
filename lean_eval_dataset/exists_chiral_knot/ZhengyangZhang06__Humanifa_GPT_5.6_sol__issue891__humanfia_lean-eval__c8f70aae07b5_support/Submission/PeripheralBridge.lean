import Submission.CoreBoundary
import Submission.SymmetryDegree
import Submission.RadialPageObstruction

open Complex
open LeanEval.KnotTheory
open scoped unitInterval

namespace Submission.PeripheralBridge

noncomputable section

def balancedPolynomial (q : Milnor.CSphere) : ℂ :=
  Complex.I * (q.1.1 ^ 2 + RadialMilnor.radialCube q.1.2)

def weightedNormSq (q : Milnor.CSphere) : ℝ :=
  normSq q.1.1 / 16 + normSq q.1.2 / 9

theorem weightedNormSq_pos (q : Milnor.CSphere) : 0 < weightedNormSq q := by
  have hz := normSq_nonneg q.1.1
  have hw := normSq_nonneg q.1.2
  have hsum := q.2
  dsimp [weightedNormSq]
  by_contra h
  have hle : normSq q.1.1 / 16 + normSq q.1.2 / 9 ≤ 0 := le_of_not_gt h
  have hz0 : normSq q.1.1 = 0 := by nlinarith
  have hw0 : normSq q.1.2 = 0 := by nlinarith
  linarith

def unbalanceFactor (q : Milnor.CSphere) : ℝ :=
  (Real.sqrt (weightedNormSq q))⁻¹

theorem unbalanceFactor_pos (q : Milnor.CSphere) : 0 < unbalanceFactor q := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (weightedNormSq_pos q))

theorem unbalanceFactor_sq (q : Milnor.CSphere) :
    unbalanceFactor q ^ 2 * weightedNormSq q = 1 := by
  have hsqrt : Real.sqrt (weightedNormSq q) ^ 2 = weightedNormSq q :=
    Real.sq_sqrt (weightedNormSq_pos q).le
  have hsqrtNe : Real.sqrt (weightedNormSq q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (weightedNormSq_pos q))
  unfold unbalanceFactor
  calc
    (Real.sqrt (weightedNormSq q))⁻¹ ^ 2 * weightedNormSq q =
        (Real.sqrt (weightedNormSq q) ^ 2)⁻¹ * weightedNormSq q := by
          rw [inv_pow]
    _ = (weightedNormSq q)⁻¹ * weightedNormSq q := by rw [hsqrt]
    _ = 1 := inv_mul_cancel₀ (weightedNormSq_pos q).ne'

def unbalanceSphere (q : Milnor.CSphere) : Milnor.CSphere :=
  ⟨(((unbalanceFactor q / 4 : ℝ) : ℂ) * q.1.1,
      ((unbalanceFactor q / 3 : ℝ) : ℂ) * q.1.2), by
    change normSq (((unbalanceFactor q / 4 : ℝ) : ℂ) * q.1.1) +
        normSq (((unbalanceFactor q / 3 : ℝ) : ℂ) * q.1.2) = 1
    rw [normSq_mul, normSq_mul, normSq_ofReal, normSq_ofReal]
    have hfactor := unbalanceFactor_sq q
    dsimp [weightedNormSq] at hfactor
    nlinarith⟩

theorem unbalanceSphere_continuous : Continuous unbalanceSphere := by
  have hweighted : Continuous weightedNormSq := by
    unfold weightedNormSq
    fun_prop
  have hfactor : Continuous unbalanceFactor := by
    unfold unbalanceFactor
    exact (Real.continuous_sqrt.comp hweighted).inv₀
      (fun q => ne_of_gt (Real.sqrt_pos.2 (weightedNormSq_pos q)))
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (hfactor.div_const 4)).mul
      (continuous_fst.comp continuous_subtype_val)).prodMk
    ((Complex.continuous_ofReal.comp (hfactor.div_const 3)).mul
      (continuous_snd.comp continuous_subtype_val))

theorem radialCube_unbalanceW (q : Milnor.CSphere) :
    RadialMilnor.radialCube
        (((unbalanceFactor q / 3 : ℝ) : ℂ) * q.1.2) =
      ((unbalanceFactor q / 3 : ℝ) : ℂ) ^ 2 *
        RadialMilnor.radialCube q.1.2 := by
  exact RadialMilnor.radialCube_smul_of_nonneg _
    (div_nonneg (unbalanceFactor_pos q).le (by norm_num)) _

theorem polynomial_unbalanceSphere (q : Milnor.CSphere) :
    RadialMilnor.polynomial (unbalanceSphere q) =
      ((unbalanceFactor q : ℝ) : ℂ) ^ 2 * balancedPolynomial q := by
  rw [RadialMilnor.polynomial, RadialMilnor.basePolynomial]
  change Complex.I *
      (16 * (((unbalanceFactor q / 4 : ℝ) : ℂ) * q.1.1) ^ 2 +
        9 * RadialMilnor.radialCube
          (((unbalanceFactor q / 3 : ℝ) : ℂ) * q.1.2)) = _
  rw [radialCube_unbalanceW]
  unfold balancedPolynomial
  push_cast
  ring

def ellipseARe (s theta : ℝ) : ℝ := (s + Real.cos theta) / 2

def ellipseAIm (s theta : ℝ) : ℝ :=
  Real.sqrt (1 - s ^ 2) * Real.sin theta / 2

def ellipseA (s theta : ℝ) : ℂ :=
  (ellipseARe s theta : ℂ) + (ellipseAIm s theta : ℂ) * Complex.I

def ellipseBRe (s theta : ℝ) : ℝ := (s - Real.cos theta) / 2

def ellipseBIm (s theta : ℝ) : ℝ :=
  -(Real.sqrt (1 - s ^ 2) * Real.sin theta / 2)

def ellipseB (s theta : ℝ) : ℂ :=
  (ellipseBRe s theta : ℂ) + (ellipseBIm s theta : ℂ) * Complex.I

@[simp] theorem ellipseA_re (s theta : ℝ) :
    (ellipseA s theta).re = ellipseARe s theta := by
  simp only [ellipseA, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]

@[simp] theorem ellipseA_im (s theta : ℝ) :
    (ellipseA s theta).im = ellipseAIm s theta := by
  simp only [ellipseA, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, mul_zero, zero_add, add_zero]

@[simp] theorem ellipseB_re (s theta : ℝ) :
    (ellipseB s theta).re = ellipseBRe s theta := by
  simp only [ellipseB, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]

@[simp] theorem ellipseB_im (s theta : ℝ) :
    (ellipseB s theta).im = ellipseBIm s theta := by
  simp only [ellipseB, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, mul_zero, zero_add, add_zero]

theorem ellipse_add (s theta : ℝ) :
    ellipseA s theta + ellipseB s theta = (s : ℂ) := by
  apply Complex.ext
  · simp [ellipseA, ellipseB, ellipseARe, ellipseBRe]
    ring
  · simp [ellipseA, ellipseB, ellipseAIm, ellipseBIm]

theorem normSq_ellipseA {s theta : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    normSq (ellipseA s theta) = ((1 + s * Real.cos theta) / 2) ^ 2 := by
  have hsqrt : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  rw [normSq_apply, ellipseA_re, ellipseA_im]
  unfold ellipseARe ellipseAIm
  field_simp
  nlinarith [hsqrt, Real.sin_sq_add_cos_sq theta]

theorem normSq_ellipseB {s theta : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    normSq (ellipseB s theta) = ((1 - s * Real.cos theta) / 2) ^ 2 := by
  have hsqrt : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  rw [normSq_apply, ellipseB_re, ellipseB_im]
  unfold ellipseBRe ellipseBIm
  field_simp
  nlinarith [hsqrt, Real.sin_sq_add_cos_sq theta]

theorem norm_ellipseA {s theta : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖ellipseA s theta‖ = (1 + s * Real.cos theta) / 2 := by
  have hright : 0 ≤ (1 + s * Real.cos theta) / 2 := by
    have hcos := Real.neg_one_le_cos theta
    nlinarith
  have hsq := normSq_ellipseA hs0 hs1 (theta := theta)
  rw [normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (ellipseA s theta)]

theorem norm_ellipseB {s theta : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖ellipseB s theta‖ = (1 - s * Real.cos theta) / 2 := by
  have hright : 0 ≤ (1 - s * Real.cos theta) / 2 := by
    have hcos := Real.cos_le_one theta
    nlinarith
  have hsq := normSq_ellipseB hs0 hs1 (theta := theta)
  rw [normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (ellipseB s theta)]

theorem norm_ellipse_add {s theta : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖ellipseA s theta‖ + ‖ellipseB s theta‖ = 1 := by
  rw [norm_ellipseA hs0 hs1, norm_ellipseB hs0 hs1]
  ring

def squareMultiplier (z : ℂ) : ℂ := z ^ ((2 : ℂ)⁻¹)

@[simp] theorem squareMultiplier_sq (z : ℂ) : squareMultiplier z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num)

theorem squareMultiplier_continuousAt_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    ContinuousAt squareMultiplier z :=
  Complex.continuousAt_cpow_const_of_re_pos (Or.inl hz) (by norm_num)

theorem radialCube_mul_of_norm_one (c w : ℂ) (hc : ‖c‖ = 1) :
    RadialMilnor.radialCube (c * w) = c ^ 3 * RadialMilnor.radialCube w := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  by_cases hw : w = 0
  · simp [hw]
  · rw [RadialMilnor.radialCube_of_ne (mul_ne_zero hc0 hw),
      RadialMilnor.radialCube_of_ne hw, mul_pow, norm_mul, hc, one_mul]
    ring

def minusThirdRoot : ℂ :=
  Complex.exp (-(((Real.pi / 3 : ℝ) : ℂ) * Complex.I))

@[simp] theorem norm_minusThirdRoot : ‖minusThirdRoot‖ = 1 := by
  have harg : -(((Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
      (((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [minusThirdRoot, harg, Complex.norm_exp_ofReal_mul_I]

@[simp] theorem minusThirdRoot_cube : minusThirdRoot ^ 3 = -1 := by
  rw [minusThirdRoot, ← Complex.exp_nat_mul]
  have harg :
      ((3 : ℕ) : ℂ) * -(((Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
        -((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_neg_pi_mul_I]

theorem log_I_mul_of_pos (r : ℝ) (hr : 0 < r) :
    Complex.log (Complex.I * (r : ℂ)) =
      Complex.log (r : ℂ) + (Real.pi / 2 : ℂ) * Complex.I := by
  rw [Complex.log_mul I_ne_zero (ofReal_ne_zero.mpr hr.ne')]
  · rw [Complex.log_I]
    ring
  · rw [Complex.arg_I, Complex.arg_ofReal_of_nonneg hr.le]
    constructor <;> nlinarith [Real.pi_pos]

theorem log_neg_I_mul_of_pos (r : ℝ) (hr : 0 < r) :
    Complex.log (-Complex.I * (r : ℂ)) =
      Complex.log (r : ℂ) - (Real.pi / 2 : ℂ) * Complex.I := by
  rw [Complex.log_mul (neg_ne_zero.mpr I_ne_zero)
    (ofReal_ne_zero.mpr hr.ne')]
  · rw [Complex.log_neg_I]
    ring
  · rw [Complex.arg_neg_I, Complex.arg_ofReal_of_nonneg hr.le]
    constructor <;> nlinarith [Real.pi_pos]

theorem squareMultiplier_I_mul (r : ℝ) (hr : 0 ≤ r) :
    squareMultiplier (Complex.I * (r : ℂ)) =
      Complex.I * squareMultiplier (-Complex.I * (r : ℂ)) := by
  by_cases hr0 : r = 0
  · simp [hr0, squareMultiplier, Complex.cpow_def]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    rw [squareMultiplier, squareMultiplier,
      Complex.cpow_def_of_ne_zero
        (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hr0)),
      Complex.cpow_def_of_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hr0)),
      log_I_mul_of_pos r hrp, log_neg_I_mul_of_pos r hrp,
      show ((2 : ℂ)⁻¹) = (1 / 2 : ℂ) by norm_num]
    let leftExponent : ℂ :=
      (Complex.log (r : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) * (1 / 2)
    let rightExponent : ℂ :=
      (Complex.log (r : ℂ) - (Real.pi / 2 : ℂ) * Complex.I) * (1 / 2)
    change Complex.exp leftExponent = Complex.I * Complex.exp rightExponent
    calc
      Complex.exp leftExponent =
          Complex.exp (((Real.pi / 2 : ℂ) * Complex.I) + rightExponent) := by
        congr 1
        dsimp [leftExponent, rightExponent]
        ring
      _ = Complex.exp ((Real.pi / 2 : ℂ) * Complex.I) *
          Complex.exp rightExponent := by rw [Complex.exp_add]
      _ = Complex.I * Complex.exp rightExponent := by
        rw [Complex.exp_pi_div_two_mul_I]

theorem minusThirdRoot_cubeRoot_I_mul (r : ℝ) (hr : 0 ≤ r) :
    minusThirdRoot * RadialMilnor.cubeRoot (Complex.I * (r : ℂ)) =
      RadialMilnor.cubeRoot (-Complex.I * (r : ℂ)) := by
  by_cases hr0 : r = 0
  · simp [hr0, minusThirdRoot, RadialMilnor.cubeRoot, Complex.cpow_def]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    rw [RadialMilnor.cubeRoot, RadialMilnor.cubeRoot,
      Complex.cpow_def_of_ne_zero
        (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hr0)),
      Complex.cpow_def_of_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hr0)),
      log_I_mul_of_pos r hrp, log_neg_I_mul_of_pos r hrp,
      show ((3 : ℂ)⁻¹) = (1 / 3 : ℂ) by norm_num]
    let rightExponent : ℂ :=
      (Complex.log (r : ℂ) - (Real.pi / 2 : ℂ) * Complex.I) * (1 / 3)
    change minusThirdRoot * Complex.exp
      ((Complex.log (r : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) * (1 / 3)) =
        Complex.exp rightExponent
    rw [minusThirdRoot, ← Complex.exp_add]
    congr 1
    dsimp [rightExponent]
    push_cast
    ring

theorem minusThirdRoot_radialMultiplier_I_mul (r : ℝ) (hr : 0 ≤ r) :
    minusThirdRoot * RadialMilnor.radialMultiplier (Complex.I * (r : ℂ)) =
      RadialMilnor.radialMultiplier (-Complex.I * (r : ℂ)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hI : Complex.I * (r : ℂ) ≠ 0 :=
      mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hr0)
    have hnI : -Complex.I * (r : ℂ) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hr0)
    rw [RadialMilnor.radialMultiplier_of_ne hI,
      RadialMilnor.radialMultiplier_of_ne hnI]
    have hcube := minusThirdRoot_cubeRoot_I_mul r hr
    have hnorm :
        ‖RadialMilnor.cubeRoot (-Complex.I * (r : ℂ))‖ =
          ‖RadialMilnor.cubeRoot (Complex.I * (r : ℂ))‖ := by
      rw [← hcube, norm_mul, norm_minusThirdRoot, one_mul]
    have hinputNorm : ‖-Complex.I * (r : ℂ)‖ = ‖Complex.I * (r : ℂ)‖ := by
      simp
    rw [hinputNorm, hnorm, ← hcube]
    ring

theorem minusThirdRoot_sq :
    minusThirdRoot ^ 2 = CoreEdges.wGenerator ^ 2 := by
  rw [minusThirdRoot, CoreEdges.wGenerator,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [show ((2 : ℕ) : ℂ) * -(((Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [show ((2 : ℕ) : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
      (((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [show (((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) +
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
    push_cast
    ring, Complex.exp_add]
  have htwoPi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    have harg : (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_two_pi_mul_I]
  rw [htwoPi, mul_one]

def wIndex (k : Fin 6) : Fin 3 :=
  ⟨(k : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

def nextCycle (k : Fin 6) : Fin 6 :=
  ⟨((k : ℕ) + 1) % 6, Nat.mod_lt _ (by norm_num)⟩

@[simp] theorem nextCycle_zero : nextCycle 0 = 1 := by
  apply Fin.ext
  norm_num [nextCycle]

@[simp] theorem nextCycle_one : nextCycle 1 = 2 := by
  apply Fin.ext
  norm_num [nextCycle]

@[simp] theorem nextCycle_two : nextCycle 2 = 3 := by
  apply Fin.ext
  norm_num [nextCycle]

@[simp] theorem nextCycle_three : nextCycle 3 = 4 := by
  apply Fin.ext
  norm_num [nextCycle]

@[simp] theorem nextCycle_four : nextCycle 4 = 5 := by
  apply Fin.ext
  norm_num [nextCycle]

@[simp] theorem nextCycle_five : nextCycle 5 = 0 := by
  apply Fin.ext
  norm_num [nextCycle]

theorem nextCycle_sign (k : Fin 6) :
    (-1 : ℂ) ^ (nextCycle k : ℕ) = -((-1 : ℂ) ^ (k : ℕ)) := by
  fin_cases k <;> norm_num [nextCycle]

theorem wRoot_nextCycle_mul_minusThirdRoot_sq (k : Fin 6) :
    CoreEdges.wRoot (wIndex (nextCycle k)) * minusThirdRoot ^ 2 =
      CoreEdges.wRoot (wIndex k) := by
  rw [minusThirdRoot_sq]
  fin_cases k
  · norm_num [nextCycle, wIndex, CoreEdges.wRoot]
    calc
      CoreEdges.wGenerator * CoreEdges.wGenerator ^ 2 =
          CoreEdges.wGenerator ^ 3 := by ring
      _ = 1 := CoreEdges.wGenerator_cube
  · norm_num [nextCycle, wIndex, CoreEdges.wRoot]
    calc
      CoreEdges.wGenerator ^ 2 * CoreEdges.wGenerator ^ 2 =
          CoreEdges.wGenerator * CoreEdges.wGenerator ^ 3 := by ring
      _ = CoreEdges.wGenerator := by rw [CoreEdges.wGenerator_cube, mul_one]
  · norm_num [nextCycle, wIndex, CoreEdges.wRoot]
  · norm_num [nextCycle, wIndex, CoreEdges.wRoot]
    calc
      CoreEdges.wGenerator * CoreEdges.wGenerator ^ 2 =
          CoreEdges.wGenerator ^ 3 := by ring
      _ = 1 := CoreEdges.wGenerator_cube
  · norm_num [nextCycle, wIndex, CoreEdges.wRoot]
    calc
      CoreEdges.wGenerator ^ 2 * CoreEdges.wGenerator ^ 2 =
          CoreEdges.wGenerator * CoreEdges.wGenerator ^ 3 := by ring
      _ = CoreEdges.wGenerator := by rw [CoreEdges.wGenerator_cube, mul_one]
  · norm_num [nextCycle, wIndex, CoreEdges.wRoot]

def evenTheta (u : unitInterval) : ℝ := Real.pi * (u : ℝ)

def oddTheta (u : unitInterval) : ℝ := Real.pi * (u : ℝ) + Real.pi

def evenA (s u : unitInterval) : ℂ := ellipseA s (evenTheta u)

def evenB (s u : unitInterval) : ℂ := ellipseB s (evenTheta u)

def oddA (s u : unitInterval) : ℂ := ellipseA s (oddTheta u)

def oddB (s u : unitInterval) : ℂ := ellipseB s (oddTheta u)

theorem sin_evenTheta_nonneg (u : unitInterval) :
    0 ≤ Real.sin (evenTheta u) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact mul_nonneg Real.pi_pos.le u.2.1
  · calc
      Real.pi * (u : ℝ) ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left u.2.2 Real.pi_pos.le
      _ = Real.pi := mul_one _

theorem sin_oddTheta_nonpos (u : unitInterval) :
    Real.sin (oddTheta u) ≤ 0 := by
  rw [oddTheta, Real.sin_add_pi]
  exact neg_nonpos.mpr (sin_evenTheta_nonneg u)

@[simp] theorem evenA_one (s : unitInterval) :
    evenA s 1 = (((s : ℝ) - 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [evenA, evenTheta, ellipseARe]
    ring
  · simp [evenA, evenTheta, ellipseAIm]

@[simp] theorem evenB_one (s : unitInterval) :
    evenB s 1 = (((s : ℝ) + 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [evenB, evenTheta, ellipseBRe]
  · simp [evenB, evenTheta, ellipseBIm]

@[simp] theorem oddA_zero (s : unitInterval) :
    oddA s 0 = (((s : ℝ) - 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [oddA, oddTheta, ellipseARe]
    ring
  · simp [oddA, oddTheta, ellipseAIm]

@[simp] theorem oddB_zero (s : unitInterval) :
    oddB s 0 = (((s : ℝ) + 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [oddB, oddTheta, ellipseBRe]
  · simp [oddB, oddTheta, ellipseBIm]

@[simp] theorem oddA_one (s : unitInterval) :
    oddA s 1 = (((s : ℝ) + 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [oddA, oddTheta, ellipseARe]
  · simp [oddA, oddTheta, ellipseAIm]

@[simp] theorem oddB_one (s : unitInterval) :
    oddB s 1 = (((s : ℝ) - 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [oddB, oddTheta, ellipseBRe]
  · simp [oddB, oddTheta, ellipseBIm]

@[simp] theorem evenA_zero (s : unitInterval) :
    evenA s 0 = (((s : ℝ) + 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [evenA, evenTheta, ellipseARe]
  · simp [evenA, evenTheta, ellipseAIm]

@[simp] theorem evenB_zero (s : unitInterval) :
    evenB s 0 = (((s : ℝ) - 1) / 2 : ℝ) := by
  apply Complex.ext
  · simp [evenB, evenTheta, ellipseBRe]
  · simp [evenB, evenTheta, ellipseBIm]

theorem evenA_im_nonneg (s u : unitInterval) : 0 ≤ (evenA s u).im := by
  have h : 0 ≤ Real.sqrt (1 - (s : ℝ) ^ 2) * Real.sin (evenTheta u) / 2 :=
    div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (sin_evenTheta_nonneg u)) (by norm_num)
  simpa [evenA, ellipseAIm] using h

theorem evenB_im_nonpos (s u : unitInterval) : (evenB s u).im ≤ 0 := by
  have h : -(Real.sqrt (1 - (s : ℝ) ^ 2) * Real.sin (evenTheta u) / 2) ≤ 0 :=
    neg_nonpos.mpr
    (div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (sin_evenTheta_nonneg u)) (by norm_num))
  simpa [evenB, ellipseBIm] using h

theorem oddA_im_nonpos (s u : unitInterval) : (oddA s u).im ≤ 0 := by
  have hmul : Real.sqrt (1 - (s : ℝ) ^ 2) *
      Real.sin (oddTheta u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
      (sin_oddTheta_nonpos u)
  have h : Real.sqrt (1 - (s : ℝ) ^ 2) * Real.sin (oddTheta u) / 2 ≤ 0 := by
    nlinarith
  simpa [oddA, ellipseAIm] using h

theorem oddB_im_nonneg (s u : unitInterval) : 0 ≤ (oddB s u).im := by
  have hmul : Real.sqrt (1 - (s : ℝ) ^ 2) *
      Real.sin (oddTheta u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
      (sin_oddTheta_nonpos u)
  have h : 0 ≤ -(Real.sqrt (1 - (s : ℝ) ^ 2) * Real.sin (oddTheta u) / 2) := by
    nlinarith
  simpa [oddB, ellipseBIm] using h

def evenZ (k : Fin 6) (s u : unitInterval) : ℂ :=
  (-1 : ℂ) ^ (k : ℕ) *
    squareMultiplier (-Complex.I * evenA s u)

def oddZ (k : Fin 6) (s u : unitInterval) : ℂ :=
  ((-1 : ℂ) ^ ((k : ℕ) + 1) * (-Complex.I)) *
    squareMultiplier (Complex.I * oddA s u)

def evenW (k : Fin 6) (s u : unitInterval) : ℂ :=
  (CoreEdges.wRoot (wIndex k) * minusThirdRoot) *
    RadialMilnor.radialMultiplier (Complex.I * evenB s u)

def oddW (k : Fin 6) (s u : unitInterval) : ℂ :=
  CoreEdges.wRoot (wIndex k) *
    RadialMilnor.radialMultiplier (-Complex.I * oddB s u)

theorem evenZ_one_eq_oddZ_zero (k : Fin 6) (s : unitInterval) :
    evenZ k s 1 = oddZ k s 0 := by
  let r : ℝ := (1 - (s : ℝ)) / 2
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith [s.2.2]
  have hevenArg : -Complex.I * evenA s 1 = Complex.I * (r : ℂ) := by
    rw [evenA_one]
    apply Complex.ext
    · simp [r, Complex.mul_re]
    · simp [r, Complex.mul_im]
      ring
  have hoddArg : Complex.I * oddA s 0 = -Complex.I * (r : ℂ) := by
    rw [oddA_zero]
    apply Complex.ext
    · simp [r, Complex.mul_re]
    · simp [r, Complex.mul_im]
      ring
  rw [evenZ, oddZ, hevenArg, hoddArg, squareMultiplier_I_mul r hr, pow_succ]
  ring

theorem evenW_one_eq_oddW_zero (k : Fin 6) (s : unitInterval) :
    evenW k s 1 = oddW k s 0 := by
  let r : ℝ := ((s : ℝ) + 1) / 2
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith [s.2.1]
  have hevenArg : Complex.I * evenB s 1 = Complex.I * (r : ℂ) := by
    rw [evenB_one]
  have hoddArg : -Complex.I * oddB s 0 = -Complex.I * (r : ℂ) := by
    rw [oddB_zero]
  rw [evenW, oddW, hevenArg, hoddArg, mul_assoc,
    minusThirdRoot_radialMultiplier_I_mul r hr]

theorem oddZ_one_eq_evenZ_next_zero (k : Fin 6) (s : unitInterval) :
    oddZ k s 1 = evenZ (nextCycle k) s 0 := by
  let r : ℝ := ((s : ℝ) + 1) / 2
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith [s.2.1]
  have hoddArg : Complex.I * oddA s 1 = Complex.I * (r : ℂ) := by
    rw [oddA_one]
  have hevenArg : -Complex.I * evenA s 0 = -Complex.I * (r : ℂ) := by
    rw [evenA_zero]
  rw [oddZ, evenZ, hoddArg, hevenArg, squareMultiplier_I_mul r hr,
    nextCycle_sign, pow_succ]
  have hII : -Complex.I * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    norm_num
  calc
    (-1 : ℂ) ^ (k : ℕ) * -1 * -Complex.I *
          (Complex.I * squareMultiplier (-Complex.I * (r : ℂ))) =
        ((-1 : ℂ) ^ (k : ℕ) * -1) * (-Complex.I * Complex.I) *
          squareMultiplier (-Complex.I * (r : ℂ)) := by ring
    _ = -((-1 : ℂ) ^ (k : ℕ)) *
          squareMultiplier (-Complex.I * (r : ℂ)) := by rw [hII]; ring

theorem oddW_one_eq_evenW_next_zero (k : Fin 6) (s : unitInterval) :
    oddW k s 1 = evenW (nextCycle k) s 0 := by
  let r : ℝ := (1 - (s : ℝ)) / 2
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith [s.2.2]
  have hoddArg : -Complex.I * oddB s 1 = Complex.I * (r : ℂ) := by
    rw [oddB_one]
    apply Complex.ext
    · simp [r, Complex.mul_re]
    · simp [r, Complex.mul_im]
      ring
  have hevenArg : Complex.I * evenB (s := s) 0 = -Complex.I * (r : ℂ) := by
    rw [evenB_zero]
    apply Complex.ext
    · simp [r, Complex.mul_re]
    · simp [r, Complex.mul_im]
      ring
  rw [oddW, evenW, hoddArg, hevenArg]
  rw [← minusThirdRoot_radialMultiplier_I_mul r hr]
  calc
    CoreEdges.wRoot (wIndex k) *
          RadialMilnor.radialMultiplier (Complex.I * (r : ℂ)) =
        (CoreEdges.wRoot (wIndex (nextCycle k)) * minusThirdRoot ^ 2) *
          RadialMilnor.radialMultiplier (Complex.I * (r : ℂ)) := by
            rw [wRoot_nextCycle_mul_minusThirdRoot_sq]
    _ = CoreEdges.wRoot (wIndex (nextCycle k)) * minusThirdRoot * minusThirdRoot *
          RadialMilnor.radialMultiplier (Complex.I * (r : ℂ)) := by
            simp only [pow_two, mul_assoc]
    _ = (CoreEdges.wRoot (wIndex (nextCycle k)) * minusThirdRoot) *
          (minusThirdRoot *
            RadialMilnor.radialMultiplier (Complex.I * (r : ℂ))) := by
            exact mul_assoc _ _ _

@[simp] theorem radialCube_radialMultiplier (z : ℂ) :
    RadialMilnor.radialCube (RadialMilnor.radialMultiplier z) = z := by
  have h := RadialMilnor.radialCube_mul_radialMultiplier z 1
  rw [show RadialMilnor.radialCube (1 : ℂ) = 1 by
    norm_num [RadialMilnor.radialCube]] at h
  simpa using h

theorem evenZ_sq (k : Fin 6) (s u : unitInterval) :
    evenZ k s u ^ 2 = -Complex.I * evenA s u := by
  rw [evenZ, mul_pow, squareMultiplier_sq]
  have hsign : ((-1 : ℂ) ^ (k : ℕ)) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

theorem oddZ_sq (k : Fin 6) (s u : unitInterval) :
    oddZ k s u ^ 2 = -Complex.I * oddA s u := by
  rw [oddZ, mul_pow, squareMultiplier_sq]
  have hsign :
      (((-1 : ℂ) ^ ((k : ℕ) + 1) * (-Complex.I)) ^ 2) = -1 := by
    rw [mul_pow]
    have hpow : (((-1 : ℂ) ^ ((k : ℕ) + 1)) ^ 2) = 1 := by
      rw [← pow_mul]
      simp
    rw [hpow, one_mul]
    norm_num [pow_two]
  rw [hsign]
  ring

theorem evenW_radialCube (k : Fin 6) (s u : unitInterval) :
    RadialMilnor.radialCube (evenW k s u) =
      -Complex.I * evenB s u := by
  rw [evenW, radialCube_mul_of_norm_one]
  · rw [mul_pow, CoreEdges.wRoot_cube, minusThirdRoot_cube,
      one_mul, radialCube_radialMultiplier]
    ring
  · rw [norm_mul, CoreEdges.norm_wRoot, norm_minusThirdRoot, one_mul]

theorem oddW_radialCube (k : Fin 6) (s u : unitInterval) :
    RadialMilnor.radialCube (oddW k s u) =
      -Complex.I * oddB s u := by
  rw [oddW, radialCube_mul_of_norm_one]
  · rw [CoreEdges.wRoot_cube, one_mul, radialCube_radialMultiplier]
  · exact CoreEdges.norm_wRoot (wIndex k)

theorem normSq_of_sq_eq (z a : ℂ) (h : z ^ 2 = a) : normSq z = ‖a‖ := by
  rw [normSq_eq_norm_sq]
  calc
    ‖z‖ ^ 2 = ‖z ^ 2‖ := (norm_pow z 2).symm
    _ = ‖a‖ := congrArg norm h

theorem normSq_of_radialCube_eq (w a : ℂ)
    (h : RadialMilnor.radialCube w = a) : normSq w = ‖a‖ := by
  rw [normSq_eq_norm_sq]
  rw [← RadialMilnor.norm_radialCube, h]

theorem normSq_evenZ (k : Fin 6) (s u : unitInterval) :
    normSq (evenZ k s u) = ‖evenA s u‖ := by
  rw [normSq_of_sq_eq _ _ (evenZ_sq k s u), norm_mul, norm_neg,
    norm_I, one_mul]

theorem normSq_oddZ (k : Fin 6) (s u : unitInterval) :
    normSq (oddZ k s u) = ‖oddA s u‖ := by
  rw [normSq_of_sq_eq _ _ (oddZ_sq k s u), norm_mul, norm_neg,
    norm_I, one_mul]

theorem normSq_evenW (k : Fin 6) (s u : unitInterval) :
    normSq (evenW k s u) = ‖evenB s u‖ := by
  rw [normSq_of_radialCube_eq _ _ (evenW_radialCube k s u),
    norm_mul, norm_neg, norm_I, one_mul]

theorem normSq_oddW (k : Fin 6) (s u : unitInterval) :
    normSq (oddW k s u) = ‖oddB s u‖ := by
  rw [normSq_of_radialCube_eq _ _ (oddW_radialCube k s u),
    norm_mul, norm_neg, norm_I, one_mul]

def evenBalancedSphere (k : Fin 6) (s u : unitInterval) : Milnor.CSphere :=
  ⟨(evenZ k s u, evenW k s u), by
    rw [normSq_evenZ, normSq_evenW]
    exact norm_ellipse_add s.2.1 s.2.2⟩

def oddBalancedSphere (k : Fin 6) (s u : unitInterval) : Milnor.CSphere :=
  ⟨(oddZ k s u, oddW k s u), by
    rw [normSq_oddZ, normSq_oddW]
    exact norm_ellipse_add s.2.1 s.2.2⟩

theorem evenBalancedSphere_one_eq_oddBalancedSphere_zero
    (k : Fin 6) (s : unitInterval) :
    evenBalancedSphere k s 1 = oddBalancedSphere k s 0 := by
  apply Subtype.ext
  apply Prod.ext
  · exact evenZ_one_eq_oddZ_zero k s
  · exact evenW_one_eq_oddW_zero k s

theorem oddBalancedSphere_one_eq_evenBalancedSphere_next_zero
    (k : Fin 6) (s : unitInterval) :
    oddBalancedSphere k s 1 = evenBalancedSphere (nextCycle k) s 0 := by
  apply Subtype.ext
  apply Prod.ext
  · exact oddZ_one_eq_evenZ_next_zero k s
  · exact oddW_one_eq_evenW_next_zero k s

theorem balancedPolynomial_even (k : Fin 6) (s u : unitInterval) :
    balancedPolynomial (evenBalancedSphere k s u) = (s : ℂ) := by
  unfold balancedPolynomial
  change Complex.I *
      (evenZ k s u ^ 2 + RadialMilnor.radialCube (evenW k s u)) = (s : ℂ)
  rw [evenZ_sq, evenW_radialCube]
  rw [show Complex.I *
      (-Complex.I * evenA s u + -Complex.I * evenB s u) =
        evenA s u + evenB s u by
      calc
        Complex.I * (-Complex.I * evenA s u + -Complex.I * evenB s u) =
            -(Complex.I * Complex.I) * (evenA s u + evenB s u) := by ring
        _ = evenA s u + evenB s u := by rw [Complex.I_mul_I]; ring]
  exact ellipse_add s (evenTheta u)

theorem balancedPolynomial_odd (k : Fin 6) (s u : unitInterval) :
    balancedPolynomial (oddBalancedSphere k s u) = (s : ℂ) := by
  unfold balancedPolynomial
  change Complex.I *
      (oddZ k s u ^ 2 + RadialMilnor.radialCube (oddW k s u)) = (s : ℂ)
  rw [oddZ_sq, oddW_radialCube]
  rw [show Complex.I *
      (-Complex.I * oddA s u + -Complex.I * oddB s u) =
        oddA s u + oddB s u by
      calc
        Complex.I * (-Complex.I * oddA s u + -Complex.I * oddB s u) =
            -(Complex.I * Complex.I) * (oddA s u + oddB s u) := by ring
        _ = oddA s u + oddB s u := by rw [Complex.I_mul_I]; ring]
  exact ellipse_add s (oddTheta u)

theorem evenA_continuous :
    Continuous (fun x : unitInterval × unitInterval => evenA x.1 x.2) := by
  unfold evenA ellipseA ellipseARe ellipseAIm evenTheta
  fun_prop

theorem evenB_continuous :
    Continuous (fun x : unitInterval × unitInterval => evenB x.1 x.2) := by
  unfold evenB ellipseB ellipseBRe ellipseBIm evenTheta
  fun_prop

theorem oddA_continuous :
    Continuous (fun x : unitInterval × unitInterval => oddA x.1 x.2) := by
  unfold oddA ellipseA ellipseARe ellipseAIm oddTheta
  fun_prop

theorem oddB_continuous :
    Continuous (fun x : unitInterval × unitInterval => oddB x.1 x.2) := by
  unfold oddB ellipseB ellipseBRe ellipseBIm oddTheta
  fun_prop

theorem evenZ_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => evenZ k x.1 x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, u⟩
  have harg : ContinuousAt
      (fun x : unitInterval × unitInterval => -Complex.I * evenA x.1 x.2)
      (s, u) := continuousAt_const.mul evenA_continuous.continuousAt
  have hre : 0 ≤ (-Complex.I * evenA s u).re := by
    simpa [Complex.mul_re] using evenA_im_nonneg s u
  have hroot : ContinuousAt
      (fun x : unitInterval × unitInterval =>
        squareMultiplier (-Complex.I * evenA x.1 x.2)) (s, u) := by
    change Filter.Tendsto
      (fun x : unitInterval × unitInterval =>
        squareMultiplier (-Complex.I * evenA x.1 x.2))
      (nhds (s, u)) (nhds (squareMultiplier (-Complex.I * evenA s u)))
    exact Filter.Tendsto.comp
      (squareMultiplier_continuousAt_of_re_nonneg hre) harg
  exact continuousAt_const.mul hroot

theorem oddZ_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => oddZ k x.1 x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, u⟩
  have harg : ContinuousAt
      (fun x : unitInterval × unitInterval => Complex.I * oddA x.1 x.2)
      (s, u) := continuousAt_const.mul oddA_continuous.continuousAt
  have hre : 0 ≤ (Complex.I * oddA s u).re := by
    simpa [Complex.mul_re] using neg_nonneg.mpr (oddA_im_nonpos s u)
  have hroot : ContinuousAt
      (fun x : unitInterval × unitInterval =>
        squareMultiplier (Complex.I * oddA x.1 x.2)) (s, u) := by
    change Filter.Tendsto
      (fun x : unitInterval × unitInterval =>
        squareMultiplier (Complex.I * oddA x.1 x.2))
      (nhds (s, u)) (nhds (squareMultiplier (Complex.I * oddA s u)))
    exact Filter.Tendsto.comp
      (squareMultiplier_continuousAt_of_re_nonneg hre) harg
  exact continuousAt_const.mul hroot

theorem evenW_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => evenW k x.1 x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, u⟩
  have harg : ContinuousAt
      (fun x : unitInterval × unitInterval => Complex.I * evenB x.1 x.2)
      (s, u) := continuousAt_const.mul evenB_continuous.continuousAt
  have hre : 0 ≤ (Complex.I * evenB s u).re := by
    simpa [Complex.mul_re] using neg_nonneg.mpr (evenB_im_nonpos s u)
  have hroot : ContinuousAt
      (fun x : unitInterval × unitInterval =>
        RadialMilnor.radialMultiplier (Complex.I * evenB x.1 x.2)) (s, u) := by
    change Filter.Tendsto
      (fun x : unitInterval × unitInterval =>
        RadialMilnor.radialMultiplier (Complex.I * evenB x.1 x.2))
      (nhds (s, u))
      (nhds (RadialMilnor.radialMultiplier (Complex.I * evenB s u)))
    exact Filter.Tendsto.comp
      (RadialMilnor.radialMultiplier_continuousAt_of_re_nonneg hre) harg
  exact continuousAt_const.mul hroot

theorem oddW_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => oddW k x.1 x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, u⟩
  have harg : ContinuousAt
      (fun x : unitInterval × unitInterval => -Complex.I * oddB x.1 x.2)
      (s, u) := continuousAt_const.mul oddB_continuous.continuousAt
  have hre : 0 ≤ (-Complex.I * oddB s u).re := by
    simpa [Complex.mul_re] using oddB_im_nonneg s u
  have hroot : ContinuousAt
      (fun x : unitInterval × unitInterval =>
        RadialMilnor.radialMultiplier (-Complex.I * oddB x.1 x.2)) (s, u) := by
    change Filter.Tendsto
      (fun x : unitInterval × unitInterval =>
        RadialMilnor.radialMultiplier (-Complex.I * oddB x.1 x.2))
      (nhds (s, u))
      (nhds (RadialMilnor.radialMultiplier (-Complex.I * oddB s u)))
    exact Filter.Tendsto.comp
      (RadialMilnor.radialMultiplier_continuousAt_of_re_nonneg hre) harg
  exact continuousAt_const.mul hroot

theorem evenBalancedSphere_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval =>
      evenBalancedSphere k x.1 x.2) := by
  apply Continuous.subtype_mk
  exact (evenZ_continuous k).prodMk (evenW_continuous k)

theorem oddBalancedSphere_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval =>
      oddBalancedSphere k x.1 x.2) := by
  apply Continuous.subtype_mk
  exact (oddZ_continuous k).prodMk (oddW_continuous k)

def evenSphere (k : Fin 6) (s u : unitInterval) : Milnor.CSphere :=
  unbalanceSphere (evenBalancedSphere k s u)

def oddSphere (k : Fin 6) (s u : unitInterval) : Milnor.CSphere :=
  unbalanceSphere (oddBalancedSphere k s u)

theorem evenSphere_one_eq_oddSphere_zero (k : Fin 6) (s : unitInterval) :
    evenSphere k s 1 = oddSphere k s 0 := by
  rw [evenSphere, oddSphere, evenBalancedSphere_one_eq_oddBalancedSphere_zero]

theorem oddSphere_one_eq_evenSphere_next_zero (k : Fin 6) (s : unitInterval) :
    oddSphere k s 1 = evenSphere (nextCycle k) s 0 := by
  rw [oddSphere, evenSphere,
    oddBalancedSphere_one_eq_evenBalancedSphere_next_zero]

theorem evenSphere_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => evenSphere k x.1 x.2) :=
  unbalanceSphere_continuous.comp (evenBalancedSphere_continuous k)

theorem oddSphere_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => oddSphere k x.1 x.2) :=
  unbalanceSphere_continuous.comp (oddBalancedSphere_continuous k)

theorem polynomial_evenSphere (k : Fin 6) (s u : unitInterval) :
    RadialMilnor.polynomial (evenSphere k s u) =
      ((unbalanceFactor (evenBalancedSphere k s u) ^ 2 * (s : ℝ) : ℝ) : ℂ) := by
  rw [evenSphere, polynomial_unbalanceSphere, balancedPolynomial_even]
  push_cast
  ring

theorem polynomial_oddSphere (k : Fin 6) (s u : unitInterval) :
    RadialMilnor.polynomial (oddSphere k s u) =
      ((unbalanceFactor (oddBalancedSphere k s u) ^ 2 * (s : ℝ) : ℝ) : ℂ) := by
  rw [oddSphere, polynomial_unbalanceSphere, balancedPolynomial_odd]
  push_cast
  ring

def positiveLevel (r : unitInterval) : unitInterval :=
  ⟨(1 + (r : ℝ)) / 2, by
    constructor
    · nlinarith [r.2.1]
    · nlinarith [r.2.2]⟩

theorem positiveLevel_pos (r : unitInterval) : 0 < (positiveLevel r : ℝ) := by
  dsimp [positiveLevel]
  nlinarith [r.2.1]

def halfLevel : unitInterval := ⟨1 / 2, by norm_num⟩

@[simp] theorem positiveLevel_zero : positiveLevel 0 = halfLevel := by
  apply Subtype.ext
  norm_num [positiveLevel, halfLevel]

@[simp] theorem positiveLevel_one : positiveLevel 1 = 1 := by
  apply Subtype.ext
  norm_num [positiveLevel]

def evenFiber (k : Fin 6) (r u : unitInterval) : RadialMilnor.Fiber :=
  ⟨evenSphere k (positiveLevel r) u, by
    rw [polynomial_evenSphere]
    constructor
    · change 0 < unbalanceFactor (evenBalancedSphere k (positiveLevel r) u) ^ 2 *
          (positiveLevel r : ℝ)
      exact mul_pos (sq_pos_of_pos (unbalanceFactor_pos _)) (positiveLevel_pos r)
    · norm_num [pow_two, Complex.mul_im]⟩

def oddFiber (k : Fin 6) (r u : unitInterval) : RadialMilnor.Fiber :=
  ⟨oddSphere k (positiveLevel r) u, by
    rw [polynomial_oddSphere]
    constructor
    · change 0 < unbalanceFactor (oddBalancedSphere k (positiveLevel r) u) ^ 2 *
          (positiveLevel r : ℝ)
      exact mul_pos (sq_pos_of_pos (unbalanceFactor_pos _)) (positiveLevel_pos r)
    · norm_num [pow_two, Complex.mul_im]⟩

theorem evenFiber_one_eq_oddFiber_zero (k : Fin 6) (r : unitInterval) :
    evenFiber k r 1 = oddFiber k r 0 := by
  apply Subtype.ext
  exact evenSphere_one_eq_oddSphere_zero k (positiveLevel r)

theorem oddFiber_one_eq_evenFiber_next_zero (k : Fin 6) (r : unitInterval) :
    oddFiber k r 1 = evenFiber (nextCycle k) r 0 := by
  apply Subtype.ext
  exact oddSphere_one_eq_evenSphere_next_zero k (positiveLevel r)

theorem positiveLevel_continuous : Continuous positiveLevel := by
  apply Continuous.subtype_mk
  exact (continuous_const.add continuous_subtype_val).div_const 2

theorem evenFiber_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => evenFiber k x.1 x.2) := by
  apply Continuous.subtype_mk
  have hpair : Continuous (fun x : unitInterval × unitInterval =>
      (positiveLevel x.1, x.2)) :=
    (positiveLevel_continuous.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using (evenSphere_continuous k).comp hpair

theorem oddFiber_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval => oddFiber k x.1 x.2) := by
  apply Continuous.subtype_mk
  have hpair : Continuous (fun x : unitInterval × unitInterval =>
      (positiveLevel x.1, x.2)) :=
    (positiveLevel_continuous.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using (oddSphere_continuous k).comp hpair

def evenBase (k : Fin 6) (r : unitInterval) : RadialMilnor.Fiber :=
  evenFiber k r 0

def oddBase (k : Fin 6) (r : unitInterval) : RadialMilnor.Fiber :=
  oddFiber k r 0

theorem evenFiber_fixed_continuous (k : Fin 6) (r : unitInterval) :
    Continuous (evenFiber k r) := by
  have hpair : Continuous (fun u : unitInterval => (r, u)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using (evenFiber_continuous k).comp hpair

theorem oddFiber_fixed_continuous (k : Fin 6) (r : unitInterval) :
    Continuous (oddFiber k r) := by
  have hpair : Continuous (fun u : unitInterval => (r, u)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using (oddFiber_continuous k).comp hpair

def evenPath (k : Fin 6) (r : unitInterval) :
    Path (evenBase k r) (oddBase k r) where
  toFun := evenFiber k r
  continuous_toFun := evenFiber_fixed_continuous k r
  source' := by rfl
  target' := by
    change evenFiber k r 1 = oddFiber k r 0
    exact evenFiber_one_eq_oddFiber_zero k r

def oddPath (k : Fin 6) (r : unitInterval) :
    Path (oddBase k r) (evenBase (nextCycle k) r) where
  toFun := oddFiber k r
  continuous_toFun := oddFiber_fixed_continuous k r
  source' := by rfl
  target' := by
    change oddFiber k r 1 = evenFiber (nextCycle k) r 0
    exact oddFiber_one_eq_evenFiber_next_zero k r

def pairPath (k : Fin 6) (r : unitInterval) :
    Path (evenBase k r) (evenBase (nextCycle k) r) :=
  (evenPath k r).trans ((oddPath k r).cast rfl rfl)

def pairPathZero (r : unitInterval) :
    Path (evenBase 0 r) (evenBase 1 r) :=
  (pairPath 0 r).cast rfl (by rw [nextCycle_zero])

def pairPathOne (r : unitInterval) :
    Path (evenBase 1 r) (evenBase 2 r) :=
  (pairPath 1 r).cast rfl (by rw [nextCycle_one])

def pairPathTwo (r : unitInterval) :
    Path (evenBase 2 r) (evenBase 3 r) :=
  (pairPath 2 r).cast rfl (by rw [nextCycle_two])

def pairPathThree (r : unitInterval) :
    Path (evenBase 3 r) (evenBase 4 r) :=
  (pairPath 3 r).cast rfl (by rw [nextCycle_three])

def pairPathFour (r : unitInterval) :
    Path (evenBase 4 r) (evenBase 5 r) :=
  (pairPath 4 r).cast rfl (by rw [nextCycle_four])

def pairPathFive (r : unitInterval) :
    Path (evenBase 5 r) (evenBase 0 r) :=
  (pairPath 5 r).cast rfl (by rw [nextCycle_five])

def boundaryPath (r : unitInterval) :
    Path (evenBase 0 r) (evenBase 0 r) :=
  (pairPathZero r).trans
    ((pairPathOne r).trans
      ((pairPathTwo r).trans
        ((pairPathThree r).trans
          ((pairPathFour r).trans (pairPathFive r)))))

theorem zTerm_evenSphere (k : Fin 6) (s u : unitInterval) :
    RadialSpine.zTerm (evenSphere k s u).1.1 =
      ((unbalanceFactor (evenBalancedSphere k s u) : ℝ) : ℂ) ^ 2 *
        evenA s u := by
  rw [evenSphere, unbalanceSphere, RadialSpine.zTerm]
  change Complex.I *
      (16 * ((((unbalanceFactor (evenBalancedSphere k s u) / 4 : ℝ) : ℂ) *
        evenZ k s u) ^ 2)) = _
  rw [mul_pow, evenZ_sq]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem wTerm_evenSphere (k : Fin 6) (s u : unitInterval) :
    RadialSpine.wTerm (evenSphere k s u).1.2 =
      ((unbalanceFactor (evenBalancedSphere k s u) : ℝ) : ℂ) ^ 2 *
        evenB s u := by
  rw [evenSphere, unbalanceSphere, RadialSpine.wTerm,
    radialCube_unbalanceW]
  change Complex.I * (9 *
      (((unbalanceFactor (evenBalancedSphere k s u) / 3 : ℝ) : ℂ) ^ 2 *
        RadialMilnor.radialCube (evenW k s u))) = _
  rw [evenW_radialCube]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zTerm_oddSphere (k : Fin 6) (s u : unitInterval) :
    RadialSpine.zTerm (oddSphere k s u).1.1 =
      ((unbalanceFactor (oddBalancedSphere k s u) : ℝ) : ℂ) ^ 2 *
        oddA s u := by
  rw [oddSphere, unbalanceSphere, RadialSpine.zTerm]
  change Complex.I *
      (16 * ((((unbalanceFactor (oddBalancedSphere k s u) / 4 : ℝ) : ℂ) *
        oddZ k s u) ^ 2)) = _
  rw [mul_pow, oddZ_sq]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem wTerm_oddSphere (k : Fin 6) (s u : unitInterval) :
    RadialSpine.wTerm (oddSphere k s u).1.2 =
      ((unbalanceFactor (oddBalancedSphere k s u) : ℝ) : ℂ) ^ 2 *
        oddB s u := by
  rw [oddSphere, unbalanceSphere, RadialSpine.wTerm,
    radialCube_unbalanceW]
  change Complex.I * (9 *
      (((unbalanceFactor (oddBalancedSphere k s u) / 3 : ℝ) : ℂ) ^ 2 *
        RadialMilnor.radialCube (oddW k s u))) = _
  rw [oddW_radialCube]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem evenA_one_im (u : unitInterval) : (evenA 1 u).im = 0 := by
  simp [evenA, ellipseAIm]

theorem evenB_one_im (u : unitInterval) : (evenB 1 u).im = 0 := by
  simp [evenB, ellipseBIm]

theorem oddA_one_im (u : unitInterval) : (oddA 1 u).im = 0 := by
  simp [oddA, ellipseAIm]

theorem oddB_one_im (u : unitInterval) : (oddB 1 u).im = 0 := by
  simp [oddB, ellipseBIm]

theorem evenA_one_re_nonneg (u : unitInterval) : 0 ≤ (evenA 1 u).re := by
  rw [evenA, ellipseA_re]
  unfold ellipseARe
  norm_num
  nlinarith [Real.neg_one_le_cos (evenTheta u)]

theorem evenB_one_re_nonneg (u : unitInterval) : 0 ≤ (evenB 1 u).re := by
  rw [evenB, ellipseB_re]
  unfold ellipseBRe
  norm_num
  nlinarith [Real.cos_le_one (evenTheta u)]

theorem oddA_one_re_nonneg (u : unitInterval) : 0 ≤ (oddA 1 u).re := by
  rw [oddA, ellipseA_re]
  unfold ellipseARe
  norm_num
  nlinarith [Real.neg_one_le_cos (oddTheta u)]

theorem oddB_one_re_nonneg (u : unitInterval) : 0 ≤ (oddB 1 u).re := by
  rw [oddB, ellipseB_re]
  unfold ellipseBRe
  norm_num
  nlinarith [Real.cos_le_one (oddTheta u)]

theorem zTerm_evenSphere_one_im (k : Fin 6) (u : unitInterval) :
    (RadialSpine.zTerm (evenSphere k 1 u).1.1).im = 0 := by
  rw [zTerm_evenSphere]
  simp [Complex.mul_im, pow_two, evenA_one_im]

theorem wTerm_evenSphere_one_im (k : Fin 6) (u : unitInterval) :
    (RadialSpine.wTerm (evenSphere k 1 u).1.2).im = 0 := by
  rw [wTerm_evenSphere]
  simp [Complex.mul_im, pow_two, evenB_one_im]

theorem zTerm_oddSphere_one_im (k : Fin 6) (u : unitInterval) :
    (RadialSpine.zTerm (oddSphere k 1 u).1.1).im = 0 := by
  rw [zTerm_oddSphere]
  simp [Complex.mul_im, pow_two, oddA_one_im]

theorem wTerm_oddSphere_one_im (k : Fin 6) (u : unitInterval) :
    (RadialSpine.wTerm (oddSphere k 1 u).1.2).im = 0 := by
  rw [wTerm_oddSphere]
  simp [Complex.mul_im, pow_two, oddB_one_im]

theorem zTerm_evenSphere_one_re_nonneg (k : Fin 6) (u : unitInterval) :
    0 ≤ (RadialSpine.zTerm (evenSphere k 1 u).1.1).re := by
  rw [zTerm_evenSphere]
  simpa [Complex.mul_re, pow_two, evenA_one_im] using
    mul_nonneg (sq_nonneg (unbalanceFactor (evenBalancedSphere k 1 u)))
      (evenA_one_re_nonneg u)

theorem wTerm_evenSphere_one_re_nonneg (k : Fin 6) (u : unitInterval) :
    0 ≤ (RadialSpine.wTerm (evenSphere k 1 u).1.2).re := by
  rw [wTerm_evenSphere]
  simpa [Complex.mul_re, pow_two, evenB_one_im] using
    mul_nonneg (sq_nonneg (unbalanceFactor (evenBalancedSphere k 1 u)))
      (evenB_one_re_nonneg u)

theorem zTerm_oddSphere_one_re_nonneg (k : Fin 6) (u : unitInterval) :
    0 ≤ (RadialSpine.zTerm (oddSphere k 1 u).1.1).re := by
  rw [zTerm_oddSphere]
  simpa [Complex.mul_re, pow_two, oddA_one_im] using
    mul_nonneg (sq_nonneg (unbalanceFactor (oddBalancedSphere k 1 u)))
      (oddA_one_re_nonneg u)

theorem wTerm_oddSphere_one_re_nonneg (k : Fin 6) (u : unitInterval) :
    0 ≤ (RadialSpine.wTerm (oddSphere k 1 u).1.2).re := by
  rw [wTerm_oddSphere]
  simpa [Complex.mul_re, pow_two, oddB_one_im] using
    mul_nonneg (sq_nonneg (unbalanceFactor (oddBalancedSphere k 1 u)))
      (oddB_one_re_nonneg u)

def evenCore (k : Fin 6) (u : unitInterval) : RadialCore.Core :=
  ⟨⟨evenFiber k 1 u, by
      change (RadialSpine.zTerm (evenSphere k (positiveLevel 1) u).1.1).im = 0 ∧
        (RadialSpine.wTerm (evenSphere k (positiveLevel 1) u).1.2).im = 0
      rw [positiveLevel_one]
      exact ⟨zTerm_evenSphere_one_im k u, wTerm_evenSphere_one_im k u⟩⟩, by
    change 0 ≤ (RadialSpine.zTerm (evenSphere k (positiveLevel 1) u).1.1).re ∧
      0 ≤ (RadialSpine.wTerm (evenSphere k (positiveLevel 1) u).1.2).re
    rw [positiveLevel_one]
    exact ⟨zTerm_evenSphere_one_re_nonneg k u,
      wTerm_evenSphere_one_re_nonneg k u⟩⟩

def oddCore (k : Fin 6) (u : unitInterval) : RadialCore.Core :=
  ⟨⟨oddFiber k 1 u, by
      change (RadialSpine.zTerm (oddSphere k (positiveLevel 1) u).1.1).im = 0 ∧
        (RadialSpine.wTerm (oddSphere k (positiveLevel 1) u).1.2).im = 0
      rw [positiveLevel_one]
      exact ⟨zTerm_oddSphere_one_im k u, wTerm_oddSphere_one_im k u⟩⟩, by
    change 0 ≤ (RadialSpine.zTerm (oddSphere k (positiveLevel 1) u).1.1).re ∧
      0 ≤ (RadialSpine.wTerm (oddSphere k (positiveLevel 1) u).1.2).re
    rw [positiveLevel_one]
    exact ⟨zTerm_oddSphere_one_re_nonneg k u,
      wTerm_oddSphere_one_re_nonneg k u⟩⟩

theorem fiberToCore_evenFiber_one (k : Fin 6) (u : unitInterval) :
    FiberAction.fiberToCore (evenFiber k 1 u) = evenCore k u := by
  have hfiber : FiberAction.coreToFiber (evenCore k u) = evenFiber k 1 u := rfl
  rw [← hfiber, FiberAction.fiberToCore_coreToFiber]

theorem fiberToCore_oddFiber_one (k : Fin 6) (u : unitInterval) :
    FiberAction.fiberToCore (oddFiber k 1 u) = oddCore k u := by
  have hfiber : FiberAction.coreToFiber (oddCore k u) = oddFiber k 1 u := rfl
  rw [← hfiber, FiberAction.fiberToCore_coreToFiber]

def quarterRotation : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

theorem quarterRotation_re : quarterRotation.re = Real.sqrt 2 / 2 := by
  rw [quarterRotation, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]

theorem quarterRotation_im : quarterRotation.im = Real.sqrt 2 / 2 := by
  rw [quarterRotation, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]

theorem quarterRotation_sq : quarterRotation ^ 2 = Complex.I := by
  rw [quarterRotation, ← Complex.exp_nat_mul]
  have harg :
      ((2 : ℕ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
        (Real.pi / 2 : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_div_two_mul_I]

theorem quarterRotation_mul_squareMultiplier_neg_I
    (r : ℝ) (hr : 0 ≤ r) :
    quarterRotation * squareMultiplier (-Complex.I * (r : ℂ)) =
      (Real.sqrt r : ℂ) := by
  by_cases hr0 : r = 0
  · simp [hr0, squareMultiplier, Complex.cpow_def]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let y := quarterRotation * squareMultiplier (-Complex.I * (r : ℂ))
    have hsq : y ^ 2 = (r : ℂ) := by
      dsimp [y]
      rw [mul_pow, quarterRotation_sq, squareMultiplier_sq]
      rw [← mul_assoc, show Complex.I * -Complex.I = 1 by
        rw [mul_neg, Complex.I_mul_I]
        norm_num, one_mul]
    have hsqrtFormula :
        squareMultiplier (-Complex.I * (r : ℂ)) =
          (Real.sqrt r / Real.sqrt 2 : ℂ) -
            (Real.sqrt r / Real.sqrt 2 : ℂ) * Complex.I := by
      change Complex.sqrt (-Complex.I * (r : ℂ)) = _
      rw [Complex.sqrt_eq_real_add_ite]
      have hnorm : ‖-Complex.I * (r : ℂ)‖ = r := by simp [abs_of_nonneg hr]
      rw [hnorm]
      simp [Complex.mul_re, Complex.mul_im, not_le.mpr hrp]
      ring
    have hyIm : y.im = 0 := by
      dsimp [y]
      rw [hsqrtFormula, Complex.mul_im, quarterRotation_re, quarterRotation_im]
      simp
    have hyRe : 0 ≤ y.re := by
      dsimp [y]
      rw [hsqrtFormula, Complex.mul_re, quarterRotation_re, quarterRotation_im]
      simp
    change y = (Real.sqrt r : ℂ)
    apply Complex.ext
    · change y.re = Real.sqrt r
      have hre := congrArg Complex.re hsq
      simp [pow_two, Complex.mul_re, hyIm] at hre
      have hsqrtSq := Real.sq_sqrt hr
      nlinarith [Real.sqrt_nonneg r]
    · change y.im = 0
      exact hyIm

def sixthRotation : ℂ :=
  Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)

theorem log_ofReal_of_pos (r : ℝ) (hr : 0 < r) :
    Complex.log (r : ℂ) = (Real.log r : ℂ) := by
  apply Complex.ext
  · exact Complex.log_ofReal_re r
  · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hr.le]
    simp

theorem cubeRoot_neg_I_mul_of_pos (r : ℝ) (hr : 0 < r) :
    RadialMilnor.cubeRoot (-Complex.I * (r : ℂ)) =
      (Real.exp (Real.log r / 3) : ℂ) *
        Complex.exp (-(((Real.pi / 6 : ℝ) : ℂ) * Complex.I)) := by
  have hr0 : r ≠ 0 := hr.ne'
  rw [RadialMilnor.cubeRoot,
    Complex.cpow_def_of_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hr0)),
    log_neg_I_mul_of_pos r hr, log_ofReal_of_pos r hr,
    show ((3 : ℂ)⁻¹) = (1 / 3 : ℂ) by norm_num]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_cubeRoot_neg_I_mul_of_pos (r : ℝ) (hr : 0 < r) :
    ‖RadialMilnor.cubeRoot (-Complex.I * (r : ℂ))‖ =
      Real.exp (Real.log r / 3) := by
  rw [cubeRoot_neg_I_mul_of_pos r hr, norm_mul]
  have hphase : -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) =
      (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hphase, Complex.norm_exp_ofReal_mul_I]
  simp
  rw [Complex.norm_exp]
  simp

theorem radialMultiplier_neg_I_mul_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    RadialMilnor.radialMultiplier (-Complex.I * (r : ℂ)) =
      (Real.sqrt r : ℂ) *
        Complex.exp (-(((Real.pi / 6 : ℝ) : ℂ) * Complex.I)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hinput : -Complex.I * (r : ℂ) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hr0)
    rw [RadialMilnor.radialMultiplier_of_ne hinput,
      show ‖-Complex.I * (r : ℂ)‖ = r by simp [abs_of_nonneg hr],
      norm_cubeRoot_neg_I_mul_of_pos r hrp,
      cubeRoot_neg_I_mul_of_pos r hrp]
    have hexp : Real.exp (Real.log r / 3) ≠ 0 := ne_of_gt (Real.exp_pos _)
    push_cast
    field_simp

theorem sixthRotation_mul_radialMultiplier_neg_I
    (r : ℝ) (hr : 0 ≤ r) :
    sixthRotation * RadialMilnor.radialMultiplier (-Complex.I * (r : ℂ)) =
      (Real.sqrt r : ℂ) := by
  rw [radialMultiplier_neg_I_mul_of_nonneg r hr]
  unfold sixthRotation
  have harg :
      (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) +
          -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) = 0 := by ring
  calc
    Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) *
          ((Real.sqrt r : ℂ) *
            Complex.exp (-(((Real.pi / 6 : ℝ) : ℂ) * Complex.I))) =
        (Real.sqrt r : ℂ) *
          (Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-(((Real.pi / 6 : ℝ) : ℂ) * Complex.I))) := by ring
    _ = (Real.sqrt r : ℂ) * Complex.exp
          ((((Real.pi / 6 : ℝ) : ℂ) * Complex.I) +
            -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I)) := by
          rw [Complex.exp_add]
    _ = (Real.sqrt r : ℂ) := by rw [harg]; simp

theorem sixthRotation_mul_minusThirdRoot_mul_radialMultiplier_I
    (r : ℝ) (hr : 0 ≤ r) :
    sixthRotation * minusThirdRoot *
        RadialMilnor.radialMultiplier (Complex.I * (r : ℂ)) =
      (Real.sqrt r : ℂ) := by
  rw [mul_assoc, minusThirdRoot_radialMultiplier_I_mul r hr]
  exact sixthRotation_mul_radialMultiplier_neg_I r hr

def zIndex (k : Fin 6) : Fin 2 :=
  ⟨(k : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem zRoot_zIndex (k : Fin 6) :
    CoreEdges.zRoot (zIndex k) = (-1 : ℂ) ^ (k : ℕ) := by
  fin_cases k <;> norm_num [zIndex, CoreEdges.zRoot]

theorem zRoot_zIndex_next (k : Fin 6) :
    CoreEdges.zRoot (zIndex (nextCycle k)) =
      (-1 : ℂ) ^ ((k : ℕ) + 1) := by
  fin_cases k <;> norm_num [zIndex, nextCycle, CoreEdges.zRoot]

def coreParameter (q : RadialCore.Core) : unitInterval :=
  ⟨normSq q.1.1.1.1.2, normSq_nonneg _, by
    have hsphere := q.1.1.1.2
    nlinarith [normSq_nonneg q.1.1.1.1.1]⟩

theorem one_sub_coreParameter (q : RadialCore.Core) :
    1 - (coreParameter q : ℝ) = normSq q.1.1.1.1.1 := by
  have hsphere := q.1.1.1.2
  dsimp [coreParameter]
  linarith

theorem sqrt_sq_mul (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    Real.sqrt (c ^ 2 * a) = c * Real.sqrt a := by
  have hleft := Real.sq_sqrt (mul_nonneg (sq_nonneg c) ha)
  have haSq := Real.sq_sqrt ha
  have hleftNonneg := Real.sqrt_nonneg (c ^ 2 * a)
  have hrightNonneg := mul_nonneg hc (Real.sqrt_nonneg a)
  nlinarith

theorem evenA_one_eq_ofReal_re (u : unitInterval) :
    evenA 1 u = ((evenA 1 u).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [evenA_one_im]

theorem evenB_one_eq_ofReal_re (u : unitInterval) :
    evenB 1 u = ((evenB 1 u).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [evenB_one_im]

theorem evenCore_z_value (k : Fin 6) (u : unitInterval) :
    (evenCore k u).1.1.1.1.1 =
      (((unbalanceFactor (evenBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
        evenZ k 1 u) := by
  dsimp only [evenCore, evenFiber, evenSphere, unbalanceSphere,
    evenBalancedSphere]
  rw [positiveLevel_one]

theorem evenCore_w_value (k : Fin 6) (u : unitInterval) :
    (evenCore k u).1.1.1.1.2 =
      (((unbalanceFactor (evenBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
        evenW k 1 u) := by
  dsimp only [evenCore, evenFiber, evenSphere, unbalanceSphere,
    evenBalancedSphere]
  rw [positiveLevel_one]

theorem zCoordinate_evenCore_raw (k : Fin 6) (u : unitInterval) :
    RadialCore.zCoordinate (evenCore k u).1.1.1.1.1 =
      ((unbalanceFactor (evenBalancedSphere k 1 u) / 4 *
        Real.sqrt (evenA 1 u).re : ℝ) : ℂ) *
        ((-1 : ℂ) ^ (k : ℕ)) := by
  rw [RadialCore.zCoordinate, evenCore_z_value]
  change quarterRotation *
      (((unbalanceFactor (evenBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
        evenZ k 1 u) = _
  rw [evenZ, evenA_one_eq_ofReal_re]
  calc
    quarterRotation *
          (((unbalanceFactor (evenBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
            ((-1 : ℂ) ^ (k : ℕ) *
              squareMultiplier (-Complex.I * ((evenA 1 u).re : ℂ)))) =
        (((unbalanceFactor (evenBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
          ((-1 : ℂ) ^ (k : ℕ))) *
            (quarterRotation *
              squareMultiplier (-Complex.I * ((evenA 1 u).re : ℂ))) := by ring
    _ = (((unbalanceFactor (evenBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
          ((-1 : ℂ) ^ (k : ℕ))) *
            (Real.sqrt (evenA 1 u).re : ℂ) := by
          rw [quarterRotation_mul_squareMultiplier_neg_I _
            (evenA_one_re_nonneg u)]
    _ = ((unbalanceFactor (evenBalancedSphere k 1 u) / 4 *
          Real.sqrt (evenA 1 u).re : ℝ) : ℂ) *
            ((-1 : ℂ) ^ (k : ℕ)) := by
          push_cast
          ring

theorem wCoordinate_evenCore_raw (k : Fin 6) (u : unitInterval) :
    RadialCore.wCoordinate (evenCore k u).1.1.1.1.2 =
      ((unbalanceFactor (evenBalancedSphere k 1 u) / 3 *
        Real.sqrt (evenB 1 u).re : ℝ) : ℂ) *
        CoreEdges.wRoot (wIndex k) := by
  rw [RadialCore.wCoordinate, evenCore_w_value]
  change sixthRotation *
      (((unbalanceFactor (evenBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
        evenW k 1 u) = _
  rw [evenW, evenB_one_eq_ofReal_re]
  calc
    sixthRotation *
          (((unbalanceFactor (evenBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
            ((CoreEdges.wRoot (wIndex k) * minusThirdRoot) *
              RadialMilnor.radialMultiplier
                (Complex.I * ((evenB 1 u).re : ℂ)))) =
        (((unbalanceFactor (evenBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
          CoreEdges.wRoot (wIndex k)) *
            (sixthRotation * minusThirdRoot *
              RadialMilnor.radialMultiplier
                (Complex.I * ((evenB 1 u).re : ℂ))) := by ring
    _ = (((unbalanceFactor (evenBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
          CoreEdges.wRoot (wIndex k)) *
            (Real.sqrt (evenB 1 u).re : ℂ) := by
          rw [sixthRotation_mul_minusThirdRoot_mul_radialMultiplier_I _
            (evenB_one_re_nonneg u)]
    _ = ((unbalanceFactor (evenBalancedSphere k 1 u) / 3 *
          Real.sqrt (evenB 1 u).re : ℝ) : ℂ) *
            CoreEdges.wRoot (wIndex k) := by
          push_cast
          ring

theorem sqrt_normSq_evenCore_z (k : Fin 6) (u : unitInterval) :
    Real.sqrt (normSq (evenCore k u).1.1.1.1.1) =
      unbalanceFactor (evenBalancedSphere k 1 u) / 4 *
        Real.sqrt (evenA 1 u).re := by
  rw [evenCore_z_value]
  rw [normSq_mul, normSq_ofReal, normSq_evenZ]
  have hnormA : ‖evenA 1 u‖ = (evenA 1 u).re := by
    rw [evenA_one_eq_ofReal_re]
    simp [abs_of_nonneg (evenA_one_re_nonneg u)]
  rw [hnormA]
  simpa [pow_two] using sqrt_sq_mul
    (unbalanceFactor (evenBalancedSphere k 1 u) / 4) (evenA 1 u).re
    (div_nonneg (unbalanceFactor_pos _).le (by norm_num))
    (evenA_one_re_nonneg u)

theorem sqrt_normSq_evenCore_w (k : Fin 6) (u : unitInterval) :
    Real.sqrt (normSq (evenCore k u).1.1.1.1.2) =
      unbalanceFactor (evenBalancedSphere k 1 u) / 3 *
        Real.sqrt (evenB 1 u).re := by
  rw [evenCore_w_value]
  rw [normSq_mul, normSq_ofReal, normSq_evenW]
  have hnormB : ‖evenB 1 u‖ = (evenB 1 u).re := by
    rw [evenB_one_eq_ofReal_re]
    simp [abs_of_nonneg (evenB_one_re_nonneg u)]
  rw [hnormB]
  simpa [pow_two] using sqrt_sq_mul
    (unbalanceFactor (evenBalancedSphere k 1 u) / 3) (evenB 1 u).re
    (div_nonneg (unbalanceFactor_pos _).le (by norm_num))
    (evenB_one_re_nonneg u)

theorem zCoordinate_evenCore (k : Fin 6) (u : unitInterval) :
    RadialCore.zCoordinate (evenCore k u).1.1.1.1.1 =
      (Real.sqrt (normSq (evenCore k u).1.1.1.1.1) : ℂ) *
        CoreEdges.zRoot (zIndex k) := by
  rw [zCoordinate_evenCore_raw, sqrt_normSq_evenCore_z, zRoot_zIndex]

theorem wCoordinate_evenCore (k : Fin 6) (u : unitInterval) :
    RadialCore.wCoordinate (evenCore k u).1.1.1.1.2 =
      (Real.sqrt (normSq (evenCore k u).1.1.1.1.2) : ℂ) *
        CoreEdges.wRoot (wIndex k) := by
  rw [wCoordinate_evenCore_raw, sqrt_normSq_evenCore_w]

theorem evenCore_eq_edge (k : Fin 6) (u : unitInterval) :
    evenCore k u = CoreEdges.edge (zIndex k) (wIndex k) (coreParameter (evenCore k u)) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · calc
      (evenCore k u).1.1.1.1.1 =
          CoreEdges.fromZCoordinate
            (RadialCore.zCoordinate (evenCore k u).1.1.1.1.1) :=
        (CoreEdges.fromZCoordinate_zCoordinate _).symm
      _ = CoreEdges.fromZCoordinate
          ((Real.sqrt (normSq (evenCore k u).1.1.1.1.1) : ℂ) *
            CoreEdges.zRoot (zIndex k)) := by rw [zCoordinate_evenCore]
      _ = CoreEdges.fromZCoordinate
          ((Real.sqrt (1 - (coreParameter (evenCore k u) : ℝ)) : ℂ) *
            CoreEdges.zRoot (zIndex k)) := by
          rw [one_sub_coreParameter]
      _ = (CoreEdges.edge (zIndex k) (wIndex k)
          (coreParameter (evenCore k u))).1.1.1.1.1 := rfl
  · calc
      (evenCore k u).1.1.1.1.2 =
          CoreEdges.fromWCoordinate
            (RadialCore.wCoordinate (evenCore k u).1.1.1.1.2) :=
        (CoreEdges.fromWCoordinate_wCoordinate _).symm
      _ = CoreEdges.fromWCoordinate
          ((Real.sqrt (normSq (evenCore k u).1.1.1.1.2) : ℂ) *
            CoreEdges.wRoot (wIndex k)) := by rw [wCoordinate_evenCore]
      _ = (CoreEdges.edge (zIndex k) (wIndex k)
          (coreParameter (evenCore k u))).1.1.1.1.2 := rfl

theorem oddA_one_eq_ofReal_re (u : unitInterval) :
    oddA 1 u = ((oddA 1 u).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [oddA_one_im]

theorem oddB_one_eq_ofReal_re (u : unitInterval) :
    oddB 1 u = ((oddB 1 u).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [oddB_one_im]

theorem oddCore_z_value (k : Fin 6) (u : unitInterval) :
    (oddCore k u).1.1.1.1.1 =
      (((unbalanceFactor (oddBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
        oddZ k 1 u) := by
  dsimp only [oddCore, oddFiber, oddSphere, unbalanceSphere,
    oddBalancedSphere]
  rw [positiveLevel_one]

theorem oddCore_w_value (k : Fin 6) (u : unitInterval) :
    (oddCore k u).1.1.1.1.2 =
      (((unbalanceFactor (oddBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
        oddW k 1 u) := by
  dsimp only [oddCore, oddFiber, oddSphere, unbalanceSphere,
    oddBalancedSphere]
  rw [positiveLevel_one]

theorem zCoordinate_oddCore_raw (k : Fin 6) (u : unitInterval) :
    RadialCore.zCoordinate (oddCore k u).1.1.1.1.1 =
      ((unbalanceFactor (oddBalancedSphere k 1 u) / 4 *
        Real.sqrt (oddA 1 u).re : ℝ) : ℂ) *
        ((-1 : ℂ) ^ ((k : ℕ) + 1)) := by
  rw [RadialCore.zCoordinate, oddCore_z_value]
  change quarterRotation *
      (((unbalanceFactor (oddBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
        oddZ k 1 u) = _
  rw [oddZ, oddA_one_eq_ofReal_re,
    squareMultiplier_I_mul _ (oddA_one_re_nonneg u)]
  calc
    quarterRotation *
          (((unbalanceFactor (oddBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
            (((-1 : ℂ) ^ ((k : ℕ) + 1) * -Complex.I) *
              (Complex.I *
                squareMultiplier (-Complex.I * ((oddA 1 u).re : ℂ))))) =
        quarterRotation *
          (((unbalanceFactor (oddBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
            (((-1 : ℂ) ^ ((k : ℕ) + 1) * (-Complex.I * Complex.I)) *
              squareMultiplier (-Complex.I * ((oddA 1 u).re : ℂ)))) := by
          ring
    _ =
        (((unbalanceFactor (oddBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
          ((-1 : ℂ) ^ ((k : ℕ) + 1))) *
            (quarterRotation *
              squareMultiplier (-Complex.I * ((oddA 1 u).re : ℂ))) := by
          rw [show -Complex.I * Complex.I = (1 : ℂ) by
            rw [neg_mul, Complex.I_mul_I]
            simp]
          ring
    _ = (((unbalanceFactor (oddBalancedSphere k 1 u) / 4 : ℝ) : ℂ) *
          ((-1 : ℂ) ^ ((k : ℕ) + 1))) *
            (Real.sqrt (oddA 1 u).re : ℂ) := by
          rw [quarterRotation_mul_squareMultiplier_neg_I _
            (oddA_one_re_nonneg u)]
    _ = ((unbalanceFactor (oddBalancedSphere k 1 u) / 4 *
          Real.sqrt (oddA 1 u).re : ℝ) : ℂ) *
            ((-1 : ℂ) ^ ((k : ℕ) + 1)) := by
          push_cast
          ring

theorem wCoordinate_oddCore_raw (k : Fin 6) (u : unitInterval) :
    RadialCore.wCoordinate (oddCore k u).1.1.1.1.2 =
      ((unbalanceFactor (oddBalancedSphere k 1 u) / 3 *
        Real.sqrt (oddB 1 u).re : ℝ) : ℂ) *
        CoreEdges.wRoot (wIndex k) := by
  rw [RadialCore.wCoordinate, oddCore_w_value]
  change sixthRotation *
      (((unbalanceFactor (oddBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
        oddW k 1 u) = _
  rw [oddW, oddB_one_eq_ofReal_re]
  calc
    sixthRotation *
          (((unbalanceFactor (oddBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
            (CoreEdges.wRoot (wIndex k) *
              RadialMilnor.radialMultiplier
                (-Complex.I * ((oddB 1 u).re : ℂ)))) =
        (((unbalanceFactor (oddBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
          CoreEdges.wRoot (wIndex k)) *
            (sixthRotation *
              RadialMilnor.radialMultiplier
                (-Complex.I * ((oddB 1 u).re : ℂ))) := by ring
    _ = (((unbalanceFactor (oddBalancedSphere k 1 u) / 3 : ℝ) : ℂ) *
          CoreEdges.wRoot (wIndex k)) *
            (Real.sqrt (oddB 1 u).re : ℂ) := by
          rw [sixthRotation_mul_radialMultiplier_neg_I _
            (oddB_one_re_nonneg u)]
    _ = ((unbalanceFactor (oddBalancedSphere k 1 u) / 3 *
          Real.sqrt (oddB 1 u).re : ℝ) : ℂ) *
            CoreEdges.wRoot (wIndex k) := by
          push_cast
          ring

theorem sqrt_normSq_oddCore_z (k : Fin 6) (u : unitInterval) :
    Real.sqrt (normSq (oddCore k u).1.1.1.1.1) =
      unbalanceFactor (oddBalancedSphere k 1 u) / 4 *
        Real.sqrt (oddA 1 u).re := by
  rw [oddCore_z_value]
  rw [normSq_mul, normSq_ofReal, normSq_oddZ]
  have hnormA : ‖oddA 1 u‖ = (oddA 1 u).re := by
    rw [oddA_one_eq_ofReal_re]
    simp [abs_of_nonneg (oddA_one_re_nonneg u)]
  rw [hnormA]
  simpa [pow_two] using sqrt_sq_mul
    (unbalanceFactor (oddBalancedSphere k 1 u) / 4) (oddA 1 u).re
    (div_nonneg (unbalanceFactor_pos _).le (by norm_num))
    (oddA_one_re_nonneg u)

theorem sqrt_normSq_oddCore_w (k : Fin 6) (u : unitInterval) :
    Real.sqrt (normSq (oddCore k u).1.1.1.1.2) =
      unbalanceFactor (oddBalancedSphere k 1 u) / 3 *
        Real.sqrt (oddB 1 u).re := by
  rw [oddCore_w_value]
  rw [normSq_mul, normSq_ofReal, normSq_oddW]
  have hnormB : ‖oddB 1 u‖ = (oddB 1 u).re := by
    rw [oddB_one_eq_ofReal_re]
    simp [abs_of_nonneg (oddB_one_re_nonneg u)]
  rw [hnormB]
  simpa [pow_two] using sqrt_sq_mul
    (unbalanceFactor (oddBalancedSphere k 1 u) / 3) (oddB 1 u).re
    (div_nonneg (unbalanceFactor_pos _).le (by norm_num))
    (oddB_one_re_nonneg u)

theorem zCoordinate_oddCore (k : Fin 6) (u : unitInterval) :
    RadialCore.zCoordinate (oddCore k u).1.1.1.1.1 =
      (Real.sqrt (normSq (oddCore k u).1.1.1.1.1) : ℂ) *
        CoreEdges.zRoot (zIndex (nextCycle k)) := by
  rw [zCoordinate_oddCore_raw, sqrt_normSq_oddCore_z,
    zRoot_zIndex_next]

theorem wCoordinate_oddCore (k : Fin 6) (u : unitInterval) :
    RadialCore.wCoordinate (oddCore k u).1.1.1.1.2 =
      (Real.sqrt (normSq (oddCore k u).1.1.1.1.2) : ℂ) *
        CoreEdges.wRoot (wIndex k) := by
  rw [wCoordinate_oddCore_raw, sqrt_normSq_oddCore_w]

theorem oddCore_eq_edge (k : Fin 6) (u : unitInterval) :
    oddCore k u = CoreEdges.edge (zIndex (nextCycle k)) (wIndex k)
      (coreParameter (oddCore k u)) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · calc
      (oddCore k u).1.1.1.1.1 =
          CoreEdges.fromZCoordinate
            (RadialCore.zCoordinate (oddCore k u).1.1.1.1.1) :=
        (CoreEdges.fromZCoordinate_zCoordinate _).symm
      _ = CoreEdges.fromZCoordinate
          ((Real.sqrt (normSq (oddCore k u).1.1.1.1.1) : ℂ) *
            CoreEdges.zRoot (zIndex (nextCycle k))) := by
          rw [zCoordinate_oddCore]
      _ = CoreEdges.fromZCoordinate
          ((Real.sqrt (1 - (coreParameter (oddCore k u) : ℝ)) : ℂ) *
            CoreEdges.zRoot (zIndex (nextCycle k))) := by
          rw [one_sub_coreParameter]
      _ = (CoreEdges.edge (zIndex (nextCycle k)) (wIndex k)
          (coreParameter (oddCore k u))).1.1.1.1.1 := rfl
  · calc
      (oddCore k u).1.1.1.1.2 =
          CoreEdges.fromWCoordinate
            (RadialCore.wCoordinate (oddCore k u).1.1.1.1.2) :=
        (CoreEdges.fromWCoordinate_wCoordinate _).symm
      _ = CoreEdges.fromWCoordinate
          ((Real.sqrt (normSq (oddCore k u).1.1.1.1.2) : ℂ) *
            CoreEdges.wRoot (wIndex k)) := by
          rw [wCoordinate_oddCore]
      _ = (CoreEdges.edge (zIndex (nextCycle k)) (wIndex k)
          (coreParameter (oddCore k u))).1.1.1.1.2 := rfl

theorem coreParameter_continuous : Continuous coreParameter := by
  apply Continuous.subtype_mk
  fun_prop

theorem evenCore_continuous (k : Fin 6) : Continuous (evenCore k) := by
  have h := FiberAction.fiberToCore.continuous.comp
    (evenFiber_fixed_continuous k 1)
  exact h.congr fun u => fiberToCore_evenFiber_one k u

theorem oddCore_continuous (k : Fin 6) : Continuous (oddCore k) := by
  have h := FiberAction.fiberToCore.continuous.comp
    (oddFiber_fixed_continuous k 1)
  exact h.congr fun u => fiberToCore_oddFiber_one k u

@[simp] theorem coreParameter_evenCore_zero (k : Fin 6) :
    coreParameter (evenCore k 0) = 0 := by
  apply Subtype.ext
  change normSq (evenCore k 0).1.1.1.1.2 = 0
  rw [evenCore_w_value, normSq_mul, normSq_ofReal, normSq_evenW]
  simp [evenB, ellipseB, ellipseBRe, ellipseBIm, evenTheta]

@[simp] theorem coreParameter_evenCore_one (k : Fin 6) :
    coreParameter (evenCore k 1) = 1 := by
  apply Subtype.ext
  have hzero : normSq (evenCore k 1).1.1.1.1.1 = 0 := by
    rw [evenCore_z_value, normSq_mul, normSq_ofReal, normSq_evenZ]
    simp [evenA, ellipseA, ellipseARe, ellipseAIm, evenTheta]
  have hone := one_sub_coreParameter (evenCore k 1)
  rw [hzero] at hone
  exact (sub_eq_zero.mp hone).symm

@[simp] theorem coreParameter_oddCore_zero (k : Fin 6) :
    coreParameter (oddCore k 0) = 1 := by
  apply Subtype.ext
  have hzero : normSq (oddCore k 0).1.1.1.1.1 = 0 := by
    rw [oddCore_z_value, normSq_mul, normSq_ofReal, normSq_oddZ]
    simp [oddA, ellipseA, ellipseARe, ellipseAIm, oddTheta]
  have hone := one_sub_coreParameter (oddCore k 0)
  rw [hzero] at hone
  exact (sub_eq_zero.mp hone).symm

@[simp] theorem coreParameter_oddCore_one (k : Fin 6) :
    coreParameter (oddCore k 1) = 0 := by
  apply Subtype.ext
  change normSq (oddCore k 1).1.1.1.1.2 = 0
  rw [oddCore_w_value, normSq_mul, normSq_ofReal, normSq_oddW]
  simp [oddB, ellipseB, ellipseBRe, ellipseBIm, oddTheta]

def evenCoreParameter (k : Fin 6) : unitInterval → unitInterval :=
  fun u => coreParameter (evenCore k u)

theorem evenCoreParameter_continuous (k : Fin 6) :
    Continuous (evenCoreParameter k) :=
  coreParameter_continuous.comp (evenCore_continuous k)

@[simp] theorem evenCoreParameter_zero (k : Fin 6) :
    evenCoreParameter k 0 = 0 :=
  coreParameter_evenCore_zero k

@[simp] theorem evenCoreParameter_one (k : Fin 6) :
    evenCoreParameter k 1 = 1 :=
  coreParameter_evenCore_one k

def oddCoreParameter (k : Fin 6) : unitInterval → unitInterval :=
  fun u => unitInterval.symm (coreParameter (oddCore k u))

theorem oddCoreParameter_continuous (k : Fin 6) :
    Continuous (oddCoreParameter k) := by
  exact unitInterval.continuous_symm.comp
    (coreParameter_continuous.comp (oddCore_continuous k))

@[simp] theorem oddCoreParameter_zero (k : Fin 6) :
    oddCoreParameter k 0 = 0 := by
  apply Subtype.ext
  simp [oddCoreParameter]

@[simp] theorem oddCoreParameter_one (k : Fin 6) :
    oddCoreParameter k 1 = 1 := by
  apply Subtype.ext
  simp [oddCoreParameter]

theorem fiberToCore_evenBase_one (k : Fin 6) :
    FiberAction.fiberToCore (evenBase k 1) =
      CoreCycles.aVertex (zIndex k) := by
  change FiberAction.fiberToCore (evenFiber k 1 0) = _
  rw [fiberToCore_evenFiber_one, evenCore_eq_edge,
    coreParameter_evenCore_zero, CoreCycles.edge_zero]

theorem fiberToCore_oddBase_one (k : Fin 6) :
    FiberAction.fiberToCore (oddBase k 1) =
      CoreCycles.bVertex (wIndex k) := by
  change FiberAction.fiberToCore (oddFiber k 1 0) = _
  rw [fiberToCore_oddFiber_one, oddCore_eq_edge,
    coreParameter_oddCore_zero, CoreCycles.edge_one]

def evenCoreEdgePath (k : Fin 6) :
    Path (FiberAction.fiberToCore (evenBase k 1))
      (FiberAction.fiberToCore (oddBase k 1)) :=
  (CoreCycles.edgePath (zIndex k) (wIndex k)).cast
    (fiberToCore_evenBase_one k) (fiberToCore_oddBase_one k)

def oddCoreEdgePath (k : Fin 6) :
    Path (FiberAction.fiberToCore (oddBase k 1))
      (FiberAction.fiberToCore (evenBase (nextCycle k) 1)) :=
  (CoreCycles.edgePath (zIndex (nextCycle k)) (wIndex k)).symm.cast
    (fiberToCore_oddBase_one k) (fiberToCore_evenBase_one (nextCycle k))

theorem fiberToCore_evenPath_one (k : Fin 6) :
    (evenPath k 1).map FiberAction.fiberToCore.continuous =
      (evenCoreEdgePath k).reparam
        (evenCoreParameter k) (evenCoreParameter_continuous k)
        (evenCoreParameter_zero k) (evenCoreParameter_one k) := by
  apply Path.ext
  funext u
  change FiberAction.fiberToCore (evenFiber k 1 u) =
    CoreEdges.edge (zIndex k) (wIndex k) (coreParameter (evenCore k u))
  rw [fiberToCore_evenFiber_one]
  exact evenCore_eq_edge k u

theorem fiberToCore_oddPath_one (k : Fin 6) :
    (oddPath k 1).map FiberAction.fiberToCore.continuous =
      (oddCoreEdgePath k).reparam
        (oddCoreParameter k) (oddCoreParameter_continuous k)
        (oddCoreParameter_zero k) (oddCoreParameter_one k) := by
  apply Path.ext
  funext u
  change FiberAction.fiberToCore (oddFiber k 1 u) =
    CoreEdges.edge (zIndex (nextCycle k)) (wIndex k)
      (unitInterval.symm (oddCoreParameter k u))
  rw [fiberToCore_oddFiber_one, oddCore_eq_edge]
  congr 1
  simp [oddCoreParameter]

def fiberToCoreEvenPathHomotopy (k : Fin 6) :
    ((evenPath k 1).map FiberAction.fiberToCore.continuous).Homotopy
      (evenCoreEdgePath k) := by
  rw [fiberToCore_evenPath_one]
  exact (Path.Homotopy.reparam _ _ (evenCoreParameter_continuous k)
    (evenCoreParameter_zero k) (evenCoreParameter_one k)).symm

def fiberToCoreOddPathHomotopy (k : Fin 6) :
    ((oddPath k 1).map FiberAction.fiberToCore.continuous).Homotopy
      (oddCoreEdgePath k) := by
  rw [fiberToCore_oddPath_one]
  exact (Path.Homotopy.reparam _ _ (oddCoreParameter_continuous k)
    (oddCoreParameter_zero k) (oddCoreParameter_one k)).symm

def pairCoreEdgePath (k : Fin 6) :
    Path (FiberAction.fiberToCore (evenBase k 1))
      (FiberAction.fiberToCore (evenBase (nextCycle k) 1)) :=
  (evenCoreEdgePath k).trans (oddCoreEdgePath k)

def fiberToCorePairPathHomotopy (k : Fin 6) :
    ((pairPath k 1).map FiberAction.fiberToCore.continuous).Homotopy
      (pairCoreEdgePath k) := by
  let H := (fiberToCoreEvenPathHomotopy k).hcomp
    (fiberToCoreOddPathHomotopy k)
  refine H.cast ?_ rfl
  rw [pairPath, Path.map_trans]
  apply Path.ext
  rfl

def pairCoreEdgePathZero :
    Path (FiberAction.fiberToCore (evenBase 0 1))
      (FiberAction.fiberToCore (evenBase 1 1)) :=
  (pairCoreEdgePath 0).cast rfl (by rw [nextCycle_zero])

def pairCoreEdgePathOne :
    Path (FiberAction.fiberToCore (evenBase 1 1))
      (FiberAction.fiberToCore (evenBase 2 1)) :=
  (pairCoreEdgePath 1).cast rfl (by rw [nextCycle_one])

def pairCoreEdgePathTwo :
    Path (FiberAction.fiberToCore (evenBase 2 1))
      (FiberAction.fiberToCore (evenBase 3 1)) :=
  (pairCoreEdgePath 2).cast rfl (by rw [nextCycle_two])

def pairCoreEdgePathThree :
    Path (FiberAction.fiberToCore (evenBase 3 1))
      (FiberAction.fiberToCore (evenBase 4 1)) :=
  (pairCoreEdgePath 3).cast rfl (by rw [nextCycle_three])

def pairCoreEdgePathFour :
    Path (FiberAction.fiberToCore (evenBase 4 1))
      (FiberAction.fiberToCore (evenBase 5 1)) :=
  (pairCoreEdgePath 4).cast rfl (by rw [nextCycle_four])

def pairCoreEdgePathFive :
    Path (FiberAction.fiberToCore (evenBase 5 1))
      (FiberAction.fiberToCore (evenBase 0 1)) :=
  (pairCoreEdgePath 5).cast rfl (by rw [nextCycle_five])

def fiberToCorePairPathZeroHomotopy :
    ((pairPathZero 1).map FiberAction.fiberToCore.continuous).Homotopy
      pairCoreEdgePathZero := by
  let H := (fiberToCorePairPathHomotopy 0).pathCast rfl (by rw [nextCycle_zero])
  exact H.cast (by apply Path.ext; rfl) (by apply Path.ext; rfl)

def fiberToCorePairPathOneHomotopy :
    ((pairPathOne 1).map FiberAction.fiberToCore.continuous).Homotopy
      pairCoreEdgePathOne := by
  let H := (fiberToCorePairPathHomotopy 1).pathCast rfl (by rw [nextCycle_one])
  exact H.cast (by apply Path.ext; rfl) (by apply Path.ext; rfl)

def fiberToCorePairPathTwoHomotopy :
    ((pairPathTwo 1).map FiberAction.fiberToCore.continuous).Homotopy
      pairCoreEdgePathTwo := by
  let H := (fiberToCorePairPathHomotopy 2).pathCast rfl (by rw [nextCycle_two])
  exact H.cast (by apply Path.ext; rfl) (by apply Path.ext; rfl)

def fiberToCorePairPathThreeHomotopy :
    ((pairPathThree 1).map FiberAction.fiberToCore.continuous).Homotopy
      pairCoreEdgePathThree := by
  let H := (fiberToCorePairPathHomotopy 3).pathCast rfl (by rw [nextCycle_three])
  exact H.cast (by apply Path.ext; rfl) (by apply Path.ext; rfl)

def fiberToCorePairPathFourHomotopy :
    ((pairPathFour 1).map FiberAction.fiberToCore.continuous).Homotopy
      pairCoreEdgePathFour := by
  let H := (fiberToCorePairPathHomotopy 4).pathCast rfl (by rw [nextCycle_four])
  exact H.cast (by apply Path.ext; rfl) (by apply Path.ext; rfl)

def fiberToCorePairPathFiveHomotopy :
    ((pairPathFive 1).map FiberAction.fiberToCore.continuous).Homotopy
      pairCoreEdgePathFive := by
  let H := (fiberToCorePairPathHomotopy 5).pathCast rfl (by rw [nextCycle_five])
  exact H.cast (by apply Path.ext; rfl) (by apply Path.ext; rfl)

def coreBoundaryWord :
    Path (FiberAction.fiberToCore (evenBase 0 1))
      (FiberAction.fiberToCore (evenBase 0 1)) :=
  pairCoreEdgePathZero.trans
    (pairCoreEdgePathOne.trans
      (pairCoreEdgePathTwo.trans
        (pairCoreEdgePathThree.trans
          (pairCoreEdgePathFour.trans pairCoreEdgePathFive))))

def fiberToCoreBoundaryPathOneHomotopy :
    ((boundaryPath 1).map FiberAction.fiberToCore.continuous).Homotopy
      coreBoundaryWord := by
  let H := fiberToCorePairPathZeroHomotopy.hcomp
    (fiberToCorePairPathOneHomotopy.hcomp
      (fiberToCorePairPathTwoHomotopy.hcomp
        (fiberToCorePairPathThreeHomotopy.hcomp
          (fiberToCorePairPathFourHomotopy.hcomp
            fiberToCorePairPathFiveHomotopy))))
  refine H.cast ?_ rfl
  simp only [boundaryPath, Path.map_trans]

theorem fiberToCore_evenBase_zero_vertex :
    FiberAction.fiberToCore (evenBase 0 1) = CoreCycles.aVertex 0 := by
  simpa [zIndex] using fiberToCore_evenBase_one 0

def standardCoreBoundary :
    Path (FiberAction.fiberToCore (evenBase 0 1))
      (FiberAction.fiberToCore (evenBase 0 1)) :=
  (CoreBoundary.commutator CoreCycles.firstCycle CoreCycles.secondCycle.symm).cast
    fiberToCore_evenBase_zero_vertex fiberToCore_evenBase_zero_vertex

def reducedCoreBoundary : Path (CoreCycles.aVertex 0) (CoreCycles.aVertex 0) :=
  ((CoreCycles.edgePath 0 0).trans (CoreCycles.edgePath 1 0).symm).trans
    (((CoreCycles.edgePath 1 1).trans (CoreCycles.edgePath 0 1).symm).trans
      (((CoreCycles.edgePath 0 2).trans (CoreCycles.edgePath 1 2).symm).trans
        (((CoreCycles.edgePath 1 0).trans (CoreCycles.edgePath 0 0).symm).trans
          (((CoreCycles.edgePath 0 1).trans (CoreCycles.edgePath 1 1).symm).trans
            ((CoreCycles.edgePath 1 2).trans (CoreCycles.edgePath 0 2).symm)))))

theorem coreBoundaryWord_eq_reduced :
    coreBoundaryWord = reducedCoreBoundary.cast
      fiberToCore_evenBase_zero_vertex fiberToCore_evenBase_zero_vertex := by
  apply Path.ext
  rfl

theorem reducedCoreBoundary_homotopic_commutator :
    reducedCoreBoundary.Homotopic
      (CoreBoundary.commutator CoreCycles.firstCycle CoreCycles.secondCycle.symm) := by
  apply Path.Homotopic.Quotient.exact
  simp [reducedCoreBoundary, CoreBoundary.commutator,
    CoreCycles.firstCycle, CoreCycles.secondCycle]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  let a := Path.Homotopic.Quotient.mk (CoreCycles.edgePath 0 0)
  let b := Path.Homotopic.Quotient.mk (CoreCycles.edgePath 1 0)
  let r := (Path.Homotopic.Quotient.mk (CoreCycles.edgePath 1 2)).trans
    (Path.Homotopic.Quotient.mk (CoreCycles.edgePath 0 2)).symm
  change r = b.trans (a.symm.trans (a.trans (b.symm.trans r)))
  symm
  calc
    b.trans (a.symm.trans (a.trans (b.symm.trans r))) =
        b.trans ((a.symm.trans a).trans (b.symm.trans r)) :=
      congrArg (fun q => b.trans q)
        (Path.Homotopic.Quotient.trans_assoc a.symm a (b.symm.trans r)).symm
    _ = b.trans (b.symm.trans r) := by simp
    _ = (b.trans b.symm).trans r :=
      (Path.Homotopic.Quotient.trans_assoc b b.symm r).symm
    _ = r := by simp

theorem coreBoundaryWord_homotopic_standard :
    coreBoundaryWord.Homotopic standardCoreBoundary := by
  rw [coreBoundaryWord_eq_reduced]
  exact reducedCoreBoundary_homotopic_commutator.pathCast
    fiberToCore_evenBase_zero_vertex fiberToCore_evenBase_zero_vertex

abbrev NegativeSymmetry := Symmetry.NegativeSymmetry AlgebraicTrefoil.knot

def complementHomeomorph (S : NegativeSymmetry) :
    RadialPhase.Complement ≃ₜ RadialPhase.Complement :=
  CompactifiedSymmetry.complementHomeomorph S

def inducedCoreMap (S : NegativeSymmetry) :
    C(RadialCore.Core, RadialCore.Core) :=
  FiberAction.inducedCore
    (RadialPageObstruction.fiberMapAt (complementHomeomorph S) 0)

theorem false_of_preservesBoundary (S : NegativeSymmetry)
    (hboundary : CoreBoundary.PreservesBoundary (inducedCoreMap S)) : False := by
  apply RadialPageObstruction.false_of_action_det_one
    (complementHomeomorph S) (SymmetryDegree.induced_degree_eq_neg_one S)
  exact CoreBoundary.action_det_eq_one_of_preservesBoundary
    (inducedCoreMap S) hboundary

end

end Submission.PeripheralBridge
