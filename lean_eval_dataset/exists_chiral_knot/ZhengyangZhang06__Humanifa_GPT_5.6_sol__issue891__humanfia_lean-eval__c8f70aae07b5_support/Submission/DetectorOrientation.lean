import Submission.PeripheralOrientation

open LeanEval.KnotTheory

namespace Submission.DetectorOrientation

noncomputable section

theorem rotate_re (n : ℕ) (t : ℝ) (z : ℂ) :
    (Milnor.rotate n t z).re =
      Real.cos (n * t) * z.re - Real.sin (n * t) * z.im := by
  rw [Milnor.rotate, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem rotate_im (n : ℕ) (t : ℝ) (z : ℂ) :
    (Milnor.rotate n t z).im =
      Real.sin (n * t) * z.re + Real.cos (n * t) * z.im := by
  rw [Milnor.rotate, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem rotate_sphereCurveZ (s t : ℝ) :
    Milnor.rotate 3 t (AlgebraicTrefoil.sphereCurveZ s) =
      AlgebraicTrefoil.sphereCurveZ (s + t) := by
  apply Complex.ext
  · rw [rotate_re]
    change Real.cos (3 * t) * ((3 / 5) * Real.cos (3 * s)) -
      Real.sin (3 * t) * ((3 / 5) * Real.sin (3 * s)) =
      (3 / 5) * Real.cos (3 * (s + t))
    rw [show 3 * (s + t) = 3 * t + 3 * s by ring, Real.cos_add]
    ring
  · rw [rotate_im]
    change Real.sin (3 * t) * ((3 / 5) * Real.cos (3 * s)) +
      Real.cos (3 * t) * ((3 / 5) * Real.sin (3 * s)) =
      (3 / 5) * Real.sin (3 * (s + t))
    rw [show 3 * (s + t) = 3 * t + 3 * s by ring, Real.sin_add]
    ring

theorem rotate_sphereCurveW (s t : ℝ) :
    Milnor.rotate 2 t (AlgebraicTrefoil.sphereCurveW s) =
      AlgebraicTrefoil.sphereCurveW (s + t) := by
  apply Complex.ext
  · rw [rotate_re]
    change Real.cos (2 * t) * ((-4 / 5) * Real.cos (2 * s)) -
      Real.sin (2 * t) * ((-4 / 5) * Real.sin (2 * s)) =
      (-4 / 5) * Real.cos (2 * (s + t))
    rw [show 2 * (s + t) = 2 * t + 2 * s by ring, Real.cos_add]
    ring
  · rw [rotate_im]
    change Real.sin (2 * t) * ((-4 / 5) * Real.cos (2 * s)) +
      Real.cos (2 * t) * ((-4 / 5) * Real.sin (2 * s)) =
      (-4 / 5) * Real.sin (2 * (s + t))
    rw [show 2 * (s + t) = 2 * t + 2 * s by ring, Real.sin_add]
    ring

def shiftedZRe (t : ℝ) (p : R3) : ℝ :=
  Real.cos (3 * t) * (2 * p.ofLp 0 / AlgebraicTrefoil.sphereDenom p) -
    Real.sin (3 * t) * (2 * p.ofLp 1 / AlgebraicTrefoil.sphereDenom p)

def shiftedZIm (t : ℝ) (p : R3) : ℝ :=
  Real.sin (3 * t) * (2 * p.ofLp 0 / AlgebraicTrefoil.sphereDenom p) +
    Real.cos (3 * t) * (2 * p.ofLp 1 / AlgebraicTrefoil.sphereDenom p)

def shiftedWRe (t : ℝ) (p : R3) : ℝ :=
  Real.cos (2 * t) * (2 * p.ofLp 2 / AlgebraicTrefoil.sphereDenom p) -
    Real.sin (2 * t) * ((AlgebraicTrefoil.radiusSq p - 1) /
      AlgebraicTrefoil.sphereDenom p)

def shiftedWIm (t : ℝ) (p : R3) : ℝ :=
  Real.sin (2 * t) * (2 * p.ofLp 2 / AlgebraicTrefoil.sphereDenom p) +
    Real.cos (2 * t) * ((AlgebraicTrefoil.radiusSq p - 1) /
      AlgebraicTrefoil.sphereDenom p)

def shiftDenom (t : ℝ) (p : R3) : ℝ := 1 - shiftedWIm t p

def ambientShift (t : ℝ) (p : R3) : R3 :=
  PeripheralOrientation.point
    (shiftedZRe t p / shiftDenom t p)
    (shiftedZIm t p / shiftDenom t p)
    (shiftedWRe t p / shiftDenom t p)

theorem ambientShift_eq_stereo_rotate (t : ℝ) (p : R3) :
    ambientShift t p = AlgebraicTrefoil.stereo
      (Milnor.rotate 3 t (AlgebraicTrefoil.inverseZ p))
      (Milnor.rotate 2 t (AlgebraicTrefoil.inverseW p)) := by
  ext i
  fin_cases i <;>
    simp [ambientShift, PeripheralOrientation.point, shiftedZRe, shiftedZIm,
      shiftedWRe, shiftedWIm, shiftDenom, AlgebraicTrefoil.stereo,
      AlgebraicTrefoil.inverseZ, AlgebraicTrefoil.inverseW,
      rotate_re, rotate_im]

theorem ambientShift_curve (s t : ℝ) :
    ambientShift t (AlgebraicTrefoil.curve s) =
      AlgebraicTrefoil.curve (s + t) := by
  rw [ambientShift_eq_stereo_rotate,
    AlgebraicTrefoil.inverseZ_curve, AlgebraicTrefoil.inverseW_curve,
    rotate_sphereCurveZ, rotate_sphereCurveW]
  rfl

theorem ambientShift_base (t : ℝ) :
    ambientShift t PeripheralOrientation.basePoint = AlgebraicTrefoil.curve t := by
  rw [← PeripheralOrientation.curve_zero, ambientShift_curve]
  congr 1
  ring

private theorem shiftedZRe_uncurry_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry shiftedZRe) := by
  unfold shiftedZRe
  exact ((Real.contDiff_cos.comp (by fun_prop)).mul
    ((contDiff_const.mul (by fun_prop)).div
      (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
      (fun x => AlgebraicTrefoil.sphereDenom_ne x.2))).sub
    ((Real.contDiff_sin.comp (by fun_prop)).mul
      ((contDiff_const.mul (by fun_prop)).div
        (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
        (fun x => AlgebraicTrefoil.sphereDenom_ne x.2)))

private theorem shiftedZIm_uncurry_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry shiftedZIm) := by
  unfold shiftedZIm
  exact ((Real.contDiff_sin.comp (by fun_prop)).mul
    ((contDiff_const.mul (by fun_prop)).div
      (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
      (fun x => AlgebraicTrefoil.sphereDenom_ne x.2))).add
    ((Real.contDiff_cos.comp (by fun_prop)).mul
      ((contDiff_const.mul (by fun_prop)).div
        (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
        (fun x => AlgebraicTrefoil.sphereDenom_ne x.2)))

private theorem shiftedWRe_uncurry_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry shiftedWRe) := by
  unfold shiftedWRe
  exact ((Real.contDiff_cos.comp (by fun_prop)).mul
    ((contDiff_const.mul (by fun_prop)).div
      (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
      (fun x => AlgebraicTrefoil.sphereDenom_ne x.2))).sub
    ((Real.contDiff_sin.comp (by fun_prop)).mul
      (((AlgebraicTrefoil.radiusSq_contDiff.comp contDiff_snd).sub
        contDiff_const).div
          (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
          (fun x => AlgebraicTrefoil.sphereDenom_ne x.2)))

private theorem shiftedWIm_uncurry_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry shiftedWIm) := by
  unfold shiftedWIm
  exact ((Real.contDiff_sin.comp (by fun_prop)).mul
    ((contDiff_const.mul (by fun_prop)).div
      (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
      (fun x => AlgebraicTrefoil.sphereDenom_ne x.2))).add
    ((Real.contDiff_cos.comp (by fun_prop)).mul
      (((AlgebraicTrefoil.radiusSq_contDiff.comp contDiff_snd).sub
        contDiff_const).div
          (AlgebraicTrefoil.sphereDenom_contDiff.comp contDiff_snd)
          (fun x => AlgebraicTrefoil.sphereDenom_ne x.2)))

private theorem shiftDenom_uncurry_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry shiftDenom) := by
  unfold shiftDenom
  exact contDiff_const.sub shiftedWIm_uncurry_contDiff

theorem shiftDenom_base_ne (t : ℝ) :
    shiftDenom t PeripheralOrientation.basePoint ≠ 0 := by
  unfold shiftDenom shiftedWIm
  have hlt := AlgebraicTrefoil.sphereCurveW_im_lt_one t
  simp [AlgebraicTrefoil.sphereCurveW, PeripheralOrientation.basePoint,
    PeripheralOrientation.point, AlgebraicTrefoil.radiusSq,
    AlgebraicTrefoil.sphereDenom] at hlt ⊢
  linarith

theorem shiftedWIm_eq_rotate (t : ℝ) (p : R3) :
    shiftedWIm t p =
      (Milnor.rotate 2 t (AlgebraicTrefoil.inverseW p)).im := by
  rw [rotate_im]
  simp [shiftedWIm, AlgebraicTrefoil.inverseW]

theorem shiftDenom_curve_ne (s t : ℝ) :
    shiftDenom t (AlgebraicTrefoil.curve s) ≠ 0 := by
  rw [shiftDenom, shiftedWIm_eq_rotate,
    AlgebraicTrefoil.inverseW_curve, rotate_sphereCurveW]
  exact sub_ne_zero.mpr
    (AlgebraicTrefoil.sphereCurveW_im_ne_one (s + t)).symm

theorem ambientShift_uncurry_contDiffAt_curve (s t : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry ambientShift)
      (t, AlgebraicTrefoil.curve s) := by
  apply contDiffAt_piLp'
  intro i
  fin_cases i
  · exact shiftedZRe_uncurry_contDiff.contDiffAt.div
      shiftDenom_uncurry_contDiff.contDiffAt (shiftDenom_curve_ne s t)
  · exact shiftedZIm_uncurry_contDiff.contDiffAt.div
      shiftDenom_uncurry_contDiff.contDiffAt (shiftDenom_curve_ne s t)
  · exact shiftedWRe_uncurry_contDiff.contDiffAt.div
      shiftDenom_uncurry_contDiff.contDiffAt (shiftDenom_curve_ne s t)

theorem ambientShift_contDiffAt_curve (s t : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (ambientShift t) (AlgebraicTrefoil.curve s) := by
  exact (ambientShift_uncurry_contDiffAt_curve s t).comp
    (AlgebraicTrefoil.curve s) (contDiffAt_const.prodMk contDiffAt_id)

theorem ambientShift_uncurry_contDiffAt (t : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry ambientShift)
      (t, PeripheralOrientation.basePoint) := by
  apply contDiffAt_piLp'
  intro i
  fin_cases i
  · exact shiftedZRe_uncurry_contDiff.contDiffAt.div
      shiftDenom_uncurry_contDiff.contDiffAt (shiftDenom_base_ne t)
  · exact shiftedZIm_uncurry_contDiff.contDiffAt.div
      shiftDenom_uncurry_contDiff.contDiffAt (shiftDenom_base_ne t)
  · exact shiftedWRe_uncurry_contDiff.contDiffAt.div
      shiftDenom_uncurry_contDiff.contDiffAt (shiftDenom_base_ne t)

theorem ambientShift_contDiffAt (t : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (ambientShift t) PeripheralOrientation.basePoint := by
  exact (ambientShift_uncurry_contDiffAt t).comp PeripheralOrientation.basePoint
    (contDiffAt_const.prodMk contDiffAt_id)

def shiftFDeriv (t : ℝ) : R3 →L[ℝ] R3 :=
  fderiv ℝ (ambientShift t) PeripheralOrientation.basePoint

theorem ambientShift_hasFDerivAt (t : ℝ) :
    HasFDerivAt (ambientShift t) (shiftFDeriv t)
      PeripheralOrientation.basePoint :=
  ((ambientShift_contDiffAt t).differentiableAt (by simp)).hasFDerivAt

theorem shiftDenom_continuous :
    Continuous (Function.uncurry shiftDenom) :=
  shiftDenom_uncurry_contDiff.continuous

theorem ambientShift_neg_apply_of_denom_ne (t : ℝ) (p : R3)
    (hdenom : shiftDenom t p ≠ 0) :
    ambientShift (-t) (ambientShift t p) = p := by
  have him :
      (Milnor.rotate 2 t (AlgebraicTrefoil.inverseW p)).im ≠ 1 := by
    intro him
    apply hdenom
    rw [shiftDenom, shiftedWIm_eq_rotate, him]
    ring
  have hsphere :
      Complex.normSq (Milnor.rotate 3 t (AlgebraicTrefoil.inverseZ p)) +
          Complex.normSq (Milnor.rotate 2 t (AlgebraicTrefoil.inverseW p)) =
        1 := by
    rw [Milnor.normSq_rotate, Milnor.normSq_rotate]
    exact AlgebraicTrefoil.inverse_normSq p
  obtain ⟨hz, hw⟩ := AlgebraicTrefoil.inverse_stereo hsphere him
  rw [ambientShift_eq_stereo_rotate, ambientShift_eq_stereo_rotate,
    hz, hw, Milnor.rotate_add, Milnor.rotate_add]
  have hsum : -t + t = 0 := by ring
  rw [hsum, Milnor.rotate_zero, Milnor.rotate_zero]
  exact AlgebraicTrefoil.stereo_inverse p

theorem ambientShift_neg_comp_eventuallyEq (t : ℝ) :
    (fun p => ambientShift (-t) (ambientShift t p)) =ᶠ[nhds PeripheralOrientation.basePoint]
      id := by
  have hcontinuous : ContinuousAt (shiftDenom t) PeripheralOrientation.basePoint :=
    shiftDenom_continuous.comp
      (continuous_const.prodMk continuous_id) |>.continuousAt
  filter_upwards [hcontinuous.eventually_ne (shiftDenom_base_ne t)] with p hp
  exact ambientShift_neg_apply_of_denom_ne t p hp

def inverseShiftFDeriv (t : ℝ) : R3 →L[ℝ] R3 :=
  fderiv ℝ (ambientShift (-t)) (AlgebraicTrefoil.curve t)

theorem inverseShiftFDeriv_comp_shiftFDeriv (t : ℝ) :
    inverseShiftFDeriv t ∘L shiftFDeriv t = ContinuousLinearMap.id ℝ R3 := by
  have hforward := ambientShift_hasFDerivAt t
  have hinverse : HasFDerivAt (ambientShift (-t)) (inverseShiftFDeriv t)
      (AlgebraicTrefoil.curve t) :=
    ((ambientShift_contDiffAt_curve t (-t)).differentiableAt
      (by simp)).hasFDerivAt
  rw [← ambientShift_base t] at hinverse
  have hcomp := hinverse.comp PeripheralOrientation.basePoint hforward
  have hidDeriv := hcomp.congr_of_eventuallyEq
    (ambientShift_neg_comp_eventuallyEq t).symm
  exact hidDeriv.unique (hasFDerivAt_id PeripheralOrientation.basePoint)

theorem shiftFDeriv_injective (t : ℝ) : Function.Injective (shiftFDeriv t) := by
  apply Function.LeftInverse.injective (g := inverseShiftFDeriv t)
  intro u
  have h := congrArg (fun L : R3 →L[ℝ] R3 => L u)
    (inverseShiftFDeriv_comp_shiftFDeriv t)
  simpa using h

theorem shiftFDeriv_det_ne_zero (t : ℝ) : (shiftFDeriv t).det ≠ 0 := by
  intro hdet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
    (LinearMap.ker_eq_bot.mpr (shiftFDeriv_injective t))

theorem shiftFDeriv_continuous : Continuous shiftFDeriv := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((ambientShift_uncurry_contDiffAt t).fderiv
    (contDiffAt_const : ContDiffAt ℝ 0
      (fun _ : ℝ => PeripheralOrientation.basePoint) t) (by simp)).continuousAt

theorem ambientShift_zero : ambientShift 0 = id := by
  funext p
  rw [ambientShift_eq_stereo_rotate, Milnor.rotate_zero, Milnor.rotate_zero]
  exact AlgebraicTrefoil.stereo_inverse p

theorem shiftFDeriv_det_zero : (shiftFDeriv 0).det = 1 := by
  rw [shiftFDeriv, ambientShift_zero, fderiv_id]
  change LinearMap.det (LinearMap.id : R3 →ₗ[ℝ] R3) = 1
  exact LinearMap.det_id

theorem shiftFDeriv_det_pos (t : ℝ) : 0 < (shiftFDeriv t).det := by
  have hne := shiftFDeriv_det_ne_zero t
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hzero_mem : 0 ∈ Set.Icc ((shiftFDeriv t).det)
        ((shiftFDeriv 0).det) := by
      rw [shiftFDeriv_det_zero]
      exact ⟨hneg.le, zero_le_one⟩
    obtain ⟨s, hs⟩ := intermediate_value_univ t 0
      (ContinuousLinearMap.continuous_det.comp shiftFDeriv_continuous) hzero_mem
    exact (shiftFDeriv_det_ne_zero s hs).elim
  · exact hpos

theorem shiftFDeriv_tangent (t : ℝ) :
    shiftFDeriv t PeripheralOrientation.tangent =
      deriv AlgebraicTrefoil.curve t := by
  have hshift := ambientShift_hasFDerivAt t
  rw [← PeripheralOrientation.curve_zero] at hshift
  have hleft := hshift.comp_hasDerivAt 0
    PeripheralOrientation.curve_hasDerivAt_zero
  have hcurve : HasDerivAt AlgebraicTrefoil.curve
      (deriv AlgebraicTrefoil.curve t) t :=
    (AlgebraicTrefoil.curve_contDiff.differentiable (by simp) t).hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ => s + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).add_const t
  have hcurve0 : HasDerivAt AlgebraicTrefoil.curve
      (deriv AlgebraicTrefoil.curve t) ((fun s : ℝ => s + t) 0) := by
    simpa using hcurve
  have hright := hcurve0.scomp 0 hinner
  have hfun : ambientShift t ∘ AlgebraicTrefoil.curve =
      fun s => AlgebraicTrefoil.curve (s + t) := by
    funext s
    exact ambientShift_curve s t
  rw [hfun] at hleft
  simpa using hleft.unique hright

theorem detectorMap_ambientShift_of_denom_ne (t : ℝ) (p : R3)
    (hdenom : shiftDenom t p ≠ 0) :
    AlgebraicTrefoil.detectorMap (ambientShift t p) =
      Complex.exp ((((6 : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        AlgebraicTrefoil.detectorMap p := by
  have him :
      (Milnor.rotate 2 t (AlgebraicTrefoil.inverseW p)).im ≠ 1 := by
    intro him
    apply hdenom
    rw [shiftDenom, shiftedWIm_eq_rotate, him]
    ring
  have hsphere :
      Complex.normSq (Milnor.rotate 3 t (AlgebraicTrefoil.inverseZ p)) +
          Complex.normSq (Milnor.rotate 2 t (AlgebraicTrefoil.inverseW p)) =
        1 := by
    rw [Milnor.normSq_rotate, Milnor.normSq_rotate]
    exact AlgebraicTrefoil.inverse_normSq p
  obtain ⟨hz, hw⟩ := AlgebraicTrefoil.inverse_stereo hsphere him
  rw [ambientShift_eq_stereo_rotate, AlgebraicTrefoil.detectorMap, hz, hw]
  exact Milnor.polynomial_weightedRotate t (Milnor.compactify p).1

theorem fderiv_detectorMap_comp_shiftFDeriv (t : ℝ) :
    fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t) ∘L
        shiftFDeriv t =
      (Complex.exp ((((6 : ℝ) * t : ℝ) : ℂ) * Complex.I)) •
        PeripheralOrientation.detectorDifferential := by
  have hdetector : HasFDerivAt AlgebraicTrefoil.detectorMap
      (fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t))
      (AlgebraicTrefoil.curve t) :=
    (AlgebraicTrefoil.detectorMap_contDiff.differentiable (by simp)
      (AlgebraicTrefoil.curve t)).hasFDerivAt
  have hdetectorAt : HasFDerivAt AlgebraicTrefoil.detectorMap
      (fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t))
      (ambientShift t PeripheralOrientation.basePoint) := by
    simpa only [ambientShift_base] using hdetector
  have hleft := hdetectorAt.comp PeripheralOrientation.basePoint
    (ambientShift_hasFDerivAt t)
  have hright := PeripheralOrientation.detectorMap_hasFDerivAt_base.const_mul
    (Complex.exp ((((6 : ℝ) * t : ℝ) : ℂ) * Complex.I))
  have hcontinuous : ContinuousAt (shiftDenom t) PeripheralOrientation.basePoint :=
    shiftDenom_continuous.comp
      (continuous_const.prodMk continuous_id) |>.continuousAt
  have hevent : Filter.EventuallyEq (nhds PeripheralOrientation.basePoint)
      (fun p => AlgebraicTrefoil.detectorMap (ambientShift t p))
      (fun p => Complex.exp ((((6 : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        AlgebraicTrefoil.detectorMap p) := by
    filter_upwards [hcontinuous.eventually_ne (shiftDenom_base_ne t)] with p hp
    exact detectorMap_ambientShift_of_denom_ne t p hp
  have hleft' := hleft.congr_of_eventuallyEq hevent.symm
  exact hleft'.unique hright

theorem complexDet_mul (c a b : ℂ) :
    LocalWinding.complexDet (c * a) (c * b) =
      Complex.normSq c * LocalWinding.complexDet a b := by
  simp [LocalWinding.complexDet, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem frameDet_swap (a u v : R3) :
    Orientation.frameDet a v u = -Orientation.frameDet a u v := by
  simp [Orientation.frameDet, Orientation.frameMatrix, Matrix.det_fin_three]
  ring

theorem complexDet_swap (a b : ℂ) :
    LocalWinding.complexDet b a = -LocalWinding.complexDet a b := by
  simp [LocalWinding.complexDet]
  ring

theorem detector_orientation_pos_of_frame_pos (t : ℝ) (u v : R3)
    (hframe : 0 < Orientation.frameDet (deriv AlgebraicTrefoil.curve t) u v) :
    0 < LocalWinding.complexDet
      (fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t) u)
      (fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t) v) := by
  have hsurj : Function.Surjective (shiftFDeriv t) :=
    LinearMap.surjective_of_injective (shiftFDeriv_injective t)
  obtain ⟨u0, hu0⟩ := hsurj u
  obtain ⟨v0, hv0⟩ := hsurj v
  have hmap := Orientation.frameDet_map (shiftFDeriv t).toLinearMap
    PeripheralOrientation.tangent u0 v0
  change Orientation.frameDet
      (shiftFDeriv t PeripheralOrientation.tangent)
      (shiftFDeriv t u0) (shiftFDeriv t v0) =
    (shiftFDeriv t).det *
      Orientation.frameDet PeripheralOrientation.tangent u0 v0 at hmap
  rw [shiftFDeriv_tangent, hu0, hv0] at hmap
  have hframe0 :
      0 < Orientation.frameDet PeripheralOrientation.tangent u0 v0 := by
    rw [hmap] at hframe
    exact pos_of_mul_pos_right hframe (shiftFDeriv_det_pos t).le
  have hdet0 : 0 < LocalWinding.complexDet
      (PeripheralOrientation.detectorDifferential u0)
      (PeripheralOrientation.detectorDifferential v0) := by
    rw [PeripheralOrientation.detectorDifferential_orientation]
    exact mul_pos (by norm_num) hframe0
  have hdiff := fderiv_detectorMap_comp_shiftFDeriv t
  have hu := congrArg (fun L : R3 →L[ℝ] ℂ => L u0) hdiff
  have hv := congrArg (fun L : R3 →L[ℝ] ℂ => L v0) hdiff
  simp only [ContinuousLinearMap.comp_apply, hu0, hv0, smul_apply] at hu hv
  rw [hu, hv]
  change 0 < LocalWinding.complexDet
    (Complex.exp ((((6 : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      PeripheralOrientation.detectorDifferential u0)
    (Complex.exp ((((6 : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      PeripheralOrientation.detectorDifferential v0)
  rw [complexDet_mul, Milnor.normSq_exp_mul_I]
  simpa using hdet0

theorem detector_orientation_neg_of_frame_neg (t : ℝ) (u v : R3)
    (hframe : Orientation.frameDet (deriv AlgebraicTrefoil.curve t) u v < 0) :
    LocalWinding.complexDet
      (fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t) u)
      (fderiv ℝ AlgebraicTrefoil.detectorMap (AlgebraicTrefoil.curve t) v) < 0 := by
  have hframeSwap :
      0 < Orientation.frameDet (deriv AlgebraicTrefoil.curve t) v u := by
    rw [frameDet_swap]
    linarith
  have hdetSwap := detector_orientation_pos_of_frame_pos t v u hframeSwap
  rw [complexDet_swap] at hdetSwap
  linarith

end

end Submission.DetectorOrientation
