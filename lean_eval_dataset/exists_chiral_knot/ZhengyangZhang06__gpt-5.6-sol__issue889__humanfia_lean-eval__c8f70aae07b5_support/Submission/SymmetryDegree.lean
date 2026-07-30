import Submission.DetectorOrientation
import Submission.AlgebraicPhase

open LeanEval.KnotTheory
open scoped unitInterval

namespace Submission.SymmetryDegree

noncomputable section

abbrev NegativeSymmetry := Symmetry.NegativeSymmetry AlgebraicTrefoil.knot
abbrev Complement := RadialPhase.Complement

def baseParameter (S : NegativeSymmetry) : ℝ := S.sigma.finv 0

def sourcePoint (S : NegativeSymmetry) : R3 :=
  AlgebraicTrefoil.curve (baseParameter S)

@[simp] theorem sigma_baseParameter (S : NegativeSymmetry) :
    S.sigma.f (baseParameter S) = 0 :=
  S.sigma.right_inv 0

@[simp] theorem map_sourcePoint (S : NegativeSymmetry) :
    S.F (sourcePoint S) = PeripheralOrientation.basePoint := by
  change S.F (AlgebraicTrefoil.knot.curve (baseParameter S)) =
    PeripheralOrientation.basePoint
  rw [S.map_curve, sigma_baseParameter]
  change AlgebraicTrefoil.curve 0 = PeripheralOrientation.basePoint
  exact PeripheralOrientation.curve_zero

@[simp] theorem inverse_basePoint (S : NegativeSymmetry) :
    S.Finv PeripheralOrientation.basePoint = sourcePoint S := by
  rw [← map_sourcePoint S]
  exact S.inv_left (sourcePoint S)

def forwardDerivative (S : NegativeSymmetry) : R3 →L[ℝ] R3 :=
  fderiv ℝ S.F (sourcePoint S)

def inverseDerivative (S : NegativeSymmetry) : R3 →L[ℝ] R3 :=
  fderiv ℝ S.Finv PeripheralOrientation.basePoint

theorem forward_hasFDerivAt (S : NegativeSymmetry) :
    HasFDerivAt S.F (forwardDerivative S) (sourcePoint S) :=
  (S.smooth.differentiable (by simp) (sourcePoint S)).hasFDerivAt

theorem inverse_hasFDerivAt (S : NegativeSymmetry) :
    HasFDerivAt S.Finv (inverseDerivative S)
      PeripheralOrientation.basePoint :=
  (S.smooth_inv.differentiable (by simp)
    PeripheralOrientation.basePoint).hasFDerivAt

theorem forward_comp_inverse (S : NegativeSymmetry) :
    forwardDerivative S ∘L inverseDerivative S =
      ContinuousLinearMap.id ℝ R3 := by
  have hforward := forward_hasFDerivAt S
  rw [← inverse_basePoint S] at hforward
  have hcomp := hforward.comp PeripheralOrientation.basePoint
    (inverse_hasFDerivAt S)
  have hfun : S.F ∘ S.Finv = id := by
    funext p
    exact S.inv_right p
  rw [hfun] at hcomp
  exact hcomp.unique (hasFDerivAt_id PeripheralOrientation.basePoint)

theorem forward_inverse_apply (S : NegativeSymmetry) (u : R3) :
    forwardDerivative S (inverseDerivative S u) = u := by
  have h := congrArg (fun L : R3 →L[ℝ] R3 => L u)
    (forward_comp_inverse S)
  simpa using h

def firstNormal (S : NegativeSymmetry) : R3 :=
  inverseDerivative S PeripheralOrientation.e1

def secondNormal (S : NegativeSymmetry) : R3 :=
  inverseDerivative S PeripheralOrientation.e0

theorem forward_tangent (S : NegativeSymmetry) :
    forwardDerivative S
        (deriv AlgebraicTrefoil.curve (baseParameter S)) =
      deriv S.sigma.f (baseParameter S) • PeripheralOrientation.tangent := by
  have hcurve : HasDerivAt AlgebraicTrefoil.curve
      (deriv AlgebraicTrefoil.curve (baseParameter S)) (baseParameter S) :=
    (AlgebraicTrefoil.curve_contDiff.differentiable (by simp)
      (baseParameter S)).hasDerivAt
  have hleft := (forward_hasFDerivAt S).comp_hasDerivAt
    (baseParameter S) hcurve
  have hsigma : HasDerivAt S.sigma.f
      (deriv S.sigma.f (baseParameter S)) (baseParameter S) :=
    (S.sigma.smooth.differentiable (by simp) (baseParameter S)).hasDerivAt
  have htarget : HasDerivAt AlgebraicTrefoil.curve
      (deriv AlgebraicTrefoil.curve (S.sigma.f (baseParameter S)))
      (S.sigma.f (baseParameter S)) :=
    (AlgebraicTrefoil.curve_contDiff.differentiable (by simp)
      (S.sigma.f (baseParameter S))).hasDerivAt
  have hright := htarget.scomp (baseParameter S) hsigma
  have hfun : S.F ∘ AlgebraicTrefoil.curve =
      AlgebraicTrefoil.curve ∘ S.sigma.f := by
    funext t
    exact S.map_curve t
  rw [hfun] at hleft
  have hderiv := hleft.unique hright
  simpa [sigma_baseParameter, PeripheralOrientation.deriv_curve_zero] using hderiv

theorem frameDet_smul_first (r : ℝ) (a u v : R3) :
    Orientation.frameDet (r • a) u v =
      r * Orientation.frameDet a u v := by
  simp [Orientation.frameDet, Orientation.frameMatrix, Matrix.det_fin_three]
  ring

theorem source_frame_pos (S : NegativeSymmetry) :
    0 < Orientation.frameDet
      (deriv AlgebraicTrefoil.curve (baseParameter S))
      (firstNormal S) (secondNormal S) := by
  have hmap := Orientation.frameDet_map (forwardDerivative S).toLinearMap
    (deriv AlgebraicTrefoil.curve (baseParameter S))
    (firstNormal S) (secondNormal S)
  change Orientation.frameDet
      (forwardDerivative S
        (deriv AlgebraicTrefoil.curve (baseParameter S)))
      (forwardDerivative S (firstNormal S))
      (forwardDerivative S (secondNormal S)) =
    (forwardDerivative S).det * Orientation.frameDet
      (deriv AlgebraicTrefoil.curve (baseParameter S))
      (firstNormal S) (secondNormal S) at hmap
  rw [forward_tangent, firstNormal, secondNormal,
    forward_inverse_apply, forward_inverse_apply] at hmap
  have htarget : Orientation.frameDet
      (deriv S.sigma.f (baseParameter S) • PeripheralOrientation.tangent)
      PeripheralOrientation.e1 PeripheralOrientation.e0 < 0 := by
    rw [frameDet_smul_first, DetectorOrientation.frameDet_swap,
      PeripheralOrientation.frameDet_tangent_e0_e1]
    have hsigma := Orientation.circleReparam_deriv_pos S.sigma (baseParameter S)
    nlinarith
  rw [hmap] at htarget
  change (forwardDerivative S).det * Orientation.frameDet
      (deriv AlgebraicTrefoil.curve (baseParameter S))
      (firstNormal S) (secondNormal S) < 0 at htarget
  have hforwardNeg : (forwardDerivative S).det < 0 :=
    S.det_neg (sourcePoint S)
  rcases lt_trichotomy
      (Orientation.frameDet
        (deriv AlgebraicTrefoil.curve (baseParameter S))
        (firstNormal S) (secondNormal S)) 0 with hneg | hzero | hpos
  · have hproduct : 0 < (forwardDerivative S).det *
        Orientation.frameDet
          (deriv AlgebraicTrefoil.curve (baseParameter S))
          (firstNormal S) (secondNormal S) :=
      mul_pos_of_neg_of_neg hforwardNeg hneg
    linarith
  · rw [hzero, mul_zero] at htarget
    exact (lt_irrefl 0 htarget).elim
  · exact hpos

theorem source_detector_orientation_pos (S : NegativeSymmetry) :
    0 < LocalWinding.complexDet
      (fderiv ℝ AlgebraicTrefoil.detectorMap (sourcePoint S) (firstNormal S))
      (fderiv ℝ AlgebraicTrefoil.detectorMap (sourcePoint S) (secondNormal S)) :=
  DetectorOrientation.detector_orientation_pos_of_frame_pos
    (baseParameter S) (firstNormal S) (secondNormal S) (source_frame_pos S)

def imageDetectorDerivative (S : NegativeSymmetry) : R3 →L[ℝ] ℂ :=
  PeripheralOrientation.detectorDifferential.comp (forwardDerivative S)

theorem imageDetector_hasFDerivAt (S : NegativeSymmetry) :
    HasFDerivAt (AlgebraicTrefoil.detectorMap ∘ S.F)
      (imageDetectorDerivative S) (sourcePoint S) := by
  have hdetector := PeripheralOrientation.detectorMap_hasFDerivAt_base
  rw [← map_sourcePoint S] at hdetector
  exact hdetector.comp (sourcePoint S) (forward_hasFDerivAt S)

theorem image_detector_orientation_neg (S : NegativeSymmetry) :
    LocalWinding.complexDet
      (imageDetectorDerivative S (firstNormal S))
      (imageDetectorDerivative S (secondNormal S)) < 0 := by
  change LocalWinding.complexDet
      (PeripheralOrientation.detectorDifferential
        (forwardDerivative S (inverseDerivative S PeripheralOrientation.e1)))
      (PeripheralOrientation.detectorDifferential
        (forwardDerivative S (inverseDerivative S PeripheralOrientation.e0))) < 0
  rw [forward_inverse_apply, forward_inverse_apply,
    DetectorOrientation.complexDet_swap]
  exact neg_lt_zero.mpr PeripheralOrientation.detectorDifferential_e0_e1_pos

def meridianPoint (S : NegativeSymmetry) (r : ℝ) (t : unitInterval) : R3 :=
  sourcePoint S + r • LocalWinding.direction (firstNormal S) (secondNormal S) t

theorem meridianPoint_continuous (S : NegativeSymmetry) (r : ℝ) :
    Continuous (meridianPoint S r) := by
  unfold meridianPoint
  exact continuous_const.add
    (continuous_const.smul
      (LocalWinding.direction_continuous (firstNormal S) (secondNormal S)))

theorem meridianPoint_one_eq_zero (S : NegativeSymmetry) (r : ℝ) :
    meridianPoint S r 1 = meridianPoint S r 0 := by
  simp [meridianPoint, LocalWinding.direction_one,
    LocalWinding.direction_zero]

def sourceDetectorValue (S : NegativeSymmetry) (r : ℝ)
    (t : unitInterval) : ℂ :=
  AlgebraicTrefoil.detectorMap (meridianPoint S r t)

def imageDetectorValue (S : NegativeSymmetry) (r : ℝ)
    (t : unitInterval) : ℂ :=
  AlgebraicTrefoil.detectorMap (S.F (meridianPoint S r t))

theorem sourceDetectorValue_continuous (S : NegativeSymmetry) (r : ℝ) :
    Continuous (sourceDetectorValue S r) :=
  AlgebraicTrefoil.detectorMap_contDiff.continuous.comp
    (meridianPoint_continuous S r)

theorem imageDetectorValue_continuous (S : NegativeSymmetry) (r : ℝ) :
    Continuous (imageDetectorValue S r) :=
  AlgebraicTrefoil.detectorMap_contDiff.continuous.comp
    (S.smooth.continuous.comp (meridianPoint_continuous S r))

theorem sourceDetectorValue_loop (S : NegativeSymmetry) (r : ℝ) :
    sourceDetectorValue S r 1 = sourceDetectorValue S r 0 := by
  rw [sourceDetectorValue, sourceDetectorValue, meridianPoint_one_eq_zero]

theorem imageDetectorValue_loop (S : NegativeSymmetry) (r : ℝ) :
    imageDetectorValue S r 1 = imageDetectorValue S r 0 := by
  rw [imageDetectorValue, imageDetectorValue, meridianPoint_one_eq_zero]

@[simp] theorem detectorMap_sourcePoint (S : NegativeSymmetry) :
    AlgebraicTrefoil.detectorMap (sourcePoint S) = 0 :=
  AlgebraicTrefoil.detectorMap_curve (baseParameter S)

@[simp] theorem detectorMap_image_sourcePoint (S : NegativeSymmetry) :
    AlgebraicTrefoil.detectorMap (S.F (sourcePoint S)) = 0 := by
  rw [map_sourcePoint]
  rw [← PeripheralOrientation.curve_zero]
  exact AlgebraicTrefoil.detectorMap_curve 0

def meridianBase (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) : Complement :=
  ⟨(Milnor.compactify (meridianPoint S r 0)).1, by
    rw [Milnor.polynomial_compactify]
    exact hne 0⟩

def meridianLoop (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) :
    Path (meridianBase S r hne) (meridianBase S r hne) where
  toFun t := ⟨(Milnor.compactify (meridianPoint S r t)).1, by
    rw [Milnor.polynomial_compactify]
    exact hne t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (Milnor.compactify_continuous.comp (meridianPoint_continuous S r))
  source' := rfl
  target' := by
    apply Subtype.ext
    change (Milnor.compactify (meridianPoint S r 1)).1 =
      (Milnor.compactify (meridianPoint S r 0)).1
    exact congrArg (fun p : R3 => (Milnor.compactify p).1)
      (meridianPoint_one_eq_zero S r)

@[simp] theorem meridianLoop_val (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) (t : unitInterval) :
    (meridianLoop S r hne t).1 =
      (Milnor.compactify (meridianPoint S r t)).1 :=
  rfl

def sourcePolynomialValue (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) (t : unitInterval) : ℂ :=
  Milnor.polynomial (meridianLoop S r hne t).1

def imagePolynomialValue (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) (t : unitInterval) : ℂ :=
  Milnor.polynomial
    ((CompactifiedSymmetry.complementHomeomorph S) (meridianLoop S r hne t)).1

theorem sourcePolynomialValue_eq (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) (t : unitInterval) :
    sourcePolynomialValue S r hne t = sourceDetectorValue S r t :=
  rfl

theorem imagePolynomialValue_eq (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) (t : unitInterval) :
    imagePolynomialValue S r hne t = imageDetectorValue S r t := by
  rw [imagePolynomialValue, CompactifiedSymmetry.complementHomeomorph_apply,
    meridianLoop_val,
    CompactifiedSymmetry.sphereHomeomorph_compactify,
    Milnor.polynomial_compactify]
  rfl

theorem sourcePolynomialValue_continuous (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) :
    Continuous (sourcePolynomialValue S r hne) := by
  have hfun : sourcePolynomialValue S r hne = sourceDetectorValue S r := by
    funext t
    exact sourcePolynomialValue_eq S r hne t
  rw [hfun]
  exact sourceDetectorValue_continuous S r

theorem imagePolynomialValue_continuous (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) :
    Continuous (imagePolynomialValue S r hne) := by
  have hfun : imagePolynomialValue S r hne = imageDetectorValue S r := by
    funext t
    exact imagePolynomialValue_eq S r hne t
  rw [hfun]
  exact imageDetectorValue_continuous S r

theorem sourcePolynomialValue_loop (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) :
    sourcePolynomialValue S r hne 1 = sourcePolynomialValue S r hne 0 := by
  rw [sourcePolynomialValue_eq, sourcePolynomialValue_eq,
    sourceDetectorValue_loop]

theorem imagePolynomialValue_loop (S : NegativeSymmetry) (r : ℝ)
    (hne : ∀ t, sourceDetectorValue S r t ≠ 0) :
    imagePolynomialValue S r hne 1 = imagePolynomialValue S r hne 0 := by
  rw [imagePolynomialValue_eq, imagePolynomialValue_eq,
    imageDetectorValue_loop]

theorem induced_degree_eq_neg_one (S : NegativeSymmetry) :
    DeckDegree.degree
      (HomeomorphismDegree.inducedCircleMap
        (CompactifiedSymmetry.complementHomeomorph S)) = -1 := by
  have hsourceDeriv : HasFDerivAt AlgebraicTrefoil.detectorMap
      (fderiv ℝ AlgebraicTrefoil.detectorMap (sourcePoint S))
      (sourcePoint S) :=
    (AlgebraicTrefoil.detectorMap_contDiff.differentiable (by simp)
      (sourcePoint S)).hasFDerivAt
  have hsourceDet := source_detector_orientation_pos S
  obtain ⟨εSource, hεSource, hsourceBound⟩ :=
    LocalWinding.exists_radius_bound_close_fderiv
      hsourceDeriv hsourceDet.ne'
  have himageDet := image_detector_orientation_neg S
  obtain ⟨εImage, hεImage, himageBound⟩ :=
    LocalWinding.exists_radius_bound_close_fderiv
      (imageDetector_hasFDerivAt S) himageDet.ne
  let ε := min εSource εImage
  let r := ε / 2
  have hε : 0 < ε := lt_min hεSource hεImage
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrSource : r < εSource := by
    dsimp [r, ε]
    have hmin : min εSource εImage ≤ εSource := min_le_left _ _
    linarith
  have hrImage : r < εImage := by
    dsimp [r, ε]
    have hmin : min εSource εImage ≤ εImage := min_le_right _ _
    linarith
  have hsourceCloseRaw := hsourceBound r hr hrSource
  have himageCloseRaw := himageBound r hr hrImage
  have hsourceScaledDet : 0 < LocalWinding.complexDet
      ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
        (sourcePoint S) (firstNormal S))
      ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
        (sourcePoint S) (secondNormal S)) := by
    rw [LocalWinding.complexDet_real_smul]
    exact mul_pos (sq_pos_of_pos hr) hsourceDet
  have himageScaledDet : LocalWinding.complexDet
      ((r : ℂ) * imageDetectorDerivative S (firstNormal S))
      ((r : ℂ) * imageDetectorDerivative S (secondNormal S)) < 0 := by
    rw [LocalWinding.complexDet_real_smul]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hr) himageDet
  have hsourceClose : ∀ t : unitInterval,
      ‖sourceDetectorValue S r t -
          LocalWinding.ellipseValue
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (firstNormal S))
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (secondNormal S)) t‖ <
        ‖LocalWinding.ellipseValue
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (firstNormal S))
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (secondNormal S)) t‖ := by
    intro t
    simpa [sourceDetectorValue, meridianPoint, detectorMap_sourcePoint] using
      hsourceCloseRaw t
  have himageClose : ∀ t : unitInterval,
      ‖imageDetectorValue S r t -
          LocalWinding.ellipseValue
            ((r : ℂ) * imageDetectorDerivative S (firstNormal S))
            ((r : ℂ) * imageDetectorDerivative S (secondNormal S)) t‖ <
        ‖LocalWinding.ellipseValue
            ((r : ℂ) * imageDetectorDerivative S (firstNormal S))
            ((r : ℂ) * imageDetectorDerivative S (secondNormal S)) t‖ := by
    intro t
    have htargetZero :
        AlgebraicTrefoil.detectorMap PeripheralOrientation.basePoint = 0 := by
      rw [← PeripheralOrientation.curve_zero]
      exact AlgebraicTrefoil.detectorMap_curve 0
    simpa [imageDetectorValue, meridianPoint, Function.comp_apply,
      detectorMap_image_sourcePoint, htargetZero] using himageCloseRaw t
  have hsourceNe : ∀ t, sourceDetectorValue S r t ≠ 0 :=
    LocalWinding.closeValue_ne_zero hsourceScaledDet.ne' hsourceClose
  let gamma := meridianLoop S r hsourceNe
  have hsourcePolynomialClose : ∀ t : unitInterval,
      ‖sourcePolynomialValue S r hsourceNe t -
          LocalWinding.ellipseValue
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (firstNormal S))
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (secondNormal S)) t‖ <
        ‖LocalWinding.ellipseValue
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (firstNormal S))
            ((r : ℂ) * fderiv ℝ AlgebraicTrefoil.detectorMap
              (sourcePoint S) (secondNormal S)) t‖ := by
    intro t
    rw [sourcePolynomialValue_eq]
    exact hsourceClose t
  have himagePolynomialClose : ∀ t : unitInterval,
      ‖imagePolynomialValue S r hsourceNe t -
          LocalWinding.ellipseValue
            ((r : ℂ) * imageDetectorDerivative S (firstNormal S))
            ((r : ℂ) * imageDetectorDerivative S (secondNormal S)) t‖ <
        ‖LocalWinding.ellipseValue
            ((r : ℂ) * imageDetectorDerivative S (firstNormal S))
            ((r : ℂ) * imageDetectorDerivative S (secondNormal S)) t‖ := by
    intro t
    rw [imagePolynomialValue_eq]
    exact himageClose t
  have hsourceNormalized := LocalWinding.windingReal_normalizedLoopOf_pos
    hsourceScaledDet (sourcePolynomialValue_continuous S r hsourceNe)
    (sourcePolynomialValue_loop S r hsourceNe) hsourcePolynomialClose
  have himageNormalized := LocalWinding.windingReal_normalizedLoopOf_neg
    himageScaledDet (imagePolynomialValue_continuous S r hsourceNe)
    (imagePolynomialValue_loop S r hsourceNe) himagePolynomialClose
  have hsourcePath :
      MeridianDegree.mapLoop AlgebraicPhase.oldPhase gamma =
        LocalWinding.normalizedLoopOf
          (sourcePolynomialValue_continuous S r hsourceNe)
          (sourcePolynomialValue_loop S r hsourceNe)
          (LocalWinding.closeValue_ne_zero hsourceScaledDet.ne'
            hsourcePolynomialClose) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rfl
  have himagePath :
      MeridianDegree.mapLoop
          (AlgebraicPhase.oldPhase.comp
            ⟨CompactifiedSymmetry.complementHomeomorph S,
              (CompactifiedSymmetry.complementHomeomorph S).continuous⟩)
          gamma =
        LocalWinding.normalizedLoopOf
          (imagePolynomialValue_continuous S r hsourceNe)
          (imagePolynomialValue_loop S r hsourceNe)
          (LocalWinding.closeValue_ne_zero himageScaledDet.ne
            himagePolynomialClose) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rfl
  have hsourceOld : CircleWinding.windingReal
      (MeridianDegree.mapLoop AlgebraicPhase.oldPhase gamma) =
        2 * Real.pi := by
    rw [hsourcePath]
    exact hsourceNormalized
  have himageOld : CircleWinding.windingReal
      (MeridianDegree.mapLoop
        (AlgebraicPhase.oldPhase.comp
          ⟨CompactifiedSymmetry.complementHomeomorph S,
            (CompactifiedSymmetry.complementHomeomorph S).continuous⟩)
        gamma) = -(2 * Real.pi) := by
    rw [himagePath]
    exact himageNormalized
  have hphaseComparison := AlgebraicPhase.windingReal_oldPhase_eq_phase gamma
  change CircleWinding.windingReal
      (MeridianDegree.mapLoop AlgebraicPhase.oldPhase gamma) =
    CircleWinding.windingReal (MeridianDegree.phaseLoop gamma) at hphaseComparison
  have hphase : CircleWinding.windingReal (MeridianDegree.phaseLoop gamma) =
      2 * Real.pi := by
    rw [← hphaseComparison]
    exact hsourceOld
  have hdegreeWinding := MeridianDegree.winding_eq_degree_mul_two_pi
    (AlgebraicPhase.oldPhase.comp
      ⟨CompactifiedSymmetry.complementHomeomorph S,
        (CompactifiedSymmetry.complementHomeomorph S).continuous⟩)
    gamma hphase
  rw [himageOld] at hdegreeWinding
  have hdegreeOldComp : DeckDegree.degree
      (AlgebraicPhase.oldPhase.comp
        ⟨CompactifiedSymmetry.complementHomeomorph S,
          (CompactifiedSymmetry.complementHomeomorph S).continuous⟩) = -1 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hcast : (DeckDegree.degree
        (AlgebraicPhase.oldPhase.comp
          ⟨CompactifiedSymmetry.complementHomeomorph S,
            (CompactifiedSymmetry.complementHomeomorph S).continuous⟩) : ℝ) =
        -1 := by
      apply mul_right_cancel₀ htwoPi
      linarith
    exact_mod_cast hcast
  have hcomposition := DegreeAlgebra.degree_comp_homeomorph
    AlgebraicPhase.oldPhase (CompactifiedSymmetry.complementHomeomorph S)
  rw [AlgebraicPhase.degree_oldPhase, one_mul] at hcomposition
  rw [← hcomposition]
  exact hdegreeOldComp

end

end Submission.SymmetryDegree
