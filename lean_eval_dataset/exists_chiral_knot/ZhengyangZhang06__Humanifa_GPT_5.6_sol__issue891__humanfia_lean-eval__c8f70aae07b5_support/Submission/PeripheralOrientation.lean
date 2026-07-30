import Submission.LocalWinding

open LeanEval.KnotTheory

namespace Submission.PeripheralOrientation

noncomputable section

def point (x y z : ℝ) : R3 :=
  WithLp.toLp 2 ![x, y, z]

def basePoint : R3 := point (3 / 5) 0 (-4 / 5)

def tangent : R3 := point (-24 / 25) (9 / 5) (32 / 25)

def e0 : R3 := point 1 0 0

def e1 : R3 := point 0 1 0

def detectorRealPart : R3 →L[ℝ] ℝ :=
  (11328 / 125 : ℝ) • EuclideanSpace.proj 0 +
    (8496 / 125 : ℝ) • EuclideanSpace.proj 2

def detectorImagPart : R3 →L[ℝ] ℝ :=
  (1296 / 25 : ℝ) • EuclideanSpace.proj 0 +
    (384 / 5 : ℝ) • EuclideanSpace.proj 1 -
      (1728 / 25 : ℝ) • EuclideanSpace.proj 2

def detectorDifferential : R3 →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    (detectorRealPart.prod detectorImagPart)

@[simp] theorem detectorDifferential_re (u : R3) :
    (detectorDifferential u).re =
      (11328 / 125 : ℝ) * u.ofLp 0 +
        (8496 / 125 : ℝ) * u.ofLp 2 := by
  simp [detectorDifferential, detectorRealPart]

@[simp] theorem detectorDifferential_im (u : R3) :
    (detectorDifferential u).im =
      (1296 / 25 : ℝ) * u.ofLp 0 +
        (384 / 5 : ℝ) * u.ofLp 1 -
          (1728 / 25 : ℝ) * u.ofLp 2 := by
  simp [detectorDifferential, detectorImagPart]

theorem detectorDifferential_orientation (u v : R3) :
    LocalWinding.complexDet (detectorDifferential u)
        (detectorDifferential v) =
      (135936 / 25 : ℝ) * Orientation.frameDet tangent u v := by
  simp [LocalWinding.complexDet, Orientation.frameDet,
    Orientation.frameMatrix, Matrix.det_fin_three, tangent,
    detectorDifferential_re, detectorDifferential_im, point]
  ring

theorem frameDet_tangent_e0_e1 :
    Orientation.frameDet tangent e0 e1 = 32 / 25 := by
  have hmatrix : Orientation.frameMatrix tangent e0 e1 =
      !![-(24 / 25 : ℝ), 1, 0; 9 / 5, 0, 1; 32 / 25, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Orientation.frameMatrix, tangent, e0, e1, point]
  rw [Orientation.frameDet, hmatrix, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one]

theorem detectorDifferential_e0_e1_pos :
    0 < LocalWinding.complexDet (detectorDifferential e0)
      (detectorDifferential e1) := by
  rw [detectorDifferential_orientation, frameDet_tangent_e0_e1]
  norm_num

private abbrev CoordinateSpace := Fin 3 → ℝ

private def rawRadius (x : CoordinateSpace) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

private def rawDenom (x : CoordinateSpace) : ℝ := rawRadius x + 1

private def rawZ (x : CoordinateSpace) : ℂ :=
  ⟨2 * x 0 * (rawDenom x)⁻¹, 2 * x 1 * (rawDenom x)⁻¹⟩

private def rawW (x : CoordinateSpace) : ℂ :=
  ⟨2 * x 2 * (rawDenom x)⁻¹,
    (rawRadius x - 1) * (rawDenom x)⁻¹⟩

private def rawDetector (x : CoordinateSpace) : ℂ :=
  64 * rawZ x ^ 2 + 45 * rawW x ^ 3

private def rawBase : CoordinateSpace := ![3 / 5, 0, -4 / 5]

private def rawRadiusDifferential : CoordinateSpace →L[ℝ] ℝ :=
  (6 / 5 : ℝ) • ContinuousLinearMap.proj 0 -
    (8 / 5 : ℝ) • ContinuousLinearMap.proj 2

private theorem rawRadiusDifferential_apply (u : CoordinateSpace) :
    rawRadiusDifferential u = 6 / 5 * u 0 - 8 / 5 * u 2 := by
  simp [rawRadiusDifferential]

private def rawDetectorRealPart : CoordinateSpace →L[ℝ] ℝ :=
  (11328 / 125 : ℝ) • ContinuousLinearMap.proj 0 +
    (8496 / 125 : ℝ) • ContinuousLinearMap.proj 2

private def rawDetectorImagPart : CoordinateSpace →L[ℝ] ℝ :=
  (1296 / 25 : ℝ) • ContinuousLinearMap.proj 0 +
    (384 / 5 : ℝ) • ContinuousLinearMap.proj 1 -
      (1728 / 25 : ℝ) • ContinuousLinearMap.proj 2

private def rawDetectorDifferential : CoordinateSpace →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    (rawDetectorRealPart.prod rawDetectorImagPart)

private theorem rawRadius_hasFDerivAt :
    HasFDerivAt rawRadius rawRadiusDifferential rawBase := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x := rawBase)
  have h1 := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt (x := rawBase)
  have h2 := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt (x := rawBase)
  have h := (h0.mul h0).add ((h1.mul h1).add (h2.mul h2))
  change HasFDerivAt
    (fun p : CoordinateSpace => p 0 * p 0 + (p 1 * p 1 + p 2 * p 2))
      _ _ at h
  have hfun :
      (fun p : CoordinateSpace => p 0 * p 0 + (p 1 * p 1 + p 2 * p 2)) =
        rawRadius := by
    funext p
    simp [rawRadius, pow_two]
    ring
  rw [hfun] at h
  apply h.congr_fderiv
  ext u
  simp [rawRadiusDifferential, rawBase]
  ring

private theorem rawDetector_hasFDerivAt :
    HasFDerivAt rawDetector rawDetectorDifferential rawBase := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x := rawBase)
  have h1 := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt (x := rawBase)
  have h2 := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt (x := rawBase)
  have hden := rawRadius_hasFDerivAt.add_const (1 : ℝ)
  have hdenNe : rawDenom rawBase ≠ 0 := by
    norm_num [rawDenom, rawRadius, rawBase, Matrix.cons_val_two,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  have hdenInv := (hasFDerivAt_inv hdenNe).comp rawBase hden
  have hzre := (h0.const_mul (2 : ℝ)).mul hdenInv
  have hzim := (h1.const_mul (2 : ℝ)).mul hdenInv
  have hzpair := hzre.prodMk hzim
  have hz := Complex.equivRealProdCLM.symm.hasFDerivAt.comp rawBase hzpair
  change HasFDerivAt rawZ _ rawBase at hz
  have hwre := (h2.const_mul (2 : ℝ)).mul hdenInv
  have hwim := (rawRadius_hasFDerivAt.sub_const (1 : ℝ)).mul hdenInv
  have hwpair := hwre.prodMk hwim
  have hw := Complex.equivRealProdCLM.symm.hasFDerivAt.comp rawBase hwpair
  change HasFDerivAt rawW _ rawBase at hw
  have hp := (hz.pow 2).const_mul (64 : ℂ) |>.add
    ((hw.pow 3).const_mul (45 : ℂ))
  change HasFDerivAt rawDetector _ rawBase at hp
  apply hp.congr_fderiv
  ext u
  apply Complex.ext <;>
    norm_num [rawDetectorDifferential, rawDetectorRealPart,
      rawDetectorImagPart, rawBase, rawZ, rawW, rawDenom, rawRadius,
      Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero,
      pow_two] <;>
    rw [rawRadiusDifferential_apply] <;>
    ring

theorem detectorMap_hasFDerivAt_base :
    HasFDerivAt AlgebraicTrefoil.detectorMap detectorDifferential basePoint := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hbase : e basePoint = rawBase := by
    funext i
    fin_cases i <;> norm_num [e, basePoint, point, rawBase]
  have hraw := rawDetector_hasFDerivAt
  rw [← hbase] at hraw
  have hcomp := hraw.comp basePoint e.hasFDerivAt
  have hfun : rawDetector ∘ e = AlgebraicTrefoil.detectorMap := by
    funext p
    rfl
  rw [hfun] at hcomp
  apply hcomp.congr_fderiv
  ext u
  apply Complex.ext <;>
    simp [rawDetectorDifferential, rawDetectorRealPart,
      rawDetectorImagPart, e, detectorDifferential, detectorRealPart,
      detectorImagPart]

theorem fderiv_detectorMap_base :
    fderiv ℝ AlgebraicTrefoil.detectorMap basePoint = detectorDifferential :=
  detectorMap_hasFDerivAt_base.fderiv

theorem curve_zero : AlgebraicTrefoil.curve 0 = basePoint := by
  ext i
  fin_cases i <;>
    norm_num [AlgebraicTrefoil.curve, AlgebraicTrefoil.stereo,
      AlgebraicTrefoil.sphereCurveZ, AlgebraicTrefoil.sphereCurveW,
      basePoint, point]

theorem curve_hasDerivAt_zero :
    HasDerivAt AlgebraicTrefoil.curve tangent 0 := by
  let coords : ℝ → Fin 3 → ℝ := fun t =>
    ![(3 / 5) * Real.cos (3 * t) /
        (1 - (-4 / 5) * Real.sin (2 * t)),
      (3 / 5) * Real.sin (3 * t) /
        (1 - (-4 / 5) * Real.sin (2 * t)),
      (-4 / 5) * Real.cos (2 * t) /
        (1 - (-4 / 5) * Real.sin (2 * t))]
  let velocity : Fin 3 → ℝ := ![-24 / 25, 9 / 5, 32 / 25]
  have htoLp : HasDerivAt
      (fun t => WithLp.toLp 2 (coords t))
      (WithLp.toLp 2 velocity) 0 := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
      |>.hasFDerivAt.comp_hasDerivAt 0
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · have htwo := (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
      have hthree := (hasDerivAt_id (0 : ℝ)).const_mul (3 : ℝ)
      have hsin2 := (Real.hasDerivAt_sin (2 * (0 : ℝ))).scomp 0 htwo
      have hcos3 := (Real.hasDerivAt_cos (3 * (0 : ℝ))).scomp 0 hthree
      have hden := (hasDerivAt_const 0 (1 : ℝ)).sub
        (hsin2.const_mul (-4 / 5 : ℝ))
      have hquot := (hcos3.const_mul (3 / 5 : ℝ)).div hden (by norm_num)
      have hfun : (fun x => coords x (0 : Fin 3)) =
          ((fun y => (3 / 5 : ℝ) * Real.cos (3 * y)) /
            ((fun _ : ℝ => (1 : ℝ)) -
              fun y => (-4 / 5 : ℝ) * Real.sin (2 * y))) := by
        funext x
        simp [coords]
      simp only [Function.comp_apply] at hquot
      rw [← hfun] at hquot
      simpa [velocity] using hquot.congr_deriv (by norm_num)
    · have htwo := (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
      have hthree := (hasDerivAt_id (0 : ℝ)).const_mul (3 : ℝ)
      have hsin2 := (Real.hasDerivAt_sin (2 * (0 : ℝ))).scomp 0 htwo
      have hsin3 := (Real.hasDerivAt_sin (3 * (0 : ℝ))).scomp 0 hthree
      have hden := (hasDerivAt_const 0 (1 : ℝ)).sub
        (hsin2.const_mul (-4 / 5 : ℝ))
      have hquot := (hsin3.const_mul (3 / 5 : ℝ)).div hden (by norm_num)
      have hfun : (fun x => coords x (1 : Fin 3)) =
          ((fun y => (3 / 5 : ℝ) * Real.sin (3 * y)) /
            ((fun _ : ℝ => (1 : ℝ)) -
              fun y => (-4 / 5 : ℝ) * Real.sin (2 * y))) := by
        funext x
        simp [coords]
      simp only [Function.comp_apply] at hquot
      rw [← hfun] at hquot
      simpa [velocity] using hquot.congr_deriv (by norm_num)
    · have htwo := (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
      have hsin2 := (Real.hasDerivAt_sin (2 * (0 : ℝ))).scomp 0 htwo
      have hcos2 := (Real.hasDerivAt_cos (2 * (0 : ℝ))).scomp 0 htwo
      have hden := (hasDerivAt_const 0 (1 : ℝ)).sub
        (hsin2.const_mul (-4 / 5 : ℝ))
      have hquot := (hcos2.const_mul (-4 / 5 : ℝ)).div hden (by norm_num)
      have hfun : (fun x => coords x (2 : Fin 3)) =
          ((fun y => (-4 / 5 : ℝ) * Real.cos (2 * y)) /
            ((fun _ : ℝ => (1 : ℝ)) -
              fun y => (-4 / 5 : ℝ) * Real.sin (2 * y))) := by
        funext x
        simp [coords]
      simp only [Function.comp_apply] at hquot
      rw [← hfun] at hquot
      simpa [velocity] using hquot.congr_deriv (by norm_num)
  have hcurve : (fun t => WithLp.toLp 2 (coords t)) =
      AlgebraicTrefoil.curve := by
    funext t
    rfl
  rw [hcurve] at htoLp
  simpa [velocity, tangent, point] using htoLp

theorem deriv_curve_zero : deriv AlgebraicTrefoil.curve 0 = tangent :=
  curve_hasDerivAt_zero.deriv

end

end Submission.PeripheralOrientation
