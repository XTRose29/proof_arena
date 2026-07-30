import Submission.SphereDegreeHomotopy
import Submission.SphereSmoothBubbleCore

open scoped ContDiff

noncomputable section

namespace Submission.SphereSmoothBubbleDegree

open Submission.SphereRegularApprox
open Submission.SphereDegreeHomotopy
open Submission.SphereSmoothBubble

def coordinateCLM (i : Fin 3) :
    Space →L[ℝ] ℝ where
  toFun u := u i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_apply i

@[simp]
theorem coordinateCLM_apply (i : Fin 3) (u : Space) :
    coordinateCLM i u = u i :=
  rfl

def targetCoordinateCLM (i : Fin 4) :
    Target 2 →L[ℝ] ℝ where
  toFun y := y i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont :=
    PiLp.continuous_apply 2
      (fun _ : Fin 4 => ℝ) i

@[simp]
theorem targetCoordinateCLM_apply (i : Fin 4)
    (y : Target 2) :
    targetCoordinateCLM i y = y i :=
  rfl

def radiusSqFDeriv (u : Space) :
    Space →L[ℝ] ℝ :=
  ∑ i, ((2 : ℕ) • u i ^ (2 - 1)) • coordinateCLM i

@[simp]
theorem radiusSqFDeriv_apply (u v : Space) :
    radiusSqFDeriv u v =
      2 * ∑ i, u i * v i := by
  simp [radiusSqFDeriv, Finset.mul_sum, mul_assoc]

theorem hasFDerivAt_radiusSq (u : Space) :
    HasFDerivAt radiusSq (radiusSqFDeriv u) u := by
  unfold radiusSq radiusSqFDeriv
  exact
    HasFDerivAt.fun_sum
      (u := Finset.univ)
      (fun i _ =>
        ((coordinateCLM i).hasFDerivAt (x := u)).pow 2)

theorem fderiv_radiusSq (u : Space) :
    fderiv ℝ radiusSq u = radiusSqFDeriv u :=
  (hasFDerivAt_radiusSq u).fderiv

def glueDeriv (x : ℝ) : ℝ :=
  x⁻¹ ^ 2 * expNegInvGlue x

theorem hasDerivAt_expNegInvGlue (x : ℝ) :
    HasDerivAt expNegInvGlue (glueDeriv x) x := by
  simpa [glueDeriv] using
    (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (1 : Polynomial ℝ) x)

def bumpFDeriv (u : Space) :
    Space →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ
      (glueDeriv (1 - radiusSq u))).comp
    (-radiusSqFDeriv u)

theorem hasFDerivAt_bump (u : Space) :
    HasFDerivAt bump (bumpFDeriv u) u := by
  have hinner :
      HasFDerivAt (fun w : Space => 1 - radiusSq w)
        (-radiusSqFDeriv u) u := by
    exact (hasFDerivAt_radiusSq u).const_sub 1
  change
    HasFDerivAt
      (expNegInvGlue ∘ fun w : Space => 1 - radiusSq w)
      (bumpFDeriv u) u
  exact
    (hasDerivAt_expNegInvGlue
      (1 - radiusSq u)).hasFDerivAt.comp u hinner

theorem fderiv_bump (u : Space) :
    fderiv ℝ bump u = bumpFDeriv u :=
  (hasFDerivAt_bump u).fderiv

theorem glueDeriv_nonneg (x : ℝ) :
    0 ≤ glueDeriv x :=
  mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)

theorem fderiv_bump_self_nonpos (u : Space) :
    fderiv ℝ bump u u ≤ 0 := by
  rw [fderiv_bump]
  simp only [bumpFDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  have hradius : 0 ≤ radiusSqFDeriv u u := by
    rw [radiusSqFDeriv_apply]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  change
    (-(radiusSqFDeriv u u)) *
      glueDeriv (1 - radiusSq u) ≤ 0
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hradius)
    (glueDeriv_nonneg _)

theorem fderiv_raw_castSucc
    (u v : Space) (i : Fin 3) :
    fderiv ℝ raw u v i.castSucc =
      2 * (fderiv ℝ bump u v * u i +
        bump u * v i) := by
  have hdiff : DifferentiableAt ℝ raw u :=
    (contDiff_raw.differentiable
      (by norm_num)).differentiableAt
  have happly :
      fderiv ℝ (fun w : Space => raw w i.castSucc) u =
        (targetCoordinateCLM i.castSucc).comp
          (fderiv ℝ raw u) :=
    ((targetCoordinateCLM i.castSucc).hasFDerivAt.comp u
      hdiff.hasFDerivAt).fderiv
  have hcoord' :
      fderiv ℝ (fun w : Space => raw w i.castSucc) u v =
        fderiv ℝ raw u v i.castSucc := by
    simpa only [ContinuousLinearMap.comp_apply,
      targetCoordinateCLM_apply] using
        congrArg (fun L => L v) happly
  rw [← hcoord']
  rw [show (fun w : Space => raw w i.castSucc) =
      fun w : Space => 2 * bump w * w i by
    funext w
    exact raw_castSucc w i]
  have hproduct :=
    ((hasFDerivAt_bump u).const_mul 2).mul
      (coordinateCLM i).hasFDerivAt
  change
    fderiv ℝ
        ((fun y : Space => 2 * bump y) *
          (coordinateCLM i : Space → ℝ)) u v =
      2 * (fderiv ℝ bump u v * u i + bump u * v i)
  rw [hproduct.fderiv, fderiv_bump]
  simp [coordinateCLM]
  ring

theorem fderiv_raw_last
    (u v : Space) :
    fderiv ℝ raw u v (Fin.last 3) =
      2 * bump u * fderiv ℝ bump u v -
        2 * ∑ i, u i * v i := by
  have hdiff : DifferentiableAt ℝ raw u :=
    (contDiff_raw.differentiable
      (by norm_num)).differentiableAt
  have happly :
      fderiv ℝ
          (fun w : Space => raw w (Fin.last 3)) u =
        (targetCoordinateCLM (Fin.last 3)).comp
          (fderiv ℝ raw u) :=
    ((targetCoordinateCLM (Fin.last 3)).hasFDerivAt.comp u
      hdiff.hasFDerivAt).fderiv
  have hcoord' :
      fderiv ℝ (fun w : Space => raw w (Fin.last 3)) u v =
        fderiv ℝ raw u v (Fin.last 3) := by
    simpa only [ContinuousLinearMap.comp_apply,
      targetCoordinateCLM_apply] using
        congrArg (fun L => L v) happly
  rw [← hcoord']
  rw [show (fun w : Space => raw w (Fin.last 3)) =
      fun w : Space => bump w ^ 2 - radiusSq w by
    funext w
    exact raw_last w]
  have hdifference :=
    ((hasFDerivAt_bump u).pow 2).sub
      (hasFDerivAt_radiusSq u)
  change
    fderiv ℝ ((fun x : Space => bump x ^ 2) - radiusSq)
        u v =
      2 * bump u * fderiv ℝ bump u v -
        2 * ∑ i, u i * v i
  rw [hdifference.fderiv, fderiv_bump]
  simp [radiusSqFDeriv_apply]

theorem fderiv_sphereMap_apply
    (u v : Space) :
    fderiv ℝ sphereMap u v =
      fderiv ℝ (fun w : Space => (denominator w)⁻¹) u v • raw u +
        (denominator u)⁻¹ • fderiv ℝ raw u v := by
  rw [show sphereMap =
      fun w : Space => (denominator w)⁻¹ • raw w by
    funext w
    exact sphereMap_formula w]
  have hden : DifferentiableAt ℝ
      (fun w : Space => (denominator w)⁻¹) u :=
    ((contDiff_denominator.inv fun w =>
      (denominator_pos w).ne').differentiable (by simp)) u
  have hraw : DifferentiableAt ℝ raw u :=
    (contDiff_raw.differentiable (by simp)) u
  rw [fderiv_fun_smul hden hraw]
  simp only [add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, add_comm]

private theorem space_eq_linear_combination (u : Space) :
    u =
      u 0 • spatialFrame (m := 2) 0 +
      u 1 • spatialFrame (m := 2) 1 +
      u 2 • spatialFrame (m := 2) 2 := by
  funext i
  fin_cases i <;> simp [spatialFrame]

private theorem fderiv_bump_self
    (u : Space) :
    fderiv ℝ bump u u =
      u 0 * fderiv ℝ bump u (spatialFrame 0) +
      u 1 * fderiv ℝ bump u (spatialFrame 1) +
      u 2 * fderiv ℝ bump u (spatialFrame 2) := by
  calc
    fderiv ℝ bump u u =
        fderiv ℝ bump u
          (u 0 • spatialFrame (m := 2) 0 +
            u 1 • spatialFrame (m := 2) 1 +
            u 2 • spatialFrame (m := 2) 2) :=
      congrArg (fderiv ℝ bump u) (space_eq_linear_combination u)
    _ = _ := by
      simp only [map_add, map_smul, smul_eq_mul]

private theorem det_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
        A 0 0 *
          (A 1 1 * A 2 2 * A 3 3 -
            A 1 1 * A 2 3 * A 3 2 -
            A 1 2 * A 2 1 * A 3 3 +
            A 1 2 * A 2 3 * A 3 1 +
            A 1 3 * A 2 1 * A 3 2 -
            A 1 3 * A 2 2 * A 3 1) -
        A 0 1 *
          (A 1 0 * A 2 2 * A 3 3 -
            A 1 0 * A 2 3 * A 3 2 -
            A 1 2 * A 2 0 * A 3 3 +
            A 1 2 * A 2 3 * A 3 0 +
            A 1 3 * A 2 0 * A 3 2 -
            A 1 3 * A 2 2 * A 3 0) +
        A 0 2 *
          (A 1 0 * A 2 1 * A 3 3 -
            A 1 0 * A 2 3 * A 3 1 -
            A 1 1 * A 2 0 * A 3 3 +
            A 1 1 * A 2 3 * A 3 0 +
            A 1 3 * A 2 0 * A 3 1 -
            A 1 3 * A 2 1 * A 3 0) -
        A 0 3 *
          (A 1 0 * A 2 1 * A 3 2 -
            A 1 0 * A 2 2 * A 3 1 -
            A 1 1 * A 2 0 * A 3 2 +
            A 1 1 * A 2 2 * A 3 0 +
            A 1 2 * A 2 0 * A 3 1 -
            A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [Fin.succAbove]
  simp_all
  ring

set_option maxHeartbeats 2000000 in
/-- Explicit Jacobian formula for the compact stereographic bubble. -/
theorem density_sphereMap (u : Space) :
    density sphereMap u =
      -8 * bump u ^ 2 *
        (bump u - fderiv ℝ bump u u) /
          denominator u ^ 3 := by
  rw [density, SphereDegreeInvariant.pulledVolumeForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    SphereDegreeForm.volumeForm_apply_det]
  have hF :
      ∀ v : Space,
        fderiv ℝ sphereMap u v =
          fderiv ℝ (fun w : Space => (denominator w)⁻¹) u v • raw u +
            (denominator u)⁻¹ • fderiv ℝ raw u v :=
    fderiv_sphereMap_apply u
  have hraw0 (v : Space) :
      fderiv ℝ raw u v (0 : Fin 4) =
        2 * (fderiv ℝ bump u v * u 0 + bump u * v 0) := by
    simpa using fderiv_raw_castSucc u v (0 : Fin 3)
  have hraw1 (v : Space) :
      fderiv ℝ raw u v (1 : Fin 4) =
        2 * (fderiv ℝ bump u v * u 1 + bump u * v 1) := by
    simpa using fderiv_raw_castSucc u v (1 : Fin 3)
  have hraw2 (v : Space) :
      fderiv ℝ raw u v (2 : Fin 4) =
        2 * (fderiv ℝ bump u v * u 2 + bump u * v 2) := by
    simpa using fderiv_raw_castSucc u v (2 : Fin 3)
  have hraw3 (v : Space) :
      fderiv ℝ raw u v (3 : Fin 4) =
        2 * bump u * fderiv ℝ bump u v -
          2 * ∑ i, u i * v i := by
    simpa using fderiv_raw_last u v
  have hvalue0 :
      raw u (0 : Fin 4) = 2 * bump u * u 0 := by
    simpa using raw_castSucc u (0 : Fin 3)
  have hvalue1 :
      raw u (1 : Fin 4) = 2 * bump u * u 1 := by
    simpa using raw_castSucc u (1 : Fin 3)
  have hvalue2 :
      raw u (2 : Fin 4) = 2 * bump u * u 2 := by
    simpa using raw_castSucc u (2 : Fin 3)
  have hvalue3 :
      raw u (3 : Fin 4) = bump u ^ 2 - radiusSq u := by
    simpa using raw_last u
  rw [sphereMap_formula, det_fin_four]
  simp [hF, spatialFrame, hraw0, hraw1, hraw2, hraw3,
    hvalue0, hvalue1, hvalue2, hvalue3]
  rw [fderiv_bump_self]
  field_simp [denominator_pos u |>.ne']
  simp [denominator, radiusSq, Fin.sum_univ_three, spatialFrame]
  ring

theorem neg_density_sphereMap_nonneg (u : Space) :
    0 ≤ -density sphereMap u := by
  rw [density_sphereMap]
  have hb := bump_nonneg u
  have hdiff :
      0 ≤ bump u - fderiv ℝ bump u u := by
    linarith [fderiv_bump_self_nonpos u]
  have hd : 0 < denominator u ^ 3 :=
    pow_pos (denominator_pos u) _
  simp only [neg_div, neg_mul, neg_neg]
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) hdiff)
    hd.le

theorem density_sphereMap_zero_ne :
    density sphereMap 0 ≠ 0 := by
  rw [density_sphereMap]
  have hb : 0 < bump (0 : Space) :=
    bump_pos_of_radiusSq_lt_one (by simp [radiusSq])
  have hdb :
      fderiv ℝ bump (0 : Space) 0 = 0 := map_zero _
  rw [hdb, sub_zero]
  have hd := denominator_pos (0 : Space)
  positivity

theorem fderiv_localCoordinates
    (x : Space) :
    fderiv ℝ localCoordinates x =
      (4 : ℝ) • ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  ext i
  have hcoord := congrArg
    (fun L : Space →L[ℝ] ℝ => L v)
    (fderiv_apply
      (Φ := localCoordinates)
      (x := x)
      ((contDiff_localCoordinates.differentiable
        (by norm_num)).differentiableAt) i)
  have hcoord' :
      fderiv ℝ (fun y : Space => localCoordinates y i) x v =
        fderiv ℝ localCoordinates x v i := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hcoord
  rw [← hcoord']
  change
    fderiv ℝ (fun y : Space => 4 * (y i - 1 / 2)) x v =
      4 * v i
  have h :
      HasFDerivAt
        (fun y : Space => 4 * (y i - 1 / 2))
        ((4 : ℝ) • coordinateCLM i) x := by
    exact
      ((coordinateCLM i).hasFDerivAt.sub_const
        (1 / 2)).const_mul 4
  rw [h.fderiv]
  rfl

theorem density_smoothMap (x : Space) :
    density SphereSmoothBubble.smoothMap x =
      64 * density sphereMap (localCoordinates x) := by
  rw [density, SphereDegreeInvariant.pulledVolumeForm]
  change
    SphereDegreeForm.volumeForm 2
        (sphereMap (localCoordinates x))
        (fun i =>
          fderiv ℝ (sphereMap ∘ localCoordinates) x
            (spatialFrame i)) =
      _
  rw [fderiv_comp x
    ((contDiff_sphereMap.differentiable
      (by norm_num)).differentiableAt)
    ((contDiff_localCoordinates.differentiable
      (by norm_num)).differentiableAt),
    fderiv_localCoordinates]
  simp only [ContinuousLinearMap.comp_apply,
    smul_apply,
    ContinuousLinearMap.id_apply]
  change
    SphereDegreeForm.volumeForm 2
        (sphereMap (localCoordinates x))
        (fun i =>
          fderiv ℝ sphereMap (localCoordinates x)
            ((4 : ℝ) • spatialFrame i)) =
      _
  have hvec :
      (fun i : Fin 3 =>
        fderiv ℝ sphereMap (localCoordinates x)
          ((4 : ℝ) • spatialFrame i)) =
        (fun i : Fin 3 =>
          (4 : ℝ) • fderiv ℝ sphereMap (localCoordinates x)
            (spatialFrame i)) := by
    funext i
    exact map_smul (fderiv ℝ sphereMap (localCoordinates x))
      (4 : ℝ) (spatialFrame i)
  rw [hvec]
  rw [ContinuousAlternatingMap.map_smul_univ]
  norm_num
  rw [density, SphereDegreeInvariant.pulledVolumeForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    SphereDegreeForm.volumeForm_apply_det]
  exact SphereDegreeForm.determinantForm_apply 2 _

theorem neg_density_smoothMap_nonneg (x : Space) :
    0 ≤ -density SphereSmoothBubble.smoothMap x := by
  rw [density_smoothMap]
  have := neg_density_sphereMap_nonneg (localCoordinates x)
  linarith

def center : Space :=
  fun _ => 1 / 2

theorem localCoordinates_center :
    localCoordinates center = 0 := by
  funext i
  norm_num [localCoordinates, center]

theorem density_smoothMap_center_ne :
    density SphereSmoothBubble.smoothMap center ≠ 0 := by
  rw [density_smoothMap, localCoordinates_center]
  exact mul_ne_zero (by norm_num) density_sphereMap_zero_ne

end Submission.SphereSmoothBubbleDegree
