import Submission.JacobianCocycle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Submission.Helpers

open LeanEval.Dynamics

noncomputable def planeQuarterTurn : EucPlane ≃ₗᵢ[ℝ] EucPlane where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 fun i =>
        if i = (0 : Fin 2) then -x.ofLp 1 else x.ofLp 0
      invFun := fun x => WithLp.toLp 2 fun i =>
        if i = (0 : Fin 2) then x.ofLp 1 else -x.ofLp 0
      left_inv := by
        intro x
        ext i
        fin_cases i <;> simp
      right_inv := by
        intro x
        ext i
        fin_cases i <;> simp
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [add_comm]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp }
  norm_map' := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, add_comm]

@[simp]
lemma planeQuarterTurn_apply_zero (x : EucPlane) :
    (planeQuarterTurn x).ofLp 0 = -x.ofLp 1 := by
  simp [planeQuarterTurn]

@[simp]
lemma planeQuarterTurn_apply_one (x : EucPlane) :
    (planeQuarterTurn x).ofLp 1 = x.ofLp 0 := by
  simp [planeQuarterTurn]

@[simp]
lemma planeQuarterTurn_symm_apply_zero (x : EucPlane) :
    (planeQuarterTurn.symm x).ofLp 0 = x.ofLp 1 := by
  change (WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then x.ofLp 1 else -x.ofLp 0)).ofLp 0 = x.ofLp 1
  simp

@[simp]
lemma planeQuarterTurn_symm_apply_one (x : EucPlane) :
    (planeQuarterTurn.symm x).ofLp 1 = -x.ofLp 0 := by
  change (WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then x.ofLp 1 else -x.ofLp 0)).ofLp 1 = -x.ofLp 0
  simp

lemma norm_linearIsometryEquiv_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (e : F ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap ∘L A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro x
    simpa using A.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (e.toContinuousLinearEquiv.toContinuousLinearMap ∘L A))
    intro x
    simpa using
      (e.toContinuousLinearEquiv.toContinuousLinearMap ∘L A).le_opNorm x

lemma norm_comp_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (e : E ≃ₗᵢ[ℝ] E) :
    ‖A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro x
    simpa using A.le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap))
    intro x
    calc
      ‖A x‖ = ‖(A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap) (e.symm x)‖ := by
        simp
      _ ≤ ‖A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap‖ * ‖e.symm x‖ :=
        (A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm _
      _ = ‖A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap‖ * ‖x‖ := by
        rw [e.symm.norm_map]

noncomputable def planeAdjugate
    (A : EucPlane →L[ℝ] EucPlane) : EucPlane →L[ℝ] EucPlane :=
  planeQuarterTurn.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (ContinuousLinearMap.adjoint A ∘L
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap)

lemma norm_planeAdjugate (A : EucPlane →L[ℝ] EucPlane) :
    ‖planeAdjugate A‖ = ‖A‖ := by
  rw [planeAdjugate, norm_linearIsometryEquiv_comp,
    norm_comp_linearIsometryEquiv]
  exact ContinuousLinearMap.adjoint.norm_map A

lemma toMatrix_planeQuarterTurn :
    (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
        planeQuarterTurn.toLinearEquiv.toLinearMap =
      !![(0 : ℝ), -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

lemma toMatrix_planeQuarterTurn_symm :
    (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
        planeQuarterTurn.symm.toLinearEquiv.toLinearMap =
      !![(0 : ℝ), 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

lemma comp_planeAdjugate (A : EucPlane →L[ℝ] EucPlane) :
    A ∘L planeAdjugate A =
      A.toLinearMap.det • ContinuousLinearMap.id ℝ EucPlane := by
  apply ContinuousLinearMap.ext
  intro x
  have hlin :
      A.toLinearMap ∘ₗ (planeAdjugate A).toLinearMap =
        A.toLinearMap.det • LinearMap.id := by
    apply (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).injective
    rw [LinearMap.toMatrix_comp
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      A.toLinearMap (planeAdjugate A).toLinearMap]
    rw [show (planeAdjugate A).toLinearMap =
        planeQuarterTurn.symm.toLinearEquiv.toLinearMap ∘ₗ
          ((ContinuousLinearMap.adjoint A).toLinearMap ∘ₗ
            planeQuarterTurn.toLinearEquiv.toLinearMap) by rfl]
    rw [LinearMap.toMatrix_comp
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    rw [LinearMap.toMatrix_comp
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    rw [toMatrix_planeQuarterTurn, toMatrix_planeQuarterTurn_symm]
    rw [← ContinuousLinearMap.adjoint_toLinearMap A]
    rw [LinearMap.toMatrix_adjoint]
    rw [← LinearMap.det_toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    rw [map_smul, LinearMap.toMatrix_id]
    let M := (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap
    change M * (!![(0 : ℝ), 1; -1, 0] *
      (M.conjTranspose * !![(0 : ℝ), -1; 1, 0])) = M.det • 1
    rw [Matrix.det_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    <;> ring
  exact LinearMap.congr_fun hlin x

lemma planeAdjugate_eq_det_smul_inverse
    (A A_inv : EucPlane →L[ℝ] EucPlane)
    (hleft : A_inv ∘L A = ContinuousLinearMap.id ℝ EucPlane) :
    planeAdjugate A = A.toLinearMap.det • A_inv := by
  apply ContinuousLinearMap.ext
  intro x
  calc
    planeAdjugate A x =
        (A_inv ∘L A) (planeAdjugate A x) := by rw [hleft]; simp
    _ = A_inv ((A ∘L planeAdjugate A) x) := rfl
    _ = A_inv ((A.toLinearMap.det •
        ContinuousLinearMap.id ℝ EucPlane) x) := by rw [comp_planeAdjugate]
    _ = (A.toLinearMap.det • A_inv) x := by simp

lemma norm_eq_abs_det_mul_norm_inverse
    (A A_inv : EucPlane →L[ℝ] EucPlane)
    (hleft : A_inv ∘L A = ContinuousLinearMap.id ℝ EucPlane) :
    ‖A‖ = |A.toLinearMap.det| * ‖A_inv‖ := by
  rw [← norm_planeAdjugate A,
    planeAdjugate_eq_det_smul_inverse A A_inv hleft, norm_smul,
    Real.norm_eq_abs]

lemma log_abs_det_eq_log_norm_sub_log_norm_inverse
    (A A_inv : EucPlane →L[ℝ] EucPlane)
    (hleft : A_inv ∘L A = ContinuousLinearMap.id ℝ EucPlane)
    (hdet : A.toLinearMap.det ≠ 0) :
    Real.log |A.toLinearMap.det| = Real.log ‖A‖ - Real.log ‖A_inv‖ := by
  have hA_inv : A_inv ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun y : EucPlane => y.ofLp 0)
      (congrArg (fun L : EucPlane →L[ℝ] EucPlane =>
        L (EuclideanSpace.single 0 1)) hleft)
    simp [hzero] at hcoord
  have hA_inv_norm : ‖A_inv‖ ≠ 0 := norm_ne_zero_iff.mpr hA_inv
  rw [norm_eq_abs_det_mul_norm_inverse A A_inv hleft]
  rw [Real.log_mul (abs_ne_zero.mpr hdet) hA_inv_norm]
  ring

end Submission.Helpers
