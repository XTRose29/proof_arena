import Submission.LyapunovJacobian
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace Submission.Helpers

open LeanEval.Dynamics

noncomputable def planeGram
    (A B : EucPlane →L[ℝ] EucPlane) : EucPlane →L[ℝ] EucPlane :=
  A.adjoint ∘L A + B.adjoint ∘L B

lemma planeAdjugate_comp (A : EucPlane →L[ℝ] EucPlane) :
    planeAdjugate A ∘L A =
      A.toLinearMap.det • ContinuousLinearMap.id ℝ EucPlane := by
  apply ContinuousLinearMap.ext
  intro x
  have hlin :
      (planeAdjugate A).toLinearMap ∘ₗ A.toLinearMap =
        A.toLinearMap.det • LinearMap.id := by
    apply (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).injective
    rw [LinearMap.toMatrix_comp
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (planeAdjugate A).toLinearMap A.toLinearMap]
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
    change (!![(0 : ℝ), 1; -1, 0] *
      (M.conjTranspose * !![(0 : ℝ), -1; 1, 0])) * M = M.det • 1
    rw [Matrix.det_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    <;> ring
  exact LinearMap.congr_fun hlin x

lemma abs_det_mul_norm_le_norm_mul_norm_apply
    (A : EucPlane →L[ℝ] EucPlane) (x : EucPlane) :
    |A.toLinearMap.det| * ‖x‖ ≤ ‖A‖ * ‖A x‖ := by
  calc
    |A.toLinearMap.det| * ‖x‖ =
        ‖(A.toLinearMap.det • ContinuousLinearMap.id ℝ EucPlane) x‖ := by
      simp [norm_smul, Real.norm_eq_abs]
    _ = ‖planeAdjugate A (A x)‖ := by
      simpa only [ContinuousLinearMap.comp_apply] using
        congrArg (fun L : EucPlane →L[ℝ] EucPlane => ‖L x‖)
          (planeAdjugate_comp A).symm
    _ ≤ ‖planeAdjugate A‖ * ‖A x‖ := (planeAdjugate A).le_opNorm (A x)
    _ = ‖A‖ * ‖A x‖ := by rw [norm_planeAdjugate]

lemma norm_planeGram_le (A B : EucPlane →L[ℝ] EucPlane) :
    ‖planeGram A B‖ ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  calc
    ‖planeGram A B‖ ≤ ‖A.adjoint ∘L A‖ + ‖B.adjoint ∘L B‖ := by
      exact norm_add_le _ _
    _ ≤ ‖A.adjoint‖ * ‖A‖ + ‖B.adjoint‖ * ‖B‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
      rw [ContinuousLinearMap.adjoint.norm_map,
        ContinuousLinearMap.adjoint.norm_map]
      ring

lemma norm_planeGram_apply_le
    (A B : EucPlane →L[ℝ] EucPlane) (x : EucPlane) :
    ‖planeGram A B x‖ ≤
      (‖A‖ + ‖B‖) * max ‖A x‖ ‖B x‖ := by
  calc
    ‖planeGram A B x‖ ≤ ‖A.adjoint (A x)‖ + ‖B.adjoint (B x)‖ := by
      exact norm_add_le _ _
    _ ≤ ‖A.adjoint‖ * ‖A x‖ + ‖B.adjoint‖ * ‖B x‖ :=
      add_le_add (A.adjoint.le_opNorm (A x)) (B.adjoint.le_opNorm (B x))
    _ = ‖A‖ * ‖A x‖ + ‖B‖ * ‖B x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map,
        ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖A‖ * max ‖A x‖ ‖B x‖ +
        ‖B‖ * max ‖A x‖ ‖B x‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg A))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg B))
    _ = (‖A‖ + ‖B‖) * max ‖A x‖ ‖B x‖ := by ring

lemma abs_det_planeGram_mul_norm_le
    (A B : EucPlane →L[ℝ] EucPlane) (x : EucPlane) :
    |(planeGram A B).toLinearMap.det| * ‖x‖ ≤
      (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) *
        max ‖A x‖ ‖B x‖ := by
  calc
    |(planeGram A B).toLinearMap.det| * ‖x‖ ≤
        ‖planeGram A B‖ * ‖planeGram A B x‖ :=
      abs_det_mul_norm_le_norm_mul_norm_apply (planeGram A B) x
    _ ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) *
        ((‖A‖ + ‖B‖) * max ‖A x‖ ‖B x‖) := by
      exact mul_le_mul (norm_planeGram_le A B) (norm_planeGram_apply_le A B x)
        (norm_nonneg _) (by positivity)
    _ = (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) *
        max ‖A x‖ ‖B x‖ := by ring

lemma norm_sq_le_matrix_sq_sum (A : EucPlane →L[ℝ] EucPlane) :
    ‖A‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2,
        ((LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap i j) ^ 2 := by
  let M := (LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap
  let F : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, (M i j) ^ 2
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hbound : ‖A‖ ≤ Real.sqrt F := by
    apply A.opNorm_le_bound (Real.sqrt_nonneg F)
    intro x
    have hcoord (i : Fin 2) :
        (A x).ofLp i = ∑ j : Fin 2, M i j * x.ofLp j := by
      have h := congrFun (LinearMap.toMatrix_mulVec_repr
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap x) i
      simpa [M, Matrix.mulVec, dotProduct] using h.symm
    have hrow (i : Fin 2) :
        ((A x).ofLp i) ^ 2 ≤
          (∑ j : Fin 2, (M i j) ^ 2) *
            ∑ j : Fin 2, (x.ofLp j) ^ 2 := by
      rw [hcoord]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j)
        (fun j => x.ofLp j)
    have hsquares : ‖A x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ i : Fin 2, ((A x).ofLp i) ^ 2) ≤
            ∑ i : Fin 2, (∑ j : Fin 2, (M i j) ^ 2) *
              ∑ j : Fin 2, (x.ofLp j) ^ 2 :=
          Finset.sum_le_sum fun i _hi => hrow i
        _ = F * ∑ j : Fin 2, (x.ofLp j) ^ 2 := by
          simp only [F, Finset.sum_mul]
    have hsqrt_sq : (Real.sqrt F) ^ 2 = F := Real.sq_sqrt hF
    have hright_nonneg : 0 ≤ Real.sqrt F * ‖x‖ :=
      mul_nonneg (Real.sqrt_nonneg F) (norm_nonneg x)
    nlinarith [norm_nonneg (A x), norm_nonneg x]
  calc
    ‖A‖ ^ 2 ≤ (Real.sqrt F) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg A) hbound 2
    _ = F := Real.sq_sqrt hF
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        ((LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap i j) ^ 2 := rfl

lemma det_id_add_adjoint_comp_self
    (A : EucPlane →L[ℝ] EucPlane) :
    (ContinuousLinearMap.id ℝ EucPlane + A.adjoint ∘L A).toLinearMap.det =
      1 +
        (∑ i : Fin 2, ∑ j : Fin 2,
          ((LinearMap.toMatrix
            (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap i j) ^ 2) +
        A.toLinearMap.det ^ 2 := by
  rw [← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [ContinuousLinearMap.toLinearMap_add]
  rw [map_add]
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.toMatrix_comp
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [← ContinuousLinearMap.adjoint_toLinearMap A]
  rw [LinearMap.toMatrix_adjoint]
  rw [← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  let M := (LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap
  change (1 + M.conjTranspose * M).det =
    1 + (∑ i : Fin 2, ∑ j : Fin 2, (M i j) ^ 2) + M.det ^ 2
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_le_det_id_add_adjoint_comp_self
    (A : EucPlane →L[ℝ] EucPlane) :
    ‖A‖ ^ 2 ≤
      (ContinuousLinearMap.id ℝ EucPlane + A.adjoint ∘L A).toLinearMap.det := by
  rw [det_id_add_adjoint_comp_self]
  have hnorm := norm_sq_le_matrix_sq_sum A
  have hdet : 0 ≤ A.toLinearMap.det ^ 2 := sq_nonneg _
  linarith

lemma det_adjoint (A : EucPlane →L[ℝ] EucPlane) :
    A.adjoint.toLinearMap.det = A.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [← ContinuousLinearMap.adjoint_toLinearMap A]
  rw [LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
  simp

lemma planeGram_factor
    (A B B_inv : EucPlane →L[ℝ] EucPlane)
    (hB_left : B_inv ∘L B = ContinuousLinearMap.id ℝ EucPlane) :
    planeGram A B =
      B.adjoint ∘L
        (ContinuousLinearMap.id ℝ EucPlane +
          (A ∘L B_inv).adjoint ∘L (A ∘L B_inv)) ∘L B := by
  apply ContinuousLinearMap.ext
  intro x
  have hB_left_apply (z : EucPlane) : B_inv (B z) = z := by
    exact congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z) hB_left
  have hB_adj : B.adjoint ∘L B_inv.adjoint =
      ContinuousLinearMap.id ℝ EucPlane := by
    rw [← ContinuousLinearMap.adjoint_comp, hB_left]
    simp
  have hB_adj_apply (z : EucPlane) : B.adjoint (B_inv.adjoint z) = z := by
    exact congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z) hB_adj
  simp only [planeGram, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp]
  rw [hB_left_apply]
  simp only [map_add, ContinuousLinearMap.id_apply]
  rw [hB_adj_apply]
  abel

lemma det_planeGram_eq
    (A B B_inv : EucPlane →L[ℝ] EucPlane)
    (hB_left : B_inv ∘L B = ContinuousLinearMap.id ℝ EucPlane) :
    (planeGram A B).toLinearMap.det =
      B.toLinearMap.det ^ 2 *
        (ContinuousLinearMap.id ℝ EucPlane +
          (A ∘L B_inv).adjoint ∘L (A ∘L B_inv)).toLinearMap.det := by
  rw [planeGram_factor A B B_inv hB_left]
  simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  rw [det_adjoint]
  ring

lemma det_mul_norm_sq_le_det_planeGram
    (A B B_inv : EucPlane →L[ℝ] EucPlane)
    (hB_left : B_inv ∘L B = ContinuousLinearMap.id ℝ EucPlane) :
    B.toLinearMap.det ^ 2 * ‖A ∘L B_inv‖ ^ 2 ≤
      (planeGram A B).toLinearMap.det := by
  rw [det_planeGram_eq A B B_inv hB_left]
  exact mul_le_mul_of_nonneg_left
    (norm_sq_le_det_id_add_adjoint_comp_self (A ∘L B_inv)) (sq_nonneg _)

lemma twoSided_linear_control
    (A B B_inv : EucPlane →L[ℝ] EucPlane)
    (hB_left : B_inv ∘L B = ContinuousLinearMap.id ℝ EucPlane)
    (x : EucPlane) :
    B.toLinearMap.det ^ 2 * ‖A ∘L B_inv‖ ^ 2 * ‖x‖ ≤
      (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) *
        max ‖A x‖ ‖B x‖ := by
  have hdet := det_mul_norm_sq_le_det_planeGram A B B_inv hB_left
  have hgram_nonneg : 0 ≤ (planeGram A B).toLinearMap.det :=
    (hdet.trans' (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  calc
    B.toLinearMap.det ^ 2 * ‖A ∘L B_inv‖ ^ 2 * ‖x‖ ≤
        (planeGram A B).toLinearMap.det * ‖x‖ :=
      mul_le_mul_of_nonneg_right hdet (norm_nonneg x)
    _ = |(planeGram A B).toLinearMap.det| * ‖x‖ := by
      rw [abs_of_nonneg hgram_nonneg]
    _ ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖A‖ + ‖B‖) *
        max ‖A x‖ ‖B x‖ := abs_det_planeGram_mul_norm_le A B x

end Submission.Helpers
