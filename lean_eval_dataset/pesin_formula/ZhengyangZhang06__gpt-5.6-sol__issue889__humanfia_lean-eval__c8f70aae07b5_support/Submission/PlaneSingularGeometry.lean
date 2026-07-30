import Submission.PlaneSingularValues

namespace Submission.Helpers

open LeanEval.Dynamics

lemma norm_minSingular_mul_norm
    (A : EucPlane →L[ℝ] EucPlane) :
    ‖A (planeSingularBasis A 1)‖ * ‖A‖ = |A.toLinearMap.det| := by
  have hsquare :
      (‖A (planeSingularBasis A 1)‖ * ‖A‖) ^ 2 =
        |A.toLinearMap.det| ^ 2 := by
    rw [mul_pow, norm_apply_planeSingularBasis_sq,
      ← planeSingularValueSq_zero_eq_norm_sq,
      mul_comm, planeSingularValueSq_mul, sq_abs]
  exact sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)
    |>.mp hsquare

noncomputable def planeCross (x y : EucPlane) : ℝ :=
  inner ℝ (planeQuarterTurn x) y

lemma planeCross_apply (x y : EucPlane) :
    planeCross x y = x.ofLp 0 * y.ofLp 1 - x.ofLp 1 * y.ofLp 0 := by
  simp [planeCross, PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma abs_planeCross_le (x y : EucPlane) :
    |planeCross x y| ≤ ‖x‖ * ‖y‖ := by
  exact (abs_real_inner_le_norm (planeQuarterTurn x) y).trans_eq
    (by rw [planeQuarterTurn.norm_map])

lemma planeCross_map_map (A : EucPlane →L[ℝ] EucPlane) (x y : EucPlane) :
    planeCross (A x) (A y) = A.toLinearMap.det * planeCross x y := by
  rw [planeCross_apply, planeCross_apply]
  rw [← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  let M := (LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap
  have hcoord (z : EucPlane) (i : Fin 2) :
      (A z).ofLp i = ∑ j : Fin 2, M i j * z.ofLp j := by
    have h := congrFun (LinearMap.toMatrix_mulVec_repr
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap z) i
    simpa [M, Matrix.mulVec, dotProduct] using h.symm
  rw [Matrix.det_fin_two]
  simp_rw [hcoord]
  simp [Fin.sum_univ_two]
  ring

lemma abs_planeCross_le_norm_maps_div_det
    (A : EucPlane →L[ℝ] EucPlane) (hdet : A.toLinearMap.det ≠ 0)
    (x y : EucPlane) :
    |planeCross x y| ≤ ‖A x‖ * ‖A y‖ / |A.toLinearMap.det| := by
  apply (le_div_iff₀ (abs_pos.mpr hdet)).2
  calc
    |planeCross x y| * |A.toLinearMap.det| =
        |A.toLinearMap.det * planeCross x y| := by
      rw [abs_mul, mul_comm]
    _ = |planeCross (A x) (A y)| := by rw [planeCross_map_map]
    _ ≤ ‖A x‖ * ‖A y‖ := abs_planeCross_le _ _

lemma norm_minSingular_eq_det_div_norm
    (A : EucPlane →L[ℝ] EucPlane) (hA : 0 < ‖A‖) :
    ‖A (planeSingularBasis A 1)‖ = |A.toLinearMap.det| / ‖A‖ := by
  apply (eq_div_iff hA.ne').2
  exact norm_minSingular_mul_norm A

lemma abs_planeCross_minSingular_le
    (A C C_inv : EucPlane →L[ℝ] EucPlane)
    (hA_det : A.toLinearMap.det ≠ 0)
    (hC_left : C_inv ∘L C = ContinuousLinearMap.id ℝ EucPlane) :
    |planeCross (planeSingularBasis A 1)
        (planeSingularBasis (C ∘L A) 1)| ≤
      ‖A (planeSingularBasis A 1)‖ * ‖C_inv‖ *
          ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ /
        |A.toLinearMap.det| := by
  have hw : ‖A (planeSingularBasis (C ∘L A) 1)‖ ≤
      ‖C_inv‖ * ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ := by
    calc
      ‖A (planeSingularBasis (C ∘L A) 1)‖ =
          ‖(C_inv ∘L C) (A (planeSingularBasis (C ∘L A) 1))‖ := by
        rw [hC_left]
        simp
      _ ≤ ‖C_inv‖ * ‖C (A (planeSingularBasis (C ∘L A) 1))‖ :=
        C_inv.le_opNorm _
      _ = _ := rfl
  calc
    |planeCross (planeSingularBasis A 1)
        (planeSingularBasis (C ∘L A) 1)| ≤
        ‖A (planeSingularBasis A 1)‖ *
            ‖A (planeSingularBasis (C ∘L A) 1)‖ /
          |A.toLinearMap.det| :=
      abs_planeCross_le_norm_maps_div_det A hA_det _ _
    _ ≤ ‖A (planeSingularBasis A 1)‖ *
            (‖C_inv‖ *
              ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖) /
          |A.toLinearMap.det| := by
      gcongr
    _ = _ := by ring

lemma inner_sq_add_planeCross_sq (x y : EucPlane) :
    inner ℝ x y ^ 2 + planeCross x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [planeCross_apply, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

noncomputable def alignPlaneVector (u v : EucPlane) : EucPlane :=
  if 0 ≤ inner ℝ u v then v else -v

lemma norm_alignPlaneVector (u v : EucPlane) :
    ‖alignPlaneVector u v‖ = ‖v‖ := by
  by_cases h : 0 ≤ inner ℝ u v
  · simp [alignPlaneVector, h]
  · simp [alignPlaneVector, h]

lemma inner_alignPlaneVector_nonneg (u v : EucPlane) :
    0 ≤ inner ℝ u (alignPlaneVector u v) := by
  rw [alignPlaneVector]
  split_ifs with h
  · exact h
  · rw [inner_neg_right]
    exact neg_nonneg.mpr (le_of_not_ge h)

lemma abs_planeCross_alignPlaneVector (u v : EucPlane) :
    |planeCross u (alignPlaneVector u v)| = |planeCross u v| := by
  rw [alignPlaneVector]
  split_ifs
  · rfl
  · simp [planeCross]

lemma norm_alignPlaneVector_sub_le
    (u v : EucPlane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖alignPlaneVector u v - u‖ ≤ Real.sqrt 2 * |planeCross u v| := by
  let w := alignPlaneVector u v
  have hw : ‖w‖ = 1 := by simpa [w, norm_alignPlaneVector] using hv
  have hinner : 0 ≤ inner ℝ u w := inner_alignPlaneVector_nonneg u v
  have hcross : |planeCross u w| = |planeCross u v| :=
    abs_planeCross_alignPlaneVector u v
  have hlagrange := inner_sq_add_planeCross_sq u w
  have hdiff := norm_sub_sq_real w u
  rw [hw, hu] at hdiff
  have hinner_comm : inner ℝ w u = inner ℝ u w := real_inner_comm _ _
  rw [hinner_comm] at hdiff
  have hcross_sq : planeCross u w ^ 2 = |planeCross u v| ^ 2 := by
    rw [← sq_abs, hcross, sq_abs]
  rw [hu, hw, hcross_sq] at hlagrange
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs_nonneg : 0 ≤ |planeCross u v| := abs_nonneg _
  have hright_nonneg : 0 ≤ Real.sqrt 2 * |planeCross u v| :=
    mul_nonneg hsqrt_nonneg habs_nonneg
  nlinarith [norm_nonneg (w - u)]

end Submission.Helpers
