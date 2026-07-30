import Submission.PlaneSingularConvergence

namespace Submission.Helpers

open LeanEval.Dynamics

noncomputable def planeStableApproximation
    (A : EucPlane →L[ℝ] EucPlane) : EucPlane →L[ℝ] EucPlane :=
  ContinuousLinearMap.id ℝ EucPlane -
    (‖A‖ ^ 2)⁻¹ • (A.adjoint ∘L A)

lemma planeStableApproximation_eq_smul_minProjection
    (A : EucPlane →L[ℝ] EucPlane) (hA : A ≠ 0) :
    planeStableApproximation A =
      (1 - planeSingularValueSq A 1 / planeSingularValueSq A 0) •
        planeMinProjection A := by
  have hnorm_sq : ‖A‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hA)
  have heigen_zero : planeSingularValueSq A 0 ≠ 0 := by
    rw [planeSingularValueSq_zero_eq_norm_sq]
    exact hnorm_sq
  apply ContinuousLinearMap.coe_injective
  apply (planeSingularBasis A).toBasis.ext
  intro i
  fin_cases i
  · have horth : inner ℝ (planeSingularBasis A 1)
        (planeSingularBasis A 0) = 0 := by
      rw [← (planeSingularBasis A).repr.inner_map_map]
      simp [PiLp.inner_apply]
    change planeStableApproximation A (planeSingularBasis A 0) =
      ((1 - planeSingularValueSq A 1 / planeSingularValueSq A 0) •
        planeMinProjection A) (planeSingularBasis A 0)
    simp only [smul_apply]
    rw [planeMinProjection_apply, horth, zero_smul]
    simp only [smul_zero]
    simp only [planeStableApproximation, sub_apply,
      ContinuousLinearMap.id_apply, smul_apply]
    rw [planeGramCLM_apply_singularBasis]
    rw [planeSingularValueSq_zero_eq_norm_sq]
    rw [inv_smul_smul₀ hnorm_sq]
    simp
  · have hself : inner ℝ (planeSingularBasis A 1)
        (planeSingularBasis A 1) = 1 := by
      rw [real_inner_self_eq_norm_sq, planeSingularBasis_norm]
      norm_num
    change planeStableApproximation A (planeSingularBasis A 1) =
      ((1 - planeSingularValueSq A 1 / planeSingularValueSq A 0) •
        planeMinProjection A) (planeSingularBasis A 1)
    simp only [smul_apply]
    rw [planeMinProjection_apply, hself, one_smul]
    simp only [planeStableApproximation, sub_apply,
      ContinuousLinearMap.id_apply, smul_apply]
    rw [planeGramCLM_apply_singularBasis]
    rw [planeSingularValueSq_zero_eq_norm_sq]
    module

lemma norm_planeMinProjection (A : EucPlane →L[ℝ] EucPlane) :
    ‖planeMinProjection A‖ = 1 := by
  rw [planeMinProjection, InnerProductSpace.norm_rankOne,
    planeSingularBasis_norm]
  norm_num

lemma planeMinProjection_idempotent (A : EucPlane →L[ℝ] EucPlane) :
    planeMinProjection A ∘L planeMinProjection A = planeMinProjection A := by
  ext x
  simp [planeMinProjection_apply]

lemma planeMinProjection_adjoint (A : EucPlane →L[ℝ] EucPlane) :
    (planeMinProjection A).adjoint = planeMinProjection A := by
  simp [planeMinProjection]

lemma planeMinProjection_comp_quarterTurn
    (A : EucPlane →L[ℝ] EucPlane) :
    planeMinProjection A ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ EucPlane - planeMinProjection A) := by
  have hv := congrArg (fun r : ℝ => r ^ 2) (planeSingularBasis_norm A 1)
  rw [EuclideanSpace.real_norm_sq_eq] at hv
  simp [Fin.sum_univ_two] at hv
  apply ContinuousLinearMap.ext
  intro x
  ext i
  fin_cases i
  · simp [planeMinProjection_apply, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination -(x.ofLp 1) * hv
  · simp [planeMinProjection_apply, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (x.ofLp 0) * hv

lemma norm_comp_planeMinProjection (A : EucPlane →L[ℝ] EucPlane) :
    ‖A ∘L planeMinProjection A‖ =
      ‖A (planeSingularBasis A 1)‖ := by
  rw [planeMinProjection, InnerProductSpace.comp_rankOne,
    InnerProductSpace.norm_rankOne, planeSingularBasis_norm, mul_one]

lemma norm_sub_planeMinProjection_sq
    (A : EucPlane →L[ℝ] EucPlane) (z : EucPlane) :
    ‖z - planeMinProjection A z‖ ^ 2 =
      ((planeSingularBasis A).repr z).ofLp 0 ^ 2 := by
  rw [← (planeSingularBasis A).repr.norm_map (z - planeMinProjection A z),
    EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two, planeMinProjection_apply,
    OrthonormalBasis.repr_apply_apply]

lemma norm_mul_norm_sub_planeMinProjection_le_norm_apply
    (A : EucPlane →L[ℝ] EucPlane) (z : EucPlane) :
    ‖A‖ * ‖z - planeMinProjection A z‖ ≤ ‖A z‖ := by
  have hcomp := norm_sub_planeMinProjection_sq A z
  have happly := norm_apply_sq_eq_singular_coordinates A z
  rw [Fin.sum_univ_two, planeSingularValueSq_zero_eq_norm_sq] at happly
  have hsquare : (‖A‖ * ‖z - planeMinProjection A z‖) ^ 2 ≤
      ‖A z‖ ^ 2 := by
    rw [mul_pow, hcomp, happly]
    nlinarith [planeSingularValueSq_nonneg A 1,
      sq_nonneg (((planeSingularBasis A).repr z).ofLp 1)]
  nlinarith [norm_nonneg A, norm_nonneg (z - planeMinProjection A z),
    norm_nonneg (A z)]

lemma norm_planeStableApproximation_sub_minProjection
    (A : EucPlane →L[ℝ] EucPlane) (hA : A ≠ 0) :
    ‖planeStableApproximation A - planeMinProjection A‖ =
      (‖A (planeSingularBasis A 1)‖ / ‖A‖) ^ 2 := by
  have hnorm_pos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have heigen_zero_pos : 0 < planeSingularValueSq A 0 := by
    rw [planeSingularValueSq_zero_eq_norm_sq]
    positivity
  have heigen_one_nonneg : 0 ≤ planeSingularValueSq A 1 :=
    planeSingularValueSq_nonneg A 1
  rw [planeStableApproximation_eq_smul_minProjection A hA]
  rw [show
      (1 - planeSingularValueSq A 1 / planeSingularValueSq A 0) •
          planeMinProjection A - planeMinProjection A =
        (-(planeSingularValueSq A 1 / planeSingularValueSq A 0)) •
          planeMinProjection A by module]
  rw [norm_smul, norm_planeMinProjection, mul_one, Real.norm_eq_abs]
  rw [abs_of_nonpos (neg_nonpos.mpr
    (div_nonneg heigen_one_nonneg heigen_zero_pos.le)), neg_neg]
  rw [div_pow, norm_apply_planeSingularBasis_sq,
    planeSingularValueSq_zero_eq_norm_sq]

end Submission.Helpers
