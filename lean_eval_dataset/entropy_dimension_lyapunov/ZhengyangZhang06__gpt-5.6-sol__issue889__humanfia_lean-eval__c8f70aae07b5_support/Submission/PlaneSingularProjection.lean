import Submission.PlaneSingularGeometry

namespace Submission.Helpers

open LeanEval.Dynamics

noncomputable def planeMinProjection
    (A : EucPlane →L[ℝ] EucPlane) : EucPlane →L[ℝ] EucPlane :=
  InnerProductSpace.rankOne ℝ (planeSingularBasis A 1)
    (planeSingularBasis A 1)

lemma planeMinProjection_apply (A : EucPlane →L[ℝ] EucPlane) (x : EucPlane) :
    planeMinProjection A x =
      inner ℝ (planeSingularBasis A 1) x • planeSingularBasis A 1 := rfl

lemma planeMinProjection_neg (v : EucPlane) :
    InnerProductSpace.rankOne ℝ (-v) (-v) =
      InnerProductSpace.rankOne ℝ v v := by
  ext x
  simp [InnerProductSpace.rankOne_apply]

lemma rankOne_self_sub_norm_le
    (u v : EucPlane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖InnerProductSpace.rankOne ℝ u u -
        InnerProductSpace.rankOne ℝ v v‖ ≤ 2 * ‖u - v‖ := by
  have heq : InnerProductSpace.rankOne ℝ u u -
      InnerProductSpace.rankOne ℝ v v =
        InnerProductSpace.rankOne ℝ (u - v) u +
          InnerProductSpace.rankOne ℝ v (u - v) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sub_apply, add_apply, InnerProductSpace.rankOne_apply,
      inner_sub_left, sub_smul]
    module
  rw [heq]
  calc
    ‖InnerProductSpace.rankOne ℝ (u - v) u +
        InnerProductSpace.rankOne ℝ v (u - v)‖ ≤
        ‖InnerProductSpace.rankOne ℝ (u - v) u‖ +
          ‖InnerProductSpace.rankOne ℝ v (u - v)‖ := norm_add_le _ _
    _ = ‖u - v‖ * ‖u‖ + ‖v‖ * ‖u - v‖ := by
      rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
    _ = 2 * ‖u - v‖ := by rw [hu, hv]; ring

lemma norm_planeMinProjection_sub_le_cross
    (A B : EucPlane →L[ℝ] EucPlane) :
    ‖planeMinProjection A - planeMinProjection B‖ ≤
      2 * Real.sqrt 2 *
        |planeCross (planeSingularBasis A 1) (planeSingularBasis B 1)| := by
  let u := planeSingularBasis A 1
  let v := planeSingularBasis B 1
  let w := alignPlaneVector u v
  have hu : ‖u‖ = 1 := planeSingularBasis_norm A 1
  have hv : ‖v‖ = 1 := planeSingularBasis_norm B 1
  have hw : ‖w‖ = 1 := by simpa [w, norm_alignPlaneVector] using hv
  have hproj : InnerProductSpace.rankOne ℝ w w =
      InnerProductSpace.rankOne ℝ v v := by
    dsimp [w]
    rw [alignPlaneVector]
    split_ifs
    · rfl
    · exact planeMinProjection_neg v
  calc
    ‖planeMinProjection A - planeMinProjection B‖ =
        ‖InnerProductSpace.rankOne ℝ u u -
          InnerProductSpace.rankOne ℝ w w‖ := by
      rw [hproj]
      rfl
    _ ≤ 2 * ‖u - w‖ := rankOne_self_sub_norm_le u w hu hw
    _ = 2 * ‖w - u‖ := by rw [norm_sub_rev]
    _ ≤ 2 * (Real.sqrt 2 * |planeCross u v|) := by
      gcongr
      exact norm_alignPlaneVector_sub_le u v hu hv
    _ = _ := by ring

lemma planeGramCLM_apply_singularBasis
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) :
    (A.adjoint ∘L A) (planeSingularBasis A i) =
      planeSingularValueSq A i • planeSingularBasis A i := by
  exact planeGramLinear_apply_singularBasis A i

lemma planeMinProjection_eq_gram_formula
    (A : EucPlane →L[ℝ] EucPlane)
    (hgap : planeSingularValueSq A 0 ≠ planeSingularValueSq A 1) :
    planeMinProjection A =
      (planeSingularValueSq A 0 - planeSingularValueSq A 1)⁻¹ •
        (planeSingularValueSq A 0 • ContinuousLinearMap.id ℝ EucPlane -
          A.adjoint ∘L A) := by
  apply ContinuousLinearMap.coe_injective
  apply (planeSingularBasis A).toBasis.ext
  intro i
  fin_cases i
  · have horth : inner ℝ (planeSingularBasis A 1)
        (planeSingularBasis A 0) = 0 := by
      rw [← (planeSingularBasis A).repr.inner_map_map]
      simp [PiLp.inner_apply]
    change planeMinProjection A (planeSingularBasis A 0) =
      ((planeSingularValueSq A 0 - planeSingularValueSq A 1)⁻¹ •
        (planeSingularValueSq A 0 • ContinuousLinearMap.id ℝ EucPlane -
          A.adjoint ∘L A)) (planeSingularBasis A 0)
    rw [planeMinProjection_apply, horth, zero_smul]
    simp only [smul_apply, sub_apply, ContinuousLinearMap.id_apply,
      planeGramCLM_apply_singularBasis]
    module
  · have hself : inner ℝ (planeSingularBasis A 1)
        (planeSingularBasis A 1) = 1 := by
      rw [real_inner_self_eq_norm_sq, planeSingularBasis_norm]
      norm_num
    change planeMinProjection A (planeSingularBasis A 1) =
      ((planeSingularValueSq A 0 - planeSingularValueSq A 1)⁻¹ •
        (planeSingularValueSq A 0 • ContinuousLinearMap.id ℝ EucPlane -
          A.adjoint ∘L A)) (planeSingularBasis A 1)
    rw [planeMinProjection_apply, hself, one_smul]
    simp only [smul_apply, sub_apply, ContinuousLinearMap.id_apply,
      planeGramCLM_apply_singularBasis]
    rw [← sub_smul]
    exact (inv_smul_smul₀ (sub_ne_zero.mpr hgap)
      (planeSingularBasis A 1)).symm

end Submission.Helpers
