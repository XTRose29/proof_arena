import Submission.PlaneTwoSidedLinear
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Submission.Helpers

open LeanEval.Dynamics

noncomputable def planeGramLinear (A : EucPlane →L[ℝ] EucPlane) :
    EucPlane →ₗ[ℝ] EucPlane := (A.adjoint ∘L A).toLinearMap

lemma planeGramLinear_positive (A : EucPlane →L[ℝ] EucPlane) :
    (planeGramLinear A).IsPositive := by
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self A
  change (A.adjoint ∘L A).IsPositive at h
  exact h.toLinearMap

lemma finrank_eucPlane : Module.finrank ℝ EucPlane = 2 := by
  simp [finrank_euclideanSpace]

noncomputable def planeSingularBasis (A : EucPlane →L[ℝ] EucPlane) :
    OrthonormalBasis (Fin 2) ℝ EucPlane :=
  (planeGramLinear_positive A).isSymmetric.eigenvectorBasis finrank_eucPlane

noncomputable def planeSingularValueSq
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) : ℝ :=
  (planeGramLinear_positive A).isSymmetric.eigenvalues finrank_eucPlane i

lemma planeSingularBasis_norm (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) :
    ‖planeSingularBasis A i‖ = 1 := by
  exact (planeSingularBasis A).norm_eq_one i

lemma planeGramLinear_apply_singularBasis
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) :
    planeGramLinear A (planeSingularBasis A i) =
      planeSingularValueSq A i • planeSingularBasis A i := by
  exact (planeGramLinear_positive A).isSymmetric.apply_eigenvectorBasis
    finrank_eucPlane i

lemma norm_apply_planeSingularBasis_sq
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) :
    ‖A (planeSingularBasis A i)‖ ^ 2 = planeSingularValueSq A i := by
  rw [← real_inner_self_eq_norm_sq]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (planeGramLinear A (planeSingularBasis A i))
      (planeSingularBasis A i) = _
  rw [planeGramLinear_apply_singularBasis]
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
    planeSingularBasis_norm]
  ring_nf

lemma planeSingularValueSq_nonneg
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) :
    0 ≤ planeSingularValueSq A i := by
  exact (planeGramLinear_positive A).nonneg_eigenvalues finrank_eucPlane i

lemma planeSingularValueSq_one_le_zero (A : EucPlane →L[ℝ] EucPlane) :
    planeSingularValueSq A 1 ≤ planeSingularValueSq A 0 := by
  exact (planeGramLinear_positive A).isSymmetric.eigenvalues_antitone
    finrank_eucPlane (by decide)

lemma det_planeGramLinear (A : EucPlane →L[ℝ] EucPlane) :
    (planeGramLinear A).det = A.toLinearMap.det ^ 2 := by
  change (A.adjoint ∘L A).toLinearMap.det = _
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    det_adjoint]
  ring

lemma planeSingularValueSq_mul (A : EucPlane →L[ℝ] EucPlane) :
    planeSingularValueSq A 0 * planeSingularValueSq A 1 =
      A.toLinearMap.det ^ 2 := by
  have hmat := (planeGramLinear_positive A).isSymmetric.toMatrix_eigenvectorBasis
    finrank_eucPlane
  have hdet := congrArg Matrix.det hmat
  rw [LinearMap.det_toMatrix, Matrix.det_diagonal] at hdet
  simpa [planeSingularValueSq, Function.comp_def, Fin.prod_univ_two,
    det_planeGramLinear] using hdet.symm

lemma norm_apply_sq_eq_singular_coordinates
    (A : EucPlane →L[ℝ] EucPlane) (x : EucPlane) :
    ‖A x‖ ^ 2 = ∑ i : Fin 2,
      planeSingularValueSq A i *
        ((planeSingularBasis A).repr x).ofLp i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (planeGramLinear A x) x = _
  rw [← (planeSingularBasis A).repr.inner_map_map]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [show ∀ i : Fin 2,
      ((planeSingularBasis A).repr (planeGramLinear A x)).ofLp i =
        planeSingularValueSq A i *
          ((planeSingularBasis A).repr x).ofLp i by
    intro i
    exact (planeGramLinear_positive A).isSymmetric.eigenvectorBasis_apply_self_apply
      finrank_eucPlane x i]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

lemma planeSingularValueSq_zero_eq_norm_sq
    (A : EucPlane →L[ℝ] EucPlane) :
    planeSingularValueSq A 0 = ‖A‖ ^ 2 := by
  apply le_antisymm
  · rw [← norm_apply_planeSingularBasis_sq A 0]
    calc
      ‖A (planeSingularBasis A 0)‖ ^ 2 ≤
          (‖A‖ * ‖planeSingularBasis A 0‖) ^ 2 := by
        gcongr
        exact A.le_opNorm _
      _ = ‖A‖ ^ 2 := by rw [planeSingularBasis_norm]; ring
  · have hbound : ∀ x : EucPlane,
        ‖A x‖ ^ 2 ≤ planeSingularValueSq A 0 * ‖x‖ ^ 2 := by
      intro x
      rw [norm_apply_sq_eq_singular_coordinates]
      rw [← (planeSingularBasis A).repr.norm_map x,
        EuclideanSpace.real_norm_sq_eq]
      have hzero := planeSingularValueSq_nonneg A 0
      have hone := planeSingularValueSq_nonneg A 1
      have horder := planeSingularValueSq_one_le_zero A
      simp only [Fin.sum_univ_two]
      nlinarith [sq_nonneg (((planeSingularBasis A).repr x).ofLp 0),
        sq_nonneg (((planeSingularBasis A).repr x).ofLp 1)]
    have hsqrt : ‖A‖ ≤ Real.sqrt (planeSingularValueSq A 0) := by
      apply A.opNorm_le_bound (Real.sqrt_nonneg _)
      intro x
      have hsquare := hbound x
      have heig := planeSingularValueSq_nonneg A 0
      have hsqrt_sq := Real.sq_sqrt heig
      have hright : 0 ≤ Real.sqrt (planeSingularValueSq A 0) * ‖x‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      nlinarith [norm_nonneg (A x)]
    nlinarith [Real.sq_sqrt (planeSingularValueSq_nonneg A 0), norm_nonneg A]

end Submission.Helpers
