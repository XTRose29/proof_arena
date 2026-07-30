import Submission.Helpers

namespace Submission.Helpers

open scoped InnerProductSpace

/-- The Laplacian is invariant under precomposition by a linear
isometry. -/
lemma laplacian_comp_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E ≃ₗᵢ[ℝ] E) (f : E → ℝ) (x : E) :
    Laplacian.laplacian (f ∘ L) x = Laplacian.laplacian f (L x) := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
      (f ∘ L)) x]
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      ((stdOrthonormalBasis ℝ E).map L)) (L x)]
  apply Finset.sum_congr rfl
  intro i _
  have h :=
    L.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
      f (s := Set.univ) uniqueDiffOn_univ (Set.mem_univ (L x)) 2
  have h' := congrArg
    (fun D ↦ D ![(stdOrthonormalBasis ℝ E) i,
      (stdOrthonormalBasis ℝ E) i]) h
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h'
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h'
  rw [h']
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Translation of the input does not change the Laplacian, apart from
translating its evaluation point. -/
lemma laplacian_comp_add_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (a x : E) :
    Laplacian.laplacian (fun y ↦ f (y + a)) x =
      Laplacian.laplacian f (x + a) := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
      (fun y ↦ f (y + a))) x]
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f)
      (x + a)]
  simp only [iteratedFDeriv_comp_add_right]

section LinearPlaneReflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear reflection in the hyperplane perpendicular to `e`. -/
noncomputable def linearPlaneReflect (e : E) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ e)ᗮ.reflection

lemma linearPlaneReflect_apply (e x : E) (he : ‖e‖ = 1) :
    linearPlaneReflect e x = x - (2 * ⟪x, e⟫_ℝ) • e := by
  rw [linearPlaneReflect, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he]
  rw [real_inner_comm]
  module

lemma planeReflect_eq_linearPlaneReflect_add (e : E) (μ : ℝ) (x : E)
    (he : ‖e‖ = 1) :
    planeReflect e μ x = linearPlaneReflect e x + (2 * μ) • e := by
  rw [planeReflect, linearPlaneReflect_apply e x he]
  module

/-- Affine plane reflections preserve the Laplacian. -/
lemma laplacian_comp_planeReflect (e : E) (μ : ℝ) (he : ‖e‖ = 1)
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : E) :
    Laplacian.laplacian (f ∘ planeReflect e μ) x =
      Laplacian.laplacian f (planeReflect e μ x) := by
  let L := linearPlaneReflect e
  let a := (2 * μ) • e
  have hreflect : planeReflect e μ = fun y ↦ L y + a := by
    funext y
    exact planeReflect_eq_linearPlaneReflect_add e μ y he
  rw [hreflect]
  change Laplacian.laplacian ((fun y ↦ f (y + a)) ∘ L) x =
    Laplacian.laplacian f (L x + a)
  rw [laplacian_comp_linearIsometryEquiv,
    laplacian_comp_add_right]

end LinearPlaneReflection

end Submission.Helpers
