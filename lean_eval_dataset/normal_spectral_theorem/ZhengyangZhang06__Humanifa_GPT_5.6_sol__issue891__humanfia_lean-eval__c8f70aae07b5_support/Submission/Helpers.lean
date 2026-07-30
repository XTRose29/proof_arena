import Mathlib

namespace Submission.Helpers

open Module Module.End
open scoped ComplexStarModule

theorem exists_orthonormal_eigenbasis_of_isStarNormal
    {E ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T)
    (hι : finrank ℂ E = Fintype.card ι) :
    ∃ (b : OrthonormalBasis ι ℂ E) (d : ι → ℂ), ∀ i, T (b i) = d i • b i := by
  classical
  let R : E →ₗ[ℂ] E := (ℜ T : E →L[ℂ] E).toLinearMap
  let I : E →ₗ[ℂ] E := (ℑ T : E →L[ℂ] E).toLinearMap
  have hR : R.IsSymmetric := (ℜ T).property.isSymmetric
  have hI : I.IsSymmetric := (ℑ T).property.isSymmetric
  have hcomm : Commute R I := by
    simpa [R, I] using
      (isStarNormal_iff_commute_realPart_imaginaryPart.mp hT).map
        ContinuousLinearMap.toLinearMapRingHom
  let V : ℂ × ℂ → Submodule ℂ E :=
    fun p ↦ eigenspace R p.2 ⊓ eigenspace I p.1
  have hsum : DirectSum.IsInternal V := by
    simpa [V] using hR.directSum_isInternal_of_commute hI hcomm
  have horth :
      OrthogonalFamily ℂ (fun p ↦ V p) (fun p ↦ (V p).subtypeₗᵢ) := by
    simpa [V] using hR.orthogonalFamily_eigenspace_inf_eigenspace hI
  let v : ∀ p, OrthonormalBasis (Fin (finrank ℂ (V p))) ℂ (V p) :=
    fun p ↦ stdOrthonormalBasis ℂ (V p)
  let vb : ∀ p, Basis (Fin (finrank ℂ (V p))) ℂ (V p) :=
    fun p ↦ (v p).toBasis
  let β := Σ p, Fin (finrank ℂ (V p))
  let B : Basis β ℂ E := hsum.collectedBasis vb
  letI : Fintype β := FiniteDimensional.fintypeBasisIndex B
  have hB : Orthonormal ℂ B := by
    change Orthonormal ℂ (hsum.collectedBasis vb)
    exact DirectSum.IsInternal.collectedBasis_orthonormal horth hsum
      (fun p ↦ (v p).orthonormal)
  let bβ : OrthonormalBasis β ℂ E := B.toOrthonormalBasis hB
  have hcard : Fintype.card β = Fintype.card ι :=
    (Module.finrank_eq_card_basis B).symm.trans hι
  let e : β ≃ ι := Fintype.equivOfCardEq hcard
  let b : OrthonormalBasis ι ℂ E := bβ.reindex e
  let d : ι → ℂ := fun i ↦
    let a := e.symm i
    a.1.2 + Complex.I * a.1.1
  refine ⟨b, d, fun i ↦ ?_⟩
  let a := e.symm i
  have hbi : b i = bβ a := by
    simp [b, a]
  have hdi : d i = a.1.2 + Complex.I * a.1.1 := by
    rfl
  have ha : bβ a ∈ V a.1 := by
    rw [show bβ a = B a by
      exact congrFun (Module.Basis.coe_toOrthonormalBasis B hB) a]
    change hsum.collectedBasis vb a ∈ V a.1
    exact hsum.collectedBasis_mem vb a
  have hRa : R (bβ a) = a.1.2 • bβ a :=
    (mem_eigenspace_iff.mp ha.1)
  have hIa : I (bβ a) = a.1.1 • bβ a :=
    (mem_eigenspace_iff.mp ha.2)
  rw [hbi, hdi]
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  change R (bβ a) + Complex.I • I (bβ a) =
    (a.1.2 + Complex.I * a.1.1) • bβ a
  rw [hRa, hIa]
  simp [add_smul, smul_smul]

theorem matrix_unitarily_diagonalizable_of_orthonormal_eigenbasis
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (d : n → ℂ) (hb : ∀ i, Matrix.toEuclideanLin A (b i) = d i • b i) :
    ∃ U ∈ unitary (Matrix n n ℂ), A = U * Matrix.diagonal d * star U := by
  classical
  let U : Matrix n n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis
  have hU : U ∈ unitary (Matrix n n ℂ) :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hU_apply (i j : n) : U i j = b j i := by
    rfl
  have hAU : A * U = U * Matrix.diagonal d := by
    ext i j
    have hij := congrArg (fun x : EuclideanSpace ℂ n ↦ x i) (hb j)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, hU_apply,
      mul_comm] using hij
  refine ⟨U, hU, ?_⟩
  calc
    A = A * (U * star U) := by rw [Unitary.mul_star_self_of_mem hU, mul_one]
    _ = (A * U) * star U := by rw [Matrix.mul_assoc]
    _ = U * Matrix.diagonal d * star U := by rw [hAU]

end Submission.Helpers
