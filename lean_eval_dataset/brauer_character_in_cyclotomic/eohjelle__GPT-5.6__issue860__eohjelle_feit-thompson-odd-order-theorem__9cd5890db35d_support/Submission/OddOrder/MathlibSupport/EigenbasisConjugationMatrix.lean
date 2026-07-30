import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Submission.OddOrder.MathlibSupport.EigenspaceIntertwining
import Submission.OddOrder.MathlibSupport.MatrixEntrywiseEigenspace

/-!
Matrix coordinates for conjugation by an operator with an eigenbasis.
-/

namespace Submission.OddOrder.MathlibSupport

open Module

universe u v w

variable {k : Type u} {V : Type v} {I : Type w}
variable [Field k] [AddCommGroup V] [Module k V]

/-- Conjugation on `End(V)` by a linear equivalence, in the orientation
`f⁻¹ T f`. -/
def linearEquivConjugation (f : V ≃ₗ[k] V) :
    Module.End k (Module.End k V) where
  toFun T := f.symm.toLinearMap * T * f.toLinearMap
  map_add' A B := by
    ext x
    simp [Module.End.mul_apply]
  map_smul' c A := by
    ext x
    simp [Module.End.mul_apply]

@[simp]
theorem linearEquivConjugation_apply
    (f : V ≃ₗ[k] V) (T : Module.End k V) :
    linearEquivConjugation f T =
      f.symm.toLinearMap * T * f.toLinearMap := rfl

/-- An operator which scales each basis vector has the corresponding
diagonal matrix. -/
theorem toMatrix_eq_diagonal_of_apply_basis_eq_smul
    [Fintype I] [DecidableEq I]
    (b : Basis I k V) (f : Module.End k V) (d : I -> k)
    (happly : ∀ i : I, f (b i) = d i • b i) :
    LinearMap.toMatrix b b f = Matrix.diagonal d := by
  ext i j
  rw [LinearMap.toMatrix_apply, happly]
  by_cases hij : i = j <;> simp [hij]

/-- In an eigenbasis with unit eigenvalues, conjugation is entrywise
scaling by the quotient of the target and source eigenvalues. -/
theorem toMatrix_linearEquivConjugation
    [Fintype I] [DecidableEq I]
    (b : Basis I k V) (f : V ≃ₗ[k] V) (d : I -> kˣ)
    (happly : ∀ i : I, f (b i) = (d i : k) • b i)
    (T : Module.End k V) :
    LinearMap.toMatrix b b (linearEquivConjugation f T) =
      matrixEntrywiseScale
        (fun p : I × I => ↑((d p.1)⁻¹ * d p.2))
        (LinearMap.toMatrix b b T) := by
  have hinv (i : I) :
      f.symm (b i) = ((d i : k)⁻¹) • b i := by
    apply f.injective
    simp [happly]
  change LinearMap.toMatrix b b
      (f.symm.toLinearMap * T * f.toLinearMap) = _
  rw [LinearMap.toMatrix_mul,
    LinearMap.toMatrix_mul,
    toMatrix_eq_diagonal_of_apply_basis_eq_smul b f.symm.toLinearMap
      (fun i => ((d i : k)⁻¹)) hinv,
    toMatrix_eq_diagonal_of_apply_basis_eq_smul b f.toLinearMap
      (fun i => (d i : k)) happly]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal,
    matrixEntrywiseScale, mul_comm, mul_left_comm]

/-- The eigenbasis matrix equivalence preserves the finranks of the
conjugation eigenspaces. -/
theorem finrank_linearEquivConjugation_eigenspace_eq_entrywise
    [Fintype I] [DecidableEq I]
    (b : Basis I k V) (f : V ≃ₗ[k] V) (d : I -> kˣ)
    (happly : ∀ i : I, f (b i) = (d i : k) • b i) (mu : k) :
    Module.finrank k
      (Module.End.eigenspace (linearEquivConjugation f) mu) =
      Module.finrank k
        (Module.End.eigenspace
          (matrixEntrywiseScale
            (fun p : I × I => ↑((d p.1)⁻¹ * d p.2))
          ) mu) := by
  apply finrank_eigenspace_eq_of_intertwining
    (LinearMap.toMatrix b b) (linearEquivConjugation f)
    (matrixEntrywiseScale
      (fun p : I × I => ↑((d p.1)⁻¹ * d p.2)))
  exact toMatrix_linearEquivConjugation b f d happly

end Submission.OddOrder.MathlibSupport
