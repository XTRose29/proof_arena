import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
Eigenspaces of entrywise scaling operators on finite matrices.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {I : Type v}
variable [Field k]

/-- Scale every matrix entry by its assigned weight. -/
def matrixEntrywiseScale (weight : I × I -> k) :
    Module.End k (Matrix I I k) where
  toFun A i j := weight (i, j) * A i j
  map_add' A B := by
    ext i j
    simp [mul_add]
  map_smul' c A := by
    ext i j
    simp [mul_left_comm]

@[simp]
theorem matrixEntrywiseScale_apply
    (weight : I × I -> k) (A : Matrix I I k) (i j : I) :
    matrixEntrywiseScale weight A i j = weight (i, j) * A i j := rfl

/-- The eigenspace of an entrywise scaling operator is linearly
equivalent to the functions on entries having the selected weight. -/
noncomputable def matrixEntrywiseEigenspaceEquiv
    (weight : I × I -> k) (mu : k) :
    Module.End.eigenspace (matrixEntrywiseScale weight) mu ≃ₗ[k]
      ({p : I × I // weight p = mu} -> k) := by
  classical
  exact
    { toFun := fun A p => A.1 p.1.1 p.1.2
      invFun := fun f =>
        ⟨fun i j => if h : weight (i, j) = mu then f ⟨(i, j), h⟩ else 0,
          Module.End.mem_eigenspace_iff.mpr (by
            ext i j
            by_cases h : weight (i, j) = mu
            · simp [matrixEntrywiseScale, h]
            · simp [matrixEntrywiseScale, h])⟩
      left_inv := fun A => by
        apply Subtype.ext
        ext i j
        by_cases h : weight (i, j) = mu
        · simp [h]
        · simp only [h, dite_false]
          have heigen := Module.End.mem_eigenspace_iff.mp A.property
          have hij := congrFun (congrFun heigen i) j
          change weight (i, j) * A.1 i j = mu * A.1 i j at hij
          have hzero : (weight (i, j) - mu) * A.1 i j = 0 := by
            rw [sub_mul, hij, sub_self]
          exact ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr h)).symm
      right_inv := fun f => by
        ext p
        simp [p.property]
      map_add' := fun A B => by
        ext p
        rfl
      map_smul' := fun c A => by
        ext p
        rfl }

/-- The finrank of an entrywise-scaling eigenspace is the number of
entries carrying that eigenvalue. -/
theorem finrank_matrixEntrywiseScale_eigenspace
    [Fintype I]
    (weight : I × I -> k) (mu : k) :
    Module.finrank k
      (Module.End.eigenspace (matrixEntrywiseScale weight) mu) =
      Nat.card {p : I × I // weight p = mu} := by
  classical
  rw [LinearEquiv.finrank_eq (matrixEntrywiseEigenspaceEquiv weight mu)]
  simp

end Submission.OddOrder.MathlibSupport
