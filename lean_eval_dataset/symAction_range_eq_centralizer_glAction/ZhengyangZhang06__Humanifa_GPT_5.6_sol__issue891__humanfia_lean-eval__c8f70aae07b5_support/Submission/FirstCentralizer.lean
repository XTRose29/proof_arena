import Submission.ActionCentralizer
import Submission.DiagonalAction
import Submission.MatrixFactor
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission.FirstCentralizer

open Submission.Helpers Submission.TensorInvariant Submission.DiagonalAction
  Submission.MatrixFactor Submission.ActionCentralizer

theorem diagonalAction_mem_glAdjoin
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) [Invertible (k.factorial : R)] (f : Module.End R M) :
    diagonalAction R M k f ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  let b := Module.finBasis R M
  let e := LinearMap.toMatrixAlgEquiv b
  let C := Algebra.adjoin R (Set.range (glAction R M k))
  let P : Matrix (Fin (Module.finrank R M)) (Fin (Module.finrank R M)) R → Prop :=
    fun A ↦ diagonalAction R M k (e.symm A) ∈ C
  have hP : P (e f) := by
    apply Matrix.diagonal_transvection_induction P (e f)
    · intro D _
      by_cases hD : IsUnit (Matrix.diagonal D)
      · apply diagonalAction_mem_adjoin_of_isUnit
        exact hD.map e.symm.toRingHom
      · obtain ⟨N, U, hN, hU, hDU⟩ :=
          diagonal_eq_nilpotent_mul_unit D hD
        rw [hDU]
        change diagonalAction R M k (e.symm (N * U)) ∈ C
        rw [map_mul, diagonalAction_mul]
        exact C.mul_mem
          (diagonalAction_mem_adjoin_of_isNilpotent R M k _
            (hN.map e.symm.toRingHom))
          (diagonalAction_mem_adjoin_of_isUnit R M k _
            (hU.map e.symm.toRingHom))
    · intro t
      apply diagonalAction_mem_adjoin_of_isUnit
      apply IsUnit.map e.symm.toRingHom
      rw [Matrix.isUnit_iff_isUnit_det]
      simp
    · intro A B hA hB
      simp only [P, map_mul, diagonalAction_mul] at hA hB ⊢
      exact C.mul_mem hA hB
  simpa only [P, e, AlgEquiv.symm_apply_apply] using hP

theorem piTensorHomMap_mem_glAdjoin_of_mem_diagonalSpan
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) [Invertible (k.factorial : R)] (x : ⨂[R]^k (Module.End R M))
    (hx : x ∈ diagonalSpan R (Module.End R M) k) :
    PiTensorProduct.piTensorHomMap x ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  let C := Algebra.adjoin R (Set.range (glAction R M k))
  have hle :
      diagonalSpan R (Module.End R M) k ≤
        C.toSubmodule.comap PiTensorProduct.piTensorHomMap := by
    rw [diagonalSpan]
    apply Submodule.span_le.2
    rintro _ ⟨f, rfl⟩
    change PiTensorProduct.piTensorHomMap
        (PiTensorProduct.tprod R (fun _ : Fin k ↦ f)) ∈ C
    rw [PiTensorProduct.piTensorHomMap_tprod_eq_map]
    exact diagonalAction_mem_glAdjoin R M k f
  exact hle hx

theorem glAction_adjoin_le_symAction_centralizer
    (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] (k : ℕ) :
    Algebra.adjoin R (Set.range (glAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (symAction R M k)) := by
  apply Algebra.adjoin_le
  rintro _ ⟨g, rfl⟩
  apply (Subalgebra.mem_centralizer_iff R).2
  rintro _ ⟨σ, rfl⟩
  exact (glAction_symAction_comm R M k g σ).symm

theorem symAction_centralizer_le_glAction_adjoin
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) [Invertible (k.factorial : R)] :
    Subalgebra.centralizer R (Set.range (symAction R M k)) ≤
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  intro z hz
  let x := (piTensorEndEquiv R M k).symm z
  have hxmap : PiTensorProduct.piTensorHomMap x = z := by
    rw [← piTensorEndEquiv_apply]
    exact (piTensorEndEquiv R M k).apply_symm_apply z
  rw [← hxmap] at hz ⊢
  exact piTensorHomMap_mem_glAdjoin_of_mem_diagonalSpan R M k x
    (mem_diagonalSpan_of_piTensorHomMap_mem_centralizer R M k x hz)

theorem glAction_adjoin_eq_symAction_centralizer
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (glAction R M k)) =
      Subalgebra.centralizer R (Set.range (symAction R M k)) :=
  le_antisymm (glAction_adjoin_le_symAction_centralizer R M k)
    (symAction_centralizer_le_glAction_adjoin R M k)

end Submission.FirstCentralizer
