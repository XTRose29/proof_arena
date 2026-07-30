import Submission.Helpers
import Submission.TensorInvariant
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission.ActionCentralizer

open Submission.Helpers Submission.TensorInvariant

theorem symAction_mul_piTensorHomMap
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (k : ℕ) (σ : Equiv.Perm (Fin k)) (x : ⨂[R]^k (Module.End R M)) :
    symAction R M k σ * PiTensorProduct.piTensorHomMap x =
      PiTensorProduct.piTensorHomMap
          (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) *
        symAction R M k σ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      ext v
      simp [Module.End.mul_apply, symAction]
  | add x y hx hy =>
      simpa only [map_add, mul_add, add_mul] using congrArg₂ (· + ·) hx hy

theorem reindex_eq_of_piTensorHomMap_mem_centralizer
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) (x : ⨂[R]^k (Module.End R M))
    (hx : PiTensorProduct.piTensorHomMap x ∈
      Subalgebra.centralizer R (Set.range (symAction R M k))) :
    ∀ σ : Equiv.Perm (Fin k),
      PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x = x := by
  intro σ
  have hcomm :
      symAction R M k σ * PiTensorProduct.piTensorHomMap x =
        PiTensorProduct.piTensorHomMap x * symAction R M k σ := by
    exact (Subalgebra.mem_centralizer_iff R).mp hx _ ⟨σ, rfl⟩
  have hcancel :
      PiTensorProduct.piTensorHomMap
          (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) *
          symAction R M k σ =
        PiTensorProduct.piTensorHomMap x * symAction R M k σ :=
    (symAction_mul_piTensorHomMap R M k σ x).symm.trans hcomm
  have hmaps :
      PiTensorProduct.piTensorHomMap
          (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) =
        PiTensorProduct.piTensorHomMap x := by
    have hinv :
        symAction R M k σ * symAction R M k σ⁻¹ = 1 := by
      rw [← map_mul]
      simp
    apply_fun fun z ↦ z * symAction R M k σ⁻¹ at hcancel
    simpa only [mul_assoc, hinv, mul_one] using hcancel
  apply (piTensorEndEquiv R M k).injective
  simpa only [piTensorEndEquiv_apply] using hmaps

theorem mem_diagonalSpan_of_piTensorHomMap_mem_centralizer
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) [Invertible (k.factorial : R)] (x : ⨂[R]^k (Module.End R M))
    (hx : PiTensorProduct.piTensorHomMap x ∈
      Subalgebra.centralizer R (Set.range (symAction R M k))) :
    x ∈ diagonalSpan R (Module.End R M) k :=
  mem_diagonalSpan_of_reindex_eq R (Module.End R M) k x
    (reindex_eq_of_piTensorHomMap_mem_centralizer R M k x hx)

end Submission.ActionCentralizer
