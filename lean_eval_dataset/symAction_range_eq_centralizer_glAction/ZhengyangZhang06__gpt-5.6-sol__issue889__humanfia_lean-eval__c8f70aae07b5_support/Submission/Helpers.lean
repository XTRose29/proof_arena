import ChallengeDeps
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.Basis

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission.Helpers

def piProdEquiv (ι α β : Type*) : (ι → α × β) ≃ (ι → α) × (ι → β) where
  toFun f := (fun i ↦ (f i).1, fun i ↦ (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def tensorBasis (R M : Type*) [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M] (k : ℕ) :
    Module.Basis (Fin k → Fin (Module.finrank R M)) R (⨂[R]^k M) :=
  Basis.piTensorProduct fun _ ↦ Module.finBasis R M

noncomputable def tensorEndBasis (R M : Type*) [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M] (k : ℕ) :
    Module.Basis (Fin k → Fin (Module.finrank R M) × Fin (Module.finrank R M)) R
      (⨂[R]^k (Module.End R M)) :=
  Basis.piTensorProduct fun _ ↦ (Module.finBasis R M).end

theorem piTensorHomMap_tensorEndBasis
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) (p : Fin k → Fin (Module.finrank R M) × Fin (Module.finrank R M)) :
    PiTensorProduct.piTensorHomMap (tensorEndBasis R M k p) =
      (tensorBasis R M k).end (piProdEquiv (Fin k) _ _ p) := by
  apply (tensorBasis R M k).ext
  intro q
  rw [Module.Basis.end_apply_apply]
  simp only [tensorEndBasis, tensorBasis, Basis.piTensorProduct_apply,
    PiTensorProduct.piTensorHomMap_tprod_tprod]
  by_cases h : (fun i ↦ (p i).2) = q
  · subst q
    rw [if_pos (by rfl)]
    apply congrArg (PiTensorProduct.tprod R)
    funext i
    rw [Module.Basis.end_apply_apply, if_pos rfl]
    rfl
  · rw [if_neg]
    · obtain ⟨i, hi⟩ : ∃ i, (p i).2 ≠ q i := by
        simpa only [not_forall, funext_iff] using h
      apply (PiTensorProduct.tprod R).map_coord_zero i
      rw [Module.Basis.end_apply_apply, if_neg hi]
    · simpa [piProdEquiv] using h

noncomputable def piTensorEndEquiv
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) : (⨂[R]^k (Module.End R M)) ≃ₗ[R] Module.End R (⨂[R]^k M) :=
  (tensorEndBasis R M k).equiv
    ((tensorBasis R M k).end)
    (piProdEquiv (Fin k) _ _)

theorem piTensorEndEquiv_apply
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (k : ℕ) (x : ⨂[R]^k (Module.End R M)) :
    piTensorEndEquiv R M k x = PiTensorProduct.piTensorHomMap x := by
  have h :
      (piTensorEndEquiv R M k).toLinearMap = PiTensorProduct.piTensorHomMap := by
    refine (tensorEndBasis R M k).ext fun p ↦ ?_
    simp [piTensorEndEquiv, piTensorHomMap_tensorEndBasis]
  exact LinearMap.congr_fun h x

theorem glAction_symAction_comm (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
    (k : ℕ) (g : (M →ₗ[R] M)ˣ) (σ : Equiv.Perm (Fin k)) :
    glAction R M k g * symAction R M k σ =
      symAction R M k σ * glAction R M k g := by
  ext x
  simp [Module.End.mul_apply, glAction, symAction]

theorem symAction_adjoin_le_glAction_centralizer
    (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] (k : ℕ) :
    Algebra.adjoin R (Set.range (symAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  apply Algebra.adjoin_le
  rintro _ ⟨σ, rfl⟩
  change ∀ z ∈ Set.range (glAction R M k), z * symAction R M k σ =
    symAction R M k σ * z
  rintro _ ⟨g, rfl⟩
  exact glAction_symAction_comm R M k g σ

end Submission.Helpers
