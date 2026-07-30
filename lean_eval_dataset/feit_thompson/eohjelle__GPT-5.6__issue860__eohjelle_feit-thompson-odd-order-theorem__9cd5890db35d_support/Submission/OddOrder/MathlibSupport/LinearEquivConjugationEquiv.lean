import Submission.OddOrder.MathlibSupport.CyclicOrbitFourierGlobalSpan

/-!
Inverse conjugation bundled as a linear equivalence of the endomorphism space.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The invertible linear operator `T ↦ f⁻¹ T f` on `End_k(V)`. -/
def linearEquivConjugationEquiv (f : V ≃ₗ[k] V) :
    Module.End k V ≃ₗ[k] Module.End k V where
  toFun T := f.symm.toLinearMap * T * f.toLinearMap
  invFun T := f.toLinearMap * T * f.symm.toLinearMap
  left_inv T := by
    ext x
    simp [Module.End.mul_apply]
  right_inv T := by
    ext x
    simp [Module.End.mul_apply]
  map_add' A B := by
    ext x
    simp [Module.End.mul_apply]
  map_smul' c A := by
    ext x
    simp [Module.End.mul_apply]

@[simp]
theorem linearEquivConjugationEquiv_apply
    (f : V ≃ₗ[k] V) (T : Module.End k V) :
    linearEquivConjugationEquiv f T =
      f.symm.toLinearMap * T * f.toLinearMap := rfl

@[simp]
theorem linearEquivConjugationEquiv_symm_apply
    (f : V ≃ₗ[k] V) (T : Module.End k V) :
    (linearEquivConjugationEquiv f).symm T =
      f.toLinearMap * T * f.symm.toLinearMap := rfl

/-- Forgetting invertibility recovers the inverse-conjugation linear map used
throughout the eigenspace rank theorems. -/
theorem linearEquivConjugationEquiv_toLinearMap
    (f : V ≃ₗ[k] V) :
    (linearEquivConjugationEquiv f).toLinearMap =
      linearEquivConjugation f := rfl

end Submission.OddOrder.MathlibSupport
