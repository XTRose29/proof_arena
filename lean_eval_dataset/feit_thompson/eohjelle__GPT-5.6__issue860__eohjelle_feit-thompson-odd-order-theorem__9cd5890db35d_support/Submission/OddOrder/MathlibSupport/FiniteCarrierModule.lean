import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
Module-finiteness from finiteness of the underlying carrier.
-/

namespace Submission.OddOrder.MathlibSupport

variable {R M : Type*} [Semiring R] [Nontrivial R] [AddCommMonoid M] [Module R M]
variable [Module.Free R M] [Finite M]

/-- A free module with a finite underlying type is finitely generated. -/
theorem moduleFiniteOfFiniteCarrier : Module.Finite R M := by
  let ⟨ι, b⟩ := (Module.Free.exists_basis R M).some
  letI : Finite ι := Finite.of_injective b b.injective
  exact Module.Finite.of_basis b

end Submission.OddOrder.MathlibSupport
