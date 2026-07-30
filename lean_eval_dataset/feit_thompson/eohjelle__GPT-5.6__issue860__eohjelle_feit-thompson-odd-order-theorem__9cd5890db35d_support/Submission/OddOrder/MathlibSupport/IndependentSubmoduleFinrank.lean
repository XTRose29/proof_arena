import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Submission.OddOrder.MathlibSupport.PrimitiveRootEigenspaces

/-!
Finrank of a finite internal direct sum of submodules.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v w

variable {k : Type u} {V : Type v} {I : Type w}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The finrank of a finite independent family spanning the ambient
space is the sum of the finranks of its members. -/
theorem finrank_eq_sum_finrank_of_iSupIndep
    [Fintype I] [DecidableEq I] [FiniteDimensional k V]
    (U : I -> Submodule k V) (hindependent : iSupIndep U)
    (hspan : ⨆ i, U i = ⊤) :
    Module.finrank k V = ∑ i : I, Module.finrank k (U i) := by
  let hinternal : DirectSum.IsInternal U :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      hindependent hspan
  let basis := hinternal.collectedBasis fun i =>
    Module.finBasis k (U i)
  rw [Module.finrank_eq_card_basis basis, Fintype.card_sigma]
  simp

/-- If the eigenspaces indexed by the powers of a primitive root span,
their finranks sum to the finrank of the ambient space. -/
theorem finrank_eq_sum_primitiveRoot_pow_eigenspaces
    [FiniteDimensional k V]
    (f : Module.End k V) {omega : k} {h : Nat}
    (homega : IsPrimitiveRoot omega h)
    (hspan :
      ⨆ i : Fin h, Module.End.eigenspace f (omega ^ (i : Nat)) = ⊤) :
    Module.finrank k V =
      ∑ i : Fin h,
        Module.finrank k (Module.End.eigenspace f (omega ^ (i : Nat))) := by
  apply finrank_eq_sum_finrank_of_iSupIndep
    (fun i : Fin h => Module.End.eigenspace f (omega ^ (i : Nat)))
    (primitiveRoot_pow_eigenspaces_iSupIndep f homega) hspan

end Submission.OddOrder.MathlibSupport
