import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RepresentationTheory.Basic

/-!
Scalar actions on one-dimensional invariant subspaces.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {F H V : Type*} [Field F] [Group H]
  [AddCommGroup V] [Module F V]

/-- The action of a group element on an invariant monoid-algebra submodule,
viewed as an endomorphism of its underlying `F`-subspace. -/
noncomputable def invariantLineAction
    (rho : Representation F H V) (m : Submodule F[H] rho.asModule) (h : H) :
    Module.End F (m.restrictScalars F) :=
  Algebra.lsmul F F (m.restrictScalars F) (MonoidAlgebra.of F H h)

/-- On a one-dimensional invariant subspace, every represented group element
acts by a unique scalar. -/
theorem existsUnique_invariantLineAction_eq_smul_id
    (rho : Representation F H V) (m : Submodule F[H] rho.asModule)
    (hm : Module.finrank F (m.restrictScalars F) = 1) (h : H) :
    ∃! a : F, invariantLineAction rho m h = a • LinearMap.id :=
  LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm
    (invariantLineAction rho m h)

end Submission.OddOrder.MathlibSupport
