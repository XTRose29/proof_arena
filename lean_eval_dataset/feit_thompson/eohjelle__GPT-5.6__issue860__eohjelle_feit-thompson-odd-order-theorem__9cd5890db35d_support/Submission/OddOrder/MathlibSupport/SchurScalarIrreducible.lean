import Submission.OddOrder.MathlibSupport.IrreducibleScalarExtension
import Submission.OddOrder.MathlibSupport.SchurScalarRepresentation

/-!
Irreducibility of the Schur-scalar representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- The action remains irreducible when it is viewed as linear over its
Schur endomorphism field. -/
theorem schurScalarRepresentation_isIrreducible
    (rho : Representation k G V)
    [Representation.IsIrreducible rho]
    [Finite V] :
    letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
    Representation.IsIrreducible (schurScalarRepresentation rho) := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  let rhoK : Representation k G rho.asModule := rho
  letI : IsSimpleOrder (Subrepresentation rhoK) := by
    change Representation.IsIrreducible rho
    infer_instance
  exact representation_isIrreducible_of_scalar_extension rhoK
    (schurScalarRepresentation rho) fun g v ↦ by
      change schurScalarRepresentation rho g v = rho g v
      exact schurScalarRepresentation_apply rho g v

end Submission.OddOrder.MathlibSupport
