import Submission.OddOrder.MathlibSupport.FiniteSchurField

/-!
Viewing an irreducible representation over its Schur endomorphism field.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- The original group action is linear over its group-algebra endomorphism
ring, acting on vectors by evaluation. -/
noncomputable def schurScalarRepresentation
    (rho : Representation k G V)
    [Field (Module.End k[G] rho.asModule)] :
    Representation (Module.End k[G] rho.asModule) G rho.asModule where
  toFun g :=
    { toFun := fun v ↦ MonoidAlgebra.single g 1 • v
      map_add' := by simp
      map_smul' := fun d v ↦ (d.map_smul (MonoidAlgebra.single g 1) v).symm }
  map_one' := by
    ext v
    simp
    rfl
  map_mul' := by
    intro g h
    ext v
    simp
    rfl

@[simp]
theorem schurScalarRepresentation_apply
    (rho : Representation k G V)
    [Field (Module.End k[G] rho.asModule)] (g : G) (v : rho.asModule) :
    schurScalarRepresentation rho g v = rho g v :=
  by
    simp [schurScalarRepresentation, Representation.single_smul]
    rfl

end Submission.OddOrder.MathlibSupport
