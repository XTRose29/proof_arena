import Submission.OddOrder.MathlibSupport.NormalConstituentAlgebraExt
import Submission.OddOrder.MathlibSupport.NormalConstituentIntertwinerFactor

/-!
Subgroup-algebra correction operators for an equivalence to an ambient
translate of a normal constituent.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]

/-- A constituent equivalence to its `x`-translate can be written as `rho x`
after a subgroup-algebra operator whose ambient action has a
subgroup-algebra left inverse. -/
theorem exists_subgroupAlgebra_correction_pair
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (hU : U ≠ ⊥)
    [Representation.IsIrreducible U.toRepresentation]
    [FiniteDimensional k U.toSubmodule] [IsAlgClosed k]
    (hequiv : ∀ z : G, Nonempty (Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation))
    (x : G)
    (e : Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N x U).toRepresentation) :
    ∃ a b : k[N],
      (∀ u : U.toSubmodule,
        (e u : V) = rho x (subgroupAlgebraEnd rho N a u)) ∧
      subgroupAlgebraEnd rho N b * subgroupAlgebraEnd rho N a = 1 := by
  let ex := conjugateNormalSubrepresentationLinearEquiv rho N x U
  let f : U.toSubmodule ≃ₗ[k] U.toSubmodule :=
    e.toLinearEquiv.trans ex.symm
  obtain ⟨a, ha⟩ :=
    exists_subgroupAlgebraEnd_restrict_eq rho N U f.toLinearMap
  obtain ⟨b, hb⟩ :=
    exists_subgroupAlgebraEnd_restrict_eq rho N U f.symm.toLinearMap
  have hab (u : U.toSubmodule) :
      subgroupAlgebraEnd rho N b (subgroupAlgebraEnd rho N a u) = u := by
    rw [ha u]
    change subgroupAlgebraEnd rho N b ((f u : U.toSubmodule) : V) = u
    rw [hb (f u)]
    exact congrArg Subtype.val (f.symm_apply_apply u)
  refine ⟨a, b, ?_,
    subgroupAlgebraEnd_mul_eq_one_of_restrict rho N U hU hequiv a b hab⟩
  intro u
  rw [ha u]
  change (e u : V) = rho x (ex.symm (e u) : V)
  exact congrArg Subtype.val (ex.apply_symm_apply (e u)).symm

end Submission.OddOrder.MathlibSupport
