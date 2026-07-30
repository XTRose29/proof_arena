import Submission.OddOrder.MathlibSupport.NormalConstituentTwistEquiv
import Submission.OddOrder.MathlibSupport.SubrepresentationBurnsideExtension

/-!
Factoring an intertwiner to a translated normal constituent through the
normal subgroup algebra.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- An equivalence from a simple normal constituent to one of its ambient
translates is ambient translation after the action of an element of the
normal subgroup algebra. -/
theorem exists_subgroupAlgebra_factor_equiv_translate
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    [FiniteDimensional k U.toSubmodule] [IsAlgClosed k]
    (z : G)
    (e : Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation) :
    ∃ a : k[N], ∀ u : U.toSubmodule,
      (e u : V) = rho z (subgroupAlgebraEnd rho N a u) := by
  let ez := conjugateNormalSubrepresentationLinearEquiv rho N z U
  let f : Module.End k U.toSubmodule :=
    ez.symm.toLinearMap.comp e.toLinearMap
  obtain ⟨a, ha⟩ := exists_subgroupAlgebraEnd_restrict_eq rho N U f
  refine ⟨a, fun u ↦ ?_⟩
  rw [ha u]
  change (e u : V) = rho z (ez.symm (e u) : V)
  exact congrArg Subtype.val (ez.apply_symm_apply (e u)).symm

end Submission.OddOrder.MathlibSupport
