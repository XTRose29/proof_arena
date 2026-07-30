import Submission.OddOrder.MathlibSupport.NormalConstituentOrbitExt
import Submission.OddOrder.MathlibSupport.SubrepresentationAlgebraIntertwiner

/-!
Extensionality for normal subgroup-algebra actions on an irreducible ambient
representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]

/-- If every ambient translate of a nonzero normal constituent is equivalent
to it, two normal subgroup-algebra elements have the same ambient action as
soon as they have the same action on that constituent. -/
theorem subgroupAlgebraEnd_eq_of_restrict_eq
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (hU : U ≠ ⊥)
    (hequiv : ∀ z : G, Nonempty (Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation))
    (a b : k[N])
    (hab : ∀ u : U.toSubmodule,
      subgroupAlgebraEnd rho N a u = subgroupAlgebraEnd rho N b u) :
    subgroupAlgebraEnd rho N a = subgroupAlgebraEnd rho N b := by
  apply LinearMap.eq_of_eqOn_normalConstituentOrbit rho N U hU
  intro z w
  obtain ⟨e⟩ := hequiv z
  obtain ⟨u, rfl⟩ := e.surjective w
  change subgroupAlgebraEnd rho N a (e u) =
    subgroupAlgebraEnd rho N b (e u)
  rw [subgroupAlgebraEnd_apply_representationEquiv rho N U _ e a u]
  rw [subgroupAlgebraEnd_apply_representationEquiv rho N U _ e b u]
  apply congrArg (fun x : U.toSubmodule ↦ (e x : V))
  apply Subtype.ext
  have hu := hab u
  rw [subgroupAlgebraEnd_apply_subrepresentation rho N U a u] at hu
  rw [subgroupAlgebraEnd_apply_subrepresentation rho N U b u] at hu
  exact hu

/-- A one-sided inverse identity for normal subgroup-algebra actions proved on
one constituent propagates to the whole irreducible ambient module. -/
theorem subgroupAlgebraEnd_mul_eq_one_of_restrict
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (hU : U ≠ ⊥)
    (hequiv : ∀ z : G, Nonempty (Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation))
    (a b : k[N])
    (hab : ∀ u : U.toSubmodule,
      subgroupAlgebraEnd rho N b (subgroupAlgebraEnd rho N a u) = u) :
    subgroupAlgebraEnd rho N b * subgroupAlgebraEnd rho N a = 1 := by
  rw [← map_mul, ← map_one (subgroupAlgebraEnd rho N)]
  apply subgroupAlgebraEnd_eq_of_restrict_eq rho N U hU hequiv
  intro u
  simp only [map_mul, Module.End.mul_apply, map_one]
  exact hab u

end Submission.OddOrder.MathlibSupport
