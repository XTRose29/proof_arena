import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Submission.OddOrder.MathlibSupport.RepresentationBurnsideDensity

/-!
Extending endomorphisms of a simple subrepresentation through the ambient
group algebra.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The natural inclusion of a subgroup algebra into the ambient group
algebra. -/
noncomputable def subgroupAlgebraMap (H : Subgroup G) : k[H] →ₐ[k] k[G] :=
  MonoidAlgebra.mapDomainAlgHom k k H.subtype

/-- The endomorphism of the ambient representation defined by an element of a
subgroup algebra. -/
noncomputable def subgroupAlgebraEnd
    (rho : Representation k G V) (H : Subgroup G) :
    k[H] →ₐ[k] Module.End k V :=
  rho.asAlgebraHom.comp (subgroupAlgebraMap H)

/-- Acting through the ambient group algebra agrees, on a subrepresentation,
with its intrinsic subgroup-algebra action. -/
theorem subgroupAlgebraEnd_apply_subrepresentation
    (rho : Representation k G V) (H : Subgroup G)
    (U : Subrepresentation (rho.comp H.subtype))
    (a : k[H]) (u : U.toSubmodule) :
    subgroupAlgebraEnd rho H a u = U.toRepresentation.asAlgebraHom a u := by
  induction a using MonoidAlgebra.induction_on with
  | hM h =>
      simp [subgroupAlgebraEnd, subgroupAlgebraMap]
      rfl
  | hadd a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
        congrArg₂ (· + ·) ha hb
  | hsmul c a ha =>
      simpa only [map_smul, LinearMap.smul_apply, RingHom.id_apply,
        Submodule.coe_smul] using congrArg (c • ·) ha

/-- Every endomorphism of a finite-dimensional simple constituent is the
restriction of the action of an element of the subgroup algebra. -/
theorem exists_subgroupAlgebraEnd_restrict_eq
    (rho : Representation k G V) (H : Subgroup G)
    (U : Subrepresentation (rho.comp H.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    [FiniteDimensional k U.toSubmodule] [IsAlgClosed k]
    (f : Module.End k U.toSubmodule) :
    ∃ a : k[H], ∀ u : U.toSubmodule,
      subgroupAlgebraEnd rho H a u = f u := by
  obtain ⟨a, ha⟩ :=
    Representation.IsIrreducible.asAlgebraHom_surjective
      U.toRepresentation f
  refine ⟨a, fun u ↦ ?_⟩
  rw [subgroupAlgebraEnd_apply_subrepresentation]
  exact congrArg Subtype.val (DFunLike.congr_fun ha u)

end Submission.OddOrder.MathlibSupport
