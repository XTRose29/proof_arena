import Submission.OddOrder.MathlibSupport.SubrepresentationBurnsideExtension

/-!
Subgroup-algebra actions commute with equivalences of subrepresentations.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- An equivalence between two subrepresentations commutes with the ambient
action of every element of the subgroup algebra. -/
theorem subgroupAlgebraEnd_apply_representationEquiv
    (rho : Representation k G V) (H : Subgroup G)
    (U W : Subrepresentation (rho.comp H.subtype))
    (e : Representation.Equiv U.toRepresentation W.toRepresentation)
    (a : k[H]) (u : U.toSubmodule) :
    subgroupAlgebraEnd rho H a (e u) =
      e (U.toRepresentation.asAlgebraHom a u) := by
  induction a using MonoidAlgebra.induction_on with
  | hM h =>
      simp [subgroupAlgebraEnd, subgroupAlgebraMap]
      exact congrArg Subtype.val
        (Representation.IntertwiningMap.isIntertwining
          U.toRepresentation W.toRepresentation e.toIntertwiningMap h u).symm
  | hadd a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, map_add, Submodule.coe_add]
        using congrArg₂ (· + ·) ha hb
  | hsmul c a ha =>
      simpa only [map_smul, LinearMap.smul_apply, RingHom.id_apply,
        map_smul, Submodule.coe_smul] using congrArg (c • ·) ha

end Submission.OddOrder.MathlibSupport
