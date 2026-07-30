import Submission.OddOrder.MathlibSupport.RepresentationBurnsideDensity
import Submission.OddOrder.MathlibSupport.SubrepresentationBurnsideExtension

/-!
Burnside density for the restriction of an ambient representation to a
subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Acting through the embedded subgroup algebra is the same algebra map as
the restricted representation's own monoid-algebra action. -/
theorem subgroupAlgebraEnd_eq_restriction_asAlgebraHom
    (rho : Representation k G V) (H : Subgroup G) :
    subgroupAlgebraEnd rho H =
      Representation.asAlgebraHom
        (rho.comp H.subtype : Representation k H V) := by
  ext h
  simp [subgroupAlgebraEnd, subgroupAlgebraMap, MonoidAlgebra.of]

/-- If the subgroup restriction is irreducible, its embedded subgroup algebra
realizes every ambient linear endomorphism. -/
theorem subgroupAlgebraEnd_surjective_of_restriction_irreducible
    (rho : Representation k G V) (H : Subgroup G)
    [Representation.IsIrreducible (rho.comp H.subtype)]
    [FiniteDimensional k V] [IsAlgClosed k] :
    Function.Surjective (subgroupAlgebraEnd rho H) := by
  rw [subgroupAlgebraEnd_eq_restriction_asAlgebraHom]
  exact Representation.IsIrreducible.asAlgebraHom_surjective
    (rho.comp H.subtype : Representation k H V)

end Submission.OddOrder.MathlibSupport
