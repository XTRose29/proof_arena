import Mathlib.LinearAlgebra.Dimension.Finrank
import Submission.OddOrder.MathlibSupport.NormalRestrictionConjugates
import Submission.OddOrder.MathlibSupport.SubrepresentationInterval

/-!
Simplicity and dimension are preserved when normal-restriction constituents
are translated by ambient group elements.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Ambient translation preserves atomic subrepresentations of a normal
restriction. -/
theorem isAtom_conjugateNormalSubrepresentation_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) :
    IsAtom (conjugateNormalSubrepresentation rho N g U) ↔ IsAtom U :=
  (conjugateNormalSubrepresentationOrderIso rho N g).isAtom_iff U

/-- A translated constituent of a normal restriction is simple exactly when
the original constituent is simple. -/
theorem irreducible_conjugateNormalSubrepresentation_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) :
    Representation.IsIrreducible
        (conjugateNormalSubrepresentation rho N g U).toRepresentation ↔
      Representation.IsIrreducible U.toRepresentation := by
  rw [irreducible_toRepresentation_iff_isAtom,
    irreducible_toRepresentation_iff_isAtom,
    isAtom_conjugateNormalSubrepresentation_iff]

/-- Ambient translation preserves the dimension of a normal-restriction
subrepresentation. -/
theorem finrank_conjugateNormalSubrepresentation
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) :
    Module.finrank k
        (conjugateNormalSubrepresentation rho N g U).toSubmodule =
      Module.finrank k U.toSubmodule := by
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)
  exact e.finrank_map_eq U.toSubmodule

end Submission.OddOrder.MathlibSupport
