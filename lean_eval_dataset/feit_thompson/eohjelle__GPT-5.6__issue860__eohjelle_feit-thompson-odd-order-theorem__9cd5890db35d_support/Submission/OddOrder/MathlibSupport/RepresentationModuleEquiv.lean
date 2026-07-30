import Mathlib.RepresentationTheory.Intertwining

/-!
Conversion between equivalences of representations and linear equivalences of
their modules over the monoid algebra.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w x

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]
variable {rho : Representation k G V} {sigma : Representation k G W}

/-- A representation equivalence is a linear equivalence over the monoid
algebra. -/
noncomputable def representationEquivLinearEquivAsModule
    (e : Representation.Equiv rho sigma) :
    rho.asModule ≃ₗ[k[G]] sigma.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
      e.toIntertwiningMap)
    e.toLinearEquiv.bijective

/-- A linear equivalence over the monoid algebra is a representation
equivalence. -/
noncomputable def representationEquivOfLinearEquivAsModule
    (e : rho.asModule ≃ₗ[k[G]] sigma.asModule) :
    Representation.Equiv rho sigma :=
  Representation.IntertwiningMap.ofBijective
    ((Representation.IntertwiningMap.equivLinearMapAsModule rho sigma).symm
      e.toLinearMap)
    e.bijective

/-- Existence of a representation equivalence is equivalent to existence of a
module equivalence over the monoid algebra. -/
theorem nonempty_representationEquiv_iff_nonempty_linearEquivAsModule :
    Nonempty (Representation.Equiv rho sigma) ↔
      Nonempty (rho.asModule ≃ₗ[k[G]] sigma.asModule) :=
  ⟨fun ⟨e⟩ ↦ ⟨representationEquivLinearEquivAsModule e⟩,
    fun ⟨e⟩ ↦ ⟨representationEquivOfLinearEquivAsModule e⟩⟩

end Submission.OddOrder.MathlibSupport
