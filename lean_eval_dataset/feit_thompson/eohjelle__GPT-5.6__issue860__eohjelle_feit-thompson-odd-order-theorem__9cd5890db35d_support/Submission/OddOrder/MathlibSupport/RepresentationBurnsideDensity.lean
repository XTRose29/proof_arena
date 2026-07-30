import Mathlib.RepresentationTheory.Irreducible
import Submission.OddOrder.MathlibSupport.BurnsideDensity

/-!
Burnside density stated for the monoid-algebra map of an irreducible
representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The monoid algebra of an irreducible finite-dimensional representation over
an algebraically closed field realizes every linear endomorphism. -/
theorem Representation.IsIrreducible.asAlgebraHom_surjective
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [FiniteDimensional k V] [IsAlgClosed k] :
    Function.Surjective rho.asAlgebraHom := by
  have hsurj :
      Function.Surjective
        (Module.toModuleEnd k (S := k[G]) rho.asModule) :=
    isSimpleModule_toModuleEnd_surjective
  intro f
  obtain ⟨r, hr⟩ := hsurj (rho.asModuleEquiv.symm.conj f)
  refine ⟨r, ?_⟩
  ext v
  have hv := DFunLike.congr_fun hr (rho.asModuleEquiv.symm v)
  have hv' := congrArg rho.asModuleEquiv hv
  simpa using hv'

end Submission.OddOrder.MathlibSupport
