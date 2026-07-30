import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.Basic

/-!
The finite Schur endomorphism field of an irreducible representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- Schur's lemma and Little Wedderburn make the group-algebra endomorphism
ring of a finite irreducible representation into a field. -/
@[reducible] noncomputable def finiteSchurField
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [Finite V] : Field (Module.End k[G] rho.asModule) := by
  letI : DecidableEq (Module.End k[G] rho.asModule) := Classical.decEq _
  letI : DivisionRing (Module.End k[G] rho.asModule) :=
    Module.End.instDivisionRing
  letI : Finite rho.asModule :=
    Finite.of_injective rho.asModuleEquiv rho.asModuleEquiv.injective
  letI : Finite (rho.asModule → rho.asModule) := by infer_instance
  letI : Finite (Module.End k[G] rho.asModule) :=
    Finite.of_injective
      (fun f : Module.End k[G] rho.asModule ↦ (f : rho.asModule → rho.asModule))
      (fun _ _ h ↦ LinearMap.ext fun x ↦ congrFun h x)
  exact littleWedderburn (Module.End k[G] rho.asModule)

end Submission.OddOrder.MathlibSupport
