import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke

/-!
A one-dimensional simple summand in a finite abelian representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra IsMulCommutative

variable {F H V : Type*} [Field F] [IsAlgClosed F]
  [Group H] [Finite H] [IsMulCommutative H]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
  [NeZero (Nat.card H : F)]

/-- Maschke semisimplicity and irreducibility over an algebraically closed
field produce a one-dimensional simple summand. -/
theorem exists_simpleSubmodule_finrank_one (rho : Representation F H V) :
    ∃ m : Submodule F[H] rho.asModule,
      IsSimpleModule F[H] m ∧
        Module.finrank F (m.restrictScalars F) = 1 := by
  letI : Nontrivial rho.asModule :=
    Function.Injective.nontrivial rho.asModuleEquiv.symm.injective
  letI : IsSemisimpleModule F[H] rho.asModule := by infer_instance
  obtain ⟨m, hm⟩ :=
    IsSemisimpleModule.exists_simple_submodule F[H] rho.asModule
  letI : IsSimpleModule F[H] m := hm
  letI : IsSimpleModule F[H] (m.restrictScalars F) :=
    IsSimpleModule.congr (m.restrictScalarsEquiv F)
  exact ⟨m, hm,
    IsSimpleModule.finrank_eq_one_of_isMulCommutative
      F[H] (m.restrictScalars F) F⟩

end Submission.OddOrder.MathlibSupport
