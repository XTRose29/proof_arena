import Submission.OddOrder.MathlibSupport.SchurScalarRepresentation
import Submission.OddOrder.MathlibSupport.FiniteSchurField
import Submission.OddOrder.MathlibSupport.SquareZeroAnticommutator
import Mathlib.RepresentationTheory.Intertwining

/-!
Square-zero deviations and their scalar anticommutator over a Schur field.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- Transport base-field endomorphisms to the representation's group-module
type synonym. -/
noncomputable def asModuleEndRingEquiv (rho : Representation k G V) :
    Module.End k V ≃+* Module.End k rho.asModule :=
  rho.asModuleEquiv.conjRingEquiv.symm

/-- The deviation from the identity in the Schur-scalar representation. -/
noncomputable def schurDeviation
    (rho : Representation k G V)
    [Field (Module.End k[G] rho.asModule)] (g : G) :
    Module.End (Module.End k[G] rho.asModule) rho.asModule :=
  schurScalarRepresentation rho g - 1

@[simp]
theorem schurDeviation_apply
    (rho : Representation k G V)
    [Field (Module.End k[G] rho.asModule)] (g : G) (v : rho.asModule) :
    schurDeviation rho g v = asModuleEndRingEquiv rho (rho g - 1) v := by
  change schurScalarRepresentation rho g v - v =
    rho.asModuleEquiv.symm ((rho g - 1) (rho.asModuleEquiv v))
  rw [schurScalarRepresentation_apply]
  rfl

theorem schurDeviation_mul_self_eq_zero
    (rho : Representation k G V)
    [Field (Module.End k[G] rho.asModule)] (g : G)
    (h : (rho g - 1) * (rho g - 1) = 0) :
    schurDeviation rho g * schurDeviation rho g = 0 := by
  have htransport :
      asModuleEndRingEquiv rho (rho g - 1) *
          asModuleEndRingEquiv rho (rho g - 1) = 0 := by
    simpa only [map_mul, map_zero] using congrArg (asModuleEndRingEquiv rho) h
  ext v
  rw [Module.End.mul_apply, schurDeviation_apply, schurDeviation_apply]
  exact LinearMap.congr_fun htransport v

/-- A central anticommutator is scalar after passing to the Schur
endomorphism field. -/
theorem schurDeviation_anticommutator_eq_smul
    (rho : Representation k G V)
    [Representation.IsIrreducible rho] [Finite V] (x y : G)
    (A : Representation.IntertwiningMap rho rho)
    (hA : A.toLinearMap = anticommutator (rho x - 1) (rho y - 1)) :
    letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
    anticommutator (schurDeviation rho x) (schurDeviation rho y) =
      ((Representation.IntertwiningMap.equivAlgEnd (ρ := rho)) A) •
        (1 : Module.End (Module.End k[G] rho.asModule) rho.asModule) := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  ext v
  have hv := LinearMap.congr_fun hA (rho.asModuleEquiv v)
  simp only [anticommutator, LinearMap.add_apply, Module.End.mul_apply,
    schurDeviation_apply]
  change rho.asModuleEquiv.symm
      ((rho x - 1) ((rho y - 1) (rho.asModuleEquiv v)) +
        (rho y - 1) ((rho x - 1) (rho.asModuleEquiv v))) = _
  simp only [anticommutator, LinearMap.add_apply, Module.End.mul_apply] at hv
  rw [← hv]
  rfl

end Submission.OddOrder.MathlibSupport
