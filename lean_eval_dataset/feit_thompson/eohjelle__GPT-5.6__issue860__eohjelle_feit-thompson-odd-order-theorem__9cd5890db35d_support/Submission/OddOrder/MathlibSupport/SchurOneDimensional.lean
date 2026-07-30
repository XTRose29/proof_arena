import Submission.OddOrder.MathlibSupport.OneDimensionalEndomorphism
import Submission.OddOrder.MathlibSupport.SchurScalarIrreducible

/-!
Commutativity of representation images in Schur dimension one.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- If the canonical Schur-field module has dimension one, every pair of
original representation images commutes. -/
theorem representation_images_commute_of_schur_finrank_eq_one
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [Finite V]
    (hdim :
      letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
      Module.finrank (Module.End k[G] rho.asModule) rho.asModule = 1)
    (x y : G) : Commute (rho x) (rho y) := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  have hcomm := endomorphisms_commute_of_finrank_eq_one hdim
    (schurScalarRepresentation rho x) (schurScalarRepresentation rho y)
  rw [commute_iff_eq] at hcomm ⊢
  ext v
  have hv := LinearMap.congr_fun hcomm (rho.asModuleEquiv.symm v)
  change schurScalarRepresentation rho x
      (schurScalarRepresentation rho y (rho.asModuleEquiv.symm v)) =
    schurScalarRepresentation rho y
      (schurScalarRepresentation rho x (rho.asModuleEquiv.symm v)) at hv
  simp only [schurScalarRepresentation_apply] at hv
  have hv' := congrArg rho.asModuleEquiv hv
  change rho x (rho y v) = rho y (rho x v) at hv'
  simpa only [Module.End.mul_apply] using hv'

end Submission.OddOrder.MathlibSupport
