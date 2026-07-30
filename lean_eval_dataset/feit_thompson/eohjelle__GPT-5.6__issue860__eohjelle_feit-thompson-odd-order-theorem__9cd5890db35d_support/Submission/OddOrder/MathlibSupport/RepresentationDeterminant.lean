import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RepresentationTheory.Basic
import Submission.OddOrder.MathlibSupport.RepresentationLinearEquivBasic

/-!
The determinant character of a linear representation.
-/

namespace Submission.OddOrder.MathlibSupport

variable {k G V : Type*} [CommRing k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- A representation as a homomorphism to the general linear group. -/
def representationLinearEquivHom (rho : Representation k G V) :
    G →* V ≃ₗ[k] V where
  toFun := representationLinearEquiv rho
  map_one' := by
    ext v
    simp [representationLinearEquiv]
  map_mul' g h := by
    ext v
    simp [representationLinearEquiv, Module.End.mul_apply]

/-- The multiplicative determinant character of a representation. -/
noncomputable def representationDeterminant
    (rho : Representation k G V) [Module.Free k V] [Module.Finite k V] :
    G →* kˣ :=
  LinearEquiv.det.comp (representationLinearEquivHom rho)

/-- The derived subgroup acts with determinant one. -/
theorem commutator_le_representationDeterminant_ker
    (rho : Representation k G V) [Module.Free k V] [Module.Finite k V] :
    _root_.commutator G ≤ (representationDeterminant rho).ker :=
  Abelianization.commutator_subset_ker (representationDeterminant rho)

theorem representationDeterminant_eq_one_of_mem_commutator
    (rho : Representation k G V) [Module.Free k V] [Module.Finite k V]
    {g : G} (hg : g ∈ _root_.commutator G) :
    representationDeterminant rho g = 1 :=
  MonoidHom.mem_ker.mp (commutator_le_representationDeterminant_ker rho hg)

end Submission.OddOrder.MathlibSupport
