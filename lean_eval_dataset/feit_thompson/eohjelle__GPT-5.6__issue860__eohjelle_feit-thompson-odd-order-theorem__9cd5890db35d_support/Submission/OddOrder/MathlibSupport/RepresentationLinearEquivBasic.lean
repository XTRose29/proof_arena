import Mathlib.RepresentationTheory.Basic

/-!
The linear equivalence underlying a represented group element.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- A represented group element, bundled as a linear equivalence. -/
def representationLinearEquiv
    (rho : Representation k G V) (g : G) : V ≃ₗ[k] V where
  toLinearMap := rho g
  invFun := rho g⁻¹
  left_inv v := by
    change (rho g⁻¹ * rho g) v = v
    rw [← map_mul]
    simp
  right_inv v := by
    change (rho g * rho g⁻¹) v = v
    rw [← map_mul]
    simp

@[simp]
theorem representationLinearEquiv_toLinearMap
    (rho : Representation k G V) (g : G) :
    (representationLinearEquiv rho g).toLinearMap = rho g := rfl

@[simp]
theorem representationLinearEquiv_symm_toLinearMap
    (rho : Representation k G V) (g : G) :
    (representationLinearEquiv rho g).symm.toLinearMap = rho g⁻¹ := rfl

@[simp]
theorem representationLinearEquiv_apply
    (rho : Representation k G V) (g : G) (v : V) :
    representationLinearEquiv rho g v = rho g v := rfl

end Submission.OddOrder.MathlibSupport
