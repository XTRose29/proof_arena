import Submission.OddOrder.MathlibSupport.NormalRestrictionConstituents

/-!
The represented ambient element identifies a conjugation twist of a normal
constituent with its translated subspace.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Multiplication by the represented ambient element is a linear equivalence
from a normal-restriction subspace to its translate. -/
def conjugateNormalSubrepresentationLinearEquiv
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) :
    U.toSubmodule ≃ₗ[k]
      (conjugateNormalSubrepresentation rho N g U).toSubmodule where
  toFun x := ⟨rho g x, ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨rho g⁻¹ y,
    (mem_conjugateNormalSubrepresentation_iff rho N g U y).mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- The conjugation twist of a constituent is equivalent to the
representation on its translated subspace. -/
def normalConstituentTwistEquiv
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) :
    Representation.Equiv
      (U.toRepresentation.comp (MulAut.conjNormal g).symm.toMonoidHom)
      (conjugateNormalSubrepresentation rho N g U).toRepresentation :=
  Representation.Equiv.mk
    (conjugateNormalSubrepresentationLinearEquiv rho N g U) (by
      intro n
      ext x
      change rho g (rho ((MulAut.conjNormal g).symm n) x) =
        rho n (rho g x)
      rw [MulAut.conjNormal_symm_apply]
      simp only [← Module.End.mul_apply, ← rho.map_mul]
      congr 2
      group)

end Submission.OddOrder.MathlibSupport
