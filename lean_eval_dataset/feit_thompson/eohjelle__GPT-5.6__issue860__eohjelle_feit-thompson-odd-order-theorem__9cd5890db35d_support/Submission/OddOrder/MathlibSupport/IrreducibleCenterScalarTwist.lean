import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar
import Submission.OddOrder.MathlibSupport.RepresentationAutomorphismTwist

/-!
Scalar center characters under automorphism twists.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Twisting an irreducible representation by an automorphism that fixes the
center pointwise leaves its scalar Schur center character unchanged. -/
theorem schurCenterScalarCharacter_comp_mulAut_eq_of_fixed_center
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [Nontrivial V] (a : MulAut G)
    (hfix : ∀ z : Subgroup.center G, a (z : G) = z) :
    letI : Representation.IsIrreducible
        (rho.comp a.toMonoidHom : Representation k G V) :=
      representation_irreducible_comp_mulAut rho a
    schurCenterScalarCharacter
        (rho.comp a.toMonoidHom : Representation k G V) =
      schurCenterScalarCharacter rho := by
  letI : Representation.IsIrreducible
      (rho.comp a.toMonoidHom : Representation k G V) :=
    representation_irreducible_comp_mulAut rho a
  apply MonoidHom.ext
  intro z
  apply Units.ext
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply smul_left_injective k hx
  calc
    (schurCenterScalarCharacter
          (rho.comp a.toMonoidHom : Representation k G V) z : k) • x =
        (rho.comp a.toMonoidHom : Representation k G V) z x := by
      rw [schurCenterScalarCharacter_smul]
    _ = rho (a (z : G)) x := rfl
    _ = rho z x := by rw [hfix z]
    _ = (schurCenterScalarCharacter rho z : k) • x := by
      rw [schurCenterScalarCharacter_smul]

end Submission.OddOrder.MathlibSupport
