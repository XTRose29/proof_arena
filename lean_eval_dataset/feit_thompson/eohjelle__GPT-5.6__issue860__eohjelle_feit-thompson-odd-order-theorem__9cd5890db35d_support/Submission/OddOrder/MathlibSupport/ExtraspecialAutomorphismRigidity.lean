import Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleRigidity
import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalarTwist

/-!
Rigidity of faithful extraspecial irreducibles under center-fixing
automorphisms.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- A faithful irreducible representation of an extraspecial group is
equivalent to every twist by an automorphism fixing the center pointwise. -/
theorem nonempty_equiv_comp_mulAut_of_fixed_center
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1))
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) (a : MulAut G)
    (hfix : ∀ z : Subgroup.center G, a (z : G) = z) :
    letI : Representation.IsIrreducible
        (rho.comp a.toMonoidHom : Representation k G V) :=
      representation_irreducible_comp_mulAut rho a
    Nonempty (rho.Equiv
      (rho.comp a.toMonoidHom : Representation k G V)) := by
  have hdegree := hG.faithful_irreducible_finrank_eq hpG hcard rho hrho
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (by
    rw [hdegree]
    exact pow_pos (Fact.out : p.Prime).pos n)
  letI : Representation.IsIrreducible
      (rho.comp a.toMonoidHom : Representation k G V) :=
    representation_irreducible_comp_mulAut rho a
  apply hG.nonempty_equiv_of_schurCenterScalarCharacter_eq hpG hcard rho
    (rho.comp a.toMonoidHom : Representation k G V) hrho
  exact (schurCenterScalarCharacter_comp_mulAut_eq_of_fixed_center
    rho a hfix).symm

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
