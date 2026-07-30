import Mathlib.LinearAlgebra.Matrix.ToLin
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientCard
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientEndomorphismBasis

/-!
The degree of a faithful irreducible extraspecial representation in any
characteristic coprime to the group order.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- The intrinsic degree-square formula, before identifying the quotient
order with a prime power. -/
theorem faithful_irreducible_finrank_sq_eq_quotient_center_card_of_card_ne_zero
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (hcardField : (Nat.card G : k) ≠ 0) :
    Module.finrank k V ^ 2 = Nat.card (G ⧸ Subgroup.center G) := by
  classical
  have hend := hG.faithful_irreducible_finrank_end_eq_quotient_center_card
    hpG rho hrho hcardField
  let b := Module.Free.chooseBasis k V
  have hEnd : Module.finrank k (Module.End k V) =
      Module.finrank k V * Module.finrank k V := by
    rw [(algEquivMatrix b).toLinearEquiv.finrank_eq]
    rw [Module.finrank_matrix]
    simp only [Module.finrank_self, mul_one]
    rw [← Module.finrank_eq_card_chooseBasisIndex k V]
  rw [pow_two, ← hEnd, hend]

/-- The degree-square formula in arbitrary nonmodular characteristic. -/
theorem faithful_irreducible_finrank_sq_eq_of_card_ne_zero
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1))
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (hcardField : (Nat.card G : k) ≠ 0) :
    Module.finrank k V ^ 2 = p ^ (2 * n) := by
  have hsquare :=
    hG.faithful_irreducible_finrank_sq_eq_quotient_center_card_of_card_ne_zero
      hpG rho hrho hcardField
  have hquotient := hG.quotient_center_card_eq hpG hcard
  exact hsquare.trans hquotient

/-- A faithful irreducible representation of an extraspecial group of order
`p ^ (2*n+1)` has degree `p^n` in arbitrary nonmodular characteristic. -/
theorem faithful_irreducible_finrank_eq_of_card_ne_zero
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1))
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (hcardField : (Nat.card G : k) ≠ 0) :
    Module.finrank k V = p ^ n := by
  apply Nat.pow_left_injective (by omega : 2 ≠ 0)
  simpa [pow_mul, Nat.mul_comm] using
    hG.faithful_irreducible_finrank_sq_eq_of_card_ne_zero
      hpG hcard rho hrho hcardField

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
