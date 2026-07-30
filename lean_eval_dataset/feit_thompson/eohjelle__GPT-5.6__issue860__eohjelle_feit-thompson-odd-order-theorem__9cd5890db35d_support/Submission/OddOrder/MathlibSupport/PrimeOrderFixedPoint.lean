import Mathlib.GroupTheory.PGroup

/-!
Fixed points for actions of finite groups of prime order.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {A : Type u} {X : Type v}
variable [Group A] [Finite A] [MulAction A X]

/-- A finite group of prime order acting on a finite set of coprime
cardinality has a fixed point. -/
theorem nonempty_fixedPoints_of_prime_natCard
    (hprime : (Nat.card A).Prime)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card X)) :
    (MulAction.fixedPoints A X).Nonempty := by
  let p := Nat.card A
  letI : Fact p.Prime := ⟨hprime⟩
  have hA : IsPGroup p A := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [p]⟩
  apply hA.nonempty_fixed_point_of_prime_not_dvd_card X
  exact hprime.coprime_iff_not_dvd.mp hcop

end Submission.OddOrder.MathlibSupport
