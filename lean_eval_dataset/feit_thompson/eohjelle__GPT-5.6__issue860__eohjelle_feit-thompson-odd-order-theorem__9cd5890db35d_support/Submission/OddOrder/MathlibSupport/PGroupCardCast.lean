import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.PGroup

/-!
Nonvanishing of a primary group order in a field of different
characteristic.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F H : Type*} [Field F] {p q : ℕ}
  [CharP F p] [Fact p.Prime] [Fact q.Prime]
  [Group H] [Finite H]

/-- The order of a finite `q`-group is nonzero in characteristic `p` when
`p != q`. -/
theorem neZero_natCard_cast_of_isPGroup
    (hH : IsPGroup q H) (hpq : p ≠ q) :
    NeZero (Nat.card H : F) := by
  apply NeZero.of_not_dvd
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn]
  intro hdvd
  exact hpq (Nat.prime_eq_prime_of_dvd_pow
    (show p.Prime from Fact.out) (show q.Prime from Fact.out) hdvd)

end Submission.OddOrder.MathlibSupport
