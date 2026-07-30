import Submission.OddOrder.BG.Section02.OddGL2PrimeCharacteristic

/-!
The characteristic-uniform form of `BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The commutator of a finite odd-order group faithfully represented in
dimension two is a `p`-group when the coefficient field has characteristic
`p`. For characteristic zero the `IsPGroup 0` conclusion is tautological. -/
theorem odd_faithful_finrank_two_commutator_isPGroup_charP
    {p : ℕ} [CharP F p]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    IsPGroup p (_root_.commutator G) := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · letI : Fact p.Prime := ⟨hp⟩
    exact odd_faithful_finrank_two_commutator_isPGroup_of_prime_characteristic
      rho hrho hdim hodd
  · intro g
    exact ⟨1, by simp⟩

end Submission.OddOrder.BG.Section02
