import Submission.OddOrder.BG.Section02.OddGL2PrimeCharacteristic

/-!
The derived-subgroup Sylow containment in
`BGsection2.charf_GL2_der_subS_abelian_Sylow` (Bender--Glauberman
Theorem 2.6(b)).
-/

namespace Submission.OddOrder.BG.Section02

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- In prime characteristic `p`, the commutator of a finite odd-order group
faithfully represented in dimension two lies in a Sylow `p`-subgroup. -/
theorem exists_sylow_commutator_le_of_odd_faithful_finrank_two
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    ∃ P : Sylow p G, _root_.commutator G ≤ (P : Subgroup G) := by
  have hprimary : IsPGroup p (_root_.commutator G) :=
    odd_faithful_finrank_two_commutator_isPGroup_of_prime_characteristic
      rho hrho hdim hodd
  exact hprimary.exists_le_sylow

end Submission.OddOrder.BG.Section02
