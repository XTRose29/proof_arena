import Submission.OddOrder.BG.Section02.OddGL2CharZero
import Submission.OddOrder.BG.Section02.OddGL2PrimeCharacteristic
import Submission.OddOrder.MathlibSupport.PSubgroupAbsentPrime

/-!
The Lean form of `BGsection2.charf'_GL2_abelian` (Bender--Glauberman
Theorem 2.6(a)).
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A finite odd-order group faithfully represented in dimension two is
abelian when the field characteristic does not divide the group order. -/
theorem odd_faithful_finrank_two_isMulCommutative_of_not_dvd_charP
    {p : ℕ} [CharP F p]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G))
    (hpG : ¬p ∣ Nat.card G) :
    IsMulCommutative G := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · letI : Fact p.Prime := ⟨hp⟩
    have hprimary : IsPGroup p (_root_.commutator G) :=
      odd_faithful_finrank_two_commutator_isPGroup_of_prime_characteristic
        rho hrho hdim hodd
    apply (_root_.commutator_eq_bot_iff G).mp
    exact subgroup_eq_bot_of_isPGroup_of_not_dvd_natCard
      (_root_.commutator G) hprimary hpG
  · letI : CharZero F := CharP.charP_to_charZero F
    exact odd_faithful_finrank_two_isMulCommutative_charZero
      rho hrho hdim hodd

end Submission.OddOrder.BG.Section02
