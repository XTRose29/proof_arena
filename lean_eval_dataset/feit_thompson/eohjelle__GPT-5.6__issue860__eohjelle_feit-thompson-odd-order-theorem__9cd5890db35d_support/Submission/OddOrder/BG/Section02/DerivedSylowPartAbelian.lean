import Submission.OddOrder.BG.Section02.DerivedSylowPartProper

/-!
The completed `abelQ` step of `BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Semiring F] [Group G] [Finite G] [AddCommMonoid V] [Module F V]

/-- The derived-Sylow intersection is commutative under the strong induction
hypothesis for faithfully represented proper odd-order subgroups. -/
theorem derivedSylowPart_isMulCommutative_of_strong_induction
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hodd : Odd (Nat.card G)) (hpq : p ≠ q) (Q : Sylow q G)
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    IsMulCommutative (derivedSylowPart Q) := by
  by_contra hnoncomm
  have hcomm : _root_.commutator (derivedSylowPart Q) ≠ ⊥ := by
    intro hbot
    exact hnoncomm
      ((_root_.commutator_eq_bot_iff (derivedSylowPart Q)).mp hbot)
  exact hnoncomm
    (derivedSylowPart_isMulCommutative_of_card_induction
      rho hrho hodd hpq Q
      (derivedSylowPart_ne_top_of_commutator_ne_bot Q hcomm) ih)

end Submission.OddOrder.BG.Section02
