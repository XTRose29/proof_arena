import Submission.OddOrder.BG.Section02.OddGL2SubgroupInduction

/-!
The normal primary part `G' ∩ Q` used in the second branch of
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

universe u v w

variable {G : Type u} [Group G]

/-- The part of the ambient commutator lying in a selected Sylow subgroup. -/
def derivedSylowPart {q : ℕ} (Q : Sylow q G) : Subgroup G :=
  _root_.commutator G ⊓ (Q : Subgroup G)

theorem derivedSylowPart_le_commutator {q : ℕ} (Q : Sylow q G) :
    derivedSylowPart Q ≤ _root_.commutator G :=
  inf_le_left

theorem derivedSylowPart_le_sylow {q : ℕ} (Q : Sylow q G) :
    derivedSylowPart Q ≤ (Q : Subgroup G) :=
  inf_le_right

/-- The derived-Sylow part is itself a `q`-group. -/
theorem derivedSylowPart_isPGroup {q : ℕ} (Q : Sylow q G) :
    IsPGroup q (derivedSylowPart Q) :=
  Q.isPGroup'.to_le (derivedSylowPart_le_sylow Q)

/-- If the selected Sylow subgroup is normal, then its intersection with the
ambient commutator is normal as well. -/
theorem derivedSylowPart_normal_of_normalizer_eq_top
    {q : ℕ} (Q : Sylow q G)
    (hQ : Subgroup.normalizer (Q : Set G) = ⊤) :
    (derivedSylowPart Q).Normal := by
  letI : (Q : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp hQ
  change (_root_.commutator G ⊓ (Q : Subgroup G)).Normal
  infer_instance

variable {F : Type v} {V : Type w}
  [Semiring F] [Finite G] [AddCommMonoid V] [Module F V]

/-- Strong induction makes a proper derived-Sylow part commutative. -/
theorem derivedSylowPart_isMulCommutative_of_card_induction
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hodd : Odd (Nat.card G)) (hpq : p ≠ q) (Q : Sylow q G)
    (hproper : derivedSylowPart Q ≠ ⊤)
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    IsMulCommutative (derivedSylowPart Q) :=
  properPSubgroup_isMulCommutative_of_card_induction
    rho hrho hodd (derivedSylowPart Q) hproper
    (derivedSylowPart_isPGroup Q) hpq ih

end Submission.OddOrder.BG.Section02
