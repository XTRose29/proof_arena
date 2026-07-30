import Mathlib.RepresentationTheory.Basic
import Submission.OddOrder.MathlibSupport.CrossPrimeDerivedAbelian
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Cardinality-induction adapters for `BGsection2.der1_odd_GL2_charf`.

The two-dimensional representation is restricted to a proper subgroup.  Its
faithfulness, odd group order, and strict cardinality decrease are then fed to
the strong induction hypothesis.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Semiring F] [Group G] [Finite G] [AddCommMonoid V] [Module F V]

/-- Restrict the faithful representation to a proper subgroup and apply the
strong cardinality-induction hypothesis. -/
theorem properSubgroup_commutator_isPGroup_of_card_induction
    {p : ℕ} (rho : Representation F G V) (hrho : Function.Injective rho)
    (hodd : Odd (Nat.card G)) (H : Subgroup G) (hH : H ≠ ⊤)
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    IsPGroup p (_root_.commutator H) := by
  apply ih (natCard_subgroup_lt_of_ne_top H hH)
    (odd_natCard_subgroup H hodd) (rho.comp H.subtype)
  exact hrho.comp H.subtype_injective

/-- The proper-normalizer specialization of the subgroup induction step. -/
theorem normalizer_commutator_isPGroup_of_card_induction
    {p q : ℕ} (rho : Representation F G V) (hrho : Function.Injective rho)
    (hodd : Odd (Nat.card G)) (Q : Sylow q G)
    (hQ : Subgroup.normalizer (Q : Set G) ≠ ⊤)
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    IsPGroup p (_root_.commutator (Subgroup.normalizer (Q : Set G))) :=
  properSubgroup_commutator_isPGroup_of_card_induction
    rho hrho hodd (Subgroup.normalizer (Q : Set G)) hQ ih

/-- The subgroup induction step makes a proper `q`-subgroup abelian when the
induction prime `p` is distinct from `q`. -/
theorem properPSubgroup_isMulCommutative_of_card_induction
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hodd : Odd (Nat.card G)) (Q : Subgroup G) (hQproper : Q ≠ ⊤)
    (hQ : IsPGroup q Q) (hpq : p ≠ q)
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    IsMulCommutative Q := by
  apply isMulCommutative_of_isPGroup_of_commutator_isPGroup hQ
    (properSubgroup_commutator_isPGroup_of_card_induction
      rho hrho hodd Q hQproper ih)
  exact hpq

end Submission.OddOrder.BG.Section02
