import Submission.OddOrder.BG.Section02.DerivedSylowAmbientAbelian
import Submission.OddOrder.BG.Section02.DerivedSylowLineSeparation
import Submission.OddOrder.BG.Section02.DerivedSylowPartDivisibility
import Submission.OddOrder.BG.Section02.OddGL2SylowNormalizerTop
import Submission.OddOrder.MathlibSupport.NonPGroupPrimeDivisor

/-!
The strong-induction step of `BGsection2.der1_odd_GL2_charf` over an
algebraically closed field.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [IsAlgClosed F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]

/-- The induction step for the odd faithful two-dimensional linear-group
theorem: assuming the characteristic-primary conclusion for smaller odd
faithfully represented groups, it holds for `G`. -/
theorem odd_faithful_finrank_two_commutator_isPGroup_step
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G))
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    IsPGroup p (_root_.commutator G) := by
  classical
  by_contra hprimary
  obtain ⟨q, hqprime, hqp, hqcomm⟩ :=
    exists_prime_ne_dvd_natCard_of_not_isPGroup hprimary
  letI : Fact q.Prime := ⟨hqprime⟩
  let Q : Sylow q G := Classical.choice Sylow.nonempty
  have hpq : p ≠ q := hqp.symm
  have hQtop : Subgroup.normalizer (Q : Set G) = ⊤ :=
    sylow_normalizer_eq_top_of_card_induction
      rho hrho hodd hpq Q hqcomm ih
  have hN : (derivedSylowPart Q).Normal :=
    derivedSylowPart_normal_of_normalizer_eq_top Q hQtop
  have habel : IsMulCommutative (derivedSylowPart Q) :=
    derivedSylowPart_isMulCommutative_of_strong_induction
      rho hrho hodd hpq Q ih
  obtain ⟨m, n, _, hmn, hmdim, hndim⟩ :=
    exists_derivedSylow_complementary_lines rho hdim hpq Q habel
  have hqpart : q ∣ Nat.card (derivedSylowPart Q) :=
    prime_dvd_card_derivedSylowPart Q hqcomm
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := derivedSylowPart Q) q hqpart
  have hxne : x ≠ 1 := by
    intro hx
    have hxone : orderOf x = 1 := orderOf_eq_one_iff.mpr hx
    exact hqprime.ne_one (hxorder.symm.trans hxone)
  have hxpow : x ^ q = 1 := by
    exact (congrArg (fun n : ℕ ↦ x ^ n) hxorder).symm.trans
      (pow_orderOf_eq_one x)
  have hqodd : Odd q :=
    hodd.of_dvd_nat
      (hqcomm.trans (_root_.commutator G).card_subgroup_dvd_card)
  obtain ⟨a, hma, _⟩ := existsUnique_invariantLineAction_eq_smul_id
    (derivedSylowRepresentation rho Q) m hmdim x
  obtain ⟨b, hna, _⟩ := existsUnique_invariantLineAction_eq_smul_id
    (derivedSylowRepresentation rho Q) n hndim x
  have hab : a ≠ b := derivedSylow_line_scalars_ne
    rho hrho Q m n hmn x hxne hqodd hxpow a b hma hna hmdim hndim
  have hbot : _root_.commutator G = ⊥ :=
    ambient_commutator_eq_bot_of_derivedSylow_lines
      hodd rho hrho Q hN m n hmn x a b hma hna hab hmdim hndim
  apply hqprime.not_dvd_one
  simpa [hbot] using hqcomm

end Submission.OddOrder.BG.Section02
