import Submission.OddOrder.BG.Section02.DerivedSylowAmbientAbelian
import Submission.OddOrder.BG.Section02.DerivedSylowLineSeparation
import Submission.OddOrder.BG.Section02.DerivedSylowPartDivisibility
import Submission.OddOrder.BG.Section02.OddGL2SylowNormalizerTop
import Submission.OddOrder.MathlibSupport.MaschkeTwoLines

/-!
The characteristic-zero strong-induction step of
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [IsAlgClosed F] [CharZero F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]

/-- In characteristic zero, the induction conclusion is that the ambient
commutator is trivial. The auxiliary prime `2` drives the proper-normalizer
and proper-subgroup branches because every divisor of an odd group order is
different from `2`. -/
theorem odd_faithful_finrank_two_commutator_eq_bot_charZero_step
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G))
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      _root_.commutator K = ⊥) :
    _root_.commutator G = ⊥ := by
  classical
  by_contra hcomm
  let D : Subgroup G := _root_.commutator G
  have hcard : Nat.card D ≠ 1 := by
    intro h
    exact hcomm (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hqprime, hqcomm⟩ := Nat.exists_prime_and_dvd hcard
  letI : Fact q.Prime := ⟨hqprime⟩
  have hqodd : Odd q :=
    hodd.of_dvd_nat (hqcomm.trans D.card_subgroup_dvd_card)
  have h2q : 2 ≠ q := by
    intro h
    subst q
    rcases hqodd with ⟨k, hk⟩
    omega
  have ih2 : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup 2 (_root_.commutator K) := by
    intro K _ _ hlt hoddK sigma hsigma
    rw [ih hlt hoddK sigma hsigma]
    exact IsPGroup.of_bot
  let Q : Sylow q G := Classical.choice Sylow.nonempty
  have hQtop : Subgroup.normalizer (Q : Set G) = ⊤ :=
    sylow_normalizer_eq_top_of_card_induction
      rho hrho hodd h2q Q hqcomm ih2
  have hN : (derivedSylowPart Q).Normal :=
    derivedSylowPart_normal_of_normalizer_eq_top Q hQtop
  have habel : IsMulCommutative (derivedSylowPart Q) :=
    derivedSylowPart_isMulCommutative_of_strong_induction
      rho hrho hodd h2q Q ih2
  letI : IsMulCommutative (derivedSylowPart Q) := habel
  letI : NeZero (Nat.card (derivedSylowPart Q)) := ⟨Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card (derivedSylowPart Q) : F) := NeZero.charZero
  obtain ⟨m, n, _, hmn, hmdim, hndim⟩ :=
    exists_complementary_simpleLine_finrank_one
      (derivedSylowRepresentation rho Q) hdim
  have hqpart : q ∣ Nat.card (derivedSylowPart Q) :=
    prime_dvd_card_derivedSylowPart Q hqcomm
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := derivedSylowPart Q) q hqpart
  have hxne : x ≠ 1 := by
    intro hx
    have hxone : orderOf x = 1 := orderOf_eq_one_iff.mpr hx
    exact hqprime.ne_one (hxorder.symm.trans hxone)
  have hxpow : x ^ q = 1 :=
    (congrArg (fun n : ℕ ↦ x ^ n) hxorder).symm.trans
      (pow_orderOf_eq_one x)
  obtain ⟨a, hma, _⟩ := existsUnique_invariantLineAction_eq_smul_id
    (derivedSylowRepresentation rho Q) m hmdim x
  obtain ⟨b, hna, _⟩ := existsUnique_invariantLineAction_eq_smul_id
    (derivedSylowRepresentation rho Q) n hndim x
  have hab : a ≠ b := derivedSylow_line_scalars_ne
    rho hrho Q m n hmn x hxne hqodd hxpow a b hma hna hmdim hndim
  exact hcomm (ambient_commutator_eq_bot_of_derivedSylow_lines
    hodd rho hrho Q hN m n hmn x a b hma hna hab hmdim hndim)

end Submission.OddOrder.BG.Section02
