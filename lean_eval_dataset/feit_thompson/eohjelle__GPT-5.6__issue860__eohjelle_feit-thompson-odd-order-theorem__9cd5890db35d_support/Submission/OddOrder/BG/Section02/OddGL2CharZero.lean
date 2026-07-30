import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.OddOrder.BG.Section02.OddGL2CharZeroAlgebraicallyClosed
import Submission.OddOrder.MathlibSupport.RepresentationBaseChange

/-!
The characteristic-zero form of `BGsection2.der1_odd_GL2_charf` over an
arbitrary field.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped TensorProduct

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [CharZero F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A finite odd-order group faithfully represented in dimension two over an
arbitrary characteristic-zero field has trivial commutator. -/
theorem odd_faithful_finrank_two_commutator_eq_bot_charZero
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    _root_.commutator G = ⊥ := by
  let A := AlgebraicClosure F
  let W := A ⊗[F] V
  let sigma : Representation A G W :=
    representationBaseChange (A := A) rho
  have hsigma : Function.Injective sigma :=
    representationBaseChange_injective (A := A) rho hrho
  have hdimA : Module.finrank A W = 2 := by
    exact (finrank_representationBaseChange
      (F := F) (A := A) (V := V)).trans hdim
  letI : Nontrivial W := Module.nontrivial_of_finrank_eq_succ hdimA
  exact odd_faithful_finrank_two_commutator_eq_bot_charZero_algClosed
    sigma hsigma hdimA hodd

/-- Equivalently, every finite odd-order subgroup of `GL₂` over a
characteristic-zero field is abelian. -/
theorem odd_faithful_finrank_two_isMulCommutative_charZero
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    IsMulCommutative G :=
  (_root_.commutator_eq_bot_iff G).mp
    (odd_faithful_finrank_two_commutator_eq_bot_charZero
      rho hrho hdim hodd)

end Submission.OddOrder.BG.Section02
