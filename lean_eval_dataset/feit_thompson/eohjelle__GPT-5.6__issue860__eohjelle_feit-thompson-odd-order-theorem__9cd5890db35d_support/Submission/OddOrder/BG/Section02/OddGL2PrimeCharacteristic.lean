import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.OddOrder.BG.Section02.OddGL2AlgebraicallyClosed
import Submission.OddOrder.MathlibSupport.RepresentationBaseChange

/-!
The positive-characteristic form of `BGsection2.der1_odd_GL2_charf` over an
arbitrary field.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped TensorProduct

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The commutator of a finite odd-order group faithfully represented in
dimension two is primary for the prime characteristic of the coefficient
field. -/
theorem odd_faithful_finrank_two_commutator_isPGroup_of_prime_characteristic
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    IsPGroup p (_root_.commutator G) := by
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
  exact odd_faithful_finrank_two_commutator_isPGroup
    sigma hsigma hdimA hodd

end Submission.OddOrder.BG.Section02
