import Submission.OddOrder.BG.AppendixAB.QuadraticRepresentation
import Submission.OddOrder.MathlibSupport.SquareZeroAnticommutator
import Mathlib.Algebra.Ring.Commute

/-!
The central operator attached to two quadratic elements.

This constructs the operator called `A` in `BGappendixAB.odd_p_stable` and
proves that it commutes with the representation images of both generators.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The anticommutator of the two conjugation deviations. -/
def quadraticAnticommutator
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    (x y : Subgroup.normalizer (E : Set G)) :
    Module.End (ZMod p) (Additive E) :=
  anticommutator (conjugationDeviation E p x) (conjugationDeviation E p y)

theorem quadraticAnticommutator_commutes_left
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x) :
    Commute (normalizerConjugationRepresentation E p ⟨x, hxN⟩)
      (quadraticAnticommutator E p ⟨x, hxN⟩ ⟨y, hyN⟩) := by
  let Dx := conjugationDeviation E p ⟨x, hxN⟩
  let Dy := conjugationDeviation E p ⟨y, hyN⟩
  have hDx : Dx * Dx = 0 :=
    conjugationDeviation_mul_self_eq_zero E p hxN hx
  have hcomm : Commute Dx (anticommutator Dx Dy) :=
    commute_anticommutator_left hDx
  have hrho : normalizerConjugationRepresentation E p ⟨x, hxN⟩ = Dx + 1 := by
    dsimp [Dx, conjugationDeviation]
    exact (sub_add_cancel _ _).symm
  rw [hrho]
  exact hcomm.add_left (Commute.one_left _)

theorem quadraticAnticommutator_commutes_right
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hy : IsQuadraticPElement p E y) :
    Commute (normalizerConjugationRepresentation E p ⟨y, hyN⟩)
      (quadraticAnticommutator E p ⟨x, hxN⟩ ⟨y, hyN⟩) := by
  let Dx := conjugationDeviation E p ⟨x, hxN⟩
  let Dy := conjugationDeviation E p ⟨y, hyN⟩
  have hDy : Dy * Dy = 0 :=
    conjugationDeviation_mul_self_eq_zero E p hyN hy
  have hcomm : Commute Dy (anticommutator Dx Dy) :=
    commute_anticommutator_right hDy
  have hrho : normalizerConjugationRepresentation E p ⟨y, hyN⟩ = Dy + 1 := by
    dsimp [Dy, conjugationDeviation]
    exact (sub_add_cancel _ _).symm
  rw [hrho]
  exact hcomm.add_left (Commute.one_left _)

end Submission.OddOrder.BG.AppendixAB
