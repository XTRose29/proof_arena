import Submission.OddOrder.PF.Section01.ClassFunction

/-!
# Applying a ring homomorphism to class-function values

This file bundles pointwise application of a ring homomorphism as an additive
homomorphism between spaces of class functions.
-/

namespace Submission.OddOrder.PF

universe u v w

namespace ClassFunction

/-- Apply a ring homomorphism pointwise to a class function. -/
def mapRingHom
    {G : Type u} {R : Type v} {S : Type w}
    [Group G] [Ring R] [Ring S]
    (σ : R →+* S) :
    ClassFunction G R →+ ClassFunction G S where
  toFun alpha :=
    ⟨fun g ↦ σ (alpha g), fun x g ↦ congrArg σ (conj_apply alpha x g)⟩
  map_zero' := by
    ext g
    exact σ.map_zero
  map_add' alpha beta := by
    ext g
    exact σ.map_add (alpha g) (beta g)

/-- Pointwise evaluation of a class function mapped along a ring homomorphism. -/
@[simp]
theorem mapRingHom_apply
    {G : Type u} {R : Type v} {S : Type w}
    [Group G] [Ring R] [Ring S]
    (σ : R →+* S) (alpha : ClassFunction G R) (g : G) :
    mapRingHom σ alpha g = σ (alpha g) :=
  rfl

end ClassFunction

end Submission.OddOrder.PF
