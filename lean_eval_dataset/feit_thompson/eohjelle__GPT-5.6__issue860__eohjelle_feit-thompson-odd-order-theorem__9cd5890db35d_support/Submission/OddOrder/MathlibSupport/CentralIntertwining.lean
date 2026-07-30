import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Ring.Commute

/-!
Central endomorphisms as intertwining maps.
-/

namespace Submission.OddOrder.MathlibSupport

variable {k G V : Type*} [Semiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V]

/-- An endomorphism commuting with every representation image is an
intertwining endomorphism. -/
def centralIntertwiningMap
    (rho : Representation k G V) (A : Module.End k V)
    (hA : ∀ g : G, Commute (rho g) A) :
    Representation.IntertwiningMap rho rho where
  toLinearMap := A
  isIntertwining' g := (hA g).eq.symm

@[simp]
theorem centralIntertwiningMap_toLinearMap
    (rho : Representation k G V) (A : Module.End k V)
    (hA : ∀ g : G, Commute (rho g) A) :
    (centralIntertwiningMap rho A hA).toLinearMap = A :=
  rfl

@[simp]
theorem centralIntertwiningMap_apply
    (rho : Representation k G V) (A : Module.End k V)
    (hA : ∀ g : G, Commute (rho g) A) (v : V) :
    centralIntertwiningMap rho A hA v = A v :=
  rfl

end Submission.OddOrder.MathlibSupport
