import Submission.BoundaryIntegrals

open scoped Polynomial

noncomputable section

namespace Submission.Helpers

def IsRationalMap (K : Set ℂ) (r : C(K, ℂ)) : Prop :=
  ∃ p q : ℂ[X],
    (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
      ∀ z : K, r z = p.eval (z : ℂ) / q.eval (z : ℂ)

end Submission.Helpers
