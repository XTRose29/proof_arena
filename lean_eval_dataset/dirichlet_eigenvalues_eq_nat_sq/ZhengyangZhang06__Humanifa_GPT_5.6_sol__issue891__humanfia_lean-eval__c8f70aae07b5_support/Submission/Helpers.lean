import Mathlib

namespace Submission.Helpers

open Set

lemma eq_left_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Icc a b, HasDerivAt f 0 x) :
    ∀ x ∈ Icc a b, f x = f a := by
  apply constant_of_has_deriv_right_zero
  · intro x hx
    exact (h x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (h x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt

end Submission.Helpers
