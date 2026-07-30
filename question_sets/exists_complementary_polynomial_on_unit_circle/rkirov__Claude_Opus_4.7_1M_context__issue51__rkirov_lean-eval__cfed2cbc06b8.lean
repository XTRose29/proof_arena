import Mathlib
import Submission.Helpers
import Submission.Final

open Polynomial Complex Submission.Helpers

namespace Submission

theorem exists_complementary_polynomial_on_unit_circle (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  -- Convert the Circle hypothesis to a complex hypothesis with ‖z‖ = 1.
  have hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1 := by
    intros z hz
    exact hP ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨Q, hQND, hQ_eq⟩ := Submission.Helpers.exists_Q_general P hPbd
  refine ⟨Q, hQND, ?_⟩
  intro z
  exact hQ_eq (z : ℂ) (Circle.norm_coe z)

end Submission
