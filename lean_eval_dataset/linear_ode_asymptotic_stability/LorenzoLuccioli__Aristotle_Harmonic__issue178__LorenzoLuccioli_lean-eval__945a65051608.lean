import Mathlib
import Submission.Helpers

open scoped Matrix
open NormedSpace Filter

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace Submission

theorem linear_ode_asymptotic_stability (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  -- For t ≥ 1, x(t) = exp((t-1)•A).mulVec(x 1) by ODE uniqueness
  have heq := linear_ode_eq_exp n A x hx
  -- exp(s•A).mulVec(x 1) → 0 as s → ∞
  have hexp := exp_mulVec_tendsto_zero n A hA (x 1)
  -- Since x t = exp((t-1)•A).mulVec(x 1) eventually, ‖x t‖ → 0
  suffices Filter.Tendsto (fun t : ℝ => x t) atTop (nhds 0) by
    have := this.norm
    simp [norm_zero] at this
    exact this
  apply Filter.Tendsto.congr'
  · show ∀ᶠ t in atTop, (exp ((t - 1) • A)).mulVec (x 1) = x t
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    exact (heq t ht).symm
  · -- exp((t-1)•A).mulVec(x 1) → 0
    exact hexp.comp (tendsto_atTop_add_const_right _ _ tendsto_id)

end Submission
