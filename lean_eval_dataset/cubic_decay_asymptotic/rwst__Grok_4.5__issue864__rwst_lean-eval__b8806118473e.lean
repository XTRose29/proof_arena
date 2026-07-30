import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Basic
import Submission.Helpers

open Filter Topology Set
open Submission.Helpers

namespace Submission

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hy_pos := pos_of_cubic hy_diff hy_cont hy0
  have hinv := inv_sq_eq_of_pos hy_diff hy_cont hy0 hy_pos
  have hy_formula : ∀ t : ℝ, 0 ≤ t → y t = (Real.sqrt (1 + 2 * t))⁻¹ := fun t ht =>
    eq_explicit_of_inv_sq (hinv t ht) (hy_pos t ht)
  have hrewrite : (fun t : ℝ => y t * Real.sqrt t) =ᶠ[atTop]
      fun t => Real.sqrt t / Real.sqrt (1 + 2 * t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hy_formula t ht, div_eq_mul_inv, mul_comm]
  exact Tendsto.congr' hrewrite.symm tendsto_explicit_asymptotic

end Submission
