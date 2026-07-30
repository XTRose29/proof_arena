import Mathlib

namespace Submission.Helpers

lemma explicitSolution_hasDerivAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => 1 / Real.sqrt (1 + 2 * s))
      (-(1 / Real.sqrt (1 + 2 * t)) ^ 3) t := by
  have hpos : 0 < 1 + 2 * t := by linarith
  have hinner : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 t := by
    simpa [add_comm] using ((hasDerivAt_id t).const_mul 2).const_add 1
  have hsqrt := hinner.sqrt hpos.ne'
  have hsqrt_pos : 0 < Real.sqrt (1 + 2 * t) := Real.sqrt_pos.2 hpos
  have hderiv :
      -(2 / (2 * Real.sqrt (1 + 2 * t))) / Real.sqrt (1 + 2 * t) ^ 2 =
        -((Real.sqrt (1 + 2 * t))⁻¹) ^ 3 := by
    field_simp [hsqrt_pos.ne']
  convert hsqrt.inv hsqrt_pos.ne' using 1
  · rfl
  · funext s
    simp only [one_div, Pi.inv_apply]
  · rw [one_div]
    exact hderiv.symm

end Submission.Helpers
