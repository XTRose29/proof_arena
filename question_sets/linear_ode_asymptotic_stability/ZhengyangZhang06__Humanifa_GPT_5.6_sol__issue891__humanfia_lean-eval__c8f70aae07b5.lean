import Submission.Helpers

open Filter Topology
open scoped Matrix
open NormedSpace

namespace Submission

theorem linear_ode_asymptotic_stability (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  let B : Matrix (Fin n) (Fin n) ℂ := A.map (algebraMap ℝ ℂ)
  let y : ℝ → (Fin n → ℂ) := fun t i => x t i
  have hy : ∀ t : ℝ, 0 < t → HasDerivAt y (B *ᵥ y t) t := by
    intro t ht
    rw [hasDerivAt_pi]
    intro i
    have hxi := hasDerivAt_pi.mp (hx t ht) i
    simpa [y, B, Matrix.mulVec, dotProduct] using hxi.ofReal_comp
  let c : Fin n → ℂ := exp ((-1 : ℝ) • B) *ᵥ y 1
  have hyrepr : ∀ t : ℝ, 0 < t → y t = exp (t • B) *ᵥ c := by
    intro t ht
    simpa [c] using Helpers.eq_exp_mulVec_of_hasDerivAt B y hy t ht
  have hcdecay :
      Tendsto (fun t : ℝ => exp ((t : ℂ) • B) *ᵥ c) atTop (nhds 0) :=
    Helpers.tendsto_exp_mulVec_of_eigenvalues_re_neg B (by simpa [B] using hA) c
  have hsmul (t : ℝ) : (t : ℂ) • B = t • B := by
    ext i j
    simp [Complex.real_smul]
  have hcdecayReal :
      Tendsto (fun t : ℝ => exp (t • B) *ᵥ c) atTop (nhds 0) := by
    simpa only [hsmul] using hcdecay
  have hyzero : Tendsto y atTop (nhds 0) := by
    refine hcdecayReal.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hyrepr t ht).symm
  have hnorm : ∀ t : ℝ, ‖y t‖ = ‖x t‖ := by
    intro t
    simp [y, Pi.norm_def]
  simpa only [hnorm, norm_zero] using hyzero.norm

end Submission
