import ChallengeDeps
import Submission.Helpers
import Submission.Hyperbolic

open LeanEval.Dynamics.StableUnstableManifoldsProblem
open scoped Topology
open Filter Polynomial

namespace Submission

theorem stable_unstable_manifolds_exist (n : ℕ) (f : E n → E n) (x₀ : E n)
    (_hf : ContDiffAt ℝ 1 f x₀)
    (_hfix : f x₀ = x₀)
    (_hhyp : IsHyperbolicLinear (fderiv ℝ f x₀))
    (_hf_inv : (fderiv ℝ f x₀).IsInvertible) :
    ∃ U : Set (E n), IsOpen U ∧ x₀ ∈ U ∧
      ∃ Ws Wu : Set (E n),
        Ws = {x | (∀ k : ℕ, f^[k] x ∈ U) ∧
                  Tendsto (fun k => f^[k] x) atTop (𝓝 x₀)} ∧
        Wu = {x | ∃ y : ℕ → E n,
                    y 0 = x ∧
                    (∀ k : ℕ, y k ∈ U) ∧
                    (∀ k : ℕ, f (y (k + 1)) = y k) ∧
                    Tendsto y atTop (𝓝 x₀)} ∧
        Ws ∩ Wu = {x₀} := by
  have hhyper :
      ∀ μ ∈
        (((fderiv ℝ f x₀ : E n →ₗ[ℝ] E n).charpoly.map
          (algebraMap ℝ ℂ)).roots),
        ‖μ‖ ≠ 1 := by
    simpa [IsHyperbolicLinear, complexEigenvalues] using _hhyp
  obtain ⟨q, hq_cont, hq_smul, hq_strict⟩ :=
    Hyperbolic.exists_strict_quadratic
      (fderiv ℝ f x₀ : E n →ₗ[ℝ] E n) hhyper
  obtain ⟨U, hUopen, hx₀U, hstrict⟩ :=
    Helpers.exists_strict_lyapunov_neighborhood
      f x₀ (fderiv ℝ f x₀)
      _hf.differentiableAt_one.hasFDerivAt _hfix
      q hq_cont hq_smul hq_strict
  refine ⟨U, hUopen, hx₀U, _, _, rfl, rfl, ?_⟩
  exact
    Helpers.stable_inter_unstable_eq_singleton_of_strict_lyapunov
      f x₀ U (fun x => q (x - x₀)) _hfix hx₀U
      (hq_cont.comp (continuous_id.sub continuous_const)).continuousAt hstrict

end Submission
