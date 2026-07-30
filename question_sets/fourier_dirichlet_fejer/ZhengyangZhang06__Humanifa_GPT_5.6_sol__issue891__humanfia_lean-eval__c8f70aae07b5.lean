import Mathlib
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.LeanEval.Analysis
open LeanEval
namespace LeanEval
namespace Analysis

/-!
# Pointwise and Cesàro convergence of Fourier series

§46 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Dirichlet's pointwise convergence theorem** (main): for a `C¹` 2π-periodic
  complex function `f`, the symmetric Fourier partial sums
  `S_N(f)(x) = ∑_{n = -N}^{N} f̂_n e^{inx}` converge to `f(x)` at every `x ∈ ℝ`.
* **Fejér's theorem** (additional): for a merely *continuous* 2π-periodic `f`,
  the Cesàro means `σ_N(f) = (S_0 + ⋯ + S_N)/(N+1)` of the partial sums converge
  to `f` uniformly on `ℝ`.

mathlib has the circle, the Fourier characters, `fourierCoeffOn`, the `L²`
Fourier series, and uniform convergence under `ℓ¹`-summability
(`hasSum_fourier_series_of_summable`). It has neither the Dirichlet kernel nor
the statement that `C¹` forces pointwise convergence of the symmetric partial
sums — the `C¹` bound `|f̂_n| ≤ C/n` is not `ℓ¹`-summable, so the summable case
does not apply — and it has no Fejér kernel, Cesàro means, or Fejér theorem. The
symmetric partial-sum order `Finset.Icc (-N) N` is essential, since the Fourier
series of a `C¹` function need not converge absolutely.
-/

open Filter Topology

/-- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
theorem dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let g : C(AddCircle (2 * Real.pi), ℂ) :=
    Submission.Helpers.periodicContinuous f _hperiod _hC1.continuous
  have hcoeff : Summable (fourierCoeff g) := by
    refine (Submission.Helpers.summable_fourierCoeffOn_of_contDiff_one_periodic
      _hperiod _hC1).congr fun n => ?_
    exact (Submission.Helpers.fourierCoeff_periodicContinuous
      f _hperiod _hC1.continuous n).symm
  have hsum := has_pointwise_sum_fourier_series_of_summable hcoeff
    (x : AddCircle (2 * Real.pi))
  have hsymmetric : HasSum
      (fun n : ℤ => fourierCoeff g n • fourier n (x : AddCircle (2 * Real.pi)))
      (g (x : AddCircle (2 * Real.pi))) (SummationFilter.symmetricIcc ℤ) :=
    Filter.Tendsto.mono_left hsum SummationFilter.le_atTop
  have htend := SummationFilter.hasSum_symmetricIcc_iff.mp hsymmetric
  simpa only [fourierPartialSum, g, Submission.Helpers.fourierCoeff_periodicContinuous,
    Submission.Helpers.periodicContinuous_apply, Submission.Helpers.fourier_two_pi_apply,
    smul_eq_mul] using htend

/-- **Fejér's theorem** (§46). For every *continuous* 2π-periodic complex
function `f` — without the `C¹` hypothesis of Dirichlet's theorem — the Cesàro
means `σ_N(f)` of the symmetric Fourier partial sums converge to `f` uniformly
on `ℝ`. -/
theorem fejer
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let g : C(AddCircle (2 * Real.pi), ℂ) :=
    Submission.Helpers.periodicContinuous f _hperiod _hcont
  have hg := Submission.Fejer.tendsto_circleCesaroMean g
  rw [Metric.tendsto_atTop] at hg
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  obtain ⟨M, hM⟩ := hg ε hε
  filter_upwards [eventually_ge_atTop M] with N hN
  intro x
  have hpoint := ContinuousMap.norm_coe_le_norm
    (Submission.Fejer.circleCesaroMean g N - g) (x : AddCircle (2 * Real.pi))
  have hglobal := hM N hN
  rw [dist_eq_norm] at hglobal
  have hlt := lt_of_le_of_lt hpoint hglobal
  rw [dist_comm]
  simpa only [dist_eq_norm, ContinuousMap.sub_apply, g,
    Submission.Helpers.circleCesaroMean_periodicContinuous,
    Submission.Helpers.periodicContinuous_apply] using hlt

end Analysis
end LeanEval

end Submission
