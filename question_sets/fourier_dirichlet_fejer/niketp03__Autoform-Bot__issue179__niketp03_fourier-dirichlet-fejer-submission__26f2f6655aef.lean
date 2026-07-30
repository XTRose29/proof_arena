/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers
import ChallengeDeps

namespace Submission

namespace LeanEval
namespace Analysis

open Filter Topology

/-- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
theorem dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => _root_.LeanEval.Analysis.fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  exact _root_.Submission.dirichlet_pointwise _hperiod _hC1 x

/-- **Fejér's theorem** (§46). For every *continuous* 2π-periodic complex
function `f` — without the `C¹` hypothesis of Dirichlet's theorem — the Cesàro
means `σ_N(f)` of the symmetric Fourier partial sums converge to `f` uniformly
on `ℝ`. -/
theorem fejer
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => _root_.LeanEval.Analysis.fourierCesaroMean f N) f atTop := by
  exact _root_.Submission.fejer _hperiod _hcont

end Analysis
end LeanEval

end Submission
