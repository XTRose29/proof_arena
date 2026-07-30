import ChallengeDeps

namespace LeanEval.Dynamics

open scoped ENNReal
open MeasureTheory

/-- Hausdorff dimension of a measure, used by the companion
entropy–dimension estimates. -/
noncomputable def dimMeasure {M : Type*} [EMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ |
    ∃ s : Set M, MeasurableSet s ∧ μ sᶜ = 0 ∧ dimH s = d}

/-- Twice the balanced forward/backward hyperbolic rate. -/
noncomputable def harmonicMeanLyapunov (lam1 lam2 : ℝ) : ℝ :=
  2 * lam1 * (-lam2) / (lam1 - lam2)

end LeanEval.Dynamics
