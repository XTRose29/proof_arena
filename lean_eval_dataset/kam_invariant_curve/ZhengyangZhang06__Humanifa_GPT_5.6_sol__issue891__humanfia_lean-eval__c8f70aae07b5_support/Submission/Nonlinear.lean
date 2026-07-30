import Submission.Cohomological

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Nonlinear

noncomputable section

/-- The average over one unit period. -/
def periodMean (g : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, g t

/-- Projection onto the functions with vanishing zero Fourier mode. -/
def removeMean (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  g t - periodMean g

theorem removeMean_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (removeMean g) := by
  exact hg.sub contDiff_const

theorem removeMean_periodic {g : ℝ → ℝ}
    (hper : Function.Periodic g 1) :
    Function.Periodic (removeMean g) 1 := by
  intro t
  simp only [removeMean, hper t]

theorem removeMean_integral_eq_zero {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t in (0 : ℝ)..1, removeMean g t = 0 := by
  have hgInt : IntervalIntegrable g volume (0 : ℝ) 1 :=
    hg.intervalIntegrable 0 1
  rw [show (fun t => removeMean g t) =
      fun t => g t - periodMean g by rfl]
  rw [intervalIntegral.integral_sub hgInt intervalIntegrable_const]
  simp [periodMean]

/-- The nonlinear forcing evaluated along the lift `t ↦ t + u t`. -/
def forcing (c : ℝ) (f u : ℝ → ℝ) (t : ℝ) : ℝ :=
  c * f (t + u t)

theorem forcing_contDiff (c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (forcing c f u) := by
  exact contDiff_const.mul (hf.comp (contDiff_id.add hu))

theorem forcing_periodic (c : ℝ) {f u : ℝ → ℝ}
    (hf : Function.Periodic f 1) (hu : Function.Periodic u 1) :
    Function.Periodic (forcing c f u) 1 := by
  intro t
  simp only [forcing, hu t]
  congr 1
  rw [show t + 1 + u t = (t + u t) + 1 by ring]
  exact hf (t + u t)

/-- The forcing with its zero Fourier mode removed. -/
def projectedForcing (c : ℝ) (f u : ℝ → ℝ) : ℝ → ℝ :=
  removeMean (forcing c f u)

theorem projectedForcing_contDiff (c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (projectedForcing c f u) :=
  removeMean_contDiff (forcing_contDiff c hf hu)

theorem projectedForcing_periodic (c : ℝ) {f u : ℝ → ℝ}
    (hf : Function.Periodic f 1) (hu : Function.Periodic u 1) :
    Function.Periodic (projectedForcing c f u) 1 :=
  removeMean_periodic (forcing_periodic c hf hu)

theorem projectedForcing_integral_eq_zero (c : ℝ) {f u : ℝ → ℝ}
    (hf : Continuous f) (hu : Continuous u) :
    ∫ t in (0 : ℝ)..1, projectedForcing c f u t = 0 := by
  apply removeMean_integral_eq_zero
  exact continuous_const.mul (hf.comp (continuous_id.add hu))

/-- One exact cohomological correction for the mean-projected nonlinear
forcing. -/
def correction (α c : ℝ) (f u : ℝ → ℝ) : ℝ → ℝ :=
  Cohomological.solve α (projectedForcing c f u)

theorem correction_contDiff {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1) :
    ContDiff ℝ ∞ (correction α c f u) := by
  exact Cohomological.solve_contDiff hα
    (projectedForcing_contDiff c hf hu)
    (projectedForcing_periodic c hfper huper)

theorem correction_periodic (α c : ℝ) (f u : ℝ → ℝ) :
    Function.Periodic (correction α c f u) 1 :=
  Cohomological.solve_periodic α (projectedForcing c f u)

theorem discreteLaplacian_correction {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1)
    (t : ℝ) :
    Helpers.discreteLaplacian α (correction α c f u) t =
      projectedForcing c f u t := by
  exact Cohomological.discreteLaplacian_solve hα
    (projectedForcing_contDiff c hf hu)
    (projectedForcing_periodic c hfper huper)
    (projectedForcing_integral_eq_zero c hf.continuous hu.continuous) t

theorem fixedPoint_equation {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1)
    (hfix : correction α c f u = u)
    (hmean : periodMean (forcing c f u) = 0) (t : ℝ) :
    Helpers.discreteLaplacian α u t = c * f (t + u t) := by
  calc
    Helpers.discreteLaplacian α u t =
        Helpers.discreteLaplacian α (correction α c f u) t := by
      rw [hfix]
    _ = projectedForcing c f u t :=
      discreteLaplacian_correction hα c hf hu hfper huper t
    _ = c * f (t + u t) := by
      simp [projectedForcing, removeMean, forcing, hmean]

/-- Once the nonlinear iteration supplies a small fixed point and its scalar
zero-mode equation, all properties in the benchmark conclusion follow. -/
theorem invariantCurve_of_fixedPoint {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (K : NNReal)
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1)
    (huLip : LipschitzWith K u) (hK : (K : ℝ) < 1)
    (hfix : correction α c f u = u)
    (hmean : periodMean (forcing c f u) = 0) :
    ∃ q : ℝ → ℝ,
      ContDiff ℝ ∞ q ∧ StrictMono q ∧
      Function.Periodic (fun t => q t - t) 1 ∧
      ∀ t : ℝ,
        q (t + α) - 2 * q t + q (t - α) = c * f (q t) := by
  apply Helpers.invariant_curve_of_correction α c f u K hu huper huLip hK
  exact fixedPoint_equation hα c hf hu hfper huper hfix hmean

end

end Submission.Nonlinear
