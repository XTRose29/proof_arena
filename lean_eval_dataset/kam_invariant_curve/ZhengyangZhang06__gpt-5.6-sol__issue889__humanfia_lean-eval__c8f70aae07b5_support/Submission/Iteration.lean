import Submission.Remainder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

/-- Integral Taylor's formula in the form used by the quantitative Newton
remainder. -/
theorem taylorRemainder_eq {f x v : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    taylorRemainder f x v t =
      f (x t + v t) - f (x t) - deriv f (x t) * v t := by
  let X := x t
  let V := v t
  have hfDiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hdfSmooth : ContDiff ℝ ∞ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2
  have hddfSmooth : ContDiff ℝ ∞ (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp hdfSmooth).2
  have hdfDiff : Differentiable ℝ (deriv f) :=
    hdfSmooth.differentiable (by simp)
  have hlineCont : Continuous (fun a : ℝ => X + a * V) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hline (a : ℝ) :
      HasDerivAt (fun b : ℝ => X + b * V) V a := by
    exact (hasDerivAt_mul_const V).const_add X
  have hcomp (a : ℝ) :
      HasDerivAt (fun b : ℝ => f (X + b * V))
        (deriv f (X + a * V) * V) a :=
    hfDiff.differentiableAt.hasDerivAt.comp a (hline a)
  have hdcomp (a : ℝ) :
      HasDerivAt (fun b : ℝ => deriv f (X + b * V))
        (deriv (deriv f) (X + a * V) * V) a :=
    hdfDiff.differentiableAt.hasDerivAt.comp a (hline a)
  have hfund :
      (∫ a in (0 : ℝ)..1, V * deriv f (X + a * V)) =
        f (X + V) - f X := by
    have hint : IntervalIntegrable
        (fun a : ℝ => deriv f (X + a * V) * V) volume 0 1 :=
      ((hdfSmooth.continuous.comp hlineCont).mul continuous_const).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun a _ => hcomp a)
      hint
    simpa only [mul_comm, one_mul, mul_one, zero_mul, mul_zero, add_zero] using h
  have hu (a : ℝ) :
      HasDerivAt (fun b : ℝ => 1 - b) (-1) a := by
    simpa using (hasDerivAt_id a).const_sub (1 : ℝ)
  have hparts :
      (∫ a in (0 : ℝ)..1,
        (1 - a) * (V * deriv (deriv f) (X + a * V))) =
        -deriv f X + ∫ a in (0 : ℝ)..1, deriv f (X + a * V) := by
    have hvint : IntervalIntegrable
        (fun a : ℝ => V * deriv (deriv f) (X + a * V)) volume 0 1 :=
      (continuous_const.mul (hddfSmooth.continuous.comp hlineCont)).intervalIntegrable 0 1
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := 1)
      (u := fun a : ℝ => 1 - a)
      (v := fun a : ℝ => deriv f (X + a * V))
      (u' := fun _ : ℝ => -1)
      (v' := fun a : ℝ => V * deriv (deriv f) (X + a * V))
      (fun a _ => hu a)
      (fun a _ => (hdcomp a).congr_deriv (mul_comm _ _))
      (continuous_const.intervalIntegrable 0 1)
      hvint
    simpa [intervalIntegral.integral_neg] using h
  simp only [taylorRemainder, taylorIntegral, sliceIntegral, taylorKernel]
  change V ^ 2 * (∫ a in (0 : ℝ)..1,
      (1 - a) * deriv (deriv f) (X + a * V)) = _
  have hfactor :
      (∫ a in (0 : ℝ)..1,
        (1 - a) * (V * deriv (deriv f) (X + a * V))) =
        V * (∫ a in (0 : ℝ)..1,
          (1 - a) * deriv (deriv f) (X + a * V)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro a _
    ring
  calc
    V ^ 2 * (∫ a in (0 : ℝ)..1,
        (1 - a) * deriv (deriv f) (X + a * V)) =
        V * (∫ a in (0 : ℝ)..1,
          (1 - a) * (V * deriv (deriv f) (X + a * V))) := by
      rw [hfactor]
      ring
    _ = V * (-deriv f X +
        ∫ a in (0 : ℝ)..1, deriv f (X + a * V)) := by rw [hparts]
    _ = -deriv f X * V +
        ∫ a in (0 : ℝ)..1, V * deriv f (X + a * V) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = f (X + V) - f X - deriv f X * V := by rw [hfund]; ring
    _ = f (x t + v t) - f (x t) - deriv f (x t) * v t := rfl

end

end Submission.Majorant
