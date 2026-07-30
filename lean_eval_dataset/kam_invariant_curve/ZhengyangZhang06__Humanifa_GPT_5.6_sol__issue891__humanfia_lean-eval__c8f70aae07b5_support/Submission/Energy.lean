import Submission.Nonlinear

open MeasureTheory
open scoped ContDiff

namespace Submission.Energy

noncomputable section

/-- A normalized primitive of a continuous real function. -/
def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, f t

theorem primitive_periodic {f : ℝ → ℝ} (hf : Continuous f)
    (hfper : Function.Periodic f 1)
    (hmean : ∫ t in (0 : ℝ)..1, f t = 0) :
    Function.Periodic (primitive f) 1 := by
  intro x
  have hleft : IntervalIntegrable f volume (0 : ℝ) x :=
    hf.intervalIntegrable 0 x
  have hright : IntervalIntegrable f volume x (x + 1) :=
    hf.intervalIntegrable x (x + 1)
  have hperiod : ∫ t in x..x + 1, f t = 0 := by
    rw [hfper.intervalIntegral_add_eq x 0]
    simpa only [zero_add] using hmean
  calc
    primitive f (x + 1) =
        (∫ t in (0 : ℝ)..x, f t) + ∫ t in x..x + 1, f t := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals hleft hright
    _ = primitive f x := by simp [primitive, hperiod]

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 x)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/-- The mean-zero condition makes the nonlinear forcing orthogonal to the
derivative of every smooth degree-one lift. -/
theorem integral_comp_id_add_mul_one_add_deriv_eq_zero
    {f u : ℝ → ℝ} (hf : Continuous f)
    (hfper : Function.Periodic f 1)
    (hmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1) :
    ∫ t in (0 : ℝ)..1,
      f (t + u t) * (1 + deriv u t) = 0 := by
  have huDiff : Differentiable ℝ u := hu.differentiable (by simp)
  let q : ℝ → ℝ := fun t => t + u t
  have hqDeriv : ∀ t : ℝ,
      HasDerivAt q (1 + deriv u t) t := by
    intro t
    exact (hasDerivAt_id t).add huDiff.differentiableAt.hasDerivAt
  have hcompDeriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => primitive f (q x))
        (f (q t) * (1 + deriv u t)) t := by
    intro t _
    exact (primitive_hasDerivAt hf (q t)).comp t (hqDeriv t)
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hforcingCont : Continuous (fun t =>
      f (q t) * (1 + deriv u t)) :=
    (hf.comp (continuous_id.add hu.continuous)).mul
      (continuous_const.add hdu)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hcompDeriv
    (hforcingCont.intervalIntegrable 0 1)
  have huOne : u 1 = u 0 := by simpa using huper 0
  have hqOne : q 1 = q 0 + 1 := by
    simp only [q, huOne]
    ring
  have hprimPer := primitive_periodic hf hfper hmean (q 0)
  rw [hqOne, hprimPer] at hfund
  simpa only [q, sub_self] using hfund

theorem integral_deriv_mul_add_mul_deriv_eq_zero {v w : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w)
    (hvper : Function.Periodic v 1) (hwper : Function.Periodic w 1) :
    ∫ t in (0 : ℝ)..1,
      deriv v t * w t + v t * deriv w t = 0 := by
  have hvDiff : Differentiable ℝ v := hv.differentiable (by simp)
  have hwDiff : Differentiable ℝ w := hw.differentiable (by simp)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => v x * w x)
        (deriv v t * w t + v t * deriv w t) t := by
    intro t _
    exact hvDiff.differentiableAt.hasDerivAt.mul
      hwDiff.differentiableAt.hasDerivAt
  have hcont : Continuous (fun t =>
      deriv v t * w t + v t * deriv w t) :=
    (hv.continuous_deriv (by simp)).mul hw.continuous |>.add
      (hv.continuous.mul (hw.continuous_deriv (by simp)))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)
  have hvOne : v 1 = v 0 := by simpa using hvper 0
  have hwOne : w 1 = w 0 := by simpa using hwper 0
  simpa only [hvOne, hwOne, sub_self] using hfund

theorem integral_mul_deriv_eq_zero {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1) :
    ∫ t in (0 : ℝ)..1, u t * deriv u t = 0 := by
  have h := integral_deriv_mul_add_mul_deriv_eq_zero hu hu huper huper
  have heq : (fun t => deriv u t * u t + u t * deriv u t) =
      fun t => 2 * (u t * deriv u t) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_const_mul] at h
  linarith

/-- The discrete Laplacian has zero pairing with the derivative of a smooth
periodic function.  This is the variational identity used to eliminate the
scalar zero mode in the KAM equation. -/
theorem integral_discreteLaplacian_mul_deriv_eq_zero
    (α : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1) :
    ∫ t in (0 : ℝ)..1,
      Helpers.discreteLaplacian α u t * deriv u t = 0 := by
  have huDiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hduper : Function.Periodic (deriv u) 1 := by
    simpa only [iteratedDeriv_one] using Helpers.periodic_iteratedDeriv huper 1
  have hshiftSmooth : ContDiff ℝ ∞ (fun t => u (t + α)) := by
    fun_prop
  have hshiftPer : Function.Periodic (fun t => u (t + α)) 1 := by
    intro t
    change u (t + 1 + α) = u (t + α)
    rw [show t + 1 + α = (t + α) + 1 by ring, huper (t + α)]
  have hproduct := integral_deriv_mul_add_mul_deriv_eq_zero
    hshiftSmooth hu hshiftPer huper
  simp only [deriv_comp_add_const] at hproduct
  have hAInt : IntervalIntegrable
      (fun t => u (t + α) * deriv u t) volume (0 : ℝ) 1 :=
    ((hu.continuous.comp (continuous_add_const α)).mul hdu).intervalIntegrable 0 1
  have hBpInt : IntervalIntegrable
      (fun t => u t * deriv u (t + α)) volume (0 : ℝ) 1 :=
    (hu.continuous.mul (hdu.comp (continuous_add_const α))).intervalIntegrable 0 1
  have hproduct' :
      (∫ t in (0 : ℝ)..1,
        u t * deriv u (t + α) + u (t + α) * deriv u t) = 0 := by
    rw [show (fun t =>
        u t * deriv u (t + α) + u (t + α) * deriv u t) =
      fun t => deriv u (t + α) * u t + u (t + α) * deriv u t by
        funext t
        ring]
    exact hproduct
  rw [intervalIntegral.integral_add hBpInt hAInt] at hproduct'
  have hABp :
      (∫ t in (0 : ℝ)..1, u (t + α) * deriv u t) +
        ∫ t in (0 : ℝ)..1, u t * deriv u (t + α) = 0 := by
    simpa only [add_comm] using hproduct'
  let h : ℝ → ℝ := fun t => u t * deriv u (t + α)
  have hhper : Function.Periodic h 1 := by
    intro t
    simp only [h]
    rw [huper t, show t + 1 + α = (t + α) + 1 by ring, hduper (t + α)]
  have hB_eq :
      (∫ t in (0 : ℝ)..1, u (t - α) * deriv u t) =
        ∫ t in (0 : ℝ)..1, u t * deriv u (t + α) := by
    calc
      (∫ t in (0 : ℝ)..1, u (t - α) * deriv u t) =
          ∫ t in (0 : ℝ)..1, h (t - α) := by
        congr 1
        funext t
        simp only [h]
        rw [show t - α + α = t by ring]
      _ = ∫ t in (0 : ℝ) - α..1 - α, h t :=
        intervalIntegral.integral_comp_sub_right h α
      _ = ∫ t in (0 : ℝ)..1, h t := by
        have hperint := hhper.intervalIntegral_add_eq (-α) 0
        rw [show -α + 1 = 1 - α by ring] at hperint
        simpa only [zero_add, zero_sub] using hperint
      _ = ∫ t in (0 : ℝ)..1, u t * deriv u (t + α) := rfl
  have hAB :
      (∫ t in (0 : ℝ)..1, u (t + α) * deriv u t) +
        ∫ t in (0 : ℝ)..1, u (t - α) * deriv u t = 0 := by
    rw [hB_eq]
    exact hABp
  have hM := integral_mul_deriv_eq_zero hu huper
  have hBInt : IntervalIntegrable
      (fun t => u (t - α) * deriv u t) volume (0 : ℝ) 1 :=
    ((hu.continuous.comp (continuous_id.sub continuous_const)).mul hdu).intervalIntegrable 0 1
  have hMInt : IntervalIntegrable
      (fun t => u t * deriv u t) volume (0 : ℝ) 1 :=
    (hu.continuous.mul hdu).intervalIntegrable 0 1
  rw [show (fun t => Helpers.discreteLaplacian α u t * deriv u t) =
      fun t => u (t + α) * deriv u t -
        2 * (u t * deriv u t) + u (t - α) * deriv u t by
    funext t
    simp only [Helpers.discreteLaplacian]
    ring]
  rw [intervalIntegral.integral_add (hAInt.sub (hMInt.const_mul 2)) hBInt,
    intervalIntegral.integral_sub hAInt (hMInt.const_mul 2),
    intervalIntegral.integral_const_mul]
  linarith

/-- At a fixed point of the projected equation, the variational identity and
the mean-zero primitive force the scalar obstruction itself to vanish. -/
theorem fixedPoint_forcing_mean_eq_zero {α : ℝ}
    (hα : LeanEval.Dynamics.IsDiophantine α) (c : ℝ)
    {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hfix : Nonlinear.correction α c f u = u) :
    Nonlinear.periodMean (Nonlinear.forcing c f u) = 0 := by
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have huDiff : Differentiable ℝ u := hu.differentiable (by simp)
  have heq : (fun t => Helpers.discreteLaplacian α u t) =
      Nonlinear.projectedForcing c f u := by
    funext t
    calc
      Helpers.discreteLaplacian α u t =
          Helpers.discreteLaplacian α (Nonlinear.correction α c f u) t := by
        rw [hfix]
      _ = Nonlinear.projectedForcing c f u t :=
        Nonlinear.discreteLaplacian_correction hα c hf hu hfper huper t
  have hLCont : Continuous (Helpers.discreteLaplacian α u) := by
    unfold Helpers.discreteLaplacian
    fun_prop
  have hLMean : ∫ t in (0 : ℝ)..1,
      Helpers.discreteLaplacian α u t = 0 := by
    rw [heq]
    exact Nonlinear.projectedForcing_integral_eq_zero
      c hf.continuous hu.continuous
  have hEnergy :=
    integral_discreteLaplacian_mul_deriv_eq_zero α hu huper
  have hLiftEnergy : ∫ t in (0 : ℝ)..1,
      Helpers.discreteLaplacian α u t * (1 + deriv u t) = 0 := by
    rw [show (fun t =>
        Helpers.discreteLaplacian α u t * (1 + deriv u t)) =
      fun t => Helpers.discreteLaplacian α u t +
        Helpers.discreteLaplacian α u t * deriv u t by
          funext t
          ring]
    change (∫ t in (0 : ℝ)..1,
      ((Helpers.discreteLaplacian α u) +
        (Helpers.discreteLaplacian α u) * deriv u) t) = 0
    calc
      _ = (∫ t in (0 : ℝ)..1, Helpers.discreteLaplacian α u t) +
          ∫ t in (0 : ℝ)..1,
            Helpers.discreteLaplacian α u t * deriv u t := by
        exact intervalIntegral.integral_add
          (hLCont.intervalIntegrable 0 1)
          ((hLCont.mul hdu).intervalIntegrable 0 1)
      _ = 0 := by rw [hLMean, hEnergy, add_zero]
  have hPrimitive := integral_comp_id_add_mul_one_add_deriv_eq_zero
    hf.continuous hfper hfmean hu huper
  have hForceLift : ∫ t in (0 : ℝ)..1,
      Nonlinear.forcing c f u t * (1 + deriv u t) = 0 := by
    rw [show (fun t => Nonlinear.forcing c f u t * (1 + deriv u t)) =
      fun t => c * (f (t + u t) * (1 + deriv u t)) by
        funext t
        simp only [Nonlinear.forcing]
        ring]
    rw [intervalIntegral.integral_const_mul, hPrimitive, mul_zero]
  have huOne : u 1 = u 0 := by simpa using huper 0
  have hduInt : ∫ t in (0 : ℝ)..1, deriv u t = 0 := by
    have hfund := intervalIntegral.integral_deriv_eq_sub
      (f := u) (a := (0 : ℝ)) (b := 1)
      (fun _ _ => huDiff.differentiableAt)
      (hdu.intervalIntegrable 0 1)
    rw [huOne] at hfund
    simpa only [sub_self] using hfund
  have hOneDu : ∫ t in (0 : ℝ)..1, (1 + deriv u t) = 1 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (hdu.intervalIntegrable 0 1), intervalIntegral.integral_const, hduInt]
    norm_num
  let μ := Nonlinear.periodMean (Nonlinear.forcing c f u)
  have hMuLift : ∫ t in (0 : ℝ)..1, μ * (1 + deriv u t) = μ := by
    rw [intervalIntegral.integral_const_mul, hOneDu, mul_one]
  have hpoint : (fun t =>
      Helpers.discreteLaplacian α u t * (1 + deriv u t)) =
      fun t => (Nonlinear.forcing c f u t - μ) * (1 + deriv u t) := by
    funext t
    rw [congrFun heq t]
    rfl
  rw [hpoint] at hLiftEnergy
  have hForceInt : IntervalIntegrable
      (fun t => Nonlinear.forcing c f u t * (1 + deriv u t))
      volume (0 : ℝ) 1 := by
    exact ((Nonlinear.forcing_contDiff c hf hu).continuous.mul
      (continuous_const.add hdu)).intervalIntegrable 0 1
  have hMuInt : IntervalIntegrable
      (fun t => μ * (1 + deriv u t)) volume (0 : ℝ) 1 :=
    (continuous_const.mul (continuous_const.add hdu)).intervalIntegrable 0 1
  rw [show (fun t =>
      (Nonlinear.forcing c f u t - μ) * (1 + deriv u t)) =
      fun t => Nonlinear.forcing c f u t * (1 + deriv u t) -
        μ * (1 + deriv u t) by
          funext t
          ring,
    intervalIntegral.integral_sub hForceInt hMuInt,
    hForceLift, hMuLift] at hLiftEnergy
  dsimp only [μ] at hLiftEnergy ⊢
  linarith

/-- Endpoint form of the KAM argument: the Newton construction only has to
produce a small smooth periodic fixed point of the projected correction. -/
theorem invariantCurve_of_fixedPoint {α : ℝ}
    (hα : LeanEval.Dynamics.IsDiophantine α) (c : ℝ)
    {f u : ℝ → ℝ} (K : NNReal)
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (huLip : LipschitzWith K u) (hK : (K : ℝ) < 1)
    (hfix : Nonlinear.correction α c f u = u) :
    ∃ q : ℝ → ℝ,
      ContDiff ℝ ∞ q ∧ StrictMono q ∧
      Function.Periodic (fun t => q t - t) 1 ∧
      ∀ t : ℝ,
        q (t + α) - 2 * q t + q (t - α) = c * f (q t) := by
  apply Nonlinear.invariantCurve_of_fixedPoint hα c K hf hu hfper huper
    huLip hK hfix
  exact fixedPoint_forcing_mean_eq_zero hα c hf hu hfper huper hfmean hfix

end

end Submission.Energy
