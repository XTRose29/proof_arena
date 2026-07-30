import Submission.Energy

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Newton

noncomputable section

/-- Forward difference along the rotation by `α`. -/
def forwardDiff (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  u (t + α) - u t

/-- Backward difference along the rotation by `α`. -/
def backwardDiff (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  u t - u (t - α)

theorem forwardDiff_backwardDiff (α : ℝ) (u : ℝ → ℝ) (t : ℝ) :
    forwardDiff α (backwardDiff α u) t =
      Helpers.discreteLaplacian α u t := by
  simp only [forwardDiff, backwardDiff, Helpers.discreteLaplacian]
  ring_nf

theorem backwardDiff_forwardDiff (α : ℝ) (u : ℝ → ℝ) (t : ℝ) :
    backwardDiff α (forwardDiff α u) t =
      Helpers.discreteLaplacian α u t := by
  simp only [forwardDiff, backwardDiff, Helpers.discreteLaplacian]
  rw [show t - α + α = t by ring]
  ring

/-- A normalized right inverse of the forward difference, obtained by taking a
backward difference of the already constructed inverse of the second
difference. -/
def solveForward (α : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  backwardDiff α (Cohomological.solve α g)

/-- A normalized right inverse of the backward difference. -/
def solveBackward (α : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  forwardDiff α (Cohomological.solve α g)

theorem solveForward_contDiff {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgper : Function.Periodic g 1) :
    ContDiff ℝ ∞ (solveForward α g) := by
  have hsolve := Cohomological.solve_contDiff hα hg hgper
  unfold solveForward backwardDiff
  fun_prop

theorem solveBackward_contDiff {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgper : Function.Periodic g 1) :
    ContDiff ℝ ∞ (solveBackward α g) := by
  have hsolve := Cohomological.solve_contDiff hα hg hgper
  unfold solveBackward forwardDiff
  fun_prop

theorem solveForward_periodic (α : ℝ) (g : ℝ → ℝ) :
    Function.Periodic (solveForward α g) 1 := by
  have hsolve := Cohomological.solve_periodic α g
  intro t
  simp only [solveForward, backwardDiff]
  rw [show t + 1 - α = (t - α) + 1 by ring, hsolve t, hsolve (t - α)]

theorem solveBackward_periodic (α : ℝ) (g : ℝ → ℝ) :
    Function.Periodic (solveBackward α g) 1 := by
  have hsolve := Cohomological.solve_periodic α g
  intro t
  simp only [solveBackward, forwardDiff]
  rw [show t + 1 + α = (t + α) + 1 by ring, hsolve (t + α), hsolve t]

theorem forwardDiff_solveForward {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgper : Function.Periodic g 1)
    (hgmean : ∫ t in (0 : ℝ)..1, g t = 0) (t : ℝ) :
    forwardDiff α (solveForward α g) t = g t := by
  rw [solveForward, forwardDiff_backwardDiff]
  exact Cohomological.discreteLaplacian_solve hα hg hgper hgmean t

theorem backwardDiff_solveBackward {α : ℝ} (hα : IsDiophantine α)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgper : Function.Periodic g 1)
    (hgmean : ∫ t in (0 : ℝ)..1, g t = 0) (t : ℝ) :
    backwardDiff α (solveBackward α g) t = g t := by
  rw [solveBackward, backwardDiff_forwardDiff]
  exact Cohomological.discreteLaplacian_solve hα hg hgper hgmean t

/-- The residual of the invariant-curve equation in the periodic correction
variable `u`. -/
def residual (α c : ℝ) (f u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Helpers.discreteLaplacian α u t - c * f (t + u t)

/-- The derivative of the residual with respect to its correction variable. -/
def linearized (α c : ℝ) (f u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  Helpers.discreteLaplacian α v t - c * deriv f (t + u t) * v t

/-- Derivative of the degree-one lift associated to `u`. -/
def liftDeriv (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 + deriv u t

theorem residual_contDiff (α c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (residual α c f u) := by
  unfold residual Helpers.discreteLaplacian
  fun_prop

theorem residual_periodic (α c : ℝ) {f u : ℝ → ℝ}
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1) :
    Function.Periodic (residual α c f u) 1 := by
  exact (Helpers.discreteLaplacian_periodic α huper).sub
    (Nonlinear.forcing_periodic c hfper huper)

theorem liftDeriv_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (liftDeriv u) := by
  exact contDiff_const.add (contDiff_infty_iff_deriv.mp hu).2

theorem liftDeriv_periodic {u : ℝ → ℝ}
    (huper : Function.Periodic u 1) :
    Function.Periodic (liftDeriv u) 1 := by
  intro t
  simp only [liftDeriv]
  have hder : Function.Periodic (deriv u) 1 := by
    simpa only [iteratedDeriv_one] using Helpers.periodic_iteratedDeriv huper 1
  rw [hder t]

theorem deriv_residual {α c : ℝ} {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    deriv (residual α c f u) t =
      linearized α c f u (liftDeriv u) t := by
  have hfu : Differentiable ℝ u := hu.differentiable (by simp)
  have hff : Differentiable ℝ f := hf.differentiable (by simp)
  have hLDiff : DifferentiableAt ℝ (Helpers.discreteLaplacian α u) t := by
    unfold Helpers.discreteLaplacian
    fun_prop
  have hL : deriv (Helpers.discreteLaplacian α u) t =
      deriv u (t + α) - 2 * deriv u t + deriv u (t - α) := by
    rw [show Helpers.discreteLaplacian α u =
      (fun x => u (x + α)) - (fun x => 2 * u x) +
        (fun x => u (x - α)) by rfl]
    rw [deriv_add (by fun_prop) (by fun_prop),
      deriv_sub (by fun_prop) (by fun_prop),
      deriv_const_mul 2 (by fun_prop),
      deriv_comp_add_const, deriv_comp_sub_const]
  have hcomp : deriv (fun x => f (x + u x)) t =
      deriv f (t + u t) * (1 + deriv u t) := by
    rw [show (fun x => f (x + u x)) =
      f ∘ (fun x => x + u x) by rfl,
      deriv_comp t (by fun_prop) (by fun_prop)]
    have hinner : deriv (fun x : ℝ => x + u x) t =
        1 + deriv u t := by
      change deriv (id + u) t = _
      rw [deriv_add differentiableAt_id hfu.differentiableAt, deriv_id]
    rw [hinner]
  rw [show residual α c f u =
      (Helpers.discreteLaplacian α u) -
        (fun x => c * f (x + u x)) by rfl]
  rw [deriv_sub hLDiff (by fun_prop), hL,
    deriv_const_mul c (by fun_prop), hcomp]
  simp only [linearized, liftDeriv, Helpers.discreteLaplacian]
  ring

theorem integral_residual_mul_liftDeriv_eq_zero (α c : ℝ)
    {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1) :
    ∫ t in (0 : ℝ)..1,
      residual α c f u t * liftDeriv u t = 0 := by
  have hL := Energy.integral_discreteLaplacian_mul_deriv_eq_zero α hu huper
  have hLMean : ∫ t in (0 : ℝ)..1,
      Helpers.discreteLaplacian α u t = 0 := by
    have huInt : IntervalIntegrable u volume (0 : ℝ) 1 :=
      hu.continuous.intervalIntegrable 0 1
    have hplus : (∫ t in (0 : ℝ)..1, u (t + α)) =
        ∫ t in (0 : ℝ)..1, u t := by
      calc
        (∫ t in (0 : ℝ)..1, u (t + α)) =
            ∫ t in (0 : ℝ) + α..1 + α, u t :=
          intervalIntegral.integral_comp_add_right u α
        _ = ∫ t in α + 0..α + 1, u t := by congr 1 <;> ring
        _ = ∫ t in (0 : ℝ)..1, u t := by
          simpa only [add_zero, zero_add] using
            huper.intervalIntegral_add_eq α 0
    have hminus : (∫ t in (0 : ℝ)..1, u (t - α)) =
        ∫ t in (0 : ℝ)..1, u t := by
      have hshift := huper.intervalIntegral_add_eq (-α) 0
      rw [show -α + 1 = 1 - α by ring] at hshift
      calc
        (∫ t in (0 : ℝ)..1, u (t - α)) =
            ∫ t in (0 : ℝ) - α..1 - α, u t :=
          intervalIntegral.integral_comp_sub_right u α
        _ = ∫ t in (0 : ℝ)..1, u t := by simpa using hshift
    have hplusInt : IntervalIntegrable (fun t => u (t + α)) volume (0 : ℝ) 1 :=
      (hu.continuous.comp (continuous_add_const α)).intervalIntegrable 0 1
    have hminusInt : IntervalIntegrable (fun t => u (t - α)) volume (0 : ℝ) 1 :=
      (hu.continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable 0 1
    simp only [Helpers.discreteLaplacian]
    rw [intervalIntegral.integral_add
      (hplusInt.sub (huInt.const_mul 2)) hminusInt,
      intervalIntegral.integral_sub hplusInt (huInt.const_mul 2),
      intervalIntegral.integral_const_mul, hplus, hminus]
    ring
  have hLift : ∫ t in (0 : ℝ)..1,
      Helpers.discreteLaplacian α u t * liftDeriv u t = 0 := by
    rw [show (fun t => Helpers.discreteLaplacian α u t * liftDeriv u t) =
      fun t => Helpers.discreteLaplacian α u t +
        Helpers.discreteLaplacian α u t * deriv u t by
          funext t
          simp only [liftDeriv]
          ring]
    have hLCont : Continuous (Helpers.discreteLaplacian α u) := by
      unfold Helpers.discreteLaplacian
      fun_prop
    have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
    calc
      (∫ t in (0 : ℝ)..1,
          Helpers.discreteLaplacian α u t +
            Helpers.discreteLaplacian α u t * deriv u t) =
          (∫ t in (0 : ℝ)..1, Helpers.discreteLaplacian α u t) +
            ∫ t in (0 : ℝ)..1,
              Helpers.discreteLaplacian α u t * deriv u t := by
        exact intervalIntegral.integral_add
          (hLCont.intervalIntegrable 0 1)
          ((hLCont.mul hdu).intervalIntegrable 0 1)
      _ = 0 := by rw [hLMean, hL, zero_add]
  have hForce := Energy.integral_comp_id_add_mul_one_add_deriv_eq_zero
    hf.continuous hfper hfmean hu huper
  rw [show (fun t => residual α c f u t * liftDeriv u t) =
      fun t => Helpers.discreteLaplacian α u t * liftDeriv u t -
        c * (f (t + u t) * (1 + deriv u t)) by
        funext t
        simp only [residual, liftDeriv]
        ring]
  have hLInt : IntervalIntegrable
      (fun t => Helpers.discreteLaplacian α u t * liftDeriv u t)
      volume (0 : ℝ) 1 := by
    have hLCont : Continuous (Helpers.discreteLaplacian α u) := by
      unfold Helpers.discreteLaplacian
      fun_prop
    exact (hLCont.mul (liftDeriv_contDiff hu).continuous).intervalIntegrable 0 1
  have hForceInt : IntervalIntegrable
      (fun t => c * (f (t + u t) * (1 + deriv u t)))
      volume (0 : ℝ) 1 := by
    exact (continuous_const.mul
      ((hf.continuous.comp (continuous_id.add hu.continuous)).mul
        (continuous_const.add (hu.continuous_deriv (by simp))))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hLInt hForceInt,
    intervalIntegral.integral_const_mul, hLift, hForce, mul_zero, sub_zero]

/-- Quantitative nondegeneracy condition used by one automatically reduced
Newton step. -/
def GoodLift (u : ℝ → ℝ) : Prop :=
  ∀ t, (1 : ℝ) / 2 ≤ liftDeriv u t ∧ liftDeriv u t ≤ 3 / 2

/-- The right-hand side of the first reduced cohomological equation. -/
def firstRhs (α c : ℝ) (f u : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(liftDeriv u t * residual α c f u t)

/-- The normalized solution of the first reduced cohomological equation before
adding its scalar normalization. -/
def firstSolution (α c : ℝ) (f u : ℝ → ℝ) : ℝ → ℝ :=
  solveForward α (firstRhs α c f u)

/-- The twist weight in the automatically reduced linearized equation. -/
def twistWeight (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  liftDeriv u t * liftDeriv u (t - α)

/-- Reciprocal twist weight. -/
def inverseTwistWeight (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (twistWeight α u t)⁻¹

/-- The unique scalar added to the first solution so that division by the twist
weight has zero mean. -/
def normalizingConstant (α c : ℝ) (f u : ℝ → ℝ) : ℝ :=
  -Nonlinear.periodMean (fun t =>
      firstSolution α c f u t * inverseTwistWeight α u t) /
    Nonlinear.periodMean (inverseTwistWeight α u)

/-- Right-hand side of the second reduced cohomological equation. -/
def secondRhs (α c : ℝ) (f u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (firstSolution α c f u t + normalizingConstant α c f u) *
    inverseTwistWeight α u t

/-- Auxiliary scalar function in the automatically reduced Newton correction. -/
def reducedUnknown (α c : ℝ) (f u : ℝ → ℝ) : ℝ → ℝ :=
  solveBackward α (secondRhs α c f u)

/-- One automatically reduced quasi-Newton correction. -/
def step (α c : ℝ) (f u : ℝ → ℝ) (t : ℝ) : ℝ :=
  liftDeriv u t * reducedUnknown α c f u t

theorem firstRhs_contDiff (α c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (firstRhs α c f u) := by
  exact (liftDeriv_contDiff hu).mul (residual_contDiff α c hf hu) |>.neg

theorem firstRhs_periodic (α c : ℝ) {f u : ℝ → ℝ}
    (hfper : Function.Periodic f 1) (huper : Function.Periodic u 1) :
    Function.Periodic (firstRhs α c f u) 1 := by
  intro t
  simp only [firstRhs]
  rw [(liftDeriv_periodic huper) t,
    (residual_periodic α c hfper huper) t]

theorem firstRhs_mean_eq_zero (α c : ℝ) {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1) :
    ∫ t in (0 : ℝ)..1, firstRhs α c f u t = 0 := by
  rw [show firstRhs α c f u = fun t =>
      -(residual α c f u t * liftDeriv u t) by
        funext t
        simp only [firstRhs]
        ring]
  rw [intervalIntegral.integral_neg,
    integral_residual_mul_liftDeriv_eq_zero α c hf hfper hfmean hu huper,
    neg_zero]

theorem firstSolution_contDiff {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1) (hu : ContDiff ℝ ∞ u)
    (huper : Function.Periodic u 1) :
    ContDiff ℝ ∞ (firstSolution α c f u) :=
  solveForward_contDiff hα (firstRhs_contDiff α c hf hu)
    (firstRhs_periodic α c hfper huper)

theorem firstSolution_periodic (α c : ℝ) (f u : ℝ → ℝ) :
    Function.Periodic (firstSolution α c f u) 1 :=
  solveForward_periodic α (firstRhs α c f u)

theorem forwardDiff_firstSolution {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1) (t : ℝ) :
    forwardDiff α (firstSolution α c f u) t =
      firstRhs α c f u t := by
  exact forwardDiff_solveForward hα (firstRhs_contDiff α c hf hu)
    (firstRhs_periodic α c hfper huper)
    (firstRhs_mean_eq_zero α c hf hfper hfmean hu huper) t

theorem twistWeight_pos {α : ℝ} {u : ℝ → ℝ} (hu : GoodLift u) (t : ℝ) :
    0 < twistWeight α u t := by
  exact mul_pos (lt_of_lt_of_le (by norm_num) (hu t).1)
    (lt_of_lt_of_le (by norm_num) (hu (t - α)).1)

theorem twistWeight_ne_zero {α : ℝ} {u : ℝ → ℝ} (hu : GoodLift u) (t : ℝ) :
    twistWeight α u t ≠ 0 :=
  (twistWeight_pos hu t).ne'

theorem twistWeight_contDiff (α : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (twistWeight α u) := by
  exact (liftDeriv_contDiff hu).mul
    ((liftDeriv_contDiff hu).comp (contDiff_id.sub contDiff_const))

theorem twistWeight_periodic (α : ℝ) {u : ℝ → ℝ}
    (huper : Function.Periodic u 1) :
    Function.Periodic (twistWeight α u) 1 := by
  intro t
  simp only [twistWeight]
  rw [(liftDeriv_periodic huper) t,
    show t + 1 - α = (t - α) + 1 by ring,
    (liftDeriv_periodic huper) (t - α)]

theorem inverseTwistWeight_contDiff (α : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hgood : GoodLift u) :
    ContDiff ℝ ∞ (inverseTwistWeight α u) := by
  exact ContDiff.inv (twistWeight_contDiff α hu) (twistWeight_ne_zero hgood)

theorem inverseTwistWeight_periodic (α : ℝ) {u : ℝ → ℝ}
    (huper : Function.Periodic u 1) :
    Function.Periodic (inverseTwistWeight α u) 1 := by
  intro t
  simp only [inverseTwistWeight]
  rw [(twistWeight_periodic α huper) t]

theorem inverseTwistWeight_pos {α : ℝ} {u : ℝ → ℝ}
    (hu : GoodLift u) (t : ℝ) : 0 < inverseTwistWeight α u t := by
  exact inv_pos.mpr (twistWeight_pos hu t)

theorem inverseTwistWeight_mean_pos {α : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hgood : GoodLift u) :
    0 < Nonlinear.periodMean (inverseTwistWeight α u) := by
  apply intervalIntegral.intervalIntegral_pos_of_pos
  · exact (inverseTwistWeight_contDiff α hu hgood).continuous.intervalIntegrable 0 1
  · exact inverseTwistWeight_pos hgood
  · norm_num

theorem secondRhs_contDiff {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1) (hu : ContDiff ℝ ∞ u)
    (huper : Function.Periodic u 1) (hgood : GoodLift u) :
    ContDiff ℝ ∞ (secondRhs α c f u) := by
  exact ((firstSolution_contDiff hα c hf hfper hu huper).add contDiff_const).mul
    (inverseTwistWeight_contDiff α hu hgood)

theorem secondRhs_periodic (α c : ℝ) {f u : ℝ → ℝ}
    (huper : Function.Periodic u 1) :
    Function.Periodic (secondRhs α c f u) 1 := by
  intro t
  simp only [secondRhs]
  rw [(firstSolution_periodic α c f u) t,
    (inverseTwistWeight_periodic α huper) t]

theorem secondRhs_mean_eq_zero {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1) (hu : ContDiff ℝ ∞ u)
    (huper : Function.Periodic u 1) (hgood : GoodLift u) :
    ∫ t in (0 : ℝ)..1, secondRhs α c f u t = 0 := by
  let A := Nonlinear.periodMean (fun t =>
    firstSolution α c f u t * inverseTwistWeight α u t)
  let B := Nonlinear.periodMean (inverseTwistWeight α u)
  have hB : B ≠ 0 := (inverseTwistWeight_mean_pos hu hgood).ne'
  have hfirst : IntervalIntegrable
      (fun t => firstSolution α c f u t * inverseTwistWeight α u t)
      volume (0 : ℝ) 1 :=
    ((firstSolution_contDiff hα c hf hfper hu huper).continuous.mul
      (inverseTwistWeight_contDiff α hu hgood).continuous).intervalIntegrable 0 1
  have hinv : IntervalIntegrable (inverseTwistWeight α u)
      volume (0 : ℝ) 1 :=
    (inverseTwistWeight_contDiff α hu hgood).continuous.intervalIntegrable 0 1
  rw [show (fun t => secondRhs α c f u t) =
      fun t => firstSolution α c f u t * inverseTwistWeight α u t +
        normalizingConstant α c f u * inverseTwistWeight α u t by
        funext t
        simp only [secondRhs]
        ring]
  rw [intervalIntegral.integral_add hfirst (hinv.const_mul _),
    intervalIntegral.integral_const_mul]
  change A + (-A / B) * B = 0
  field_simp [hB]
  ring

theorem reducedUnknown_contDiff {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1) (hu : ContDiff ℝ ∞ u)
    (huper : Function.Periodic u 1) (hgood : GoodLift u) :
    ContDiff ℝ ∞ (reducedUnknown α c f u) :=
  solveBackward_contDiff hα
    (secondRhs_contDiff hα c hf hfper hu huper hgood)
    (secondRhs_periodic α c huper)

theorem reducedUnknown_periodic (α c : ℝ) (f u : ℝ → ℝ) :
    Function.Periodic (reducedUnknown α c f u) 1 :=
  solveBackward_periodic α (secondRhs α c f u)

theorem backwardDiff_reducedUnknown {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1) (hu : ContDiff ℝ ∞ u)
    (huper : Function.Periodic u 1) (hgood : GoodLift u) (t : ℝ) :
    backwardDiff α (reducedUnknown α c f u) t =
      secondRhs α c f u t := by
  exact backwardDiff_solveBackward hα
    (secondRhs_contDiff hα c hf hfper hu huper hgood)
    (secondRhs_periodic α c huper)
    (secondRhs_mean_eq_zero hα c hf hfper hu huper hgood) t

theorem step_contDiff {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1) (hu : ContDiff ℝ ∞ u)
    (huper : Function.Periodic u 1) (hgood : GoodLift u) :
    ContDiff ℝ ∞ (step α c f u) :=
  (liftDeriv_contDiff hu).mul
    (reducedUnknown_contDiff hα c hf hfper hu huper hgood)

theorem step_periodic (α c : ℝ) {f u : ℝ → ℝ}
    (huper : Function.Periodic u 1) :
    Function.Periodic (step α c f u) 1 :=
  (liftDeriv_periodic huper).mul (reducedUnknown_periodic α c f u)

/-- Exact automatic-reducibility identity behind the quasi-Newton step. -/
theorem linearized_step {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1)
    (hgood : GoodLift u) (t : ℝ) :
    linearized α c f u (step α c f u) t =
      -residual α c f u t +
        deriv (residual α c f u) t * reducedUnknown α c f u t := by
  let l := liftDeriv u
  let w := reducedUnknown α c f u
  let z := firstSolution α c f u + fun _ => normalizingConstant α c f u
  have hl : l t ≠ 0 := by
    exact (lt_of_lt_of_le (by norm_num) (hgood t).1).ne'
  have hw (x : ℝ) : backwardDiff α w x =
      z x * inverseTwistWeight α u x := by
    rw [backwardDiff_reducedUnknown hα c hf hfper hu huper hgood x]
    rfl
  have hz (x : ℝ) : forwardDiff α z x =
      -(l x * residual α c f u x) := by
    rw [show forwardDiff α z x =
      forwardDiff α (firstSolution α c f u) x by
        simp only [z, forwardDiff, Pi.add_apply]
        ring]
    exact forwardDiff_firstSolution hα c hf hfper hfmean hu huper x
  have hfactor :
      Helpers.discreteLaplacian α (fun x => l x * w x) t -
          c * deriv f (t + u t) * (l t * w t) =
        (forwardDiff α z t) / l t +
          deriv (residual α c f u) t * w t := by
    rw [deriv_residual hf hu t]
    simp only [linearized, liftDeriv] at *
    have hzweight (x : ℝ) : z x =
        (l x * l (x - α)) * backwardDiff α w x := by
      rw [hw x]
      have ha : twistWeight α u x ≠ 0 := twistWeight_ne_zero hgood x
      change z x = twistWeight α u x *
        (z x * (twistWeight α u x)⁻¹)
      field_simp [ha]
    simp only [Helpers.discreteLaplacian, forwardDiff]
    rw [hzweight t, hzweight (t + α)]
    rw [show t + α - α = t by ring]
    simp only [backwardDiff, l, liftDeriv]
    have hl' : 1 + deriv u t ≠ 0 := by
      simpa only [l, liftDeriv] using hl
    field_simp [hl']
    ring_nf
  change Helpers.discreteLaplacian α (step α c f u) t -
      c * deriv f (t + u t) * step α c f u t = _
  rw [show step α c f u = fun x => l x * w x by rfl, hfactor, hz t]
  field_simp [hl]
  simp only [w]

/-- After the quasi-Newton correction, the new residual consists only of the
automatic-reducibility defect and the nonlinear Taylor remainder. -/
theorem residual_add_step {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hu : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1)
    (hgood : GoodLift u) (t : ℝ) :
    residual α c f (fun x => u x + step α c f u x) t =
      deriv (residual α c f u) t * reducedUnknown α c f u t -
        c * (f (t + u t + step α c f u t) - f (t + u t) -
          deriv f (t + u t) * step α c f u t) := by
  rw [show residual α c f (fun x => u x + step α c f u x) t =
      residual α c f u t +
        linearized α c f u (step α c f u) t -
        c * (f (t + u t + step α c f u t) - f (t + u t) -
          deriv f (t + u t) * step α c f u t) by
      simp only [residual, linearized, Helpers.discreteLaplacian]
      ring_nf]
  rw [linearized_step hα c hf hfper hfmean hu huper hgood t]
  ring

end

end Submission.Newton
