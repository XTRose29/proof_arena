import Submission.DerivativeDistortion
import Submission.Orbit
import Submission.PointwiseErgodic
import Mathlib.LinearAlgebra.Determinant

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

noncomputable def logJacobian (T : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  Real.log |(fderiv ℝ T x).toLinearMap.det|

noncomputable def logJacobianIterate
    (T : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) : ℝ :=
  Real.log |(fderiv ℝ (T^[n]) x).toLinearMap.det|

lemma det_fderiv_iterate_ne_zero
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    (fderiv ℝ (T^[n]) x).toLinearMap.det ≠ 0 := by
  let A := fderiv ℝ (T^[n]) x
  have hcomp := fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n x
  have hsurj : Function.Surjective A := by
    intro y
    refine ⟨A.inverse y, ?_⟩
    have hy := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L y) hcomp
    simpa [A] using hy
  have hinj : Function.Injective A.toLinearMap :=
    LinearMap.injective_iff_surjective.mpr hsurj
  intro hdet
  have hker : A.toLinearMap.ker ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  exact hker (LinearMap.ker_eq_bot.mpr hinj)

lemma logJacobianIterate_succ
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    logJacobianIterate T (n + 1) x =
      logJacobianIterate T n (T x) + logJacobian T x := by
  have hn := det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n (T x)
  have h_one := det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right 1 x
  unfold logJacobianIterate logJacobian
  rw [fderiv_iterate_succ_eq T hT_smooth n x]
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul]
  rw [Real.log_mul (abs_ne_zero.mpr hn) (abs_ne_zero.mpr (by
    simpa [Function.iterate_one] using h_one))]

lemma logJacobianIterate_eq_birkhoffSum
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    logJacobianIterate T n x = birkhoffSum T (logJacobian T) n x := by
  induction n generalizing x with
  | zero =>
      simp [logJacobianIterate, fderiv_id, LinearMap.det_id]
  | succ n ih =>
      rw [logJacobianIterate_succ T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x]
      rw [birkhoffSum_succ']
      rw [ih]
      ring

lemma continuous_logJacobian
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    Continuous (logJacobian T) := by
  have hdet : Continuous fun x : EucPlane => (fderiv ℝ T x).toLinearMap.det := by
    exact ContinuousLinearMap.continuous_det.comp
      (hT_smooth.continuous_fderiv (by norm_num))
  unfold logJacobian
  apply hdet.abs.log
  intro x
  apply abs_ne_zero.mpr
  simpa [Function.iterate_one] using
    det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right 1 x

lemma integrable_logJacobian
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0) :
    Integrable (logJacobian T) mu := by
  have hOn : IntegrableOn (logJacobian T) K mu :=
    (continuous_logJacobian T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right).continuousOn.integrableOn_compact hK_compact
  have hIndicator : Integrable (K.indicator (logJacobian T)) mu :=
    hOn.integrable_indicator hK_compact.isClosed.measurableSet
  apply hIndicator.congr
  filter_upwards [mem_ae_iff.mpr hmu_supp] with x hx
  rw [Set.indicator_of_mem hx]

lemma ae_tendsto_logJacobianIterate_div_integral
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    ∀ᵐ x ∂mu, Filter.Tendsto
      (fun n : ℕ => logJacobianIterate T n x / n)
      Filter.atTop (nhds (∫ y, logJacobian T y ∂mu)) := by
  have havg := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg (logJacobian T)
      (continuous_logJacobian T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right).measurable
      (integrable_logJacobian T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right hK_compact mu hmu_supp)
  filter_upwards [havg] with x hx
  apply hx.congr'
  exact Filter.Eventually.of_forall fun n => by
    change birkhoffAverage ℝ T (logJacobian T) n x =
      logJacobianIterate T n x / n
    rw [logJacobianIterate_eq_birkhoffSum T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x]
    simp [birkhoffAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]

end Submission.Helpers
