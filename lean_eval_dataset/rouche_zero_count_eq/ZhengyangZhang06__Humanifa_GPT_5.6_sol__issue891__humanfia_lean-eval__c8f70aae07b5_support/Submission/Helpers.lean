import Mathlib

namespace Submission.Helpers

open Complex Filter Function Metric Set Topology
open MeromorphicOn

lemma circleIntegral_deriv_eq_zero {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : ∀ z ∈ sphere c |R|, AnalyticAt ℂ F z) :
    (∮ z in C(c, R), deriv F z) = 0 := by
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt'
  intro z hz
  exact (hF z hz).differentiableAt.hasDerivAt.hasDerivWithinAt

lemma circleIntegral_logDeriv_eq_finsum_divisor {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hF : MeromorphicOn F (closedBall 0 R))
    (hboundary : ∀ z ∈ sphere 0 R, AnalyticAt ℂ F z ∧ F z ≠ 0) :
    (∮ z in C(0, R), logDeriv F z) =
      (((∑ᶠ z, (divisor F (closedBall 0 R)) z) : ℤ) : ℂ) * (2 * Real.pi * I) := by
  let CB : Set ℂ := closedBall 0 R
  let D := divisor F CB
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  let w : ℂ := circleMap 0 R 0
  have hwSphere : w ∈ sphere 0 R := circleMap_mem_sphere 0 hR.le 0
  have hwCB : w ∈ CB := sphere_subset_closedBall hwSphere
  have hwOrder : meromorphicOrderAt F w = 0 :=
    (hboundary w hwSphere).1.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2
      (hboundary w hwSphere).2
  have horders : ∀ u : CB, meromorphicOrderAt F u ≠ ⊤ := by
    apply
      (hF.exists_meromorphicOrderAt_ne_top_iff_forall
        ⟨nonempty_closedBall.mpr hR.le, (convex_closedBall (0 : ℂ) R).isPreconnected⟩).1
    refine ⟨⟨w, hwCB⟩, ?_⟩
    rw [hwOrder]
    simp
  obtain ⟨a, ha, ha_ne, hfactor⟩ := hF.extract_zeros_poles horders hD
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hfactor' : F =ᶠ[codiscreteWithin CB] P * a := by
    simpa only [P, D, Pi.smul_apply', smul_eq_mul] using hfactor
  have hperfect : Perfect CB := by
    change Perfect (closedBall (0 : ℂ) R)
    rw [← closure_ball (0 : ℂ) hR.ne']
    exact isOpen_ball.perfect_closure
  have hDz {z : ℂ} (hz : z ∈ sphere 0 R) : D z = 0 := by
    have hzCB : z ∈ CB := sphere_subset_closedBall hz
    change (divisor F CB) z = 0
    rw [divisor_apply hF hzCB,
      (hboundary z hz).1.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2
        (hboundary z hz).2]
    simp
  have hPprod : P = ∏ u ∈ hD.toFinset, (· - u) ^ D u := by
    apply finprod_eq_prod_of_mulSupport_subset
    simp [FactorizedRational.mulSupport]
  have hlog (z : ℂ) (hz : z ∈ sphere 0 R) :
      logDeriv F z =
        (∑ u ∈ hD.toFinset, (D u : ℂ) * (z - u)⁻¹) + logDeriv a z := by
    have hzCB : z ∈ CB := sphere_subset_closedBall hz
    have hP_analytic : AnalyticAt ℂ P z :=
      FactorizedRational.analyticAt (show 0 ≤ D z by rw [hDz hz])
    have hP_ne : P z ≠ 0 := FactorizedRational.ne_zero (hDz hz)
    have ha_analytic : AnalyticAt ℂ a z := ha z hzCB
    have ha_ne' : a z ≠ 0 := ha_ne ⟨z, hzCB⟩
    have hlocal_ne : F =ᶠ[𝓝[≠] z] P * a :=
      (hF z hzCB).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (hP_analytic.mul ha_analytic).meromorphicAt hzCB (hperfect.acc z hzCB) hfactor'
    have hlocal : F =ᶠ[𝓝 z] P * a :=
      (hboundary z hz).1.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        (hP_analytic.mul ha_analytic).continuousAt |>.1 hlocal_ne
    calc
      logDeriv F z = logDeriv (P * a) z := by
        simp only [logDeriv_apply]
        rw [hlocal.deriv_eq, hlocal.eq_of_nhds]
      _ = logDeriv P z + logDeriv a z :=
        logDeriv_mul z hP_ne ha_ne' hP_analytic.differentiableAt ha_analytic.differentiableAt
      _ = (∑ u ∈ hD.toFinset, (D u : ℂ) * (z - u)⁻¹) + logDeriv a z := by
        rw [hPprod]
        have hfactor_ne :
            ∀ u ∈ hD.toFinset, ((fun x : ℂ ↦ x - u) ^ D u) z ≠ 0 := by
          intro u hu
          have hDu : D u ≠ 0 := by
            simpa [Function.mem_support] using hD.mem_toFinset.mp hu
          have hzu : z ≠ u := by
            intro h
            subst u
            exact hDu (hDz hz)
          exact zpow_ne_zero _ (sub_ne_zero.mpr hzu)
        have hfactor_diff :
            ∀ u ∈ hD.toFinset, DifferentiableAt ℂ ((fun x : ℂ ↦ x - u) ^ D u) z := by
          intro u hu
          have hDu : D u ≠ 0 := by
            simpa [Function.mem_support] using hD.mem_toFinset.mp hu
          have hzu : z ≠ u := by
            intro h
            subst u
            exact hDu (hDz hz)
          exact
            ((analyticAt_id.fun_sub analyticAt_const).fun_zpow
              (sub_ne_zero.mpr hzu)).differentiableAt
        have hfun :
            (∏ u ∈ hD.toFinset, (fun x : ℂ ↦ x - u) ^ D u) =
              fun x : ℂ ↦
                ∏ u ∈ hD.toFinset, ((fun y : ℂ ↦ y - u) ^ D u) x := by
          funext x
          simp
        rw [hfun]
        rw [logDeriv_prod hfactor_ne hfactor_diff]
        apply congrArg (· + logDeriv a z)
        apply Finset.sum_congr rfl
        intro u hu
        have hpow :
            (fun x : ℂ ↦ x - u) ^ D u = fun x : ℂ ↦ (x - u) ^ D u := by
          funext x
          simp
        rw [hpow]
        rw [logDeriv_fun_zpow (f := fun x : ℂ ↦ x - u)
          (differentiableAt_id.sub_const u) (D u)]
        simp [logDeriv_apply]
  have huBall (u : ℂ) (hu : u ∈ hD.toFinset) : u ∈ ball 0 R := by
    rw [← closedBall_sdiff_sphere]
    refine ⟨D.supportWithinDomain (hD.mem_toFinset.mp hu), ?_⟩
    intro huSphere
    have hDu : D u ≠ 0 := by
      simpa [Function.mem_support] using hD.mem_toFinset.mp hu
    exact hDu (hDz huSphere)
  have hterm_integrable (u : ℂ) (hu : u ∈ hD.toFinset) :
      CircleIntegrable (fun z ↦ (D u : ℂ) * (z - u)⁻¹) 0 R := by
    have huNotSphere : u ∉ sphere 0 |R| := by
      rw [abs_of_pos hR]
      intro huSphere
      have hlt := mem_ball.mp (huBall u hu)
      have heq := mem_sphere.mp huSphere
      linarith
    have hinv : CircleIntegrable (fun z ↦ (z - u)⁻¹) 0 R :=
      circleIntegrable_sub_inv_iff.2 (Or.inr huNotSphere)
    simpa only [smul_eq_mul] using
      (hinv.const_fun_smul (a := (D u : ℂ)))
  have hlogA_analytic (z : ℂ) (hz : z ∈ CB) : AnalyticAt ℂ (logDeriv a) z := by
    simpa only [logDeriv] using (ha z hz).deriv.div (ha z hz) (ha_ne ⟨z, hz⟩)
  have hlogA_integrable : CircleIntegrable (logDeriv a) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hlogA_analytic z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hlogA_integral : (∮ z in C(0, R), logDeriv a z) = 0 := by
    apply
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
    · intro z hz
      exact (hlogA_analytic z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hlogA_analytic z (ball_subset_closedBall hz.1)).differentiableAt
  calc
    (∮ z in C(0, R), logDeriv F z) =
        ∮ z in C(0, R),
          (∑ u ∈ hD.toFinset, (D u : ℂ) * (z - u)⁻¹) + logDeriv a z :=
      circleIntegral.integral_congr hR.le hlog
    _ = (∮ z in C(0, R), ∑ u ∈ hD.toFinset, (D u : ℂ) * (z - u)⁻¹) +
        ∮ z in C(0, R), logDeriv a z :=
      circleIntegral.integral_add
        (CircleIntegrable.fun_sum hD.toFinset hterm_integrable) hlogA_integrable
    _ = (∑ u ∈ hD.toFinset,
          ∮ z in C(0, R), (D u : ℂ) * (z - u)⁻¹) := by
      rw [circleIntegral.integral_fun_sum hterm_integrable, hlogA_integral, add_zero]
    _ = ∑ u ∈ hD.toFinset, (D u : ℂ) * (2 * Real.pi * I) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (huBall u hu)]
    _ = (((∑ u ∈ hD.toFinset, D u) : ℤ) : ℂ) * (2 * Real.pi * I) := by
      rw [Int.cast_sum, Finset.sum_mul]
    _ = (((∑ᶠ u, D u) : ℤ) : ℂ) * (2 * Real.pi * I) := by
      rw [finsum_eq_sum D hD]
    _ = (((∑ᶠ z, (divisor F (closedBall 0 R)) z) : ℤ) : ℂ) *
        (2 * Real.pi * I) := by
      rfl

end Submission.Helpers
