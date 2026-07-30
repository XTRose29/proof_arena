import Submission.CoefficientMajorant

open Filter FormalMultilinearSeries

namespace Submission

theorem taylor_coeff_zero
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) (hf0 : f 0 = 0) :
    p.coeff 0 = 0 := by
  rw [FormalMultilinearSeries.coeff, hp.coeff_zero, hf0]

theorem taylor_coeff_one
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {lam : ℂ}
    (hp : HasFPowerSeriesAt f p 0) (hmult : deriv f 0 = lam) :
    p.coeff 1 = lam := by
  change p 1 (fun _ => 1) = lam
  rw [← hp.deriv]
  exact hmult

/-- Analytic realization of a convergent formal solution of Schröder's
equation. -/
theorem exists_analytic_linearization
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (lam : ℂ)
    (f : ℂ → ℂ)
    (hp : HasFPowerSeriesAt f p 0)
    (hp0 : p.coeff 0 = 0)
    (hp1 : p.coeff 1 = lam)
    (hnonresonant : ∀ n : ℕ, 2 ≤ n → lam ^ n ≠ lam)
    (hradius : 0 < (linearizationFMS p.coeff lam).radius) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), f (u z) = u (lam * z) := by
  let U := linearizationFMS p.coeff lam
  let u : ℂ → ℂ := U.sum
  have huSeries : HasFPowerSeriesAt u U 0 :=
    (U.hasFPowerSeriesOnBall hradius).hasFPowerSeriesAt
  have hu0 : u 0 = 0 := by
    simpa [U, linearizationFMS] using
      (huSeries.coeff_zero (fun _ : Fin 0 => (0 : ℂ))).symm
  have huAnalytic : AnalyticAt ℂ u 0 := huSeries.analyticAt
  have huDeriv : deriv u 0 = 1 := by
    rw [huSeries.deriv]
    simp [U]
  have hleft :
      HasFPowerSeriesAt (fun z => f (u z)) (p.comp U) 0 := by
    have hp_at_u_zero : HasFPowerSeriesAt f p (u 0) := by
      simpa [hu0] using hp
    simpa [Function.comp_def] using hp_at_u_zero.comp huSeries
  have hright :
      HasFPowerSeriesAt (fun z => u (lam * z))
        (U.compContinuousLinearMap (rotationCLM lam)) 0 := by
    have huSeries_at_rotation_zero :
        HasFPowerSeriesAt u U (rotationCLM lam 0) := by
      simpa using huSeries
    simpa [Function.comp_def] using
      huSeries_at_rotation_zero.compContinuousLinearMap
        (u := rotationCLM lam) (x := 0)
  have hseries :
      p.comp U = U.compContinuousLinearMap (rotationCLM lam) := by
    simpa [U] using comp_linearizationFMS p lam hp0 hp1 hnonresonant
  refine ⟨u, huAnalytic, hu0, huDeriv, ?_⟩
  rw [hseries] at hleft
  filter_upwards [hleft.eventually_hasSum_sub,
    hright.eventually_hasSum_sub] with z hz₁ hz₂
  exact hz₁.unique hz₂

end Submission
