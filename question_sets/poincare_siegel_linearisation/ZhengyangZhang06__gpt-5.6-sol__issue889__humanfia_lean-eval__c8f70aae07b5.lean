import ChallengeDeps
import Submission.AnalyticAssembly

open LeanEval.ComplexAnalysis

namespace Submission

theorem poincare_siegel (α : ℝ) (_hα : IsDiophantine α)
    (lam : ℂ) (_hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))
    (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (_hf0 : f 0 = 0)
    (_hmult : deriv f 0 = lam) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), f (u z) = u (lam * z) := by
  obtain ⟨p, hp⟩ := _hf
  have hp0 : p.coeff 0 = 0 :=
    taylor_coeff_zero hp _hf0
  have hp1 : p.coeff 1 = lam :=
    taylor_coeff_one hp _hmult
  have hlam_norm : ‖lam‖ = 1 := by
    rw [_hlam, Complex.norm_exp]
    simp
  have hnonzero : ∀ n : ℕ, n ≠ 0 → lam ^ n ≠ 1 :=
    fun n hn =>
      Helpers.pow_ne_one_of_isDiophantine _hα _hlam hn
  have hnonresonant : ∀ n : ℕ, 2 ≤ n → lam ^ n ≠ lam :=
    fun n hn =>
      Helpers.pow_ne_self_of_isDiophantine _hα _hlam hn
  obtain ⟨c, T, hc, hT, hbound⟩ :=
    Helpers.exists_norm_pow_sub_one_lower_bound_nat _hα _hlam
  have hradius : 0 < (linearizationFMS p.coeff lam).radius :=
    linearizationFMS_radius_pos p hp.radius_pos lam hlam_norm
      hc hT hnonzero hbound
  exact exists_analytic_linearization p lam f hp hp0 hp1
    hnonresonant hradius

end Submission
