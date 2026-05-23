/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: sturm_separation
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: ecd95c4cc46b14181d140adadbefe67021533ea7
issue_number: 128
-/
import Mathlib
import Submission.Helpers

open Filter Topology Set

namespace Submission

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  -- Convert hW from raw form to Wronskian form.
  have hW' : ∃ x₀ ∈ J, Submission.Helpers.W y₁ y₂ x₀ ≠ 0 := hW
  obtain ⟨c, hc_in, hc_zero⟩ := Submission.Helpers.exists_zero_y₂
    J hJ_open hJ_conn hp hq hJ_sub hy₁ hy₁' hy₂ hy₂' hW' hab hza hzb hne
  refine ⟨c, ⟨hc_in, hc_zero⟩, ?_⟩
  rintro c' ⟨hc'_in, hc'_zero⟩
  exact Submission.Helpers.unique_zero_y₂
    J hJ_open hJ_conn hp hq hJ_sub hy₁ hy₁' hy₂ hy₂' hW' hab hne hc'_in hc_in hc'_zero hc_zero

end Submission
