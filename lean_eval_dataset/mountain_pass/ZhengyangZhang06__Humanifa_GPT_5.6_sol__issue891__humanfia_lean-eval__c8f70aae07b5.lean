import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.MountainPassProblem
open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace Submission

theorem mountain_pass (f : E → ℝ) (_hf : ContDiff ℝ 1 f) (_hps : PalaisSmale f)
    {a b : E} {ε r : ℝ} (_hmr : MountainRange f a b ε r) :
    ∃ x : E, IsCriticalPoint f x ∧
      f x = mountainPassLevel f a b ∧ ε ≤ mountainPassLevel f a b := by
  obtain ⟨x, hx_critical, hx_value⟩ :=
    Helpers.exists_criticalPoint_at_mountainPassLevel f _hf _hps _hmr
  exact ⟨x, hx_critical, hx_value,
    Helpers.epsilon_le_mountainPassLevel _hf.continuous _hmr⟩

end Submission
