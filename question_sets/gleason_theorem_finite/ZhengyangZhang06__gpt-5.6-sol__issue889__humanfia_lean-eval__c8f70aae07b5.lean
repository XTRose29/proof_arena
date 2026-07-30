import ChallengeDeps
import Submission.Bridge
import Submission.Regularity

open LeanEval.Analysis

namespace Submission

theorem gleason_theorem_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (f : FrameFunction H) :
    ∃! ρ : H →L[ℂ] H,
      ContinuousLinearMap.IsPositive ρ ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P) := by
  apply existsUnique_density_of_orthogonal_parallelogram f hdim
  intro x y hxy
  exact (quadraticDefect_eq_zero_iff f.homogeneousValue x y).mp
    (f.quadraticDefect_eq_zero_of_orthogonal hdim hxy)

end Submission
