import ChallengeDeps

open LeanEval.Geometry.Darboux
open Set Function Matrix
open scoped ContDiff

namespace Submission.Helpers

theorem darbouxZero {U : Set (E 0)} (hU : IsOpen U)
    (α : E 0 → E 0 [⋀^Fin 2]→L[ℝ] ℝ) (x : E 0) (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E 0) (E 0),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E 0 → E 0) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : E 0 → E 0) φ.target ∧
      ∀ z ∈ φ.target,
        IsDarbouxNormal
          ((α (φ.symm z)).compContinuousLinearMap
            (fderiv ℝ (φ.symm : E 0 → E 0) z)) := by
  let φ := OpenPartialHomeomorph.ofSet U hU
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [φ]
  · simp [φ]
  · simpa [φ] using (contDiff_id : ContDiff ℝ ∞ (id : E 0 → E 0)).contDiffOn
  · simpa [φ] using (contDiff_id : ContDiff ℝ ∞ (id : E 0 → E 0)).contDiffOn
  · intro z hz
    simp [IsDarbouxNormal]

end Submission.Helpers
