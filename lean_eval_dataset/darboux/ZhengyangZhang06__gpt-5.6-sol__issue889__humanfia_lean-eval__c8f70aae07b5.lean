import Submission.Darboux

open LeanEval.Geometry.Darboux
open Set Function Matrix
open scoped ContDiff

namespace Submission

theorem darboux {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (hα : IsSymplecticOn α U)
    {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → E n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : E n → E n) φ.target ∧
      ∀ z ∈ φ.target,
        IsDarbouxNormal
          ((α (φ.symm z)).compContinuousLinearMap
            (fderiv ℝ (φ.symm : E n → E n) z)) := by
  exact Submission.Darboux.darboux hU α hα hx

end Submission
