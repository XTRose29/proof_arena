import ChallengeDeps
import Submission.General

open LeanEval.Geometry.SardTheoremProblem
open MeasureTheory Module
open scoped ContDiff

namespace Submission

theorem sard {m n : ℕ} (f : E m → E n) (_hf : ContDiff ℝ ∞ f) :
    volume (criticalValues f) = 0 := by
  rw [criticalValues]
  apply measure_mono_null _ (sardCritical f _hf)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  change ¬Function.Surjective (fderiv ℝ f x).toLinearMap
  apply (Helpers.finrank_range_lt_iff_not_surjective
    (fderiv ℝ f x).toLinearMap).mp
  simpa only [fderivRank, finrank_euclideanSpace_fin] using hx.2

end Submission
