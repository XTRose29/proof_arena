import Mathlib
import Submission.Helpers

open scoped NNReal

namespace Submission

theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ)
    (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
      (∀ i, 0 < v i) := by
  obtain ⟨r, v, hr, hv, hAv⟩ := Helpers.exists_positive_eigenpair A hA
  have hradius : (spectralRadius ℝ A).toReal = r :=
    Helpers.spectralRadius_eq_of_positive_eigenvector hA.nonneg hr hv hAv
  refine ⟨v, ?_, hv⟩
  rw [Module.End.hasEigenvector_iff]
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · simpa only [Matrix.toLin'_apply, hradius] using hAv
  · intro hv0
    let i : n := Classical.choice inferInstance
    simpa [hv0] using hv i

end Submission
