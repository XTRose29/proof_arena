import Mathlib
import Submission.Helpers

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Submission

theorem normal_spectral_theorem (A : Matrix n n ℂ) :
    IsStarNormal A ↔
      ∃ U ∈ unitary (Matrix n n ℂ), ∃ d : n → ℂ,
        A = U * diagonal d * star U := by
  constructor
  · intro hA
    let T := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A
    have hT : IsStarNormal T := by
      letI : IsStarNormal A := hA
      simpa [T] using
        (IsStarNormal.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A)
    obtain ⟨b, d, hb⟩ :=
      Helpers.exists_orthonormal_eigenbasis_of_isStarNormal T hT finrank_euclideanSpace
    obtain ⟨U, hU, hAU⟩ :=
      Helpers.matrix_unitarily_diagonalizable_of_orthonormal_eigenbasis A b d hb
    exact ⟨U, hU, d, hAU⟩
  · rintro ⟨U, hU, d, rfl⟩
    letI : IsStarNormal (diagonal d) := by
      rw [isStarNormal_iff]
      simpa [star_eq_conjTranspose] using Matrix.commute_diagonal (star d) d
    let u : unitary (Matrix n n ℂ) := ⟨U, hU⟩
    have hconj :
        IsStarNormal (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u (diagonal d)) :=
      inferInstance
    simpa [u] using hconj

end Submission
