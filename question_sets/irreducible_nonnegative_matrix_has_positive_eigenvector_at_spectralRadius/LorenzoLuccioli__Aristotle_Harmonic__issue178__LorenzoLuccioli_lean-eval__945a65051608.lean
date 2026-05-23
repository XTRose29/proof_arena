/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 945a650516082dfeba205b6b4c2ffab1515b0669
issue_number: 178
-/
import Mathlib
import Submission.Helpers

open scoped NNReal

namespace Submission

open Submission.Helpers

theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ)
    (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
      (∀ i, 0 < v i) := by
  -- Get the Perron root and eigenvector from core theorem
  obtain ⟨rho, v, hrho_nn, hv_nn, hv_nz, hAv⟩ := perron_frobenius_core A hA
  -- The eigenvector is actually positive (by irreducibility)
  have hv_pos : ∀ i, 0 < v i := nonneg_eigenvec_is_pos hA hv_nn hv_nz hAv hrho_nn
  -- The eigenvalue is nonneg
  have hrho_nn' : 0 ≤ rho := perron_eigenvalue_nonneg hA.1 hv_pos hAv
  -- The eigenvalue dominates all real eigenvalues
  have hdom : ∀ mu : ℝ, mu ∈ spectrum ℝ A → ‖mu‖₊ ≤ ‖rho‖₊ := by
    intro mu hmu
    obtain ⟨w, hw_nz, hAw⟩ := eigenvector_from_spectrum A mu hmu
    have h_abs := abs_eigenvalue_le hA.1 hv_pos hAv hw_nz hAw
    have : ‖mu‖ ≤ ‖rho‖ := by
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrho_nn']
    exact_mod_cast this
  -- rho equals the spectral radius
  have hrho_eq : (spectralRadius ℝ A).toReal = rho :=
    perron_root_eq_spectralRadius A hA.1 hv_pos hAv hrho_nn' hdom
  -- Construct the eigenvector
  refine ⟨v, ?_, hv_pos⟩
  refine ⟨?_, ne_of_apply_ne (fun x => x (Classical.arbitrary n)) (ne_of_gt (hv_pos _))⟩
  rw [Module.End.mem_eigenspace_iff, hrho_eq, Matrix.toLin'_apply]
  exact hAv

end Submission
