/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: dirichlet_eigenvalues_eq_nat_sq
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 00b32807abe0d286c4638daf888c739e1bb4b90c
issue_number: 172
-/
import Mathlib
import Submission.Helpers

open scoped Real
open Submission.Helpers

namespace Submission

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · exact backward_direction lam
  · rintro ⟨n, hn, hlam⟩
    exact forward_direction hn hlam

end Submission
