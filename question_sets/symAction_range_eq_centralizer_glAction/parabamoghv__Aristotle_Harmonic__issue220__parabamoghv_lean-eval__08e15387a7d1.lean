/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: symAction_range_eq_centralizer_glAction
user: parabamoghv
model: Aristotle (Harmonic)
submission_repo: parabamoghv/lean-eval
submission_ref: 08e15387a7d1e8c066ceb916e384d44c5e76296b
issue_number: 220
-/
import ChallengeDeps
import Submission.Helpers

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

theorem symAction_range_eq_centralizer_glAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (symAction R M k)) =
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  apply le_antisymm
  · exact adjoin_symAction_le_centralizer_glAction
  · exact centralizer_glAction_le_adjoin_symAction

end Submission
