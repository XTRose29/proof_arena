import ChallengeDeps
import Submission.Helpers

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

theorem glAction_range_eq_centralizer_symAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (glAction R M k)) =
      Subalgebra.centralizer R (Set.range (symAction R M k)) := by
  apply le_antisymm
  · exact Submission.Helpers.adjoin_le_centralizer
  · exact Submission.Helpers.centralizer_le_adjoin

end Submission
