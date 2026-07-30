import ChallengeDeps
import Submission.AlgebraicTrefoil
import Submission.CompactifiedSymmetry
import Submission.CyclicCover
import Submission.CoverSymmetry
import Submission.PageObstruction
import Submission.Milnor
import Submission.Monodromy
import Submission.PeripheralConclusion
import Submission.Symmetry

open LeanEval.KnotTheory

namespace Submission

theorem exists_chiral_knot : ∃ K : Knot, K.Chiral := by
  exact ⟨AlgebraicTrefoil.knot,
    Symmetry.chiral_of_no_negativeSymmetry AlgebraicTrefoil.knot
      PeripheralConclusion.no_negativeSymmetry⟩

end Submission
