import ChallengeDeps
import Submission.Helpers
import Submission.Hyperbolic

open LeanEval.Geometry

namespace Submission

theorem parallel_postulate_independent :
    (∃ (M : Type) (T : TarskiAbsolute M), Euclidean M T) ∧
    (∃ (M : Type) (T : TarskiAbsolute M), ¬ Euclidean M T) := by
  exact
    ⟨⟨Helpers.EPoint, Helpers.euclideanTarski,
        Helpers.euclideanTarski_isEuclidean⟩,
      ⟨Hyperbolic.HPoint, Hyperbolic.hyperbolicTarski,
        Hyperbolic.hyperbolicTarski_notEuclidean⟩⟩

end Submission
