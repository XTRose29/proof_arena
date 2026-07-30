import ChallengeDeps
import Submission.Helpers
import Submission.SphereEuler

open LeanEval.Combinatorics.DehnSommerville

namespace Submission

theorem dehn_sommerville {d j : ℕ} (X : FiniteSimplicialSphere d) (hj : j ≤ d) :
    hVector X j = hVector X (d - j) :=
  Helpers.DehnSommerville.dehn_sommerville_of_hasSignedEulerianLinks X
    (Helpers.DehnSommerville.hasSignedEulerianLinks_of_hasSphereDeletionEuler X
      (Helpers.DehnSommerville.FinitePolyhedron.hasSphereDeletionEuler d X)) hj

end Submission
