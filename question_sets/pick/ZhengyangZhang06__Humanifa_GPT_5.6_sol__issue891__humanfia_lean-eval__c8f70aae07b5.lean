import Submission.InductiveSolution

open LeanEval.Geometry.PicksTheorem

namespace Submission

theorem pick {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    area ((latPoly v).boundary (R := ℝ))
      = (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1 :=
  InductiveSolution.pick hn v hsimple

end Submission
