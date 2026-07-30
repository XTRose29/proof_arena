import Submission.Preamble

open Classical
noncomputable section

-- [TABLET NODE: unitDist]
noncomputable def UnitDistanceUpperBoundProof.unitDist
    (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
-- BODY
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2
