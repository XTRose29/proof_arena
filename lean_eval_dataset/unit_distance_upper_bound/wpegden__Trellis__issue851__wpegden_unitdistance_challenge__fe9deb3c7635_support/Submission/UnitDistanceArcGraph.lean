import Submission.CrossingNumber
import Submission.PolygonalReplacementForGeometricArcs
import Submission.UnitCircle
import Submission.UnitCircleIncidenceCount
import Submission.UnitCircleIncidenceDoubleCount
import Submission.UnitCirclesIntersectionsAtMostTwo
import Submission.UnitDistanceArcSelectionDrawing
import Submission.unitDist

local notation "unitDist" => UnitDistanceUpperBoundProof.unitDist

open Classical
open scoped Real
noncomputable section

-- [TABLET NODE: UnitDistanceArcGraph]
lemma UnitDistanceArcGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet),
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (CrossingNumber G : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
-- BODY
  rcases UnitDistanceArcSelectionDrawing P with ⟨G, hGfin, D, hedge, hlocal⟩
  letI := hGfin
  rcases PolygonalReplacementForGeometricArcs G D with ⟨_D', _hcard, hcross⟩
  refine ⟨G, hGfin, hedge, ?_⟩
  exact (Nat.cast_le.mpr hcross).trans hlocal
