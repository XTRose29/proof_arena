import Submission.CrossingFreeEdgeInteriorDisjoint
import Submission.DartSuccessorFromLocalClockwiseNext
import Submission.OrdinaryPolygonalDrawing
import Submission.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import Submission.PlanarClockwiseSweptTwoRayEndpointConesInSector
import Submission.PlanarSlitDiskEndpointConesAvoidRay
import Submission.PlaneDrawingDartGeometricClockwiseSectors
import Submission.PlaneDrawingDartArcData
import Submission.PlaneDrawingDartFirstGermsForRadii
import Submission.PlaneDrawingDartSourceEndpointRayCovers
import Submission.PlaneDrawingDartUnitFirstGermsForRadii
import Submission.PlaneDrawingDartVertexStarData
import Submission.PlaneDrawingDartVertexSectorGeometry
import Submission.PolygonalArc
import Submission.PolygonalArcCarrierCompact
import Submission.PolygonalArcReverse
import Submission.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexSectorGeometryExists]
lemma PlaneDrawingDartVertexSectorGeometryExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    Nonempty (PlaneDrawingDartVertexSectorGeometry G D A) := by
-- BODY
  rcases PlaneDrawingDartGeometricClockwiseSectors G D hD A with ⟨C, _hmodel⟩
  exact ⟨C⟩
