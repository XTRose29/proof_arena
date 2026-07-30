import Submission.ConnectedSubsetContainedInUniqueComplementComponent
import Submission.DrawingFaceComponent
import Submission.OrdinaryDrawingImageWithoutEdge
import Submission.PlaneDrawingDartCollarChoiceData
import Submission.PlaneDrawingDartCollarChoiceDataExists
import Submission.PlaneDrawingDartSectorWitnessDataFromCollarChoices
import Submission.PlaneDrawingDartArcData
import Submission.PlaneDrawingDartSectorWitnessData
import Submission.PlaneDrawingDartSideStripData
import Submission.PlaneDrawingDartSideStripDataFromCollarChoices
import Submission.PlaneDrawingDartVertexStarData
import Submission.PlaneDrawingDartVertexSectorGeometry
import Submission.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import Submission.PolygonalArc
import Submission.PolygonalArcCarrierCompact
import Submission.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import Submission.PolygonalArcCollarControlRadiiExistsBelow
import Submission.PolygonalArcCollarLocalSideData
import Submission.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import Submission.PolygonalArcCollarMiddleForbiddenMarginsExists
import Submission.PolygonalArcCollarMiddleSegmentDataExists
import Submission.PolygonalArcCollarVertexLocalPieceData
import Submission.PolygonalArcEndpointIsolationExists
import Submission.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import Submission.PolygonalArcInitialEndpointLeftCone
import Submission.PolygonalArcOpenSegmentSubsetRelativeInterior
import Submission.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import Submission.PolygonalArcSideStripAssembly
import Submission.PolygonalArcTerminalEndpointLeftCone
import Submission.PolygonalSideStrips
import Submission.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSideStripsWithSectorWitnessesExist]
lemma PlaneDrawingDartSideStripsWithSectorWitnessesExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by
-- BODY
  obtain ⟨P⟩ := PlaneDrawingDartCollarChoiceDataExists G D hD A C
  obtain ⟨S, hleft, _hright⟩ :=
    PlaneDrawingDartSideStripDataFromCollarChoices G D A C P
  exact ⟨S, PlaneDrawingDartSectorWitnessDataFromCollarChoices G D A C P S hleft⟩
