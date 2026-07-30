import Submission.PlaneFaceData
import Submission.PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement
import Submission.PlaneTreeDrawingComplementConnected
import Submission.PlaneTreeLeafDeletionDrawingData
import Submission.PlaneTreeLeafDeletionGraphData
import Submission.PlaneTreeLeafPendantAttachment
import Submission.PlaneTreeNoEdgeComplementConnected
import Submission.PendantArcComplementConnected
import Submission.OrdinaryDrawingImageCompact
import Submission.OrdinaryDrawingImage
import Submission.OrdinaryPolygonalDrawing
import Submission.PolygonalArc
import Submission.PolygonallyPathConnected
import Submission.DrawingFaceComponent
import Submission.ComplementComponent
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeOneFace]
lemma PlaneTreeOneFace {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.IsTree → @Fintype.card A.Face A.faceFintype = 1 := by
-- BODY
  intro hTree
  exact PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement G D A
    (PlaneTreeDrawingComplementConnected G D hD hTree)
    (by
      rcases (OrdinaryDrawingImageCompact G D).isBounded.exists_norm_le with ⟨R, hR⟩
      let p : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (max R 0 + 1)
      refine ⟨p, ?_⟩
      intro hp
      have hp_norm_le : ‖p‖ ≤ R := hR p hp
      have hp_norm : ‖p‖ = max R 0 + 1 := by
        have hnonneg : 0 ≤ max R 0 + 1 := by
          nlinarith [le_max_right R 0]
        simp [p, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hR_lt : R < max R 0 + 1 := by
        nlinarith [le_max_left R 0]
      nlinarith)
