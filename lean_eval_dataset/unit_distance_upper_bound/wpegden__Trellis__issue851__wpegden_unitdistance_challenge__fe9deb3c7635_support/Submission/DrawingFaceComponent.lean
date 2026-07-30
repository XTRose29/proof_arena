import Submission.OrdinaryDrawingImage
import Submission.ComplementComponent

open Classical
noncomputable section

-- [TABLET NODE: DrawingFaceComponent]
def DrawingFaceComponent {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  ComplementComponent (OrdinaryDrawingImage G D) F
