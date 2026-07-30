import Submission.OrdinaryPolygonalDrawing
import Submission.OrdinaryDrawingEmptyPartialData
import Submission.OrdinaryDrawingPartialDataComplete
import Submission.OrdinaryDrawingPartialDataOneEdgeExtension
import Submission.TwoSegmentPolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryPolygonalDrawingNonempty]
lemma OrdinaryPolygonalDrawingNonempty {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    Nonempty (OrdinaryPolygonalDrawing G) := by
-- BODY
  classical
  obtain ⟨edgeOrder, hedgeOrder_nodup, hedgeOrder_cover⟩ :=
    Finite.exists_univ_list G.edgeFinset
  have partialAlong :
      ∀ l : List G.edgeFinset, l.Nodup →
        Nonempty (OrdinaryDrawingPartialData G l.toFinset) := by
    intro l
    induction l with
    | nil =>
        intro _hnodup
        simpa using OrdinaryDrawingEmptyPartialData G
    | cons e l ih =>
        intro hnodup
        have hparts := List.nodup_cons.mp hnodup
        have he_not : e ∉ l.toFinset := by
          simpa using hparts.1
        obtain ⟨Ptail⟩ := ih hparts.2
        simpa using OrdinaryDrawingPartialDataOneEdgeExtension G Ptail e he_not
  obtain ⟨PfullList⟩ := partialAlong edgeOrder hedgeOrder_nodup
  have hfull :
      edgeOrder.toFinset = (Finset.univ : Finset G.edgeFinset) := by
    ext e
    simp [hedgeOrder_cover e]
  have Pfull : OrdinaryDrawingPartialData G (Finset.univ : Finset G.edgeFinset) := by
    simpa [hfull] using PfullList
  exact ⟨OrdinaryDrawingPartialDataComplete G Pfull⟩
