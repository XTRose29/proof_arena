import Submission.SimpleClosedPolygonalCurve
import Submission.FinitePolygonalSet
import Submission.PolygonalPathInGeneralPosition
import Submission.PolygonalPathIntersectionMultiplicity
import Submission.CyclicCurvePresentation
import Submission.CyclicCurvePresentationIntersectionMultiplicity
import Submission.CyclicPresentationTriangleGeneralPosition
import Submission.FinitePolygonalSetCyclicCurvePresentation
import Submission.PolygonalPathMultiplicityCyclicPresentation
import Submission.CyclicPresentationClosedPathEvenIntersections
import Submission.TriangleBoundaryCyclicIntersectionMultiplicity
import Submission.TriangleBoundaryEvenIntersections

open Classical
noncomputable section

-- [TABLET NODE: ClosedPolygonalPathEvenIntersections]
lemma ClosedPolygonalPathEvenIntersections
    (J : SimpleClosedPolygonalCurve) (Γ : PolygonalPath)
    (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (hΓ : Γ.source = Γ.target)
    (hgp : PolygonalPathInGeneralPosition Γ K) :
    Even (PolygonalPathIntersectionMultiplicity Γ K) := by
-- BODY
  obtain ⟨R⟩ := FinitePolygonalSetCyclicCurvePresentation J K hKJ
  rw [PolygonalPathMultiplicityCyclicPresentation J Γ K hKJ hgp R]
  exact CyclicPresentationClosedPathEvenIntersections J Γ K hΓ hgp R
