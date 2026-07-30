import Submission.CyclicCurvePresentation
import Submission.CyclicPresentationTriangleGeneralPosition
import Submission.TriangleBoundaryCyclicIntersectionMultiplicity
import Submission.TriangleBoundaryMultiplicityEqualsOccurrenceNcard
import Submission.TriangleBoundaryOccurrenceSetEvenByIntervals

open Classical
noncomputable section

-- [TABLET NODE: TriangleBoundaryEvenIntersections]
lemma TriangleBoundaryEvenIntersections
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2))
    (hza : z ≠ a) (hab : a ≠ b) (hbz : b ≠ z)
    (hncol : ¬ ∃ c : ℝ, b - a = c • (z - a))
    (hgp : CyclicPresentationTriangleGeneralPosition R z a b) :
    Even (TriangleBoundaryCyclicIntersectionMultiplicity R z a b) := by
-- BODY
  rw [TriangleBoundaryMultiplicityEqualsOccurrenceNcard R z a b hgp]
  exact TriangleBoundaryOccurrenceSetEvenByIntervals R z a b hza hab hbz hncol hgp
