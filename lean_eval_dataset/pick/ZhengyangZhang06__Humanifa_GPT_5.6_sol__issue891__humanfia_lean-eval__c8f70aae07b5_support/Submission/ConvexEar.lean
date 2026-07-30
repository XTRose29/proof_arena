import Submission.EarTopology

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.ConvexEar

/-- If the parent and its two ear children are frontiers of compact convex
regions, the ordinary interior decomposition is already the exact core ear
certificate.  `ConvexInside` converts each ordinary interior back to the
challenge's bounded-component definition. -/
theorem coreIsEarAtOne_of_regions
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (parentRegion triangleRegion reducedRegion :
      Set (ℝ × ℝ))
    (hparentConvex : Convex ℝ parentRegion)
    (hparentCompact : IsCompact parentRegion)
    (hparentNonempty : parentRegion.Nonempty)
    (htriangleConvex : Convex ℝ triangleRegion)
    (htriangleCompact : IsCompact triangleRegion)
    (htriangleNonempty : triangleRegion.Nonempty)
    (hreducedConvex : Convex ℝ reducedRegion)
    (hreducedCompact : IsCompact reducedRegion)
    (hreducedNonempty : reducedRegion.Nonempty)
    (hparentBoundary :
      (latPoly v).boundary (R := ℝ) =
        frontier parentRegion)
    (htriangleBoundary :
      (latPoly (EarRemoval.earTriangle hn v)).boundary
          (R := ℝ) =
        frontier triangleRegion)
    (hreducedBoundary :
      (latPoly (EarRemoval.removeSecond v)).boundary
          (R := ℝ) =
        frontier reducedRegion)
    (hpartition :
      interior parentRegion =
        (interior triangleRegion ∪
          interior reducedRegion) ∪
          openSegment ℝ (toPlane (v 0))
            (toPlane (v ⟨2, by omega⟩)))
    (hdisjoint :
      Disjoint
        (interior triangleRegion)
        (interior reducedRegion)) :
    CleanEar.CoreIsEarAtOne hn v := by
  have hparentInside :
      inside ((latPoly v).boundary (R := ℝ)) =
        interior parentRegion := by
    rw [hparentBoundary]
    exact
      ConvexInside.inside_frontier_eq_interior
        hparentConvex hparentCompact hparentNonempty
  have htriangleInside :
      inside
          ((latPoly
            (EarRemoval.earTriangle hn v)).boundary
              (R := ℝ)) =
        interior triangleRegion := by
    rw [htriangleBoundary]
    exact
      ConvexInside.inside_frontier_eq_interior
        htriangleConvex htriangleCompact htriangleNonempty
  have hreducedInside :
      inside
          ((latPoly
            (EarRemoval.removeSecond v)).boundary
              (R := ℝ)) =
        interior reducedRegion := by
    rw [hreducedBoundary]
    exact
      ConvexInside.inside_frontier_eq_interior
        hreducedConvex hreducedCompact hreducedNonempty
  refine ⟨?_, ?_⟩
  · rw [hparentInside, htriangleInside, hreducedInside]
    exact hpartition
  · rw [htriangleInside, hreducedInside]
    exact hdisjoint

end Submission.ConvexEar
