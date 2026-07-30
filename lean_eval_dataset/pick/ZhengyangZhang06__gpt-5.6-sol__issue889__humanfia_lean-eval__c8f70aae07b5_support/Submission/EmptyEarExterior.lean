import Submission.EmptyEarFill
import Submission.TriangleAttachment

open LeanEval.Geometry.PicksTheorem

namespace Submission.EmptyEarExterior

/-- The two filled children of a strictly exposed vertex-empty candidate
have a single exterior component. -/
theorem childFill_compl_isPreconnected
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (M : ℤ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          ExtremeVertex.exposingFunctional M
              (toPlane (v j)) <
            ExtremeVertex.exposingFunctional M
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1)))))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (hempty :
      EmptyCap.VertexEmptyAtOne hn v htriangle) :
    IsPreconnected
      (FilledRegion.fill
            ((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ)) ∪
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)))ᶜ := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let triangleBoundary :=
    (latPoly ear).boundary (R := ℝ)
  let reducedBoundary :=
    (latPoly reduced).boundary (R := ℝ)
  let t := LatticeTriangle.triangle ear htriangle
  have htPolygon :
      t.toPolygon = latPoly ear := by
    rfl
  have htriangleFill :
      FilledRegion.fill triangleBoundary =
        t.closedInterior := by
    change
      FilledRegion.fill
          ((latPoly ear).boundary (R := ℝ)) =
        t.closedInterior
    rw [← htPolygon,
      TriangleFill.fill_toPolygon_boundary_eq_closedInterior]
  have hfillInter :
      t.closedInterior ∩
          FilledRegion.fill reducedBoundary =
        (t.faceOpposite 1).closedInterior := by
    calc
      t.closedInterior ∩
            FilledRegion.fill reducedBoundary =
          FilledRegion.fill triangleBoundary ∩
            FilledRegion.fill reducedBoundary := by
              rw [htriangleFill]
      _ = CleanEar.diagonal hn v := by
        simpa [triangleBoundary, reducedBoundary, ear, reduced] using
          EmptyEarFill.childFill_inter_eq_diagonal
            hn v hsimple M hvertices htriangle hempty
      _ = (t.faceOpposite 1).closedInterior := by
        rw [Submission.Triangle.closedInterior_faceOpposite_one,
          affineSegment_eq_segment]
        simp [CleanEar.diagonal, t, ear]
  have hfillInter' :
      FilledRegion.fill reducedBoundary ∩
          t.closedInterior =
        (t.faceOpposite 1).closedInterior := by
    rw [Set.inter_comm]
    exact hfillInter
  have hreducedClosed :
      IsClosed
        (FilledRegion.fill reducedBoundary) :=
    FilledRegion.isClosed_fill
      (Helpers.isCompact_boundary
        (latPoly reduced)).isClosed
  have hreducedCompl :
      IsPreconnected
        (FilledRegion.fill reducedBoundary)ᶜ :=
    FilledRegion.isPreconnected_compl_fill
      (Helpers.isBounded_boundary
        (latPoly reduced))
  have hattached :=
    TriangleAttachment.isPreconnected_compl_union_closedInterior
      t hreducedClosed hreducedCompl hfillInter'
  rw [htriangleFill]
  simpa [triangleBoundary, reducedBoundary, Set.union_comm] using
    hattached

end Submission.EmptyEarExterior
