import Submission.EmptyCap
import Submission.FillEar
import Submission.ReducedSupport
import Submission.TriangleFill

open LeanEval.Geometry.PicksTheorem

namespace Submission.EmptyEarFill

/-- A strictly exposed, vertex-empty candidate triangle meets the filled
reduced polygon exactly along its base. -/
theorem childFill_inter_eq_diagonal
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
    FilledRegion.fill
          ((latPoly
            (EarRemoval.earTriangle hn v)).boundary
              (R := ℝ)) ∩
        FilledRegion.fill
          ((latPoly
            (EarRemoval.removeSecond v)).boundary
              (R := ℝ)) =
      CleanEar.diagonal hn v := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let triangleBoundary :=
    (latPoly ear).boundary (R := ℝ)
  let reducedBoundary :=
    (latPoly reduced).boundary (R := ℝ)
  let L := ExtremeVertex.exposingFunctional M
  let t := LatticeTriangle.triangle ear htriangle
  have htPolygon :
      t.toPolygon = latPoly ear := by
    rfl
  obtain ⟨c, hc, hfillReduced⟩ :=
    ReducedSupport.exists_fill_reduced_support_level
      hn v M hvertices
  have hcapCompl :
      TriangleCap.openCap t ⊆ reducedBoundaryᶜ := by
    simpa [t, ear, reducedBoundary, reduced] using
      EmptyCap.openCap_subset_reducedBoundary_compl_of_vertexEmpty
        hn v hsimple htriangle hempty
  have htip :
      t.points 1 ∉
        FilledRegion.fill reducedBoundary := by
    intro htipFill
    have htipLe :
        L (t.points 1) ≤ c :=
      hfillReduced htipFill
    have htipValue :
        L (t.points 1) =
          L
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1)))) := by
      simp [t, ear]
    rw [htipValue] at htipLe
    exact (not_lt_of_ge htipLe) hc
  have hfaceFill :
      (t.faceOpposite 1).closedInterior ⊆
        FilledRegion.fill reducedBoundary := by
    intro x hxFace
    have hxDiagonal :
        x ∈ CleanEar.diagonal hn v := by
      rw [Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_eq_segment] at hxFace
      simpa [CleanEar.diagonal, t, ear] using hxFace
    exact
      Or.inl <|
        FillEar.diagonal_subset_reducedBoundary
          hn v hxDiagonal
  have hintersection :
      t.closedInterior ∩
          FilledRegion.fill reducedBoundary =
        (t.faceOpposite 1).closedInterior :=
    TriangleCap.closedInterior_inter_fill_eq_faceOpposite_one
      t hcapCompl htip hfaceFill
  change
    FilledRegion.fill triangleBoundary ∩
        FilledRegion.fill reducedBoundary =
      CleanEar.diagonal hn v
  calc
    FilledRegion.fill triangleBoundary ∩
          FilledRegion.fill reducedBoundary =
        t.closedInterior ∩
          FilledRegion.fill reducedBoundary := by
            change
              FilledRegion.fill
                    ((latPoly ear).boundary (R := ℝ)) ∩
                  FilledRegion.fill reducedBoundary =
                t.closedInterior ∩
                  FilledRegion.fill reducedBoundary
            rw [← htPolygon,
              TriangleFill.fill_toPolygon_boundary_eq_closedInterior]
    _ = (t.faceOpposite 1).closedInterior :=
      hintersection
    _ = CleanEar.diagonal hn v := by
      rw [Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_eq_segment]
      simp [CleanEar.diagonal, t, ear]

end Submission.EmptyEarFill
