import Submission.EmptyEarFill
import Submission.TriangleSeam

open LeanEval.Geometry.PicksTheorem

namespace Submission.EmptyEarSeam

/-- If the reduced filled region is regular closed, every non-parent point
of the prospective ear diagonal is interior to the union of the two child
fills. -/
theorem diagonal_sdiff_parent_subset_interior
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
      EmptyCap.VertexEmptyAtOne hn v htriangle)
    (houter :
      (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v =
        {toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)})
    (hregular :
      closure
          (interior
            (FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ)))) =
        FilledRegion.fill
          ((latPoly
            (EarRemoval.removeSecond v)).boundary
              (R := ℝ))) :
    CleanEar.diagonal hn v \
          (latPoly v).boundary (R := ℝ) ⊆
      interior
        (FilledRegion.fill
              ((latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ)) ∪
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ))) := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let parentBoundary :=
    (latPoly v).boundary (R := ℝ)
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
  have hdiagonalFace :
      CleanEar.diagonal hn v =
        (t.faceOpposite 1).closedInterior := by
    rw [Submission.Triangle.closedInterior_faceOpposite_one,
      affineSegment_eq_segment]
    simp [CleanEar.diagonal, t, ear]
  have hfillInter :
      FilledRegion.fill reducedBoundary ∩
          t.closedInterior =
        (t.faceOpposite 1).closedInterior := by
    rw [Set.inter_comm, ← htriangleFill,
      EmptyEarFill.childFill_inter_eq_diagonal
        hn v hsimple M hvertices htriangle hempty,
      hdiagonalFace]
  have hboundaryUnion :
      triangleBoundary ∪ reducedBoundary =
        parentBoundary ∪ CleanEar.diagonal hn v := by
    simpa [triangleBoundary, reducedBoundary, parentBoundary,
      ear, reduced, CleanEar.diagonal] using
      EarRemoval.child_boundaries_union hn v
  have hreducedSubset :
      reducedBoundary ⊆
        parentBoundary ∪ CleanEar.diagonal hn v := by
    intro x hx
    rw [← hboundaryUnion]
    exact Or.inr hx
  intro p hp
  have hpOpen :
      p ∈
        openSegment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩)) :=
    FillEar.mem_openDiagonal_of_mem_diagonal_of_notMem_parent
      hn v hsimple houter hp.1 hp.2
  have hpFace :
      p ∈ (t.faceOpposite 1).closedInterior := by
    rw [← hdiagonalFace]
    exact hp.1
  have hpCoordZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 p := by
    have hzero :
        toPlane (v 0) = t.points 0 := by
      simp [t, ear]
    have htwo :
        toPlane (v ⟨2, by omega⟩) =
          t.points 2 := by
      simp [t, ear]
    rw [hzero, htwo, openSegment_eq_image_lineMap] at hpOpen
    obtain ⟨r, hr, rfl⟩ := hpOpen
    simp
    exact hr.2
  have hpCoordTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 p := by
    have hzero :
        toPlane (v 0) = t.points 0 := by
      simp [t, ear]
    have htwo :
        toPlane (v ⟨2, by omega⟩) =
          t.points 2 := by
      simp [t, ear]
    rw [hzero, htwo, openSegment_eq_image_lineMap] at hpOpen
    obtain ⟨r, hr, rfl⟩ := hpOpen
    simp
    exact hr.1
  let N : Set (ℝ × ℝ) :=
    parentBoundaryᶜ ∩
      {q |
        0 <
          (Submission.Triangle.affineBasis t).coord 0 q} ∩
      {q |
        0 <
          (Submission.Triangle.affineBasis t).coord 2 q}
  have hNopen : IsOpen N := by
    have hParentOpen : IsOpen parentBoundaryᶜ := by
      dsimp [parentBoundary]
      exact
        (Helpers.isCompact_boundary (latPoly v)).isClosed.isOpen_compl
    exact
      (hParentOpen.inter
          (isOpen_Ioi.preimage <|
            AffineMap.continuous_of_finiteDimensional
              ((Submission.Triangle.affineBasis t).coord 0))).inter
        (isOpen_Ioi.preimage <|
          AffineMap.continuous_of_finiteDimensional
            ((Submission.Triangle.affineBasis t).coord 2))
  have hpN : p ∈ N :=
    ⟨⟨hp.2, hpCoordZero⟩, hpCoordTwo⟩
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.mp hNopen p hpN
  have hside :
      ∀ q ∈ Metric.ball p ρ,
        0 <
            (Submission.Triangle.affineBasis t).coord 0 q ∧
          0 <
            (Submission.Triangle.affineBasis t).coord 2 q := by
    intro q hq
    exact ⟨(hball hq).1.2, (hball hq).2⟩
  have hboundary :
      ∀ q ∈ Metric.ball p ρ,
        q ∈ reducedBoundary →
          (Submission.Triangle.affineBasis t).coord 1 q = 0 := by
    intro q hqBall hqReduced
    rcases hreducedSubset hqReduced with hqParent | hqDiagonal
    · exact False.elim ((hball hqBall).1.1 hqParent)
    · have hqFace :
          q ∈ (t.faceOpposite 1).closedInterior := by
        rw [← hdiagonalFace]
        exact hqDiagonal
      exact
        (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
          t
          (t.closedInterior_faceOpposite_subset_closedInterior
            1 hqFace)
          1).mpr hqFace
  have hopposite :
      ∃ z ∈ Metric.ball p ρ,
        (Submission.Triangle.affineBasis t).coord 1 z < 0 ∧
          z ∈ FilledRegion.fill reducedBoundary := by
    apply
      TriangleSeam.exists_opposite_fill_point_of_regular
        t hρ hside
    · simpa [reducedBoundary, reduced] using hregular
    · exact hfillInter
    · exact hpFace
  have hpInterior :=
    TriangleSeam.mem_interior_union_closedInterior_of_opposite_fill_point
      t hρ hside hboundary hopposite
  rw [htriangleFill]
  simpa [triangleBoundary, reducedBoundary, ear, reduced,
    Set.union_comm] using
    hpInterior

end Submission.EmptyEarSeam
