import Submission.EmptyCap

open LeanEval.Geometry.PicksTheorem

namespace Submission.MinimalTriangleVertex

/-- If the candidate triangle contains a polygon vertex other than its own
three vertices, one can choose such a vertex of minimum barycentric depth.
Original simplicity keeps the chosen point off both sides incident to the
tip, so its two side coordinates are strictly positive. -/
theorem exists_minimal_nonbase_vertex
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (hexists :
      let t :=
        LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v) htriangle
      ∃ j : Fin (n + 1),
        j ≠ 0 ∧
          j ≠ (⟨1, by omega⟩ : Fin (n + 1)) ∧
          j ≠ (⟨2, by omega⟩ : Fin (n + 1)) ∧
          toPlane (v j) ∈ t.closedInterior) :
    let t :=
      LatticeTriangle.triangle
        (EarRemoval.earTriangle hn v) htriangle
    ∃ q : Fin (n + 1),
      q ≠ 0 ∧
        q ≠ (⟨1, by omega⟩ : Fin (n + 1)) ∧
        q ≠ (⟨2, by omega⟩ : Fin (n + 1)) ∧
        toPlane (v q) ∈ t.closedInterior ∧
        0 <
          (Submission.Triangle.affineBasis t).coord
            0 (toPlane (v q)) ∧
        0 <
          (Submission.Triangle.affineBasis t).coord
            2 (toPlane (v q)) ∧
        ∀ j : Fin (n + 1),
          j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
            toPlane (v j) ∈ t.closedInterior →
              TriangleCoords.depth t (toPlane (v q)) ≤
                TriangleCoords.depth t (toPlane (v j)) := by
  classical
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  let eligible : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun j =>
      j ≠ 0 ∧
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) ∧
        j ≠ (⟨2, by omega⟩ : Fin (n + 1)) ∧
        toPlane (v j) ∈ t.closedInterior
  have heligible : eligible.Nonempty := by
    rcases hexists with
      ⟨j, hjzero, hjone, hjtwo, hjclosed⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨hjzero, hjone, hjtwo, hjclosed⟩
  obtain ⟨q, hqEligible, hqMinimal⟩ :=
    Finset.exists_min_image eligible
      (fun j : Fin (n + 1) =>
        TriangleCoords.depth t (toPlane (v j)))
      heligible
  have hqData :
      q ≠ 0 ∧
        q ≠ (⟨1, by omega⟩ : Fin (n + 1)) ∧
        q ≠ (⟨2, by omega⟩ : Fin (n + 1)) ∧
        toPlane (v q) ∈ t.closedInterior :=
    (Finset.mem_filter.mp hqEligible).2
  rcases hqData with
    ⟨hqzero, hqone, hqtwo, hqclosed⟩
  have hqcoordNonneg :
      ∀ i : Fin 3,
        0 ≤
          (Submission.Triangle.affineBasis t).coord
            i (toPlane (v q)) :=
    (TriangleCoords.mem_closedInterior_iff_coord_nonneg
      t (toPlane (v q))).mp hqclosed
  have hqcoordZeroNe :
      (Submission.Triangle.affineBasis t).coord
          0 (toPlane (v q)) ≠
        0 := by
    intro hzero
    have hface :
        toPlane (v q) ∈
          (t.faceOpposite 0).closedInterior :=
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hqclosed 0).mp hzero
    have hparentEdge :
        toPlane (v q) ∈
          (latPoly v).edgeSet ℝ
            (⟨1, by omega⟩ : Fin (n + 1)) := by
      rw [← EarRemoval.ear_edge_one hn v]
      rw [Submission.Triangle.closedInterior_faceOpposite_zero]
        at hface
      simpa [Polygon.edgeSet, t, ear, latPoly] using hface
    have hcases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple q
          (⟨1, by omega⟩ : Fin (n + 1))).mp
        hparentEdge
    rcases hcases with hq | hq
    · exact hqone hq
    · rw [CleanEar.finRotate_one hn] at hq
      exact hqtwo hq
  have hqcoordTwoNe :
      (Submission.Triangle.affineBasis t).coord
          2 (toPlane (v q)) ≠
        0 := by
    intro htwo
    have hface :
        toPlane (v q) ∈
          (t.faceOpposite 2).closedInterior :=
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hqclosed 2).mp htwo
    have hparentEdge :
        toPlane (v q) ∈
          (latPoly v).edgeSet ℝ
            (0 : Fin (n + 1)) := by
      rw [← EarRemoval.ear_edge_zero hn v]
      rw [Submission.Triangle.closedInterior_faceOpposite_two]
        at hface
      simpa [Polygon.edgeSet, t, ear, latPoly] using hface
    have hcases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple q
          (0 : Fin (n + 1))).mp
        hparentEdge
    rcases hcases with hq | hq
    · exact hqzero hq
    · rw [CleanEar.finRotate_zero hn] at hq
      exact hqone hq
  have hqcoordZeroPos :
      0 <
        (Submission.Triangle.affineBasis t).coord
          0 (toPlane (v q)) :=
    lt_of_le_of_ne (hqcoordNonneg 0)
      hqcoordZeroNe.symm
  have hqcoordTwoPos :
      0 <
        (Submission.Triangle.affineBasis t).coord
          2 (toPlane (v q)) :=
    lt_of_le_of_ne (hqcoordNonneg 2)
      hqcoordTwoNe.symm
  have hqDepthLeOne :
      TriangleCoords.depth t (toPlane (v q)) ≤ 1 := by
    dsimp [TriangleCoords.depth]
    linarith [hqcoordNonneg 1]
  have hdepthZero :
      TriangleCoords.depth t (toPlane (v 0)) = 1 := by
    have hpoint :
        t.points 0 = toPlane (v 0) := by
      calc
        t.points 0 = toPlane (ear 0) :=
          LatticeTriangle.triangle_points ear htriangle
            (0 : Fin 3)
        _ = toPlane (v 0) :=
          congrArg toPlane
            (EarRemoval.earTriangle_zero hn v)
    rw [← hpoint]
    exact TriangleCoords.depth_point_zero t
  have hdepthTwo :
      TriangleCoords.depth t
          (toPlane (v ⟨2, by omega⟩)) =
        1 := by
    have hpoint :
        t.points 2 =
          toPlane (v ⟨2, by omega⟩) := by
      calc
        t.points 2 = toPlane (ear 2) :=
          LatticeTriangle.triangle_points ear htriangle
            (2 : Fin 3)
        _ = toPlane (v ⟨2, by omega⟩) :=
          congrArg toPlane
            (EarRemoval.earTriangle_two hn v)
    rw [← hpoint]
    exact TriangleCoords.depth_point_two t
  have hminimal :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          toPlane (v j) ∈ t.closedInterior →
            TriangleCoords.depth t (toPlane (v q)) ≤
              TriangleCoords.depth t (toPlane (v j)) := by
    intro j hjone hjclosed
    by_cases hjzero : j = 0
    · subst j
      rw [hdepthZero]
      exact hqDepthLeOne
    by_cases hjtwo :
        j = (⟨2, by omega⟩ : Fin (n + 1))
    · subst j
      rw [hdepthTwo]
      exact hqDepthLeOne
    exact
      hqMinimal j <|
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,
            hjzero, hjone, hjtwo, hjclosed⟩
  exact
    ⟨q, hqzero, hqone, hqtwo, hqclosed,
      hqcoordZeroPos, hqcoordTwoPos, hminimal⟩

end Submission.MinimalTriangleVertex
