import Submission.VisibleFillIntersection

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleSeam

/-- Every non-parent point of the visible chord is locally interior to the
union of the two filled children. -/
theorem chord_sdiff_parent_subset_interior
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (visible :
      VisibleDiagonal.Witness hn v htriangle)
    (hq : 3 ≤ visible.q.val)
    (hfront :
      IsSimple
        (latPoly
          (FrontSubpolygon.vertices v visible.q)))
    (hback :
      IsSimple
        (latPoly
          (BackSubpolygon.vertices v visible.q hq)))
    (frontData :
      DiskData.Holds
        (FrontSubpolygon.vertices v visible.q))
    (backData :
      DiskData.Holds
        (BackSubpolygon.vertices v visible.q hq))
    (hfillInter :
      DiskData.region
            (FrontSubpolygon.vertices v visible.q) ∩
          DiskData.region
            (BackSubpolygon.vertices v visible.q hq) =
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v visible.q))) :
    segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v visible.q)) \
        (latPoly v).boundary (R := ℝ) ⊆
      interior
        (DiskData.region
            (FrontSubpolygon.vertices v visible.q) ∪
          DiskData.region
            (BackSubpolygon.vertices v visible.q hq)) := by
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  let qPoint := toPlane (v visible.q)
  let frontVertices :=
    FrontSubpolygon.vertices v visible.q
  let backVertices :=
    BackSubpolygon.vertices v visible.q hq
  let frontPoly := latPoly frontVertices
  let backPoly := latPoly backVertices
  let A := DiskData.region frontVertices
  let B := DiskData.region backVertices
  let D :=
    segment ℝ
      (toPlane
        (v
          (⟨1, by omega⟩ :
            Fin (n + 1))))
      (toPlane (v visible.q))
  let frontLast : Fin visible.q.val :=
    ⟨visible.q.val - 1, by omega⟩
  let backLast :
      Fin (BackSubpolygon.size visible.q) :=
    ⟨BackSubpolygon.size visible.q - 1, by
      have :=
        BackSubpolygon.three_le_size visible.q hq
      omega⟩
  have htipNeQ :
      toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))) ≠
        toPlane (v visible.q) := by
    intro h
    apply visible.q_ne_one
    apply
      Helpers.lattice_vertex_injective_of_isSimple
        hsimple
    exact LatticeTriangle.toPlaneIntLinear_injective h.symm
  intro p hp
  have hpOpen :
      p ∈
        openSegment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v visible.q)) := by
    rw [Diagonal.openSegment_eq_segment_sdiff htipNeQ]
    refine ⟨hp.1, ?_⟩
    intro hpEndpoints
    have hpInter :
        p ∈
          (latPoly v).boundary (R := ℝ) ∩ D := by
      rw [visible.boundary_inter]
      simpa [D] using hpEndpoints
    exact hp.2 hpInter.1
  have hpOpenT :
      p ∈ openSegment ℝ (t.points 1) qPoint := by
    simpa [t, ear, qPoint] using hpOpen
  obtain ⟨ρZero, hρZero, hzero⟩ :=
    VisibleSide.exists_ball_zero_subset_segment
      t qPoint p
        visible.q_coord_zero_pos
        visible.q_coord_two_pos hpOpenT
  have hpFrontOpenEdge :
      p ∈ PolygonLocal.openEdge frontPoly frontLast := by
    change
      p ∈
        openSegment ℝ
          (toPlane (frontVertices frontLast))
          (toPlane
            (frontVertices
              (finRotate visible.q.val frontLast)))
    have hlastIndex :
        FrontSubpolygon.frontIndex
            visible.q frontLast =
          visible.q := by
      simpa [frontLast] using
        FrontSubpolygon.frontIndex_last
          visible.q (by omega)
    have hrotateLast :
        finRotate visible.q.val frontLast =
          (⟨0, by omega⟩ : Fin visible.q.val) := by
      simpa [frontLast] using
        FrontSubpolygon.finRotate_frontLast
          visible.q (by omega)
    rw [hrotateLast]
    change
      p ∈
        openSegment ℝ
          (toPlane
            (v
              (FrontSubpolygon.frontIndex
                visible.q frontLast)))
          (toPlane
            (v
              (FrontSubpolygon.frontIndex
                visible.q
                  (⟨0, by omega⟩ :
                    Fin visible.q.val))))
    rw [hlastIndex,
      FrontSubpolygon.frontIndex_zero
        visible.q (by omega),
      openSegment_symm]
    exact hpOpen
  obtain ⟨ρFront, hρFront, hfrontLocal⟩ :=
    PolygonLocal.exists_ball_boundary_subset_edge
      frontPoly hfront frontLast hpFrontOpenEdge
  have hpBackOpenEdge :
      p ∈ PolygonLocal.openEdge backPoly backLast := by
    change
      p ∈
        openSegment ℝ
          (toPlane (backVertices backLast))
          (toPlane
            (backVertices
              (finRotate
                (BackSubpolygon.size visible.q)
                  backLast)))
    have hrotateLast :
        finRotate
            (BackSubpolygon.size visible.q)
            backLast =
          (⟨0, by
            have :=
              BackSubpolygon.three_le_size
                visible.q hq
            omega⟩ :
            Fin (BackSubpolygon.size visible.q)) := by
      rw [finRotate_apply]
      apply Fin.ext
      simp [Fin.add_def, backLast]
      have hsize :
          BackSubpolygon.size visible.q - 1 + 1 =
            BackSubpolygon.size visible.q := by
        have :=
          BackSubpolygon.three_le_size visible.q hq
        omega
      rw [hsize, Nat.mod_self]
    rw [hrotateLast]
    change
      p ∈
        openSegment ℝ
          (toPlane
            (BackSubpolygon.vertices
              v visible.q hq
                (⟨BackSubpolygon.size visible.q - 1, by
                  have :=
                    BackSubpolygon.three_le_size
                      visible.q hq
                  omega⟩ :
                  Fin (BackSubpolygon.size visible.q))))
          (toPlane
            (BackSubpolygon.vertices
              v visible.q hq
                (⟨0, by
                  have :=
                    BackSubpolygon.three_le_size
                      visible.q hq
                  omega⟩ :
                  Fin (BackSubpolygon.size visible.q))))
    rw [BackSubpolygon.vertices_last,
      BackSubpolygon.vertices_zero]
    exact hpOpen
  obtain ⟨ρBack, hρBack, hbackLocal⟩ :=
    PolygonLocal.exists_ball_boundary_subset_edge
      backPoly hback backLast hpBackOpenEdge
  let ρ := min ρZero (min ρFront ρBack)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hballZero :
      Metric.ball p ρ ⊆ Metric.ball p ρZero := by
    intro z hz
    exact
      lt_of_lt_of_le hz
        (min_le_left ρZero (min ρFront ρBack))
  have hballFront :
      Metric.ball p ρ ⊆ Metric.ball p ρFront := by
    intro z hz
    exact
      lt_of_lt_of_le hz
        ((min_le_right ρZero
          (min ρFront ρBack)).trans
            (min_le_left ρFront ρBack))
  have hballBack :
      Metric.ball p ρ ⊆ Metric.ball p ρBack := by
    intro z hz
    exact
      lt_of_lt_of_le hz
        ((min_le_right ρZero
          (min ρFront ρBack)).trans
            (min_le_right ρFront ρBack))
  have hAclosed : IsClosed A := by
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary frontPoly).isClosed
  have hBclosed : IsClosed B := by
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary backPoly).isClosed
  have hDfrontierA : D ⊆ frontier A := by
    rw [← frontData.boundary_eq_frontier]
    intro z hzD
    rw [Polygon.boundary]
    refine Set.mem_iUnion.mpr ⟨frontLast, ?_⟩
    dsimp [frontPoly, frontVertices, frontLast]
    rwa [FrontSubpolygon.edge_last
      v visible.q (by omega)]
  have hDfrontierB : D ⊆ frontier B := by
    rw [← backData.boundary_eq_frontier]
    intro z hzD
    rw [Polygon.boundary]
    refine Set.mem_iUnion.mpr ⟨backLast, ?_⟩
    dsimp [backPoly, backVertices, backLast]
    rwa [BackSubpolygon.edge_last
      v visible.q hq]
  have hzero' :
      ∀ z ∈ Metric.ball p ρ,
        VisibleSide.sideMap t qPoint z = 0 →
          z ∈ D := by
    intro z hzBall hzSide
    have hz :=
      hzero z (hballZero hzBall) hzSide
    simpa [D, t, ear, qPoint] using hz
  have hfrontierA :
      ∀ z ∈ Metric.ball p ρ,
        z ∈ frontier A →
          VisibleSide.sideMap t qPoint z = 0 := by
    intro z hzBall hzFrontier
    have hzBoundary :
        z ∈ frontPoly.boundary (R := ℝ) := by
      rw [frontData.boundary_eq_frontier]
      exact hzFrontier
    have hzEdge :=
      hfrontLocal z (hballFront hzBall)
        hzBoundary
    have hzD : z ∈ D := by
      dsimp [frontPoly, frontVertices, frontLast] at hzEdge
      rw [FrontSubpolygon.edge_last
        v visible.q (by omega)] at hzEdge
      exact hzEdge
    apply
      VisibleSide.sideMap_eq_zero_on_segment_one
        t qPoint
    simpa [D, t, ear, qPoint] using hzD
  have hfrontierB :
      ∀ z ∈ Metric.ball p ρ,
        z ∈ frontier B →
          VisibleSide.sideMap t qPoint z = 0 := by
    intro z hzBall hzFrontier
    have hzBoundary :
        z ∈ backPoly.boundary (R := ℝ) := by
      rw [backData.boundary_eq_frontier]
      exact hzFrontier
    have hzEdge :=
      hbackLocal z (hballBack hzBall)
        hzBoundary
    have hzD : z ∈ D := by
      dsimp [backPoly, backVertices, backLast] at hzEdge
      rw [BackSubpolygon.edge_last
        v visible.q hq] at hzEdge
      exact hzEdge
    apply
      VisibleSide.sideMap_eq_zero_on_segment_one
        t qPoint
    simpa [D, t, ear, qPoint] using hzD
  apply
    DiskGluing.mem_interior_union_of_local_zero
      (VisibleSide.sideMap t qPoint)
      hρ hAclosed hBclosed
      frontData.regular backData.regular
      (by simpa [A, B, D, frontVertices,
        backVertices] using hfillInter)
      hDfrontierA hDfrontierB
      (by simpa [D] using hp.1)
      hzero' hfrontierA hfrontierB

end Submission.VisibleSeam
