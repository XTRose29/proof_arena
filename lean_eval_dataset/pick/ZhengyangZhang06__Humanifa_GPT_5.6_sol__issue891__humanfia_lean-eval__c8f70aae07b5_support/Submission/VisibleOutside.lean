import Submission.VisibleLocal

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleOutside

/-- A short point of the original `1`--`2` edge belongs to the front child
but lies outside the filled complementary child. -/
theorem exists_front_point_outside_back
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
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
    (visible :
      VisibleDiagonal.Witness hn v htriangle)
    (hq : 3 ≤ visible.q.val)
    (hback :
      IsSimple
        (latPoly
          (BackSubpolygon.vertices v visible.q hq))) :
    ∃ x,
      x ∈
          (latPoly
            (FrontSubpolygon.vertices
              v visible.q)).boundary
                (R := ℝ) \
            segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v visible.q)) ∧
        x ∉
          FilledRegion.fill
            ((latPoly
              (BackSubpolygon.vertices
                v visible.q hq)).boundary
                  (R := ℝ)) := by
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  let qPoint := toPlane (v visible.q)
  let back :=
    latPoly
      (BackSubpolygon.vertices v visible.q hq)
  let last : Fin (BackSubpolygon.size visible.q) :=
    ⟨BackSubpolygon.size visible.q - 1, by
      have :=
        BackSubpolygon.three_le_size
          visible.q hq
      omega⟩
  letI : NeZero (BackSubpolygon.size visible.q) :=
    ⟨by
      have :=
        BackSubpolygon.three_le_size visible.q hq
      omega⟩
  obtain ⟨ρ, hρ, hlocal⟩ :=
    PolygonLocal.exists_ball_boundary_subset_incident
      back hback last
  have hlastPoint :
      back last = t.points 1 := by
    dsimp [back, last, t, ear]
    change
      toPlane
          (BackSubpolygon.vertices v visible.q hq
            (⟨BackSubpolygon.size visible.q - 1, by
              have :=
                BackSubpolygon.three_le_size
                  visible.q hq
              omega⟩ :
              Fin (BackSubpolygon.size visible.q))) =
        toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1)))
    rw [BackSubpolygon.vertices_last]
  have hlocal' :
      ∀ z ∈ Metric.ball (t.points 1) ρ,
        z ∈ back.boundary (R := ℝ) →
          z ∈ back.edgeSet ℝ last ∪
            back.edgeSet ℝ
              ((finRotate
                (BackSubpolygon.size visible.q)).symm
                  last) := by
    intro z hzBall hzBoundary
    apply hlocal z
    · rw [hlastPoint]
      exact hzBall
    · exact hzBoundary
  have hboundarySide :
      ∀ z ∈ Metric.ball (t.points 1) ρ,
        z ∈ back.boundary (R := ℝ) →
          0 ≤ VisibleSide.sideMap t qPoint z := by
    intro z hzBall hzBoundary
    rcases hlocal' z hzBall hzBoundary with
      hzLast | hzPrevious
    · have hzChord :
          z ∈ segment ℝ (t.points 1) qPoint := by
        dsimp [back, last] at hzLast
        rw [BackSubpolygon.edge_last] at hzLast
        simpa [t, ear, qPoint] using hzLast
      exact
        (VisibleSide.sideMap_eq_zero_on_segment_one
          t qPoint hzChord).ge
    · have hprevious :
          (finRotate
              (BackSubpolygon.size visible.q)).symm
                last =
            (⟨BackSubpolygon.size visible.q - 2, by
              have :=
                BackSubpolygon.three_le_size
                  visible.q hq
              omega⟩ :
              Fin (BackSubpolygon.size visible.q)) := by
          simpa [last] using
            BackSubpolygon.previous_last
              visible.q hq
      rw [hprevious] at hzPrevious
      have hzParentEdge :
          z ∈ (latPoly v).edgeSet ℝ 0 := by
        dsimp [back] at hzPrevious
        rwa [BackSubpolygon.edge_predecessor_last
          hn v visible.q hq] at hzPrevious
      have hzSide :
          z ∈ segment ℝ (t.points 0) (t.points 1) := by
        simpa [Polygon.edgeSet, latPoly,
          affineSegment_eq_segment, t, ear,
          CleanEar.finRotate_zero hn] using
            hzParentEdge
      exact
        VisibleSide.sideMap_nonneg_on_segment_zero_one
          t qPoint visible.q_coord_two_pos hzSide
  have hfZero :
      ExtremeVertex.exposingFunctional M (t.points 0) <
        ExtremeVertex.exposingFunctional M (t.points 1) := by
    simpa [t, ear] using
      hvertices (0 : Fin (n + 1))
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_zero] at hval
          omega)
  have hfill :
      FilledRegion.fill (back.boundary (R := ℝ)) ⊆
        {z : ℝ × ℝ |
          ExtremeVertex.exposingFunctional M z ≤
            ExtremeVertex.exposingFunctional M
              (t.points 1)} := by
    simpa [back, t, ear] using
      VisibleSupport.backFill_subset_halfspace
        v (by omega) M hvertices visible.q hq
  obtain ⟨x, hxOpen, hxOutside⟩ :=
    VisibleLocal.exists_one_two_point_not_mem_fill
      t qPoint (back.boundary (R := ℝ))
        (ExtremeVertex.exposingFunctional M)
        visible.q_coord_zero_pos
        visible.q_coord_two_pos
        hfZero hfill hρ hboundarySide
  have hxFrontEdge :
      x ∈
        (latPoly
          (FrontSubpolygon.vertices
            v visible.q)).edgeSet ℝ
              (⟨0, by omega⟩ :
                Fin visible.q.val) := by
    rw [FrontSubpolygon.edge_zero
      v visible.q hq]
    simpa [Polygon.edgeSet, latPoly,
      affineSegment_eq_segment, t, ear,
      CleanEar.finRotate_one hn] using
        openSegment_subset_segment ℝ _ _ hxOpen
  have hxFrontBoundary :
      x ∈
        (latPoly
          (FrontSubpolygon.vertices
            v visible.q)).boundary
              (R := ℝ) := by
    rw [Polygon.boundary]
    exact
      Set.mem_iUnion.mpr
        ⟨(⟨0, by omega⟩ :
          Fin visible.q.val), hxFrontEdge⟩
  have hxNotChord :
      x ∉
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v visible.q)) := by
    intro hxChord
    have hxZero :
        VisibleSide.sideMap t qPoint x = 0 := by
      apply
        VisibleSide.sideMap_eq_zero_on_segment_one
          t qPoint
      simpa [t, ear, qPoint] using hxChord
    have hxNeg :
        VisibleSide.sideMap t qPoint x < 0 :=
      VisibleSide.sideMap_neg_on_openSegment_one_two
        t qPoint visible.q_coord_zero_pos hxOpen
    linarith
  exact
    ⟨x,
      ⟨hxFrontBoundary, hxNotChord⟩,
      by simpa [back] using hxOutside⟩

/-- Symmetrically, a short point of original edge `0` belongs to the
complementary child but lies outside the filled front child. -/
theorem exists_back_point_outside_front
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
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
    (visible :
      VisibleDiagonal.Witness hn v htriangle)
    (hq : 3 ≤ visible.q.val)
    (hfront :
      IsSimple
        (latPoly
          (FrontSubpolygon.vertices v visible.q))) :
    ∃ x,
      x ∈
          (latPoly
            (BackSubpolygon.vertices
              v visible.q hq)).boundary
                (R := ℝ) \
            segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v visible.q)) ∧
        x ∉
          FilledRegion.fill
            ((latPoly
              (FrontSubpolygon.vertices
                v visible.q)).boundary
                  (R := ℝ)) := by
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  let qPoint := toPlane (v visible.q)
  let front :=
    latPoly
      (FrontSubpolygon.vertices v visible.q)
  let zero : Fin visible.q.val :=
    ⟨0, by omega⟩
  let last : Fin visible.q.val :=
    ⟨visible.q.val - 1, by omega⟩
  letI : NeZero visible.q.val :=
    ⟨by omega⟩
  obtain ⟨ρ, hρ, hlocal⟩ :=
    PolygonLocal.exists_ball_boundary_subset_incident
      front hfront zero
  have hzeroPoint :
      front zero = t.points 1 := by
    dsimp [front, zero, t, ear]
    change
      toPlane
          (v
            (FrontSubpolygon.frontIndex visible.q
              (⟨0, by omega⟩ :
                Fin visible.q.val))) =
        toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1)))
    rw [FrontSubpolygon.frontIndex_zero
      visible.q (by omega)]
  have hprevious :
      (finRotate visible.q.val).symm zero =
        last := by
    apply (finRotate visible.q.val).injective
    rw [(finRotate visible.q.val).apply_symm_apply]
    simpa [zero, last] using
      (FrontSubpolygon.finRotate_frontLast
        visible.q (by omega)).symm
  have hboundarySide :
      ∀ z ∈ Metric.ball (t.points 1) ρ,
        z ∈ front.boundary (R := ℝ) →
          VisibleSide.sideMap t qPoint z ≤ 0 := by
    intro z hzBall hzBoundary
    have hzBall' :
        z ∈ Metric.ball (front zero) ρ := by
      rwa [hzeroPoint]
    rcases hlocal z hzBall' hzBoundary with
      hzZero | hzPrevious
    · have hzParentEdge :
          z ∈
            (latPoly v).edgeSet ℝ
              (⟨1, by omega⟩ :
                Fin (n + 1)) := by
        dsimp [front, zero] at hzZero
        have hzeroIndex :
            (0 : Fin visible.q.val) =
              (⟨0, by omega⟩ :
                Fin visible.q.val) := by
          apply Fin.ext
          simp
        rw [hzeroIndex,
          FrontSubpolygon.edge_zero
            v visible.q hq] at hzZero
        exact hzZero
      have hzSide :
          z ∈ segment ℝ (t.points 1) (t.points 2) := by
        simpa [Polygon.edgeSet, latPoly,
          affineSegment_eq_segment, t, ear,
          CleanEar.finRotate_one hn] using
            hzParentEdge
      exact
        VisibleSide.sideMap_nonpos_on_segment_one_two
          t qPoint visible.q_coord_zero_pos hzSide
    · rw [hprevious] at hzPrevious
      have hzChord :
          z ∈ segment ℝ (t.points 1) qPoint := by
        dsimp [front, last] at hzPrevious
        rw [FrontSubpolygon.edge_last
          v visible.q (by omega)] at hzPrevious
        simpa [t, ear, qPoint] using hzPrevious
      exact
        (VisibleSide.sideMap_eq_zero_on_segment_one
          t qPoint hzChord).le
  have hfTwo :
      ExtremeVertex.exposingFunctional M (t.points 2) <
        ExtremeVertex.exposingFunctional M (t.points 1) := by
    simpa [t, ear] using
      hvertices
        (⟨2, by omega⟩ :
          Fin (n + 1))
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only at hval
          omega)
  have hfill :
      FilledRegion.fill (front.boundary (R := ℝ)) ⊆
        {z : ℝ × ℝ |
          ExtremeVertex.exposingFunctional M z ≤
            ExtremeVertex.exposingFunctional M
              (t.points 1)} := by
    simpa [front, t, ear] using
      VisibleSupport.frontFill_subset_halfspace
        v (by omega) M hvertices visible.q
  obtain ⟨x, hxOpen, hxOutside⟩ :=
    VisibleLocal.exists_zero_one_point_not_mem_fill
      t qPoint (front.boundary (R := ℝ))
        (ExtremeVertex.exposingFunctional M)
        visible.q_coord_zero_pos
        visible.q_coord_two_pos
        hfTwo hfill hρ hboundarySide
  have hxBackEdge :
      x ∈
        (latPoly
          (BackSubpolygon.vertices
            v visible.q hq)).edgeSet ℝ
              (⟨BackSubpolygon.size visible.q - 2, by
                have :=
                  BackSubpolygon.three_le_size
                    visible.q hq
                omega⟩ :
                Fin
                  (BackSubpolygon.size
                    visible.q)) := by
    rw [BackSubpolygon.edge_predecessor_last
      hn v visible.q hq]
    simpa [Polygon.edgeSet, latPoly,
      affineSegment_eq_segment, t, ear,
      CleanEar.finRotate_zero hn] using
        openSegment_subset_segment ℝ _ _ hxOpen
  have hxBackBoundary :
      x ∈
        (latPoly
          (BackSubpolygon.vertices
            v visible.q hq)).boundary
              (R := ℝ) := by
    rw [Polygon.boundary]
    exact
      Set.mem_iUnion.mpr
        ⟨_, hxBackEdge⟩
  have hxNotChord :
      x ∉
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v visible.q)) := by
    intro hxChord
    have hxZero :
        VisibleSide.sideMap t qPoint x = 0 := by
      apply
        VisibleSide.sideMap_eq_zero_on_segment_one
          t qPoint
      simpa [t, ear, qPoint] using hxChord
    have hxPos :
        0 < VisibleSide.sideMap t qPoint x :=
      VisibleSide.sideMap_pos_on_openSegment_zero_one
        t qPoint visible.q_coord_two_pos hxOpen
    linarith
  exact
    ⟨x,
      ⟨hxBackBoundary, hxNotChord⟩,
      by simpa [front] using hxOutside⟩

end Submission.VisibleOutside
