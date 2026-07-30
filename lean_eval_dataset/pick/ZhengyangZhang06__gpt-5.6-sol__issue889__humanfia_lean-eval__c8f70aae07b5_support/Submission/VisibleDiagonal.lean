import Submission.MinimalTriangleVertex

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleDiagonal

/-- A reduced edge cannot run from a positive-coordinate point outside the
candidate triangle to a point in its interior.  Such a segment crosses an
incident triangle side, while checked child-boundary incidence says every
triangle/reduced-boundary intersection lies on the zero-coordinate base. -/
theorem outside_positive_endpoint_cannot_reach_interior
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (i r : Fin n)
    {x : ℝ × ℝ}
    (hxInterior :
      x ∈
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).interior)
    (hxEdge :
      x ∈
        (latPoly (EarRemoval.removeSecond v)).edgeSet
          ℝ i)
    (hrEndpoint :
      toPlane (v (EarRemoval.reducedIndex r)) ∈
        (latPoly (EarRemoval.removeSecond v)).edgeSet
          ℝ i)
    (hrOutside :
      toPlane (v (EarRemoval.reducedIndex r)) ∉
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).closedInterior)
    (hrpos :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 1
          (toPlane (v (EarRemoval.reducedIndex r)))) :
    False := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let t := LatticeTriangle.triangle ear htriangle
  let b := Submission.Triangle.affineBasis t
  have htPolygon :
      t.toPolygon = latPoly ear := by
    rfl
  obtain ⟨z, hzToX, hzpos, hzFace⟩ :=
    TriangleCoords.exists_mem_incidentFace_on_segment
      t hrOutside
        (by simpa [t, ear, b] using hrpos)
        (by simpa [t, ear] using hxInterior)
  have hxSegment :
      x ∈
        segment ℝ
          (toPlane
            (v (EarRemoval.reducedIndex i)))
          (toPlane
            (v
              (EarRemoval.reducedIndex
                (finRotate n i)))) := by
    simpa only [reduced, EarRemoval.removeSecond,
      Polygon.edgeSet, latPoly,
      affineSegment_eq_segment] using hxEdge
  have hrSegment :
      toPlane (v (EarRemoval.reducedIndex r)) ∈
        segment ℝ
          (toPlane
            (v (EarRemoval.reducedIndex i)))
          (toPlane
            (v
              (EarRemoval.reducedIndex
                (finRotate n i)))) := by
    simpa only [reduced, EarRemoval.removeSecond,
      Polygon.edgeSet, latPoly,
      affineSegment_eq_segment] using hrEndpoint
  have hzSegment :
      z ∈
        segment ℝ
          (toPlane
            (v (EarRemoval.reducedIndex i)))
          (toPlane
            (v
              (EarRemoval.reducedIndex
                (finRotate n i)))) :=
    (convex_segment _ _).segment_subset
      hrSegment hxSegment hzToX
  have hzReduced :
      z ∈
        (latPoly reduced).boundary (R := ℝ) := by
    rw [Polygon.boundary]
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simpa only [reduced, EarRemoval.removeSecond,
      Polygon.edgeSet, latPoly,
      affineSegment_eq_segment] using hzSegment
  have hzTriangle :
      z ∈ (latPoly ear).boundary (R := ℝ) := by
    rw [← htPolygon]
    rcases hzFace with hzZero | hzTwo
    · exact EmptyCap.faceOpposite_subset_boundary t 0 hzZero
    · exact EmptyCap.faceOpposite_subset_boundary t 2 hzTwo
  have hzDiagonal :
      z ∈ CleanEar.diagonal hn v := by
    have hzBoth :
        z ∈
          (latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ) ∩
            (latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ) := by
      simpa [ear, reduced] using
        And.intro hzTriangle hzReduced
    rw [CleanEar.childBoundaryInter_of_isSimple
      hn v hsimple] at hzBoth
    exact hzBoth
  have hzFaceOne :
      z ∈ (t.faceOpposite 1).closedInterior := by
    rw [Submission.Triangle.closedInterior_faceOpposite_one,
      affineSegment_eq_segment]
    simpa [CleanEar.diagonal, t, ear] using
      hzDiagonal
  have hzClosed :
      z ∈ t.closedInterior :=
    t.closedInterior_faceOpposite_subset_closedInterior
      1 hzFaceOne
  have hzzero :
      b.coord 1 z = 0 := by
    simpa [b] using
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hzClosed 1).mpr hzFaceOne
  exact
    (ne_of_gt (by simpa [t, ear, b] using hzpos))
      hzzero

/-- If `q` has minimum depth among all non-tip vertices of the candidate
triangle, every reduced-boundary point lying in the triangle interior has
depth at least that of `q`. -/
theorem minimal_depth_le_of_mem_reducedBoundary
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (q : Fin (n + 1))
    (hqclosed :
      toPlane (v q) ∈
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).closedInterior)
    (hminimal :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          toPlane (v j) ∈
              (LatticeTriangle.triangle
                (EarRemoval.earTriangle hn v)
                  htriangle).closedInterior →
            TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v q)) ≤
              TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v j)))
    {x : ℝ × ℝ}
    (hxInterior :
      x ∈
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).interior)
    (hxReduced :
      x ∈
        (latPoly
          (EarRemoval.removeSecond v)).boundary
            (R := ℝ)) :
    TriangleCoords.depth
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle)
        (toPlane (v q)) ≤
      TriangleCoords.depth
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle) x := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let t := LatticeTriangle.triangle ear htriangle
  let b := Submission.Triangle.affineBasis t
  have hqcoordNonneg :
      0 ≤ b.coord 1 (toPlane (v q)) := by
    simpa [t, ear, b] using
      (TriangleCoords.mem_closedInterior_iff_coord_nonneg
        t (toPlane (v q))).mp
        (by simpa [t, ear] using hqclosed) 1
  rw [Polygon.boundary] at hxReduced
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxReduced
  have hxSegment :
      x ∈
        segment ℝ
          (toPlane (v (EarRemoval.reducedIndex i)))
          (toPlane
            (v
              (EarRemoval.reducedIndex
                (finRotate n i)))) := by
    simpa only [reduced, EarRemoval.removeSecond,
      Polygon.edgeSet, latPoly,
      affineSegment_eq_segment] using hxi
  have endpointCoordLe
      (r : Fin n)
      (hrEndpoint :
        toPlane (v (EarRemoval.reducedIndex r)) ∈
          (latPoly reduced).edgeSet ℝ i) :
      b.coord 1
          (toPlane (v (EarRemoval.reducedIndex r))) ≤
        b.coord 1 (toPlane (v q)) := by
    by_cases hrclosed :
        toPlane (v (EarRemoval.reducedIndex r)) ∈
          t.closedInterior
    · have hrne :
          EarRemoval.reducedIndex r ≠
            (⟨1, by omega⟩ : Fin (n + 1)) :=
        EarRemoval.reducedIndex_ne_one (by omega) r
      have hdepth :=
        hminimal (EarRemoval.reducedIndex r)
          hrne
          (by simpa [t, ear] using hrclosed)
      change
        1 - b.coord 1 (toPlane (v q)) ≤
          1 -
            b.coord 1
              (toPlane (v (EarRemoval.reducedIndex r)))
        at hdepth
      linarith
    · by_cases hrpos :
        0 <
          b.coord 1
            (toPlane (v (EarRemoval.reducedIndex r)))
      · exact False.elim <|
          outside_positive_endpoint_cannot_reach_interior
            hn v hsimple htriangle i r
              hxInterior
              (by simpa [reduced] using hxi)
              hrEndpoint
              (by simpa [t, ear] using hrclosed)
              (by simpa [t, ear, b] using hrpos)
      · exact
          (le_of_not_gt hrpos).trans hqcoordNonneg
  have hleft :
      b.coord 1
          (toPlane (v (EarRemoval.reducedIndex i))) ≤
        b.coord 1 (toPlane (v q)) :=
    endpointCoordLe i <| by
      change
        toPlane (v (EarRemoval.reducedIndex i)) ∈
          affineSegment ℝ
            (toPlane (v (EarRemoval.reducedIndex i)))
            (toPlane
              (v
                (EarRemoval.reducedIndex
                  (finRotate n i))))
      exact left_mem_affineSegment ℝ _ _
  have hright :
      b.coord 1
          (toPlane
            (v
              (EarRemoval.reducedIndex
                (finRotate n i)))) ≤
        b.coord 1 (toPlane (v q)) :=
    endpointCoordLe (finRotate n i) <| by
      change
        toPlane
            (v
              (EarRemoval.reducedIndex
                (finRotate n i))) ∈
          affineSegment ℝ
            (toPlane (v (EarRemoval.reducedIndex i)))
            (toPlane
              (v
                (EarRemoval.reducedIndex
                  (finRotate n i))))
      exact right_mem_affineSegment ℝ _ _
  have hhalf :
      Convex ℝ
        (b.coord 1 ⁻¹'
          Set.Iic (b.coord 1 (toPlane (v q)))) :=
    Convex.affine_preimage
      (b.coord 1)
      (convex_Iic (b.coord 1 (toPlane (v q))))
  have hxcoord :
      b.coord 1 x ≤ b.coord 1 (toPlane (v q)) :=
    hhalf.segment_subset hleft hright hxSegment
  dsimp [TriangleCoords.depth]
  simpa [t, ear, b] using
    (show
      1 - b.coord 1 (toPlane (v q)) ≤
        1 - b.coord 1 x by linarith)

/-- The open radial segment from the tip to a minimum-depth non-neighbor
vertex is disjoint from the reduced boundary. -/
theorem openSegment_tip_disjoint_reducedBoundary
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (q : Fin (n + 1))
    (hqclosed :
      toPlane (v q) ∈
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).closedInterior)
    (hqzero :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 0 (toPlane (v q)))
    (hqtwo :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 2 (toPlane (v q)))
    (hminimal :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          toPlane (v j) ∈
              (LatticeTriangle.triangle
                (EarRemoval.earTriangle hn v)
                  htriangle).closedInterior →
            TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v q)) ≤
              TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v j))) :
    Disjoint
      (openSegment ℝ
        ((LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).points 1)
        (toPlane (v q)))
      ((latPoly
        (EarRemoval.removeSecond v)).boundary
          (R := ℝ)) := by
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  let b := Submission.Triangle.affineBasis t
  have hradialInterior :
      openSegment ℝ (t.points 1) (toPlane (v q)) ⊆
        t.interior :=
    TriangleCoords.openSegment_pointOne_subset_interior
      t
      (by simpa [t, ear] using hqclosed)
      (by simpa [t, ear, b] using hqzero)
      (by simpa [t, ear, b] using hqtwo)
  have hqne :
      toPlane (v q) ≠ t.points 1 := by
    intro h
    have hqzero' :
        0 < b.coord 0 (toPlane (v q)) := by
      simpa [t, ear, b] using hqzero
    rw [h] at hqzero'
    have htipZero :
        b.coord 0 (t.points 1) = 0 := by
      simp [b]
    exact (ne_of_gt hqzero') htipZero
  have hqdepthPos :
      0 <
        TriangleCoords.depth t (toPlane (v q)) :=
    TriangleCoords.depth_pos_of_mem_closedInterior_of_ne
      t (by simpa [t, ear] using hqclosed) hqne
  rw [Set.disjoint_left]
  intro x hxOpen hxReduced
  have hxInterior :
      x ∈ t.interior :=
    hradialInterior hxOpen
  have hdepthLower :
      TriangleCoords.depth t (toPlane (v q)) ≤
        TriangleCoords.depth t x := by
    simpa [t, ear] using
      minimal_depth_le_of_mem_reducedBoundary
        hn v hsimple htriangle q hqclosed hminimal
          (by simpa [t, ear] using hxInterior)
          hxReduced
  rw [openSegment_eq_image_lineMap] at hxOpen
  obtain ⟨r, hr, rfl⟩ := hxOpen
  rw [TriangleCoords.depth_lineMap] at hdepthLower
  have hstrict :
      r * TriangleCoords.depth t (toPlane (v q)) <
        TriangleCoords.depth t (toPlane (v q)) := by
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right hr.2 hqdepthPos
  exact (not_lt_of_ge hdepthLower) hstrict

/-- The same visible radial segment is disjoint from the original polygon
boundary.  The child-boundary union sends any hypothetical intersection to
the triangle boundary or the reduced boundary; radial interiority excludes
the first and the preceding theorem excludes the second. -/
theorem openSegment_tip_disjoint_parentBoundary
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (q : Fin (n + 1))
    (hqclosed :
      toPlane (v q) ∈
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).closedInterior)
    (hqzero :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 0 (toPlane (v q)))
    (hqtwo :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 2 (toPlane (v q)))
    (hminimal :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          toPlane (v j) ∈
              (LatticeTriangle.triangle
                (EarRemoval.earTriangle hn v)
                  htriangle).closedInterior →
            TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v q)) ≤
              TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v j))) :
    Disjoint
      (openSegment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v q)))
      ((latPoly v).boundary (R := ℝ)) := by
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  have htPolygon :
      t.toPolygon = latPoly ear := by
    rfl
  have hradialInterior :
      openSegment ℝ (t.points 1) (toPlane (v q)) ⊆
        t.interior :=
    TriangleCoords.openSegment_pointOne_subset_interior
      t
      (by simpa [t, ear] using hqclosed)
      (by simpa [t, ear] using hqzero)
      (by simpa [t, ear] using hqtwo)
  have hreducedDisjoint :
      Disjoint
        (openSegment ℝ (t.points 1) (toPlane (v q)))
        ((latPoly
          (EarRemoval.removeSecond v)).boundary
            (R := ℝ)) :=
    openSegment_tip_disjoint_reducedBoundary
      hn v hsimple htriangle q hqclosed
        hqzero hqtwo hminimal
  rw [Set.disjoint_left]
  intro x hxOpen hxParent
  have hxOpen' :
      x ∈ openSegment ℝ (t.points 1) (toPlane (v q)) := by
    simpa [t, ear] using hxOpen
  have hxInterior : x ∈ t.interior :=
    hradialInterior hxOpen'
  have hxChildren :
      x ∈
        (latPoly ear).boundary (R := ℝ) ∪
          (latPoly
            (EarRemoval.removeSecond v)).boundary
              (R := ℝ) := by
    rw [EarRemoval.child_boundaries_union hn v]
    exact Or.inl hxParent
  rcases hxChildren with hxTriangle | hxReduced
  · have hxSurface :
        x ∈ t.closedInterior \ t.interior := by
      rw [← Submission.Triangle.toPolygon_boundary_eq_surface,
        htPolygon]
      exact hxTriangle
    exact hxSurface.2 hxInterior
  · exact
      Set.disjoint_left.mp hreducedDisjoint
        hxOpen' hxReduced

/-- Consequently the visible segment meets the old boundary exactly at its
two endpoint vertices. -/
theorem parentBoundary_inter_visibleSegment
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (q : Fin (n + 1))
    (hqclosed :
      toPlane (v q) ∈
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle).closedInterior)
    (hqzero :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 0 (toPlane (v q)))
    (hqtwo :
      0 <
        (Submission.Triangle.affineBasis
          (LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v)
              htriangle)).coord 2 (toPlane (v q)))
    (hminimal :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          toPlane (v j) ∈
              (LatticeTriangle.triangle
                (EarRemoval.earTriangle hn v)
                  htriangle).closedInterior →
            TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v q)) ≤
              TriangleCoords.depth
                (LatticeTriangle.triangle
                  (EarRemoval.earTriangle hn v)
                    htriangle)
                (toPlane (v j)))
    (hqone :
      q ≠ (⟨1, by omega⟩ : Fin (n + 1))) :
    (latPoly v).boundary (R := ℝ) ∩
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v q)) =
      {toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))),
        toPlane (v q)} := by
  let p :=
    toPlane
      (v
        (⟨1, by omega⟩ :
          Fin (n + 1)))
  let z := toPlane (v q)
  have hpz : p ≠ z := by
    intro h
    apply hqone
    apply
      Helpers.vertex_injective_of_isSimple hsimple
    change
      toPlane (v q) =
        toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1)))
    exact h.symm
  have hopen :
      Disjoint (openSegment ℝ p z)
        ((latPoly v).boundary (R := ℝ)) := by
    simpa [p, z] using
      openSegment_tip_disjoint_parentBoundary
        hn v hsimple htriangle q hqclosed
          hqzero hqtwo hminimal
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxEndpoints : x ∈ ({p, z} : Set (ℝ × ℝ))
    · simpa [p, z] using hxEndpoints
    · have hxOpen : x ∈ openSegment ℝ p z := by
        rw [Diagonal.openSegment_eq_segment_sdiff hpz]
        exact ⟨hx.2, hxEndpoints⟩
      exact False.elim <|
        Set.disjoint_left.mp hopen hxOpen hx.1
  · intro x hx
    have hpBoundary :
        p ∈ (latPoly v).boundary (R := ℝ) := by
      change
        toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))) ∈
          (latPoly v).boundary (R := ℝ)
      exact
        (Helpers.boundaryVertex v
          (⟨1, by omega⟩ :
            Fin (n + 1))).property
    have hzBoundary :
        z ∈ (latPoly v).boundary (R := ℝ) := by
      change
        toPlane (v q) ∈
          (latPoly v).boundary (R := ℝ)
      exact (Helpers.boundaryVertex v q).property
    rcases hx with rfl | rfl
    · exact ⟨hpBoundary, left_mem_segment ℝ _ _⟩
    · exact ⟨hzBoundary, right_mem_segment ℝ _ _⟩

/-- Data carried by the clean diagonal found inside a nonempty exposed
candidate triangle. -/
structure Witness
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v))) : Type where
  q : Fin (n + 1)
  q_ne_zero : q ≠ 0
  q_ne_one :
    q ≠ (⟨1, by omega⟩ : Fin (n + 1))
  q_ne_two :
    q ≠ (⟨2, by omega⟩ : Fin (n + 1))
  q_mem_closedInterior :
    toPlane (v q) ∈
      (LatticeTriangle.triangle
        (EarRemoval.earTriangle hn v)
          htriangle).closedInterior
  q_coord_zero_pos :
    0 <
      (Submission.Triangle.affineBasis
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle)).coord 0 (toPlane (v q))
  q_coord_two_pos :
    0 <
      (Submission.Triangle.affineBasis
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle)).coord 2 (toPlane (v q))
  minimal :
    ∀ j : Fin (n + 1),
      j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
        toPlane (v j) ∈
            (LatticeTriangle.triangle
              (EarRemoval.earTriangle hn v)
                htriangle).closedInterior →
          TriangleCoords.depth
              (LatticeTriangle.triangle
                (EarRemoval.earTriangle hn v)
                  htriangle)
              (toPlane (v q)) ≤
            TriangleCoords.depth
              (LatticeTriangle.triangle
                (EarRemoval.earTriangle hn v)
                  htriangle)
              (toPlane (v j))
  boundary_inter :
    (latPoly v).boundary (R := ℝ) ∩
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v q)) =
      {toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))),
        toPlane (v q)}

/-- An exposed candidate triangle is either vertex-empty or contains a
minimum-depth non-neighbor joined to the tip by a clean diagonal. -/
theorem vertexEmpty_or_visibleDiagonal
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v))) :
    EmptyCap.VertexEmptyAtOne hn v htriangle ∨
      Nonempty (Witness hn v htriangle) := by
  classical
  by_cases hempty :
      EmptyCap.VertexEmptyAtOne hn v htriangle
  · exact Or.inl hempty
  · right
    have hexists :
        let t :=
          LatticeTriangle.triangle
            (EarRemoval.earTriangle hn v) htriangle
        ∃ j : Fin (n + 1),
          j ≠ 0 ∧
            j ≠ (⟨1, by omega⟩ : Fin (n + 1)) ∧
            j ≠ (⟨2, by omega⟩ : Fin (n + 1)) ∧
            toPlane (v j) ∈ t.closedInterior := by
      simp only [EmptyCap.VertexEmptyAtOne, not_forall,
        not_or] at hempty
      rcases hempty with
        ⟨j, hjone, hjclosed, hjzero, hjtwo⟩
      exact ⟨j, hjzero, hjone, hjtwo, hjclosed⟩
    obtain
      ⟨q, hqzero, hqone, hqtwo, hqclosed,
        hqcoordZero, hqcoordTwo, hminimal⟩ :=
      MinimalTriangleVertex.exists_minimal_nonbase_vertex
        hn v hsimple htriangle hexists
    have hinter :=
      parentBoundary_inter_visibleSegment
        hn v hsimple htriangle q hqclosed
          hqcoordZero hqcoordTwo hminimal hqone
    exact
      ⟨⟨q, hqzero, hqone, hqtwo, hqclosed,
        hqcoordZero, hqcoordTwo, hminimal,
        hinter⟩⟩

end Submission.VisibleDiagonal
