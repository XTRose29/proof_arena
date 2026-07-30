import Submission.TriangleCap

open LeanEval.Geometry.PicksTheorem
open Filter
open scoped Topology

namespace Submission.EmptyCap

/-- If an affine coordinate is positive at a point of a segment, it is
positive at at least one endpoint. -/
theorem exists_endpoint_coord_pos
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {a c x : ℝ × ℝ}
    (hx : x ∈ segment ℝ a c)
    (hxpos :
      0 <
        (Submission.Triangle.affineBasis t).coord 1 x) :
    0 <
        (Submission.Triangle.affineBasis t).coord 1 a ∨
      0 <
        (Submission.Triangle.affineBasis t).coord 1 c := by
  by_contra h
  simp only [not_or, not_lt] at h
  let b := Submission.Triangle.affineBasis t
  have hhalf :
      Convex ℝ
        (b.coord 1 ⁻¹' Set.Iic (0 : ℝ)) :=
    Convex.affine_preimage
      (b.coord 1) (convex_Iic 0)
  have hxnonpos :
      b.coord 1 x ≤ 0 :=
    hhalf.segment_subset h.1 h.2 hx
  exact
    (not_lt_of_ge hxnonpos)
      (by simpa [b] using hxpos)

/-- Every opposite face of a triangle lies on its polygonal boundary. -/
theorem faceOpposite_subset_boundary
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) :
    (t.faceOpposite i).closedInterior ⊆
      t.toPolygon.boundary (R := ℝ) := by
  intro x hx
  rw [Submission.Triangle.toPolygon_boundary_eq_surface]
  refine
    ⟨t.closedInterior_faceOpposite_subset_closedInterior
        i hx,
      ?_⟩
  intro hxInterior
  exact
    Set.disjoint_left.mp
      (t.disjoint_interior_closedInterior_faceOpposite i)
      hxInterior hx

/-- If a segment passes through the relative interior of the base and one
endpoint has positive tip-coordinate, then the segment enters the triangle
interior. -/
theorem exists_interior_on_segment_of_openBase_of_endpoint_pos
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {a c x : ℝ × ℝ}
    (hxBase :
      x ∈ openSegment ℝ (t.points 0) (t.points 2))
    (hxSegment : x ∈ segment ℝ a c)
    (haPos :
      0 <
        (Submission.Triangle.affineBasis t).coord 1 a) :
    ∃ y : ℝ × ℝ,
      y ∈ t.interior ∧
        y ∈ segment ℝ a c := by
  let b := Submission.Triangle.affineBasis t
  rw [openSegment_eq_image_lineMap] at hxBase
  obtain ⟨r, hr, hx⟩ := hxBase
  have hxZero :
      b.coord 0 x > 0 := by
    rw [← hx]
    simp [b]
    exact hr.2
  have hxTwo :
      b.coord 2 x > 0 := by
    rw [← hx]
    simp [b]
    exact hr.1
  have hxOne :
      b.coord 1 x = 0 := by
    rw [← hx]
    simp [b]
  let U : Set (ℝ × ℝ) :=
    {z |
      0 < b.coord 0 z ∧
        0 < b.coord 2 z}
  have hUOpen : IsOpen U := by
    exact
      (isOpen_Ioi.preimage
          (b.coord 0).continuous_of_finiteDimensional).inter
        (isOpen_Ioi.preimage
          (b.coord 2).continuous_of_finiteDimensional)
  have hxU : x ∈ U :=
    ⟨hxZero, hxTwo⟩
  have hnear :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        AffineMap.lineMap x a δ ∈ U :=
    AffineMap.lineMap_continuous.continuousWithinAt.eventually_mem
      (by simpa using hUOpen.mem_nhds hxU)
  have hsmall :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        AffineMap.lineMap x a δ ∈ U ∧
          δ ∈ Set.Ioo (0 : ℝ) 1 :=
    hnear.and (Ioo_mem_nhdsGT zero_lt_one)
  obtain ⟨δ, hδU, hδ⟩ := hsmall.exists
  let y := AffineMap.lineMap x a δ
  have hyOne :
      0 < b.coord 1 y := by
    have hmul :
        0 < δ * b.coord 1 a :=
      mul_pos hδ.1
        (by simpa [b] using haPos)
    simpa [y, hxOne] using hmul
  have hyInterior : y ∈ t.interior := by
    rw [Submission.Triangle.mem_interior_iff_coord_pos]
    intro i
    fin_cases i
    · exact hδU.1
    · exact hyOne
    · exact hδU.2
  have hySegmentXA :
      y ∈ segment ℝ x a := by
    exact
      lineMap_mem_segment ℝ x a
        ⟨hδ.1.le, hδ.2.le⟩
  have hySegment :
      y ∈ segment ℝ a c := by
    exact
      (convex_segment a c).segment_subset
        hxSegment (left_mem_segment ℝ a c)
        hySegmentXA
  exact ⟨y, hyInterior, hySegment⟩

/-- If a segment through the relative interior of the base avoids the
triangle interior, both endpoint tip-coordinates are nonpositive. -/
theorem endpoint_coords_nonpos_of_openBase_of_disjoint_interior
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {a c x : ℝ × ℝ}
    (hxBase :
      x ∈ openSegment ℝ (t.points 0) (t.points 2))
    (hxSegment : x ∈ segment ℝ a c)
    (hdisjoint :
      Disjoint t.interior (segment ℝ a c)) :
    (Submission.Triangle.affineBasis t).coord 1 a ≤ 0 ∧
      (Submission.Triangle.affineBasis t).coord 1 c ≤ 0 := by
  constructor
  · by_contra hnonpos
    have hpos :
        0 <
          (Submission.Triangle.affineBasis t).coord 1 a :=
      lt_of_not_ge hnonpos
    obtain ⟨y, hyInterior, hySegment⟩ :=
      exists_interior_on_segment_of_openBase_of_endpoint_pos
        t hxBase hxSegment hpos
    exact
      Set.disjoint_left.mp hdisjoint
        hyInterior hySegment
  · by_contra hnonpos
    have hpos :
        0 <
          (Submission.Triangle.affineBasis t).coord 1 c :=
      lt_of_not_ge hnonpos
    obtain ⟨y, hyInterior, hySegment⟩ :=
      exists_interior_on_segment_of_openBase_of_endpoint_pos
        t (a := c) (c := a) hxBase
          (by simpa [segment_symm] using hxSegment)
          hpos
    exact
      Set.disjoint_left.mp hdisjoint
        hyInterior
        (by simpa [segment_symm] using hySegment)

/-- If the base point is also in the relative interior of the other
segment, the preceding nonpositive coordinates must both vanish. -/
theorem endpoint_coords_zero_of_openBase_openSegment
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {a c x : ℝ × ℝ}
    (hxBase :
      x ∈ openSegment ℝ (t.points 0) (t.points 2))
    (hxSegment : x ∈ openSegment ℝ a c)
    (hdisjoint :
      Disjoint t.interior (segment ℝ a c)) :
    (Submission.Triangle.affineBasis t).coord 1 a = 0 ∧
      (Submission.Triangle.affineBasis t).coord 1 c = 0 := by
  let b := Submission.Triangle.affineBasis t
  have hnonpos :=
    endpoint_coords_nonpos_of_openBase_of_disjoint_interior
      t hxBase
        (openSegment_subset_segment ℝ a c hxSegment)
        hdisjoint
  have hxFace :
      x ∈ (t.faceOpposite 1).closedInterior := by
    rw [Submission.Triangle.closedInterior_faceOpposite_one,
      affineSegment_eq_segment]
    exact
      openSegment_subset_segment ℝ
        (t.points 0) (t.points 2) hxBase
  have hxClosed :
      x ∈ t.closedInterior :=
    t.closedInterior_faceOpposite_subset_closedInterior
      1 hxFace
  have hxOne : b.coord 1 x = 0 := by
    simpa [b] using
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hxClosed 1).mpr hxFace
  rw [openSegment_eq_image_lineMap] at hxSegment
  obtain ⟨r, hr, hx⟩ := hxSegment
  rw [← hx] at hxOne
  simp [b] at hxOne
  have honeMinus : 0 < 1 - r :=
    sub_pos.mpr hr.2
  constructor
  · apply le_antisymm hnonpos.1
    by_contra ha
    have haNeg : b.coord 1 a < 0 :=
      lt_of_not_ge ha
    have hleft :
        (1 - r) * b.coord 1 a < 0 :=
      mul_neg_of_pos_of_neg honeMinus haNeg
    have hright :
        r * b.coord 1 c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        hr.1.le hnonpos.2
    exact
      (ne_of_lt (add_neg_of_neg_of_nonpos hleft hright))
        hxOne
  · apply le_antisymm hnonpos.2
    by_contra hc
    have hcNeg : b.coord 1 c < 0 :=
      lt_of_not_ge hc
    have hleft :
        (1 - r) * b.coord 1 a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        honeMinus.le hnonpos.1
    have hright :
        r * b.coord 1 c < 0 :=
      mul_neg_of_pos_of_neg hr.1 hcNeg
    exact
      (ne_of_lt (add_neg_of_nonpos_of_neg hleft hright))
        hxOne

/-- On the base line, a second segment whose endpoints avoid the relative
interior of the base but whose relative interior meets it must span the
whole base. -/
theorem base_subset_segment_of_endpoint_coords
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {a c x : ℝ × ℝ}
    (hxBase :
      x ∈ openSegment ℝ (t.points 0) (t.points 2))
    (hxSegment : x ∈ openSegment ℝ a c)
    (haOne :
      (Submission.Triangle.affineBasis t).coord 1 a = 0)
    (hcOne :
      (Submission.Triangle.affineBasis t).coord 1 c = 0)
    (haNotBase :
      (Submission.Triangle.affineBasis t).coord 2 a ∉
        Set.Ioo (0 : ℝ) 1)
    (hcNotBase :
      (Submission.Triangle.affineBasis t).coord 2 c ∉
        Set.Ioo (0 : ℝ) 1) :
    segment ℝ (t.points 0) (t.points 2) ⊆
      segment ℝ a c := by
  let b := Submission.Triangle.affineBasis t
  let A := b.coord 2 a
  let C := b.coord 2 c
  have hsideA : A ≤ 0 ∨ 1 ≤ A := by
    by_cases hA : A ≤ 0
    · exact Or.inl hA
    · right
      have hApos : 0 < A := lt_of_not_ge hA
      have hnot : ¬ A < 1 := by
        intro hAlt
        exact haNotBase ⟨hApos, hAlt⟩
      exact le_of_not_gt hnot
  have hsideC : C ≤ 0 ∨ 1 ≤ C := by
    by_cases hC : C ≤ 0
    · exact Or.inl hC
    · right
      have hCpos : 0 < C := lt_of_not_ge hC
      have hnot : ¬ C < 1 := by
        intro hClt
        exact hcNotBase ⟨hCpos, hClt⟩
      exact le_of_not_gt hnot
  rw [openSegment_eq_image_lineMap] at hxBase
  obtain ⟨r, hr, hxr⟩ := hxBase
  have hxCoord :
      b.coord 2 x = r := by
    rw [← hxr]
    simp [b]
  rw [openSegment_eq_image_lineMap] at hxSegment
  obtain ⟨s, hs, hxs⟩ := hxSegment
  have hxCombination :
      b.coord 2 x = A + s * (C - A) := by
    rw [← hxs]
    simp [A, C, b]
    ring
  have hxAffine :
      b.coord 2 x = (1 - s) * A + s * C := by
    rw [hxCombination]
    ring
  have hopposite :
      (A ≤ 0 ∧ 1 ≤ C) ∨
        (C ≤ 0 ∧ 1 ≤ A) := by
    rcases hsideA with hA | hA <;>
        rcases hsideC with hC | hC
    · exfalso
      have hleft :
          (1 - s) * A ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr hs.2.le) hA
      have hright :
          s * C ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          hs.1.le hC
      linarith [hxCoord, hxAffine, hr.1]
    · exact Or.inl ⟨hA, hC⟩
    · exact Or.inr ⟨hC, hA⟩
    · exfalso
      have hleft :
          1 - s ≤ (1 - s) * A := by
        simpa using
          mul_le_mul_of_nonneg_left hA
            (sub_nonneg.mpr hs.2.le)
      have hright :
          s ≤ s * C := by
        simpa using
          mul_le_mul_of_nonneg_left hC hs.1.le
      linarith [hxCoord, hxAffine, hr.2]
  have span_of_order
      {u w : ℝ × ℝ}
      (U W : ℝ)
      (huOne : b.coord 1 u = 0)
      (hwOne : b.coord 1 w = 0)
      (huTwo : b.coord 2 u = U)
      (hwTwo : b.coord 2 w = W)
      (hU : U ≤ 0)
      (hW : 1 ≤ W) :
      segment ℝ (t.points 0) (t.points 2) ⊆
        segment ℝ u w := by
    have hden : 0 < W - U := by
      linarith
    have pointAt
        (k : ℝ) (hUk : U ≤ k) (hkW : k ≤ W) :
        ∃ y ∈ segment ℝ u w,
          b.coord 1 y = 0 ∧
            b.coord 2 y = k := by
      let d : ℝ := (k - U) / (W - U)
      have hdNonneg : 0 ≤ d := by
        exact div_nonneg (sub_nonneg.mpr hUk) hden.le
      have hdLe : d ≤ 1 := by
        exact (div_le_one hden).2 (by linarith)
      let y := AffineMap.lineMap u w d
      have hySegment :
          y ∈ segment ℝ u w :=
        lineMap_mem_segment ℝ u w
          ⟨hdNonneg, hdLe⟩
      have hdEval :
          d * (W - U) = k - U := by
        exact div_mul_cancel₀ _ hden.ne'
      have hyOne : b.coord 1 y = 0 := by
        simp [y, huOne, hwOne]
      have hyTwo : b.coord 2 y = k := by
        simp [y, huTwo, hwTwo]
        nlinarith
      exact ⟨y, hySegment, hyOne, hyTwo⟩
    obtain ⟨y0, hy0Segment, hy0One, hy0Two⟩ :=
      pointAt 0 hU (by linarith)
    obtain ⟨y2, hy2Segment, hy2One, hy2Two⟩ :=
      pointAt 1 (by linarith) hW
    have hy0 :
        y0 = t.points 0 := by
      apply b.ext_elem
      intro i
      fin_cases i
      · have hsum := b.sum_coord_apply_eq_one y0
        simp only [Fin.sum_univ_three] at hsum
        simp [b]
        linarith
      · simpa [b] using
          hy0One
      · simpa [b] using
          hy0Two
    have hy2 :
        y2 = t.points 2 := by
      apply b.ext_elem
      intro i
      fin_cases i
      · have hsum := b.sum_coord_apply_eq_one y2
        simp only [Fin.sum_univ_three] at hsum
        simp [b]
        linarith
      · simpa [b] using
          hy2One
      · simpa [b] using
          hy2Two
    exact
      (convex_segment u w).segment_subset
        (hy0 ▸ hy0Segment)
        (hy2 ▸ hy2Segment)
  rcases hopposite with hAC | hCA
  · exact
      span_of_order A C
        (by simpa [b] using haOne)
        (by simpa [b] using hcOne)
        rfl rfl hAC.1 hAC.2
  · simpa [segment_symm] using
      span_of_order C A
        (u := c) (w := a)
        (by simpa [b] using hcOne)
        (by simpa [b] using haOne)
        rfl rfl hCA.1 hCA.2

/-- A candidate triangle is vertex-empty away from its two base endpoints. -/
def VertexEmptyAtOne
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v))) :
    Prop :=
  let t :=
    LatticeTriangle.triangle
      (EarRemoval.earTriangle hn v) htriangle
  ∀ j : Fin (n + 1),
    j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
      toPlane (v j) ∈ t.closedInterior →
        j = 0 ∨
          j = (⟨2, by omega⟩ : Fin (n + 1))

/-- If the candidate triangle contains no other polygon vertex, no reduced
edge can enter its ordinary interior.  Any entering segment has a
positive-coordinate endpoint outside the triangle and therefore crosses an
incident triangle side, contradicting the already checked child-boundary
incidence. -/
theorem triangleInterior_disjoint_reducedBoundary_of_vertexEmpty
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (hempty : VertexEmptyAtOne hn v htriangle) :
    Disjoint
      (LatticeTriangle.triangle
        (EarRemoval.earTriangle hn v)
          htriangle).interior
      ((latPoly
        (EarRemoval.removeSecond v)).boundary
          (R := ℝ)) := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let t := LatticeTriangle.triangle ear htriangle
  let b := Submission.Triangle.affineBasis t
  have htPolygon :
      t.toPolygon = latPoly ear := by
    rfl
  have hendpointOutside :
      ∀ r : Fin n,
        0 <
            b.coord 1
              (toPlane
                (v (EarRemoval.reducedIndex r))) →
          toPlane (v (EarRemoval.reducedIndex r)) ∉
            t.closedInterior := by
    intro r hrpos hrclosed
    have hrne :
        EarRemoval.reducedIndex r ≠
          (⟨1, by omega⟩ : Fin (n + 1)) :=
      EarRemoval.reducedIndex_ne_one (by omega) r
    have hempty' :
        EarRemoval.reducedIndex r = 0 ∨
          EarRemoval.reducedIndex r =
            (⟨2, by omega⟩ : Fin (n + 1)) :=
      hempty (EarRemoval.reducedIndex r)
        hrne hrclosed
    rcases hempty' with hzero | htwo
    · have hpoint :
          toPlane (v (EarRemoval.reducedIndex r)) =
            t.points 0 := by
        rw [hzero]
        simp [t, ear]
      rw [hpoint] at hrpos
      simp [b] at hrpos
    · have hpoint :
          toPlane (v (EarRemoval.reducedIndex r)) =
            t.points 2 := by
        rw [htwo]
        simp [t, ear]
      rw [hpoint] at hrpos
      simp [b] at hrpos
  rw [Set.disjoint_left]
  intro x hxInterior hxReduced
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
  have hxpos :
      0 < b.coord 1 x := by
    simpa [t, b] using
      (Submission.Triangle.mem_interior_iff_coord_pos
        t x).mp hxInterior 1
  have hpositiveEndpoint :
      0 <
          b.coord 1
            (toPlane
              (v (EarRemoval.reducedIndex i))) ∨
        0 <
          b.coord 1
            (toPlane
              (v
                (EarRemoval.reducedIndex
                  (finRotate n i)))) := by
    simpa [b] using
      exists_endpoint_coord_pos t hxSegment
        (by simpa [b] using hxpos)
  have endpointContradiction
      (r : Fin n)
      (hrEndpoint :
        toPlane (v (EarRemoval.reducedIndex r)) ∈
          segment ℝ
            (toPlane (v (EarRemoval.reducedIndex i)))
            (toPlane
              (v
                (EarRemoval.reducedIndex
                  (finRotate n i)))))
      (hrpos :
        0 <
          b.coord 1
            (toPlane
              (v (EarRemoval.reducedIndex r)))) :
      False := by
    have hrOutside :
        toPlane (v (EarRemoval.reducedIndex r)) ∉
          t.closedInterior :=
      hendpointOutside r hrpos
    obtain ⟨z, hzToX, hzpos, hzFace⟩ :=
      TriangleCoords.exists_mem_incidentFace_on_segment
        t hrOutside
          (by simpa [b] using hrpos)
          hxInterior
    have hzSegment :
        z ∈
          segment ℝ
            (toPlane (v (EarRemoval.reducedIndex i)))
            (toPlane
              (v
                (EarRemoval.reducedIndex
                  (finRotate n i)))) :=
      (convex_segment _ _).segment_subset
        hrEndpoint hxSegment hzToX
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
      · exact faceOpposite_subset_boundary t 0 hzZero
      · exact faceOpposite_subset_boundary t 2 hzTwo
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
    exact (ne_of_gt (by simpa [b] using hzpos)) hzzero
  rcases hpositiveEndpoint with hiPos | hnextPos
  · exact endpointContradiction i
      (left_mem_segment ℝ _ _) hiPos
  · exact endpointContradiction (finRotate n i)
      (right_mem_segment ℝ _ _) hnextPos

/-- Vertex-emptiness rules the whole base-deleted cap out of the reduced
boundary.  Points of the cap are either in the triangle interior, handled
above, or on the triangle boundary; the checked child-boundary intersection
then puts the latter on the base, where coordinate `1` is zero. -/
theorem openCap_subset_reducedBoundary_compl_of_vertexEmpty
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (hempty : VertexEmptyAtOne hn v htriangle) :
    TriangleCap.openCap
        (LatticeTriangle.triangle
          (EarRemoval.earTriangle hn v)
            htriangle) ⊆
      ((latPoly
        (EarRemoval.removeSecond v)).boundary
          (R := ℝ))ᶜ := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let t := LatticeTriangle.triangle ear htriangle
  let b := Submission.Triangle.affineBasis t
  have htPolygon :
      t.toPolygon = latPoly ear := by
    rfl
  have hinteriorDisjoint :
      Disjoint t.interior
        ((latPoly reduced).boundary (R := ℝ)) := by
    simpa [t, ear, reduced] using
      triangleInterior_disjoint_reducedBoundary_of_vertexEmpty
        hn v hsimple htriangle hempty
  intro x hxCap hxReduced
  have hxClosed :
      x ∈ t.closedInterior :=
    hxCap.1
  have hxpos :
      0 < b.coord 1 x := by
    simpa [TriangleCap.openCap, b] using hxCap.2
  by_cases hxInterior : x ∈ t.interior
  · exact
      Set.disjoint_left.mp hinteriorDisjoint
        hxInterior hxReduced
  · have hxTriangleBoundary :
        x ∈ (latPoly ear).boundary (R := ℝ) := by
      rw [← htPolygon,
        Submission.Triangle.toPolygon_boundary_eq_surface]
      exact ⟨hxClosed, hxInterior⟩
    have hxDiagonal :
        x ∈ CleanEar.diagonal hn v := by
      have hxBoth :
          x ∈
            (latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ) ∩
              (latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ) := by
        simpa [ear, reduced] using
          And.intro hxTriangleBoundary hxReduced
      rw [CleanEar.childBoundaryInter_of_isSimple
        hn v hsimple] at hxBoth
      exact hxBoth
    have hxFaceOne :
        x ∈ (t.faceOpposite 1).closedInterior := by
      rw [Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_eq_segment]
      simpa [CleanEar.diagonal, t, ear] using
        hxDiagonal
    have hxzero :
        b.coord 1 x = 0 := by
      simpa [b] using
        (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
          t hxClosed 1).mpr hxFaceOne
    exact (ne_of_gt hxpos) hxzero

/-- Vertex-emptiness also makes the prospective base a clean diagonal:
the old boundary meets it only at its two endpoint vertices. -/
theorem parentBoundary_inter_diagonal_of_vertexEmpty
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (hempty : VertexEmptyAtOne hn v htriangle) :
    (latPoly v).boundary (R := ℝ) ∩
        CleanEar.diagonal hn v =
      {toPlane (v 0),
        toPlane (v ⟨2, by omega⟩)} := by
  let ear := EarRemoval.earTriangle hn v
  let t := LatticeTriangle.triangle ear htriangle
  let b := Submission.Triangle.affineBasis t
  let p0 := toPlane (v 0)
  let p2 :=
    toPlane
      (v (⟨2, by omega⟩ : Fin (n + 1)))
  have hp0p2 : p0 ≠ p2 := by
    intro h
    have hv :
        v (0 : Fin (n + 1)) ≠
          v (⟨2, by omega⟩ : Fin (n + 1)) :=
      (Helpers.lattice_vertex_injective_of_isSimple
        hsimple).ne (by
          intro hi
          have hval := congrArg Fin.val hi
          simp only [Fin.val_zero] at hval
          omega)
    exact
      hv (LatticeTriangle.toPlaneIntLinear_injective
        (by
          change p0 = p2
          exact h))
  have hinteriorDisjoint :
      Disjoint t.interior
        ((latPoly
          (EarRemoval.removeSecond v)).boundary
            (R := ℝ)) := by
    simpa [t, ear] using
      triangleInterior_disjoint_reducedBoundary_of_vertexEmpty
        hn v hsimple htriangle hempty
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxEndpoints :
        x ∈ ({p0, p2} : Set (ℝ × ℝ))
    · simpa [p0, p2] using hxEndpoints
    have hxBase :
        x ∈ openSegment ℝ p0 p2 := by
      rw [Diagonal.openSegment_eq_segment_sdiff hp0p2]
      exact
        ⟨by simpa [CleanEar.diagonal, p0, p2] using hx.2,
          hxEndpoints⟩
    have hxFace :
        x ∈ (t.faceOpposite 1).closedInterior := by
      rw [Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_eq_segment]
      simpa [t, ear, p0, p2] using
        openSegment_subset_segment ℝ p0 p2 hxBase
    have hxClosed :
        x ∈ t.closedInterior :=
      t.closedInterior_faceOpposite_subset_closedInterior
        1 hxFace
    rw [Polygon.boundary] at hx
    obtain ⟨j, hxEdge⟩ := Set.mem_iUnion.mp hx.1
    by_cases hjzero : j = (0 : Fin (n + 1))
    · subst j
      have hxTriangle :
          x ∈
            (latPoly ear).edgeSet ℝ (2 : Fin 3) ∩
              (latPoly ear).edgeSet ℝ (0 : Fin 3) := by
        constructor
        · rw [EarRemoval.ear_edge_two hn v]
          simpa [CleanEar.diagonal, p0, p2] using hx.2
        · rw [EarRemoval.ear_edge_zero hn v]
          exact hxEdge
      have hinter := htriangle.2.2 (2 : Fin 3)
      have hrotate :
          finRotate 3 (2 : Fin 3) = (0 : Fin 3) := by
        decide
      rw [hrotate] at hinter
      rw [hinter] at hxTriangle
      have hxp0 : x = p0 := by
        simpa [latPoly, ear, p0] using
          Set.mem_singleton_iff.mp hxTriangle
      exact False.elim <|
        hxEndpoints (by simp [hxp0])
    by_cases hjone :
        j =
          (⟨1, by omega⟩ : Fin (n + 1))
    · subst j
      have hxTriangle :
          x ∈
            (latPoly ear).edgeSet ℝ (1 : Fin 3) ∩
              (latPoly ear).edgeSet ℝ (2 : Fin 3) := by
        constructor
        · rw [EarRemoval.ear_edge_one hn v]
          exact hxEdge
        · rw [EarRemoval.ear_edge_two hn v]
          simpa [CleanEar.diagonal, p0, p2] using hx.2
      have hinter := htriangle.2.2 (1 : Fin 3)
      have hrotate :
          finRotate 3 (1 : Fin 3) = (2 : Fin 3) := by
        decide
      rw [hrotate] at hinter
      rw [hinter] at hxTriangle
      have hxp2 : x = p2 := by
        simpa [latPoly, ear, p2] using
          Set.mem_singleton_iff.mp hxTriangle
      exact False.elim <|
        hxEndpoints (by simp [hxp2])
    have hjValZero : j.val ≠ 0 := by
      intro h
      apply hjzero
      apply Fin.ext
      simpa using h
    have hjValOne : j.val ≠ 1 := by
      intro h
      apply hjone
      apply Fin.ext
      simpa using h
    have hjTwo : 2 ≤ j.val := by
      omega
    let i : Fin n :=
      ⟨j.val - 1, by omega⟩
    have hi : i.val ≠ 0 := by
      dsimp [i]
      omega
    have hindex :
        EarRemoval.reducedIndex i = j := by
      apply Fin.ext
      rw [EarRemoval.reducedIndex_of_val_ne_zero i hi]
      dsimp [i]
      omega
    let a := toPlane (v j)
    let c :=
      toPlane (v (finRotate (n + 1) j))
    have hxSegment :
        x ∈ segment ℝ a c := by
      simpa [a, c, Polygon.edgeSet,
        affineSegment_eq_segment, latPoly] using hxEdge
    have hxReducedEdge :
        x ∈
          (latPoly
            (EarRemoval.removeSecond v)).edgeSet ℝ i := by
      rw [EarRemoval.reduced_edge_of_ne_zero
        hn v i hi, hindex]
      exact hxEdge
    have hedgeSubset :
        segment ℝ a c ⊆
          (latPoly
            (EarRemoval.removeSecond v)).boundary
              (R := ℝ) := by
      intro y hy
      rw [Polygon.boundary]
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [EarRemoval.reduced_edge_of_ne_zero
        hn v i hi, hindex]
      simpa [a, c, Polygon.edgeSet,
        affineSegment_eq_segment, latPoly] using hy
    have hsegmentDisjoint :
        Disjoint t.interior (segment ℝ a c) := by
      rw [Set.disjoint_left]
      intro y hyInterior hySegment
      exact
        Set.disjoint_left.mp hinteriorDisjoint
          hyInterior (hedgeSubset hySegment)
    have hnextOne :
        finRotate (n + 1) j ≠
          (⟨1, by omega⟩ : Fin (n + 1)) := by
      intro h
      have hj0 :
          j = (0 : Fin (n + 1)) := by
        apply (finRotate (n + 1)).injective
        rw [h, CleanEar.finRotate_zero hn]
      exact hjzero hj0
    have hxneA : x ≠ a := by
      intro hxa
      have haClosed :
          a ∈ t.closedInterior := by
        simpa [hxa] using hxClosed
      have hjCases := hempty j hjone haClosed
      rcases hjCases with hj0 | hj2
      · exact hjzero hj0
      · apply hxEndpoints
        right
        simpa [a, p2, hj2] using hxa
    have hxneC : x ≠ c := by
      intro hxc
      have hcClosed :
          c ∈ t.closedInterior := by
        simpa [hxc] using hxClosed
      have hjCases :=
        hempty (finRotate (n + 1) j)
          hnextOne hcClosed
      rcases hjCases with hj0 | hj2
      · apply hxEndpoints
        left
        simpa [c, p0, hj0] using hxc
      · apply hxEndpoints
        right
        simpa [c, p2, hj2] using hxc
    have hac : a ≠ c := by
      simpa [a, c, latPoly] using hsimple.1 j
    have hxOpenEdge :
        x ∈ openSegment ℝ a c := by
      rw [Diagonal.openSegment_eq_segment_sdiff hac]
      refine ⟨hxSegment, ?_⟩
      simpa only [Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] using
        And.intro hxneA hxneC
    have hcoordZero :=
      endpoint_coords_zero_of_openBase_openSegment
        t (by simpa [t, ear, p0, p2] using hxBase)
          hxOpenEdge hsegmentDisjoint
    have haNotBase :
        b.coord 2 a ∉ Set.Ioo (0 : ℝ) 1 := by
      intro haIoo
      have hsum := b.sum_coord_apply_eq_one a
      rw [Fin.sum_univ_three] at hsum
      have haZero : 0 ≤ b.coord 0 a := by
        have haOne : b.coord 1 a = 0 :=
          hcoordZero.1
        have haTwoLt : b.coord 2 a < 1 :=
          haIoo.2
        linarith
      have haClosed :
          a ∈ t.closedInterior := by
        rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
        intro k
        fin_cases k
        · exact haZero
        · exact hcoordZero.1.ge
        · exact haIoo.1.le
      have hjCases := hempty j hjone haClosed
      rcases hjCases with hj0 | hj2
      · exact hjzero hj0
      · have haTwo : b.coord 2 a = 1 := by
          have haPoint : a = t.points 2 := by
            simp [a, t, ear, hj2]
          rw [haPoint]
          simp [b]
        exact (ne_of_lt haIoo.2) haTwo
    have hcNotBase :
        b.coord 2 c ∉ Set.Ioo (0 : ℝ) 1 := by
      intro hcIoo
      have hsum := b.sum_coord_apply_eq_one c
      rw [Fin.sum_univ_three] at hsum
      have hcZero : 0 ≤ b.coord 0 c := by
        have hcOne : b.coord 1 c = 0 :=
          hcoordZero.2
        have hcTwoLt : b.coord 2 c < 1 :=
          hcIoo.2
        linarith
      have hcClosed :
          c ∈ t.closedInterior := by
        rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
        intro k
        fin_cases k
        · exact hcZero
        · exact hcoordZero.2.ge
        · exact hcIoo.1.le
      have hjCases :=
        hempty (finRotate (n + 1) j)
          hnextOne hcClosed
      rcases hjCases with hj0 | hj2
      · have hcTwo : b.coord 2 c = 0 := by
          have hcPoint : c = t.points 0 := by
            simp [c, t, ear, hj0]
          rw [hcPoint]
          simp [b]
        exact (ne_of_gt hcIoo.1) hcTwo
      · have hcTwo : b.coord 2 c = 1 := by
          have hcPoint : c = t.points 2 := by
            simp [c, t, ear, hj2]
          rw [hcPoint]
          simp [b]
        exact (ne_of_lt hcIoo.2) hcTwo
    have hbaseSubset :
        segment ℝ p0 p2 ⊆ segment ℝ a c := by
      simpa [t, ear, p0, p2] using
        base_subset_segment_of_endpoint_coords
          t
          (by simpa [t, ear, p0, p2] using hxBase)
          hxOpenEdge hcoordZero.1 hcoordZero.2
          haNotBase hcNotBase
    have hp0Edge :
        toPlane (v 0) ∈ (latPoly v).edgeSet ℝ j := by
      have hp0Segment :=
        hbaseSubset (left_mem_segment ℝ p0 p2)
      simpa [p0, a, c, Polygon.edgeSet,
        affineSegment_eq_segment, latPoly] using hp0Segment
    have hp2Edge :
        toPlane
            (v (⟨2, by omega⟩ :
              Fin (n + 1))) ∈
          (latPoly v).edgeSet ℝ j := by
      have hp2Segment :=
        hbaseSubset (right_mem_segment ℝ p0 p2)
      simpa [p2, a, c, Polygon.edgeSet,
        affineSegment_eq_segment, latPoly] using hp2Segment
    have hzeroCases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple
          (0 : Fin (n + 1)) j).mp hp0Edge
    have htwoCases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple
          (⟨2, by omega⟩ : Fin (n + 1)) j).mp
        hp2Edge
    rcases hzeroCases with hzero | hzero
    · exact False.elim (hjzero hzero.symm)
    · rcases htwoCases with htwo | htwo
      · have hrotate :
            finRotate (n + 1)
                (⟨2, by omega⟩ : Fin (n + 1)) =
              (0 : Fin (n + 1)) := by
          exact
            (congrArg (finRotate (n + 1)) htwo).trans
              hzero.symm
        have hnotLast :
            (⟨2, by omega⟩ : Fin (n + 1)) ≠
              Fin.last n := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last] at hval
          omega
        have hval :=
          congrArg Fin.val hrotate
        rw [coe_finRotate_of_ne_last hnotLast] at hval
        simp only [Fin.val_zero] at hval
        omega
      · have hval :=
          congrArg Fin.val (hzero.trans htwo.symm)
        simp only [Fin.val_zero] at hval
        omega
  · intro x hx
    rcases hx with hx0 | hx2
    · have hxEq : x = toPlane (v 0) := by
        simpa using hx0
      subst x
      constructor
      · exact
          (Helpers.boundaryVertex v
            (0 : Fin (n + 1))).property
      · exact left_mem_segment ℝ _ _
    · have hxEq :
          x =
            toPlane
              (v (⟨2, by omega⟩ :
                Fin (n + 1))) := by
        simpa using hx2
      subst x
      constructor
      · exact
          (Helpers.boundaryVertex v
            (⟨2, by omega⟩ :
              Fin (n + 1))).property
      · exact right_mem_segment ℝ _ _

end Submission.EmptyCap
