import Submission.EmptyEar
import Submission.EmptyEarExterior
import Submission.EmptyEarSeam

open LeanEval.Geometry.PicksTheorem

namespace Submission.RegularFill

/-- The filled region of a polygonal boundary is regular closed. -/
def Holds {n : ℕ} (v : Fin n → ℤ × ℤ) : Prop :=
  closure
      (interior
        (FilledRegion.fill
          ((latPoly v).boundary (R := ℝ)))) =
    FilledRegion.fill
      ((latPoly v).boundary (R := ℝ))

/-- A closed affine triangle is the closure of its ordinary interior. -/
theorem closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    closure (interior t.closedInterior) =
      t.closedInterior := by
  let b := Submission.Triangle.affineBasis t
  let w : Fin 3 → ℝ := fun _ => 1 / 3
  have hw : ∑ i, w i = 1 := by
    simp [w]
  let x :=
    Finset.univ.affineCombination ℝ b w
  have hxIntrinsic : x ∈ t.interior := by
    rw [Submission.Triangle.mem_interior_iff_coord_pos]
    intro i
    change 0 < b.coord i x
    dsimp [x]
    rw [b.coord_apply_combination_of_mem
      (Finset.mem_univ i) hw]
    norm_num [w]
  have hxOrdinary :
      x ∈ interior t.closedInterior :=
    interior_maximal
      t.interior_subset_closedInterior
      (Submission.Triangle.isOpen_interior t)
      hxIntrinsic
  calc
    closure (interior t.closedInterior) =
        closure t.closedInterior :=
      Convex.closure_interior_eq_closure_of_nonempty_interior
        (Submission.Triangle.convex_closedInterior t)
        ⟨x, hxOrdinary⟩
    _ = t.closedInterior :=
      t.isClosed_closedInterior.closure_eq

/-- The intrinsic affine-simplex interior is nonempty in the ambient
plane. -/
theorem intrinsicInterior_nonempty
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    t.interior.Nonempty := by
  let b := Submission.Triangle.affineBasis t
  let w : Fin 3 → ℝ := fun _ => 1 / 3
  have hw : ∑ i, w i = 1 := by
    simp [w]
  let x :=
    Finset.univ.affineCombination ℝ b w
  refine ⟨x, ?_⟩
  rw [Submission.Triangle.mem_interior_iff_coord_pos]
  intro i
  change 0 < b.coord i x
  dsimp [x]
  rw [b.coord_apply_combination_of_mem
    (Finset.mem_univ i) hw]
  norm_num [w]

/-- The closure of the intrinsic affine-simplex interior is the closed
triangle. -/
theorem closure_intrinsicInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    closure t.interior = t.closedInterior := by
  apply Set.Subset.antisymm
  · exact
      closure_minimal
        t.interior_subset_closedInterior
        t.isClosed_closedInterior
  · intro x hxClosed
    obtain ⟨y, hyInterior⟩ :=
      intrinsicInterior_nonempty t
    have hsegment :
        openSegment ℝ y x ⊆ t.interior := by
      intro z hz
      rw [openSegment_eq_image_lineMap] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      rw [Submission.Triangle.mem_interior_iff_coord_pos]
      intro i
      rw [TriangleCoords.coord_lineMap]
      have hyPos :
          0 <
            (Submission.Triangle.affineBasis t).coord i y :=
        (Submission.Triangle.mem_interior_iff_coord_pos
          t y).mp hyInterior i
      have hxNonneg :
          0 ≤
            (Submission.Triangle.affineBasis t).coord i x :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t x).mp hxClosed i
      exact
        add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr hr.2) hyPos)
          (mul_nonneg hr.1.le hxNonneg)
    exact
      closure_mono hsegment <|
        segment_subset_closure_openSegment <|
          right_mem_segment ℝ y x

/-- For a full-dimensional affine triangle, the intrinsic simplex interior
is its ordinary topological interior. -/
theorem interior_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    interior t.closedInterior = t.interior := by
  rw [← closure_intrinsicInterior t]
  calc
    interior (closure t.interior) =
        interior t.interior :=
      Convex.interior_closure_eq_interior_of_nonempty_interior
        (Submission.Triangle.convex_interior t)
        (by
          rw [(Submission.Triangle.isOpen_interior t).interior_eq]
          exact intrinsicInterior_nonempty t)
    _ = t.interior :=
      (Submission.Triangle.isOpen_interior t).interior_eq

/-- The topological frontier of a closed affine triangle is its polygonal
surface. -/
theorem frontier_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    frontier t.closedInterior =
      t.toPolygon.boundary (R := ℝ) := by
  rw [frontier, t.isClosed_closedInterior.closure_eq,
    interior_closedInterior,
    Submission.Triangle.toPolygon_boundary_eq_surface]

/-- Every simple lattice triangle has a regular filled region. -/
theorem triangle
    (v : Fin 3 → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    Holds v := by
  let t := LatticeTriangle.triangle v hsimple
  have htPolygon :
      t.toPolygon = latPoly v := by
    rfl
  unfold Holds
  rw [← htPolygon,
    TriangleFill.fill_toPolygon_boundary_eq_closedInterior]
  exact closedInterior t

/-- Regularity is preserved when an empty exposed triangle is attached.
The same construction simultaneously proves that the exposed vertex is an
ear of the parent polygon. -/
theorem of_vertexEmpty
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
    (hreducedRegular :
      Holds (EarRemoval.removeSecond v)) :
    Holds v ∧ CleanEar.CoreIsEarAtOne hn v := by
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
  have hseam :=
    EmptyEarSeam.diagonal_sdiff_parent_subset_interior
      hn v hsimple M hvertices htriangle hempty houter
        hreducedRegular
  have hcompl :=
    EmptyEarExterior.childFill_compl_isPreconnected
      hn v hsimple M hvertices htriangle hempty
  have hfillUnion :=
    EmptyEar.parentFill_eq_childFill_union_of_local
      hn v hseam hcompl
  have htriangleRegular :
      closure
          (interior
            (FilledRegion.fill triangleBoundary)) =
        FilledRegion.fill triangleBoundary := by
    rw [htriangleFill]
    exact closedInterior t
  have hunionRegular :
      closure
          (interior
            (FilledRegion.fill triangleBoundary ∪
              FilledRegion.fill reducedBoundary)) =
        FilledRegion.fill triangleBoundary ∪
          FilledRegion.fill reducedBoundary := by
    apply FillFrontier.closure_interior_union_eq
    · exact
        FilledRegion.isClosed_fill
          (Helpers.isCompact_boundary
            (latPoly ear)).isClosed
    · exact
        FilledRegion.isClosed_fill
          (Helpers.isCompact_boundary
            (latPoly reduced)).isClosed
    · exact htriangleRegular
    · simpa [Holds, reducedBoundary, reduced] using
        hreducedRegular
  constructor
  · unfold Holds
    rw [hfillUnion]
    simpa [triangleBoundary, reducedBoundary, ear, reduced] using
      hunionRegular
  · exact
      EmptyEar.coreIsEarAtOne_of_vertexEmpty_of_local
        hn v hsimple M hvertices htriangle hempty houter
          hseam hcompl

end Submission.RegularFill
