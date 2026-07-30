import Submission.DiskGluing
import Submission.RegularFill

open LeanEval.Geometry.PicksTheorem

namespace Submission.DiskData

/-- The filled region associated to a lattice polygon. -/
def region {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    Set (ℝ × ℝ) :=
  FilledRegion.fill
    ((latPoly v).boundary (R := ℝ))

/-- Disk-like topology in exactly the form needed by clean-chord
induction. -/
structure Holds {n : ℕ}
    (v : Fin n → ℤ × ℤ) : Prop where
  regular :
    closure (interior (region v)) = region v
  interiorPreconnected :
    IsPreconnected (interior (region v))
  boundary_eq_frontier :
    (latPoly v).boundary (R := ℝ) =
      frontier (region v)
  edgeAttachable :
    ∀ i : Fin n,
      DiskGluing.EdgeAttachable
        (region v)
        ((latPoly v).edgeSet ℝ i)

/-- Reindex the three points of an affine triangle. -/
noncomputable def reindexTriangle
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (e : Fin 3 ≃ Fin 3) :
    Affine.Triangle ℝ (ℝ × ℝ) where
  points := t.points ∘ e
  independent :=
    (affineIndependent_equiv e).mpr t.independent

@[simp]
theorem reindexTriangle_points
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    (reindexTriangle t e).points i =
      t.points (e i) :=
  rfl

/-- Reindexing triangle vertices does not change the closed triangle. -/
theorem reindexTriangle_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (e : Fin 3 ≃ Fin 3) :
    (reindexTriangle t e).closedInterior =
      t.closedInterior := by
  rw [← (reindexTriangle t e).convexHull_eq_closedInterior,
    ← t.convexHull_eq_closedInterior]
  congr 1
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro x ⟨i, rfl⟩
    refine ⟨e.symm i, ?_⟩
    simp

/-- The triangle-attachment theorem applies along any one of the three
faces, not only the face opposite index `1`. -/
theorem triangle_edgeAttachable
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) :
    DiskGluing.EdgeAttachable
      t.closedInterior
      (t.faceOpposite i).closedInterior := by
  let e : Fin 3 ≃ Fin 3 :=
    Equiv.swap 1 i
  let u := reindexTriangle t e
  have huClosed :
      u.closedInterior = t.closedInterior :=
    reindexTriangle_closedInterior t e
  have huFace :
      (u.faceOpposite 1).closedInterior =
        (t.faceOpposite i).closedInterior := by
    dsimp [u, e]
    fin_cases i <;>
      simp [Submission.Triangle.closedInterior_faceOpposite_zero,
        Submission.Triangle.closedInterior_faceOpposite_one,
        Submission.Triangle.closedInterior_faceOpposite_two,
        reindexTriangle, Equiv.swap_apply_def]
  intro R hRclosed hRcompl hRinter
  have hinter :
      R ∩ u.closedInterior =
        (u.faceOpposite 1).closedInterior := by
    rw [huClosed, huFace]
    exact hRinter
  have h :=
    TriangleAttachment.isPreconnected_compl_union_closedInterior
      u hRclosed hRcompl hinter
  simpa [huClosed] using h

/-- Every simple lattice triangle carries the disk data used by the
recursive gluing argument. -/
theorem triangle
    (v : Fin 3 → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    Holds v := by
  let t := LatticeTriangle.triangle v hsimple
  have htPolygon :
      t.toPolygon = latPoly v := by
    rfl
  have hfill :
      region v = t.closedInterior := by
    unfold region
    rw [← htPolygon,
      TriangleFill.fill_toPolygon_boundary_eq_closedInterior]
  refine
    { regular := ?_
      interiorPreconnected := ?_
      boundary_eq_frontier := ?_
      edgeAttachable := ?_ }
  · simpa [region, RegularFill.Holds] using
      RegularFill.triangle v hsimple
  · rw [hfill, RegularFill.interior_closedInterior]
    exact
      (Submission.Triangle.convex_interior t).isPreconnected
  · rw [hfill, RegularFill.frontier_closedInterior,
      htPolygon]
  · intro i
    rw [hfill]
    fin_cases i
    · simpa [t, Polygon.edgeSet, latPoly,
        Submission.Triangle.closedInterior_faceOpposite_two,
        affineSegment_comm] using
        triangle_edgeAttachable t 2
    · simpa [t, Polygon.edgeSet, latPoly,
        Submission.Triangle.closedInterior_faceOpposite_zero,
        affineSegment_comm] using
        triangle_edgeAttachable t 0
    · simpa [t, Polygon.edgeSet, latPoly,
        Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_comm] using
        triangle_edgeAttachable t 1

end Submission.DiskData
