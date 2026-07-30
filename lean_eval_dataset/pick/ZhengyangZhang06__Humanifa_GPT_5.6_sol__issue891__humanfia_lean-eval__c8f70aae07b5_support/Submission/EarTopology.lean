import Submission.CleanEar
import Submission.ConvexInside

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.EarTopology

/-- The proposed bounded side after attaching the ear triangle to the reduced
polygon: both child interiors together with their open common seam. -/
def attachedRegion {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) : Set (ℝ × ℝ) :=
  (inside
      ((latPoly (EarRemoval.earTriangle hn v)).boundary
        (R := ℝ)) ∪
    inside
      ((latPoly (EarRemoval.removeSecond v)).boundary
        (R := ℝ))) ∪
    openSegment ℝ (toPlane (v 0))
      (toPlane (v ⟨2, by omega⟩))

/-- The proposed attached region is bounded independently of whether it is
the actual bounded side of the parent boundary. -/
theorem isBounded_attachedRegion
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    Bornology.IsBounded (attachedRegion hn v) := by
  have htriangle :
      Bornology.IsBounded
        (inside
          ((latPoly (EarRemoval.earTriangle hn v)).boundary
            (R := ℝ))) :=
    Helpers.isBounded_inside_of_isBounded
      (Helpers.isBounded_boundary
        (latPoly (EarRemoval.earTriangle hn v)))
  have hreduced :
      Bornology.IsBounded
        (inside
          ((latPoly (EarRemoval.removeSecond v)).boundary
            (R := ℝ))) :=
    Helpers.isBounded_inside_of_isBounded
      (Helpers.isBounded_boundary
        (latPoly (EarRemoval.removeSecond v)))
  have hdiagonal :
      Bornology.IsBounded
        (segment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩))) := by
    rw [← EarRemoval.reduced_edge_zero hn v]
    exact
      Helpers.isBounded_edgeSet
        (latPoly (EarRemoval.removeSecond v))
        (⟨0, by omega⟩ : Fin n)
  exact
    (htriangle.union hreduced).union <|
      hdiagonal.subset <|
        openSegment_subset_segment ℝ _ _

/-- Concrete complement data sufficient to recognize an internal ear.  The
first six fields identify the bounded component side of the parent; the last
field independently keeps the two child interiors apart. -/
structure Witness
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) : Type where
  exterior : Set (ℝ × ℝ)
  complementPartition :
    ((latPoly v).boundary (R := ℝ))ᶜ =
      attachedRegion hn v ∪ exterior
  attachedOpen :
    IsOpen (attachedRegion hn v)
  exteriorOpen :
    IsOpen exterior
  sidesDisjoint :
    Disjoint (attachedRegion hn v) exterior
  exteriorEscape :
    ∀ x ∈ exterior,
      ∃ W : Set (ℝ × ℝ),
        x ∈ W ∧
          IsPreconnected W ∧
          W ⊆ ((latPoly v).boundary (R := ℝ))ᶜ ∧
          ¬ Bornology.IsBounded W
  triangleEscape :
    ∀ x ∈
        inside
          ((latPoly (EarRemoval.earTriangle hn v)).boundary
            (R := ℝ)),
      ∃ W : Set (ℝ × ℝ),
        x ∈ W ∧
          IsPreconnected W ∧
          W ⊆
            ((latPoly (EarRemoval.removeSecond v)).boundary
              (R := ℝ))ᶜ ∧
          ¬ Bornology.IsBounded W

/-- An open-side/escape witness supplies the exact bounded-component
partition and disjointness fields used by `CleanEar`. -/
theorem Witness.toCoreIsEarAtOne
    {n : ℕ} {hn : 3 ≤ n}
    {v : Fin (n + 1) → ℤ × ℤ}
    (witness : Witness hn v) :
    CleanEar.CoreIsEarAtOne hn v := by
  refine ⟨?_, ?_⟩
  · change
      inside ((latPoly v).boundary (R := ℝ)) =
        attachedRegion hn v
    exact
      Inside.inside_eq_of_open_partition
        witness.complementPartition
        witness.attachedOpen
        witness.exteriorOpen
        witness.sidesDisjoint
        (isBounded_attachedRegion hn v)
        witness.exteriorEscape
  · exact
      Inside.disjoint_inside_of_unbounded_witness
        witness.triangleEscape

/-- Conversely, an exact core ear has a canonical witness: its exterior is
the union of the unbounded components of the parent complement.  This shows
that the open-side/escape interface adds no mathematical assumption. -/
def Witness.ofCoreIsEarAtOne
    {n : ℕ} {hn : 3 ≤ n}
    {v : Fin (n + 1) → ℤ × ℤ}
    (core : CleanEar.CoreIsEarAtOne hn v) :
    Witness hn v := by
  let parentBoundary :=
    (latPoly v).boundary (R := ℝ)
  have hAttached :
      attachedRegion hn v = inside parentBoundary :=
    core.insidePartition.symm
  refine
    { exterior := Inside.unboundedOutside parentBoundary
      complementPartition := ?_
      attachedOpen := ?_
      exteriorOpen := ?_
      sidesDisjoint := ?_
      exteriorEscape := ?_
      triangleEscape := ?_ }
  · rw [Inside.compl_eq_inside_union_unboundedOutside,
      hAttached]
  · rw [hAttached]
    exact
      Helpers.isOpen_polygon_inside (latPoly v)
  · apply Inside.isOpen_unboundedOutside_of_isClosed
    exact
      (Helpers.isCompact_boundary (latPoly v)).isClosed
  · rw [hAttached]
    exact
      Inside.inside_disjoint_unboundedOutside
        parentBoundary
  · intro x hx
    exact
      Inside.exists_unbounded_escape_of_mem_unboundedOutside
        hx
  · intro x hxTriangle
    let triangleBoundary :=
      (latPoly (EarRemoval.earTriangle hn v)).boundary
        (R := ℝ)
    let reducedBoundary :=
      (latPoly (EarRemoval.removeSecond v)).boundary
        (R := ℝ)
    have hxParentInside :
        x ∈ inside parentBoundary := by
      rw [core.insidePartition]
      exact Or.inl (Or.inl hxTriangle)
    have hxNotReduced :
        x ∉ reducedBoundary := by
      intro hxReduced
      have hxParentOrDiagonal :
          x ∈ parentBoundary ∪
            segment ℝ (toPlane (v 0))
              (toPlane (v ⟨2, by omega⟩)) := by
        rw [← EarRemoval.child_boundaries_union hn v]
        exact Or.inr hxReduced
      rcases hxParentOrDiagonal with hxParent | hxDiagonal
      · exact hxParentInside.1 hxParent
      · have hxTriangleBoundary :
            x ∈
              (latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ) := by
          rw [Polygon.boundary]
          refine Set.mem_iUnion.mpr ⟨(2 : Fin 3), ?_⟩
          rw [EarRemoval.ear_edge_two hn v]
          exact hxDiagonal
        exact hxTriangle.1 hxTriangleBoundary
    have hcomponentUnbounded :
        ¬ Bornology.IsBounded
          (connectedComponentIn reducedBoundaryᶜ x) := by
      intro hcomponentBounded
      have hxReducedInside :
          x ∈ inside reducedBoundary :=
        ⟨hxNotReduced, hcomponentBounded⟩
      exact
        Set.disjoint_left.mp core.interiorsDisjoint
          hxTriangle hxReducedInside
    exact
      ⟨connectedComponentIn reducedBoundaryᶜ x,
        mem_connectedComponentIn hxNotReduced,
        isPreconnected_connectedComponentIn,
        connectedComponentIn_subset reducedBoundaryᶜ x,
        hcomponentUnbounded⟩

end Submission.EarTopology
