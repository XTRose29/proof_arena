import Submission.FillSplit
import Submission.VisibleDisk

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.VisibleDecomposition

/-- A clean visible chord and checked decompositions of its two subpolygons
produce a checked decomposition of the parent polygon. -/
noncomputable def glue
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
    (frontDecomposition :
      Dissection.PickDecomposition
        (FrontSubpolygon.vertices v visible.q))
    (backDecomposition :
      Dissection.PickDecomposition
        (BackSubpolygon.vertices v visible.q hq)) :
    Dissection.PickDecomposition v := by
  let front := FrontSubpolygon.vertices v visible.q
  let back := BackSubpolygon.vertices v visible.q hq
  let tipIndex :=
    (⟨1, by omega⟩ : Fin (n + 1))
  let tip := toPlane (v tipIndex)
  let qPoint := toPlane (v visible.q)
  let Dreal : Set (ℝ × ℝ) :=
    segment ℝ tip qPoint
  let diagonal :=
    Diagonal.closedLatticeSegment
      (v tipIndex) (v visible.q)
  let diagonalInterior :=
    Diagonal.openLatticeSegment
      (v tipIndex) (v visible.q)
  let P := (latPoly v).boundary (R := ℝ)
  let L := (latPoly front).boundary (R := ℝ)
  let R := (latPoly back).boundary (R := ℝ)
  have hv :
      v tipIndex ≠ v visible.q := by
    exact
      (Helpers.lattice_vertex_injective_of_isSimple hsimple).ne
        visible.q_ne_one.symm
  have htipq : tip ≠ qPoint := by
    intro h
    exact hv
      (LatticeTriangle.toPlaneIntLinear_injective h)
  have hchildren : L ∪ R = P ∪ Dreal := by
    simpa [L, R, P, Dreal, front, back, tip,
      qPoint, tipIndex] using
      VisibleBoundary.childBoundaries_union
        v visible.q hq
  have hboundaryInter : L ∩ R = Dreal := by
    simpa [L, R, Dreal, front, back, tip,
      qPoint, tipIndex] using
      VisibleBoundary.childBoundaries_inter
        hn v hsimple visible.q hq
  have houter : P ∩ Dreal = {tip, qPoint} := by
    simpa [P, Dreal, tip, qPoint, tipIndex] using
      visible.boundary_inter
  have hDleft : Dreal ⊆ L := by
    intro x hx
    have hxBoth : x ∈ L ∩ R := by
      rw [hboundaryInter]
      exact hx
    exact hxBoth.1
  have hDright : Dreal ⊆ R := by
    intro x hx
    have hxBoth : x ∈ L ∩ R := by
      rw [hboundaryInter]
      exact hx
    exact hxBoth.2
  have hfillUnion :
      FilledRegion.fill P =
        FilledRegion.fill L ∪ FilledRegion.fill R := by
    simpa [P, L, R, front, back, DiskData.region] using
      VisibleDisk.parentRegion_eq_union
        hn v hsimple M hvertices htriangle visible hq
          hfront hback frontData backData
  have hfillInter :
      FilledRegion.fill L ∩ FilledRegion.fill R =
        Dreal := by
    simpa [L, R, Dreal, front, back, tip,
      qPoint, tipIndex, DiskData.region] using
      VisibleFillIntersection.childFills_inter
        hn v hsimple M hvertices htriangle visible hq
          hfront hback frontData backData
  have hcore :
      inside P =
          (inside L ∪ inside R) ∪
            openSegment ℝ tip qPoint ∧
        Disjoint (inside L) (inside R) :=
    FillSplit.inside_partition_and_disjoint
      htipq hchildren houter rfl hDleft hDright
        hfillUnion hfillInter
  have hseam :
      Disjoint
        (inside L ∪ inside R)
        (openSegment ℝ tip qPoint) :=
    FillSplit.inside_union_disjoint_openSegment
      (D := Dreal) rfl hDleft hDright
  have harea :
      area ((latPoly v).boundary (R := ℝ)) =
        area ((latPoly front).boundary (R := ℝ)) +
          area ((latPoly back).boundary (R := ℝ)) := by
    apply
      Split.area_add_of_inside_partition
        v front back (openSegment ℝ tip qPoint)
    · simpa [P, L, R] using hcore.1
    · simpa [L, R] using hcore.2
    · simpa [L, R] using hseam
    · exact
        Diagonal.measurableSet_openSegment_real htipq
    · exact Diagonal.volume_openSegment_real _ _
  have hinterior :
      Split.interiorLatticeSet v =
        (Split.interiorLatticeSet front ∪
          Split.interiorLatticeSet back) ∪
            diagonalInterior := by
    unfold Split.interiorLatticeSet diagonalInterior
      Diagonal.openLatticeSegment
    change
      toPlane ⁻¹' inside P =
        (toPlane ⁻¹' inside L ∪
          toPlane ⁻¹' inside R) ∪
            toPlane ⁻¹' openSegment ℝ tip qPoint
    rw [hcore.1, Set.preimage_union,
      Set.preimage_union]
  have hinteriorLeftRight :
      Disjoint
        (Split.interiorLatticeSet front)
        (Split.interiorLatticeSet back) := by
    rw [Set.disjoint_left]
    intro z hzFront hzBack
    exact
      Set.disjoint_left.mp hcore.2 hzFront hzBack
  have hinteriorDiagonal :
      Disjoint
        (Split.interiorLatticeSet front ∪
          Split.interiorLatticeSet back)
        diagonalInterior := by
    rw [Set.disjoint_left]
    intro z hzChildren hzDiagonal
    exact
      Set.disjoint_left.mp hseam
        hzChildren hzDiagonal
  have hboundary :
      Split.boundaryLatticeSet front ∪
          Split.boundaryLatticeSet back =
        Split.boundaryLatticeSet v ∪ diagonal := by
    unfold Split.boundaryLatticeSet diagonal
      Diagonal.closedLatticeSegment
    change
      toPlane ⁻¹' (L ∪ R) =
        toPlane ⁻¹' (P ∪ Dreal)
    rw [hchildren]
  have hboundaryInter' :
      Split.boundaryLatticeSet front ∩
          Split.boundaryLatticeSet back =
        diagonal := by
    unfold Split.boundaryLatticeSet diagonal
      Diagonal.closedLatticeSegment
    change
      toPlane ⁻¹' (L ∩ R) =
        toPlane ⁻¹' Dreal
    rw [hboundaryInter]
  have houterSet :
      Split.boundaryLatticeSet v ∩ diagonal =
        {v tipIndex, v visible.q} := by
    unfold Split.boundaryLatticeSet diagonal
      Diagonal.closedLatticeSegment
    change
      toPlane ⁻¹' (P ∩ Dreal) =
        {v tipIndex, v visible.q}
    rw [houter]
    simpa [tip, qPoint] using
      EarRemoval.preimage_toPlane_pair
        (v tipIndex) (v visible.q)
  have hboundaryEndpoints :
      (Split.boundaryLatticeSet v ∩ diagonal).ncard = 2 := by
    rw [houterSet]
    simp [hv]
  apply
    Split.glueDecompositions v front back
      diagonal diagonalInterior harea hinterior
        hinteriorLeftRight hinteriorDiagonal
  · exact Diagonal.finite_openLatticeSegment _ _
  · exact Diagonal.ncard_open_add_two hv
  · exact hboundary
  · exact hboundaryInter'
  · exact hboundaryEndpoints
  · exact Diagonal.finite_closedLatticeSegment _ _
  · exact frontDecomposition
  · exact backDecomposition

end Submission.VisibleDecomposition
