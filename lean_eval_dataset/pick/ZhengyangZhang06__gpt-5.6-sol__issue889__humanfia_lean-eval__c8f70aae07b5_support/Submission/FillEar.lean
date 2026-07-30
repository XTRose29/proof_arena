import Submission.FilledRegion
import Submission.CleanEar

open LeanEval.Geometry.PicksTheorem

namespace Submission.FillEar

/-- The prospective diagonal is an edge of the ear triangle. -/
theorem diagonal_subset_triangleBoundary
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    CleanEar.diagonal hn v ⊆
      (latPoly (EarRemoval.earTriangle hn v)).boundary
        (R := ℝ) := by
  intro x hx
  rw [Polygon.boundary]
  refine Set.mem_iUnion.mpr ⟨(2 : Fin 3), ?_⟩
  rw [EarRemoval.ear_edge_two hn v]
  exact hx

/-- The prospective diagonal is also the initial edge of the reduced
polygon. -/
theorem diagonal_subset_reducedBoundary
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    CleanEar.diagonal hn v ⊆
      (latPoly (EarRemoval.removeSecond v)).boundary
        (R := ℝ) := by
  intro x hx
  rw [Polygon.boundary]
  refine
    Set.mem_iUnion.mpr
      ⟨(⟨0, by omega⟩ : Fin n), ?_⟩
  rw [EarRemoval.reduced_edge_zero hn v]
  exact hx

/-- A point of a clean diagonal away from the parent boundary lies on its
relative interior. -/
theorem mem_openDiagonal_of_mem_diagonal_of_notMem_parent
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (houter :
      (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v =
        {toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)})
    {x : ℝ × ℝ}
    (hxDiagonal : x ∈ CleanEar.diagonal hn v)
    (hxParent : x ∉ (latPoly v).boundary (R := ℝ)) :
    x ∈ openSegment ℝ (toPlane (v 0))
      (toPlane (v ⟨2, by omega⟩)) := by
  have hindices :
      (0 : Fin (n + 1)) ≠
        (⟨2, by omega⟩ : Fin (n + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero] at hval
    omega
  have hvertices :
      v 0 ≠ v ⟨2, by omega⟩ :=
    (Helpers.lattice_vertex_injective_of_isSimple hsimple).ne
      hindices
  have hverticesPlane :
      toPlane (v 0) ≠
        toPlane (v ⟨2, by omega⟩) := by
    intro h
    exact
      hvertices
        (LatticeTriangle.toPlaneIntLinear_injective h)
  rw [Diagonal.openSegment_eq_segment_sdiff hverticesPlane]
  refine ⟨hxDiagonal, ?_⟩
  intro hxEndpoints
  have hxInter :
      x ∈
        (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v := by
    rw [houter]
    exact hxEndpoints
  exact hxParent hxInter.1

/-- A point of the open prospective diagonal is off the parent boundary
when the diagonal is clean. -/
theorem openDiagonal_disjoint_parent
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (houter :
      (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v =
        {toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)}) :
    Disjoint
      (openSegment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩)))
      ((latPoly v).boundary (R := ℝ)) := by
  have hindices :
      (0 : Fin (n + 1)) ≠
        (⟨2, by omega⟩ : Fin (n + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero] at hval
    omega
  have hvertices :
      v 0 ≠ v ⟨2, by omega⟩ :=
    (Helpers.lattice_vertex_injective_of_isSimple hsimple).ne
      hindices
  have hverticesPlane :
      toPlane (v 0) ≠
        toPlane (v ⟨2, by omega⟩) := by
    intro h
    exact
      hvertices
        (LatticeTriangle.toPlaneIntLinear_injective h)
  rw [Set.disjoint_left]
  intro x hxOpen hxParent
  have hxDiagonal :
      x ∈ CleanEar.diagonal hn v :=
    openSegment_subset_segment ℝ _ _ hxOpen
  have hxEndpoints :
      x ∈
        ({toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)} :
          Set (ℝ × ℝ)) := by
    rw [← houter]
    exact ⟨hxParent, hxDiagonal⟩
  rw [Diagonal.openSegment_eq_segment_sdiff hverticesPlane]
    at hxOpen
  exact hxOpen.2 hxEndpoints

/-- Filled-set gluing is sufficient for the exact bounded-component ear
certificate.  This packages the remaining topology as two closed-region
equalities: the parent fill is the union of the child fills, and the child
fills meet precisely on their common diagonal. -/
theorem coreIsEarAtOne_of_fill_gluing
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (houter :
      (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v =
        {toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)})
    (hfillUnion :
      FilledRegion.fill
          ((latPoly v).boundary (R := ℝ)) =
        FilledRegion.fill
            ((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ)) ∪
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)))
    (hfillInter :
      FilledRegion.fill
            ((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ)) ∩
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)) =
        CleanEar.diagonal hn v) :
    CleanEar.CoreIsEarAtOne hn v := by
  let parentBoundary :=
    (latPoly v).boundary (R := ℝ)
  let triangleBoundary :=
    (latPoly (EarRemoval.earTriangle hn v)).boundary
      (R := ℝ)
  let reducedBoundary :=
    (latPoly (EarRemoval.removeSecond v)).boundary
      (R := ℝ)
  let diagonal :=
    CleanEar.diagonal hn v
  let openDiagonal :=
    openSegment ℝ (toPlane (v 0))
      (toPlane (v ⟨2, by omega⟩))
  have hchildren :
      triangleBoundary ∪ reducedBoundary =
        parentBoundary ∪ diagonal := by
    exact EarRemoval.child_boundaries_union hn v
  have htriangleSubset :
      triangleBoundary ⊆ parentBoundary ∪ diagonal := by
    intro x hx
    rw [← hchildren]
    exact Or.inl hx
  have hreducedSubset :
      reducedBoundary ⊆ parentBoundary ∪ diagonal := by
    intro x hx
    rw [← hchildren]
    exact Or.inr hx
  have hdiagonalTriangle :
      diagonal ⊆ triangleBoundary :=
    diagonal_subset_triangleBoundary hn v
  have hdiagonalReduced :
      diagonal ⊆ reducedBoundary :=
    diagonal_subset_reducedBoundary hn v
  have hopenParent :
      Disjoint openDiagonal parentBoundary := by
    exact
      openDiagonal_disjoint_parent hn v hsimple houter
  refine ⟨?_, ?_⟩
  · change
      inside parentBoundary =
        (inside triangleBoundary ∪
          inside reducedBoundary) ∪ openDiagonal
    ext x
    constructor
    · intro hxParentInside
      have hxParentFill :
          x ∈ FilledRegion.fill parentBoundary :=
        Or.inr hxParentInside
      rw [hfillUnion] at hxParentFill
      rcases hxParentFill with hxTriangleFill | hxReducedFill
      · rcases hxTriangleFill with
          hxTriangleBoundary | hxTriangleInside
        · rcases htriangleSubset hxTriangleBoundary with
            hxParentBoundary | hxDiagonal
          · exact False.elim (hxParentInside.1 hxParentBoundary)
          · exact Or.inr <|
              mem_openDiagonal_of_mem_diagonal_of_notMem_parent
                hn v hsimple houter hxDiagonal
                  hxParentInside.1
        · exact Or.inl (Or.inl hxTriangleInside)
      · rcases hxReducedFill with
          hxReducedBoundary | hxReducedInside
        · rcases hreducedSubset hxReducedBoundary with
            hxParentBoundary | hxDiagonal
          · exact False.elim (hxParentInside.1 hxParentBoundary)
          · exact Or.inr <|
              mem_openDiagonal_of_mem_diagonal_of_notMem_parent
                hn v hsimple houter hxDiagonal
                  hxParentInside.1
        · exact Or.inl (Or.inr hxReducedInside)
    · rintro ((hxTriangleInside | hxReducedInside) | hxOpen)
      · have hxNotParent : x ∉ parentBoundary := by
          intro hxParentBoundary
          have hxChildren :
              x ∈ triangleBoundary ∪ reducedBoundary := by
            rw [hchildren]
            exact Or.inl hxParentBoundary
          rcases hxChildren with
            hxTriangleBoundary | hxReducedBoundary
          · exact hxTriangleInside.1 hxTriangleBoundary
          · have hxBoth :
                x ∈
                  FilledRegion.fill triangleBoundary ∩
                    FilledRegion.fill reducedBoundary :=
              ⟨Or.inr hxTriangleInside,
                Or.inl hxReducedBoundary⟩
            rw [hfillInter] at hxBoth
            exact
              hxTriangleInside.1
                (hdiagonalTriangle hxBoth)
        have hxParentFill :
            x ∈ FilledRegion.fill parentBoundary := by
          rw [hfillUnion]
          exact Or.inl (Or.inr hxTriangleInside)
        rcases hxParentFill with
          hxParentBoundary | hxParentInside
        · exact False.elim (hxNotParent hxParentBoundary)
        · exact hxParentInside
      · have hxNotParent : x ∉ parentBoundary := by
          intro hxParentBoundary
          have hxChildren :
              x ∈ triangleBoundary ∪ reducedBoundary := by
            rw [hchildren]
            exact Or.inl hxParentBoundary
          rcases hxChildren with
            hxTriangleBoundary | hxReducedBoundary
          · have hxBoth :
                x ∈
                  FilledRegion.fill triangleBoundary ∩
                    FilledRegion.fill reducedBoundary :=
              ⟨Or.inl hxTriangleBoundary,
                Or.inr hxReducedInside⟩
            rw [hfillInter] at hxBoth
            exact
              hxReducedInside.1
                (hdiagonalReduced hxBoth)
          · exact hxReducedInside.1 hxReducedBoundary
        have hxParentFill :
            x ∈ FilledRegion.fill parentBoundary := by
          rw [hfillUnion]
          exact Or.inr (Or.inr hxReducedInside)
        rcases hxParentFill with
          hxParentBoundary | hxParentInside
        · exact False.elim (hxNotParent hxParentBoundary)
        · exact hxParentInside
      · have hxNotParent : x ∉ parentBoundary :=
          Set.disjoint_left.mp hopenParent hxOpen
        have hxDiagonal : x ∈ diagonal :=
          openSegment_subset_segment ℝ _ _ hxOpen
        have hxParentFill :
            x ∈ FilledRegion.fill parentBoundary := by
          rw [hfillUnion]
          exact
            Or.inl
              (Or.inl (hdiagonalTriangle hxDiagonal))
        rcases hxParentFill with
          hxParentBoundary | hxParentInside
        · exact False.elim (hxNotParent hxParentBoundary)
        · exact hxParentInside
  · rw [Set.disjoint_left]
    intro x hxTriangleInside hxReducedInside
    have hxBoth :
        x ∈
          FilledRegion.fill triangleBoundary ∩
            FilledRegion.fill reducedBoundary :=
      ⟨Or.inr hxTriangleInside,
        Or.inr hxReducedInside⟩
    rw [hfillInter] at hxBoth
    exact
      hxTriangleInside.1
        (hdiagonalTriangle hxBoth)

end Submission.FillEar
