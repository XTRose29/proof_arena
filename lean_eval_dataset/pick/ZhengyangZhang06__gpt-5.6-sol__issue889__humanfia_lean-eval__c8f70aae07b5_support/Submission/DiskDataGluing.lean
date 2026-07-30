import Submission.DiskData
import Submission.FillFrontier

open LeanEval.Geometry.PicksTheorem

namespace Submission.DiskDataGluing

/-- Attachability of an inherited edge composes across an exact child seam. -/
theorem edgeAttachable_union_of_left
    {A B D E : Set (ℝ × ℝ)}
    (hattachA : DiskGluing.EdgeAttachable A E)
    (hattachB : DiskGluing.EdgeAttachable B D)
    (hAclosed : IsClosed A)
    (hinter : A ∩ B = D)
    (hEsubsetA : E ⊆ A) :
    DiskGluing.EdgeAttachable (A ∪ B) E := by
  apply
    DiskGluing.EdgeAttachable.union_of_left
      hattachA hattachB hAclosed hinter hEsubsetA
  rintro x ⟨hxE, hxB⟩
  have hxBoth : x ∈ A ∩ B :=
    ⟨hEsubsetA hxE, hxB⟩
  rwa [hinter] at hxBoth

/-- If the parent boundary differs from the two free child boundaries only
at the endpoints of their common seam, and those endpoints are limit points
of the free boundaries, then the whole parent boundary is in their closure. -/
theorem parent_subset_closure_free
    {P L R D : Set (ℝ × ℝ)}
    {a b : ℝ × ℝ}
    (hunion : L ∪ R = P ∪ D)
    (hinter : P ∩ D = {a, b})
    (ha :
      a ∈ closure ((L \ D) ∪ (R \ D)))
    (hb :
      b ∈ closure ((L \ D) ∪ (R \ D))) :
    P ⊆ closure ((L \ D) ∪ (R \ D)) := by
  intro x hxP
  by_cases hxD : x ∈ D
  · have hx : x ∈ P ∩ D := ⟨hxP, hxD⟩
    rw [hinter] at hx
    rcases hx with hxa | hxb
    · subst x
      exact ha
    · have hxb' : x = b :=
        Set.mem_singleton_iff.mp hxb
      subst x
      exact hb
  · apply subset_closure
    have hxChildren : x ∈ L ∪ R := by
      rw [hunion]
      exact Or.inl hxP
    rcases hxChildren with hxL | hxR
    · exact Or.inl ⟨hxL, hxD⟩
    · exact Or.inr ⟨hxR, hxD⟩

/-- Disk data is preserved by an exact two-child gluing once the parent fill,
one interior seam point, density of the free child boundaries, and
attachability of the inherited parent edges have been established. -/
theorem holds_of_gluing
    {n leftSize rightSize : ℕ}
    (v : Fin n → ℤ × ℤ)
    (left : Fin leftSize → ℤ × ℤ)
    (right : Fin rightSize → ℤ × ℤ)
    (D : Set (ℝ × ℝ))
    (leftData : DiskData.Holds left)
    (rightData : DiskData.Holds right)
    (hinter :
      DiskData.region left ∩ DiskData.region right = D)
    (hunion :
      DiskData.region v =
        DiskData.region left ∪ DiskData.region right)
    (hseamPoint :
      ∃ p,
        p ∈ DiskData.region left ∧
          p ∈ DiskData.region right ∧
            p ∈
              interior
                (DiskData.region left ∪
                  DiskData.region right))
    (hdense :
      (latPoly v).boundary (R := ℝ) ⊆
        closure
          (((latPoly left).boundary (R := ℝ) \ D) ∪
            ((latPoly right).boundary (R := ℝ) \ D)))
    (hedges :
      ∀ i : Fin n,
        DiskGluing.EdgeAttachable
          (DiskData.region left ∪ DiskData.region right)
          ((latPoly v).edgeSet ℝ i)) :
    DiskData.Holds v := by
  let A := DiskData.region left
  let B := DiskData.region right
  let L := (latPoly left).boundary (R := ℝ)
  let R := (latPoly right).boundary (R := ℝ)
  have hAclosed : IsClosed A := by
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary (latPoly left)).isClosed
  have hBclosed : IsClosed B := by
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary (latPoly right)).isClosed
  have hfreeFrontier :
      (L \ D) ∪ (R \ D) ⊆ frontier (A ∪ B) := by
    rintro x (hxL | hxR)
    · have hxFrontierA : x ∈ frontier A := by
        rw [← leftData.boundary_eq_frontier]
        exact hxL.1
      have hxNotB : x ∉ B := by
        intro hxB
        have hxBoth : x ∈ A ∩ B :=
          ⟨hAclosed.frontier_subset hxFrontierA, hxB⟩
        rw [hinter] at hxBoth
        exact hxL.2 hxBoth
      exact
        DiskGluing.mem_frontier_union_of_notMem_right
          hAclosed hBclosed hxFrontierA hxNotB
    · have hxFrontierB : x ∈ frontier B := by
        rw [← rightData.boundary_eq_frontier]
        exact hxR.1
      have hxNotA : x ∉ A := by
        intro hxA
        have hxBoth : x ∈ A ∩ B :=
          ⟨hxA, hBclosed.frontier_subset hxFrontierB⟩
        rw [hinter] at hxBoth
        exact hxR.2 hxBoth
      simpa [Set.union_comm] using
        DiskGluing.mem_frontier_union_of_notMem_right
          hBclosed hAclosed hxFrontierB hxNotA
  refine
    { regular := ?_
      interiorPreconnected := ?_
      boundary_eq_frontier := ?_
      edgeAttachable := ?_ }
  · rw [hunion]
    exact
      FillFrontier.closure_interior_union_eq
        hAclosed hBclosed leftData.regular rightData.regular
  · obtain ⟨p, hpA, hpB, hpInterior⟩ := hseamPoint
    rw [hunion]
    exact
      DiskGluing.isPreconnected_interior_union
        leftData.regular rightData.regular
        leftData.interiorPreconnected
        rightData.interiorPreconnected
        hpA hpB hpInterior
  · apply Set.Subset.antisymm
    · intro x hxParent
      have hxClosure :
          x ∈ closure ((L \ D) ∪ (R \ D)) := by
        exact hdense hxParent
      rw [hunion]
      exact
        closure_minimal hfreeFrontier isClosed_frontier
          hxClosure
    · intro x hxFrontier
      change
        x ∈
          frontier
            (FilledRegion.fill
              ((latPoly v).boundary (R := ℝ))) at hxFrontier
      exact
        FilledRegion.frontier_fill_subset
          (Helpers.isCompact_boundary
            (latPoly v)).isClosed hxFrontier
  · intro i
    rw [hunion]
    exact hedges i

end Submission.DiskDataGluing
