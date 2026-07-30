import Submission.FilledRegion
import Submission.Diagonal

open LeanEval.Geometry.PicksTheorem

namespace Submission.FillSplit

/-- Filled-set union and intersection data recover the exact bounded-component
partition for any clean two-child chord split. -/
theorem inside_partition_and_disjoint
    {P L R D : Set (ℝ × ℝ)}
    {a b : ℝ × ℝ}
    (hab : a ≠ b)
    (hchildren : L ∪ R = P ∪ D)
    (houter : P ∩ D = {a, b})
    (hD : D = segment ℝ a b)
    (hDleft : D ⊆ L)
    (hDright : D ⊆ R)
    (hfillUnion :
      FilledRegion.fill P =
        FilledRegion.fill L ∪ FilledRegion.fill R)
    (hfillInter :
      FilledRegion.fill L ∩ FilledRegion.fill R = D) :
    inside P =
        (inside L ∪ inside R) ∪
          openSegment ℝ a b ∧
      Disjoint (inside L) (inside R) := by
  have hleftSubset : L ⊆ P ∪ D := by
    intro x hx
    rw [← hchildren]
    exact Or.inl hx
  have hrightSubset : R ⊆ P ∪ D := by
    intro x hx
    rw [← hchildren]
    exact Or.inr hx
  have hopenParent :
      Disjoint (openSegment ℝ a b) P := by
    rw [Set.disjoint_left]
    intro x hxOpen hxP
    have hxD : x ∈ D := by
      rw [hD]
      exact
        openSegment_subset_segment ℝ a b hxOpen
    have hxEndpoints : x ∈ ({a, b} : Set (ℝ × ℝ)) := by
      rw [← houter]
      exact ⟨hxP, hxD⟩
    rw [Diagonal.openSegment_eq_segment_sdiff hab] at hxOpen
    exact hxOpen.2 hxEndpoints
  have mem_open_of_mem_D_of_not_mem_P :
      ∀ {x : ℝ × ℝ}, x ∈ D → x ∉ P →
        x ∈ openSegment ℝ a b := by
    intro x hxD hxP
    rw [Diagonal.openSegment_eq_segment_sdiff hab]
    constructor
    · rw [← hD]
      exact hxD
    · intro hxEndpoints
      have hxBoth : x ∈ P ∩ D := by
        rw [houter]
        exact hxEndpoints
      exact hxP hxBoth.1
  constructor
  · ext x
    constructor
    · intro hxParentInside
      have hxParentFill :
          x ∈ FilledRegion.fill P :=
        Or.inr hxParentInside
      rw [hfillUnion] at hxParentFill
      rcases hxParentFill with hxLeftFill | hxRightFill
      · rcases hxLeftFill with hxLeftBoundary | hxLeftInside
        · rcases hleftSubset hxLeftBoundary with
            hxParentBoundary | hxD
          · exact False.elim
              (hxParentInside.1 hxParentBoundary)
          · exact Or.inr <|
              mem_open_of_mem_D_of_not_mem_P
                hxD hxParentInside.1
        · exact Or.inl (Or.inl hxLeftInside)
      · rcases hxRightFill with hxRightBoundary | hxRightInside
        · rcases hrightSubset hxRightBoundary with
            hxParentBoundary | hxD
          · exact False.elim
              (hxParentInside.1 hxParentBoundary)
          · exact Or.inr <|
              mem_open_of_mem_D_of_not_mem_P
                hxD hxParentInside.1
        · exact Or.inl (Or.inr hxRightInside)
    · rintro ((hxLeftInside | hxRightInside) | hxOpen)
      · have hxNotParent : x ∉ P := by
          intro hxParentBoundary
          have hxChildren : x ∈ L ∪ R := by
            rw [hchildren]
            exact Or.inl hxParentBoundary
          rcases hxChildren with hxLeftBoundary | hxRightBoundary
          · exact hxLeftInside.1 hxLeftBoundary
          · have hxBoth :
                x ∈
                  FilledRegion.fill L ∩
                    FilledRegion.fill R :=
              ⟨Or.inr hxLeftInside,
                Or.inl hxRightBoundary⟩
            rw [hfillInter] at hxBoth
            exact hxLeftInside.1 (hDleft hxBoth)
        have hxParentFill :
            x ∈ FilledRegion.fill P := by
          rw [hfillUnion]
          exact Or.inl (Or.inr hxLeftInside)
        rcases hxParentFill with hxParentBoundary | hxParentInside
        · exact False.elim (hxNotParent hxParentBoundary)
        · exact hxParentInside
      · have hxNotParent : x ∉ P := by
          intro hxParentBoundary
          have hxChildren : x ∈ L ∪ R := by
            rw [hchildren]
            exact Or.inl hxParentBoundary
          rcases hxChildren with hxLeftBoundary | hxRightBoundary
          · have hxBoth :
                x ∈
                  FilledRegion.fill L ∩
                    FilledRegion.fill R :=
              ⟨Or.inl hxLeftBoundary,
                Or.inr hxRightInside⟩
            rw [hfillInter] at hxBoth
            exact hxRightInside.1 (hDright hxBoth)
          · exact hxRightInside.1 hxRightBoundary
        have hxParentFill :
            x ∈ FilledRegion.fill P := by
          rw [hfillUnion]
          exact Or.inr (Or.inr hxRightInside)
        rcases hxParentFill with hxParentBoundary | hxParentInside
        · exact False.elim (hxNotParent hxParentBoundary)
        · exact hxParentInside
      · have hxNotParent : x ∉ P :=
          Set.disjoint_left.mp hopenParent hxOpen
        have hxD : x ∈ D := by
          rw [hD]
          exact
            openSegment_subset_segment ℝ a b hxOpen
        have hxParentFill :
            x ∈ FilledRegion.fill P := by
          rw [hfillUnion]
          exact Or.inl (Or.inl (hDleft hxD))
        rcases hxParentFill with hxParentBoundary | hxParentInside
        · exact False.elim (hxNotParent hxParentBoundary)
        · exact hxParentInside
  · rw [Set.disjoint_left]
    intro x hxLeftInside hxRightInside
    have hxBoth :
        x ∈
          FilledRegion.fill L ∩
            FilledRegion.fill R :=
      ⟨Or.inr hxLeftInside, Or.inr hxRightInside⟩
    rw [hfillInter] at hxBoth
    exact hxLeftInside.1 (hDleft hxBoth)

/-- The child interiors are disjoint from the relative interior of their
common boundary chord. -/
theorem inside_union_disjoint_openSegment
    {L R D : Set (ℝ × ℝ)}
    {a b : ℝ × ℝ}
    (hD : D = segment ℝ a b)
    (hDleft : D ⊆ L)
    (hDright : D ⊆ R) :
    Disjoint
      (inside L ∪ inside R)
      (openSegment ℝ a b) := by
  rw [Set.disjoint_left]
  intro x hxInside hxOpen
  have hxD : x ∈ D := by
    rw [hD]
    exact openSegment_subset_segment ℝ a b hxOpen
  rcases hxInside with hxLeft | hxRight
  · exact hxLeft.1 (hDleft hxD)
  · exact hxRight.1 (hDright hxD)

end Submission.FillSplit
