import Submission.FillUnion

namespace Submission.FillFrontier

/-!
A compact region with one unbounded exterior is already the fill of any
intermediate obstacle between its frontier and the region itself.  For child
gluing this replaces a separate proof that the new diagonal lies in the
parent fill: it is enough to prove that the diagonal is not part of the
frontier of the glued child region.
-/

/-- Finite unions preserve the property of being the closure of their
ordinary interior. -/
theorem closure_interior_union_eq
    {A B : Set (ℝ × ℝ)}
    (hAclosed : IsClosed A)
    (hBclosed : IsClosed B)
    (hAregular : closure (interior A) = A)
    (hBregular : closure (interior B) = B) :
    closure (interior (A ∪ B)) = A ∪ B := by
  apply Set.Subset.antisymm
  · exact
      closure_minimal interior_subset
        (hAclosed.union hBclosed)
  · apply Set.union_subset
    · calc
        A = closure (interior A) := hAregular.symm
        _ ⊆ closure (interior (A ∪ B)) :=
          closure_mono <|
            interior_mono Set.subset_union_left
    · calc
        B = closure (interior B) := hBregular.symm
        _ ⊆ closure (interior (A ∪ B)) :=
          closure_mono <|
            interior_mono Set.subset_union_right

/-- A compact set with preconnected unbounded complement is the fill of its
frontier. -/
theorem fill_frontier_eq
    {K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K)
    (hKcomplPreconnected : IsPreconnected Kᶜ)
    (hKcomplUnbounded : ¬ Bornology.IsBounded Kᶜ) :
    FilledRegion.fill (frontier K) = K := by
  have hKclosed : IsClosed K :=
    hKcompact.isClosed
  unfold FilledRegion.fill
  rw [FilledRegion.inside_frontier_eq_interior
      hKcompact hKcomplPreconnected hKcomplUnbounded,
    Set.union_comm,
    ← closure_eq_interior_union_frontier,
    hKclosed.closure_eq]

/-- If `P` contains the frontier of such a compact region and is itself
contained in the region, then filling `P` recovers exactly that region. -/
theorem fill_eq_of_frontier_subset
    {P K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K)
    (hKcomplPreconnected : IsPreconnected Kᶜ)
    (hKcomplUnbounded : ¬ Bornology.IsBounded Kᶜ)
    (hfrontier : frontier K ⊆ P)
    (hPK : P ⊆ K) :
    FilledRegion.fill P = K := by
  have hKclosed : IsClosed K :=
    hKcompact.isClosed
  have hfrontierSubset : frontier K ⊆ K := by
    intro x hx
    have hxClosure : x ∈ closure K :=
      frontier_subset_closure hx
    rwa [hKclosed.closure_eq] at hxClosure
  have hfrontierBounded :
      Bornology.IsBounded (frontier K) :=
    hKcompact.isBounded.subset hfrontierSubset
  have hfillFrontier :
      FilledRegion.fill (frontier K) = K :=
    fill_frontier_eq hKcompact hKcomplPreconnected
      hKcomplUnbounded
  calc
    FilledRegion.fill P =
        FilledRegion.fill (frontier K) := by
      apply
        FilledRegion.fill_eq_of_subset_of_subset_fill
          hfrontierBounded hfrontier
      intro x hxP
      rw [hfillFrontier]
      exact hPK hxP
    _ = K := hfillFrontier

/-- The frontier of two filled children is contained in the parent boundary
once every non-parent point of the added seam is interior to their union. -/
theorem frontier_childFill_union_subset_parent
    {A B P D : Set (ℝ × ℝ)}
    (hAclosed : IsClosed A)
    (hBclosed : IsClosed B)
    (hboundaryUnion : A ∪ B = P ∪ D)
    (hseamInterior :
      D \ P ⊆
        interior
          (FilledRegion.fill A ∪
            FilledRegion.fill B)) :
    frontier
        (FilledRegion.fill A ∪
          FilledRegion.fill B) ⊆
      P := by
  intro x hxFrontier
  have hxChildFrontier :
      x ∈ frontier (FilledRegion.fill A) ∪
        frontier (FilledRegion.fill B) := by
    have hxDetailed :=
      frontier_union_subset
        (FilledRegion.fill A)
        (FilledRegion.fill B) hxFrontier
    rcases hxDetailed with hxA | hxB
    · exact Or.inl hxA.1
    · exact Or.inr hxB.2
  have hxChildren : x ∈ A ∪ B := by
    rcases hxChildFrontier with hxA | hxB
    · exact Or.inl <|
        FilledRegion.frontier_fill_subset hAclosed hxA
    · exact Or.inr <|
        FilledRegion.frontier_fill_subset hBclosed hxB
  have hxParentOrSeam : x ∈ P ∪ D := by
    rw [← hboundaryUnion]
    exact hxChildren
  rcases hxParentOrSeam with hxParent | hxSeam
  · exact hxParent
  · by_contra hxParent
    have hxInterior :
        x ∈
          interior
            (FilledRegion.fill A ∪
              FilledRegion.fill B) :=
      hseamInterior ⟨hxSeam, hxParent⟩
    exact
      Set.disjoint_left.mp disjoint_interior_frontier
        hxInterior hxFrontier

/-- A local seam-interior proof and a one-component exterior proof suffice
for the complete parent-fill equality. -/
theorem parentFill_eq_childFill_union
    {P A B D : Set (ℝ × ℝ)}
    (hAclosed : IsClosed A)
    (hBclosed : IsClosed B)
    (hAbounded : Bornology.IsBounded A)
    (hBbounded : Bornology.IsBounded B)
    (hboundaryUnion : A ∪ B = P ∪ D)
    (hseamInterior :
      D \ P ⊆
        interior
          (FilledRegion.fill A ∪
            FilledRegion.fill B))
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill A ∪
          FilledRegion.fill B)ᶜ) :
    FilledRegion.fill P =
      FilledRegion.fill A ∪
        FilledRegion.fill B := by
  let K :=
    FilledRegion.fill A ∪
      FilledRegion.fill B
  have hAcompact :
      IsCompact (FilledRegion.fill A) :=
    FilledRegion.isCompact_fill hAclosed hAbounded
  have hBcompact :
      IsCompact (FilledRegion.fill B) :=
    FilledRegion.isCompact_fill hBclosed hBbounded
  have hKcompact : IsCompact K := by
    exact hAcompact.union hBcompact
  have hKbounded : Bornology.IsBounded K :=
    hKcompact.isBounded
  have hKcomplUnbounded :
      ¬ Bornology.IsBounded Kᶜ :=
    FillUnion.compl_unbounded_of_isBounded hKbounded
  have hfrontier : frontier K ⊆ P := by
    exact
      frontier_childFill_union_subset_parent
        hAclosed hBclosed hboundaryUnion
        (by simpa [K] using hseamInterior)
  have hPK : P ⊆ K := by
    intro x hxP
    have hxChildren : x ∈ A ∪ B := by
      rw [hboundaryUnion]
      exact Or.inl hxP
    rcases hxChildren with hxA | hxB
    · exact Or.inl (Or.inl hxA)
    · exact Or.inr (Or.inl hxB)
  exact
    fill_eq_of_frontier_subset hKcompact
      (by simpa [K] using hcomplPreconnected)
      hKcomplUnbounded hfrontier hPK

end Submission.FillFrontier
