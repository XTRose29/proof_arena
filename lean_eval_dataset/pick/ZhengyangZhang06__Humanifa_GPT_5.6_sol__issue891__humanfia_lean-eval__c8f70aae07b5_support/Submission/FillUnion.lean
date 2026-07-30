import Submission.FilledRegion

namespace Submission.FillUnion

/-- A set with one preconnected unbounded complement component has no
bounded complementary components. -/
theorem inside_eq_empty_of_compl_preconnected
    {K : Set (ℝ × ℝ)}
    (hpreconnected : IsPreconnected Kᶜ)
    (hunbounded : ¬ Bornology.IsBounded Kᶜ) :
    LeanEval.Geometry.PicksTheorem.inside K = ∅ := by
  apply Set.Subset.antisymm
  · intro x hxInside
    have hcomponent :
        Kᶜ ⊆ connectedComponentIn Kᶜ x :=
      hpreconnected.subset_connectedComponentIn
        hxInside.1 (Set.Subset.refl _)
    exact
      hunbounded
        (hxInside.2.subset hcomponent)
  · exact Set.empty_subset _

/-- Under the same hypotheses, filling does not enlarge the set. -/
theorem fill_eq_self_of_compl_preconnected
    {K : Set (ℝ × ℝ)}
    (hpreconnected : IsPreconnected Kᶜ)
    (hunbounded : ¬ Bornology.IsBounded Kᶜ) :
    FilledRegion.fill K = K := by
  change
    K ∪ LeanEval.Geometry.PicksTheorem.inside K = K
  rw [inside_eq_empty_of_compl_preconnected
    hpreconnected hunbounded, Set.union_empty]

/-- The complement of a bounded subset of the real plane is unbounded. -/
theorem compl_unbounded_of_isBounded
    {K : Set (ℝ × ℝ)}
    (hK : Bornology.IsBounded K) :
    ¬ Bornology.IsBounded Kᶜ := by
  intro hcompl
  apply NormedSpace.unbounded_univ ℝ (ℝ × ℝ)
  rw [← Set.union_compl_self K]
  exact hK.union hcompl

/-- Let two filled child regions have a preconnected unbounded exterior.
If their boundary union is obtained by adding a diagonal already contained
in the parent's fill, their union is exactly the parent fill. -/
theorem parentFill_eq_childFill_union
    {P A B D : Set (ℝ × ℝ)}
    (hPbounded : Bornology.IsBounded P)
    (hboundaryUnion : A ∪ B = P ∪ D)
    (hdiagonal : D ⊆ FilledRegion.fill P)
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill A ∪
          FilledRegion.fill B)ᶜ)
    (hcomplUnbounded :
      ¬ Bornology.IsBounded
        (FilledRegion.fill A ∪
          FilledRegion.fill B)ᶜ) :
    FilledRegion.fill P =
      FilledRegion.fill A ∪
        FilledRegion.fill B := by
  let K :=
    FilledRegion.fill A ∪
      FilledRegion.fill B
  have hPsubsetK : P ⊆ K := by
    intro x hxP
    have hxChildren : x ∈ A ∪ B := by
      rw [hboundaryUnion]
      exact Or.inl hxP
    rcases hxChildren with hxA | hxB
    · exact Or.inl (Or.inl hxA)
    · exact Or.inr (Or.inl hxB)
  have haddedFill :
      FilledRegion.fill (P ∪ D) =
        FilledRegion.fill P :=
    FilledRegion.fill_union_eq_fill
      hPbounded hdiagonal
  have hKsubsetParent : K ⊆ FilledRegion.fill P := by
    rintro x (hxA | hxB)
    · have hxAdded :
          x ∈ FilledRegion.fill (P ∪ D) := by
        apply
          FilledRegion.fill_mono
            (S := A) (T := P ∪ D)
        · rw [← hboundaryUnion]
          exact Set.subset_union_left
        · exact hxA
      rw [haddedFill] at hxAdded
      exact hxAdded
    · have hxAdded :
          x ∈ FilledRegion.fill (P ∪ D) := by
        apply
          FilledRegion.fill_mono
            (S := B) (T := P ∪ D)
        · rw [← hboundaryUnion]
          exact Set.subset_union_right
        · exact hxB
      rw [haddedFill] at hxAdded
      exact hxAdded
  have hfillK :
      FilledRegion.fill K =
        FilledRegion.fill P :=
    FilledRegion.fill_eq_of_subset_of_subset_fill
      hPbounded hPsubsetK hKsubsetParent
  have hKfixed :
      FilledRegion.fill K = K :=
    fill_eq_self_of_compl_preconnected
      (by simpa [K] using hcomplPreconnected)
      (by simpa [K] using hcomplUnbounded)
  rw [hKfixed] at hfillK
  exact hfillK.symm

/-- Bounded child obstacles make the unbounded-exterior hypothesis in the
preceding theorem automatic. -/
theorem parentFill_eq_childFill_union_of_bounded
    {P A B D : Set (ℝ × ℝ)}
    (hPbounded : Bornology.IsBounded P)
    (hAbounded : Bornology.IsBounded A)
    (hBbounded : Bornology.IsBounded B)
    (hboundaryUnion : A ∪ B = P ∪ D)
    (hdiagonal : D ⊆ FilledRegion.fill P)
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill A ∪
          FilledRegion.fill B)ᶜ) :
    FilledRegion.fill P =
      FilledRegion.fill A ∪
        FilledRegion.fill B := by
  apply parentFill_eq_childFill_union
    hPbounded hboundaryUnion hdiagonal
      hcomplPreconnected
  exact
    compl_unbounded_of_isBounded <|
      (FilledRegion.isBounded_fill hAbounded).union
        (FilledRegion.isBounded_fill hBbounded)

end Submission.FillUnion
