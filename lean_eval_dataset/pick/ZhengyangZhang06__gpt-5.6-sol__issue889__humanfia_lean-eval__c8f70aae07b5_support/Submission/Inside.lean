import Submission.Helpers

open LeanEval.Geometry.PicksTheorem

namespace Submission.Inside

/-- The union of the unbounded connected components of an obstacle's
complement. -/
def unboundedOutside (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x |
    x ∉ S ∧
      ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- The complement of an obstacle is partitioned according to whether the
component of a point is bounded or unbounded. -/
theorem compl_eq_inside_union_unboundedOutside
    (S : Set (ℝ × ℝ)) :
    Sᶜ = inside S ∪ unboundedOutside S := by
  ext x
  constructor
  · intro hxCompl
    by_cases hbounded :
        Bornology.IsBounded (connectedComponentIn Sᶜ x)
    · exact Or.inl ⟨hxCompl, hbounded⟩
    · exact Or.inr ⟨hxCompl, hbounded⟩
  · rintro (hxInside | hxOutside)
    · exact hxInside.1
    · exact hxOutside.1

/-- Bounded and unbounded complement components are disjoint. -/
theorem inside_disjoint_unboundedOutside
    (S : Set (ℝ × ℝ)) :
    Disjoint (inside S) (unboundedOutside S) := by
  rw [Set.disjoint_left]
  intro x hxInside hxOutside
  exact hxOutside.2 hxInside.2

/-- For a closed obstacle, its unbounded-component region is open. -/
theorem isOpen_unboundedOutside_of_isClosed
    {S : Set (ℝ × ℝ)} (hS : IsClosed S) :
    IsOpen (unboundedOutside S) := by
  rw [isOpen_iff_mem_nhds]
  intro x hxOutside
  change
    x ∉ S ∧
      ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x)
    at hxOutside
  have hxCompl : x ∈ Sᶜ :=
    hxOutside.1
  have hxComponent :
      x ∈ connectedComponentIn Sᶜ x :=
    mem_connectedComponentIn hxCompl
  refine Filter.mem_of_superset
    (hS.isOpen_compl.connectedComponentIn.mem_nhds
      hxComponent) ?_
  intro y hy
  change
    y ∉ S ∧
      ¬ Bornology.IsBounded (connectedComponentIn Sᶜ y)
  have hyCompl : y ∈ Sᶜ :=
    connectedComponentIn_subset Sᶜ x hy
  refine ⟨hyCompl, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hxOutside.2

/-- An unbounded outside component itself is a canonical escape witness for
each of its points. -/
theorem exists_unbounded_escape_of_mem_unboundedOutside
    {S : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    (hx : x ∈ unboundedOutside S) :
    ∃ W : Set (ℝ × ℝ),
      x ∈ W ∧
        IsPreconnected W ∧
        W ⊆ Sᶜ ∧
        ¬ Bornology.IsBounded W := by
  exact
    ⟨connectedComponentIn Sᶜ x,
      mem_connectedComponentIn hx.1,
      isPreconnected_connectedComponentIn,
      connectedComponentIn_subset Sᶜ x,
      hx.2⟩

/-- An unbounded preconnected subset of the complement witnesses that its
base point lies in an unbounded complement component. -/
theorem not_mem_inside_of_unbounded_preconnected
    {S W : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    (hxW : x ∈ W)
    (hWpreconnected : IsPreconnected W)
    (hWcompl : W ⊆ Sᶜ)
    (hWunbounded : ¬ Bornology.IsBounded W) :
    x ∉ inside S := by
  intro hxInside
  change
    x ∉ S ∧
      Bornology.IsBounded (connectedComponentIn Sᶜ x)
    at hxInside
  have hWcomponent :
      W ⊆ connectedComponentIn Sᶜ x :=
    hWpreconnected.subset_connectedComponentIn hxW hWcompl
  exact
    hWunbounded
      (hxInside.2.subset hWcomponent)

/-- Characterize the bounded side of an obstacle from an open partition of
its complement.  The first side is uniformly bounded; every point of the
second side has an explicit unbounded preconnected escape set. -/
theorem inside_eq_of_open_partition
    {S boundedSide unboundedSide : Set (ℝ × ℝ)}
    (hpartition : Sᶜ = boundedSide ∪ unboundedSide)
    (hboundedOpen : IsOpen boundedSide)
    (hunboundedOpen : IsOpen unboundedSide)
    (hsidesDisjoint : Disjoint boundedSide unboundedSide)
    (hbounded : Bornology.IsBounded boundedSide)
    (hescape :
      ∀ x ∈ unboundedSide,
        ∃ W : Set (ℝ × ℝ),
          x ∈ W ∧
            IsPreconnected W ∧
            W ⊆ Sᶜ ∧
            ¬ Bornology.IsBounded W) :
    inside S = boundedSide := by
  ext x
  constructor
  · intro hxInside
    change
      x ∉ S ∧
        Bornology.IsBounded (connectedComponentIn Sᶜ x)
      at hxInside
    have hxPartition : x ∈ boundedSide ∪ unboundedSide := by
      rw [← hpartition]
      exact hxInside.1
    rcases hxPartition with hxBounded | hxUnbounded
    · exact hxBounded
    · obtain
        ⟨W, hxW, hWpreconnected, hWcompl, hWunbounded⟩ :=
          hescape x hxUnbounded
      exact False.elim <|
        not_mem_inside_of_unbounded_preconnected
          hxW hWpreconnected hWcompl hWunbounded hxInside
  · intro hxBounded
    have hxCompl : x ∈ Sᶜ := by
      rw [hpartition]
      exact Or.inl hxBounded
    refine ⟨hxCompl, ?_⟩
    apply hbounded.subset
    apply
      isPreconnected_connectedComponentIn.subset_left_of_subset_union
        hboundedOpen hunboundedOpen hsidesDisjoint
    · rw [← hpartition]
      exact connectedComponentIn_subset Sᶜ x
    · exact
        ⟨x, mem_connectedComponentIn hxCompl, hxBounded⟩

/-- To prove two `inside` regions disjoint, it suffices to give every point
of the first region an unbounded preconnected escape set avoiding the second
boundary. -/
theorem disjoint_inside_of_unbounded_witness
    {A B : Set (ℝ × ℝ)}
    (hescape :
      ∀ x ∈ inside A,
        ∃ W : Set (ℝ × ℝ),
          x ∈ W ∧
            IsPreconnected W ∧
            W ⊆ Bᶜ ∧
            ¬ Bornology.IsBounded W) :
    Disjoint (inside A) (inside B) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  obtain
    ⟨W, hxW, hWpreconnected, hWcompl, hWunbounded⟩ :=
      hescape x hxA
  exact
    not_mem_inside_of_unbounded_preconnected
      hxW hWpreconnected hWcompl hWunbounded hxB

end Submission.Inside
