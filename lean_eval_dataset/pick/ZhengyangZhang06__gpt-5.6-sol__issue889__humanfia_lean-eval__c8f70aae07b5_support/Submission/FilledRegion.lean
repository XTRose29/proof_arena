import Submission.Exterior

open LeanEval.Geometry.PicksTheorem

namespace Submission.FilledRegion

/-- Fill every bounded component of a planar obstacle's complement. -/
def fill (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  S ∪ inside S

/-- The bounded-component interior is contained in the ordinary interior of
the fill. -/
theorem inside_subset_interior_fill
    {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) :
    inside S ⊆ interior (fill S) := by
  exact
    interior_maximal
      (fun _ hx => Or.inr hx)
      (Helpers.isOpen_inside_of_isClosed hS)

/-- For a closed obstacle, its bounded-component interior is precisely the
ordinary interior of the fill away from the obstacle itself. -/
theorem inside_eq_interior_fill_sdiff
    {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) :
    inside S = interior (fill S) \ S := by
  ext x
  constructor
  · intro hx
    exact
      ⟨inside_subset_interior_fill hS hx, hx.1⟩
  · rintro ⟨hxInterior, hxS⟩
    have hxFill : x ∈ fill S :=
      interior_subset hxInterior
    rcases hxFill with hxS' | hxInside
    · exact False.elim (hxS hxS')
    · exact hxInside

/-- Filling an obstacle leaves exactly its unbounded exterior as complement. -/
theorem compl_fill (S : Set (ℝ × ℝ)) :
    (fill S)ᶜ = Inside.unboundedOutside S := by
  ext x
  constructor
  · intro hx
    have hxS : x ∈ Sᶜ := by
      intro hxS
      exact hx (Or.inl hxS)
    have hxPartition :
        x ∈ inside S ∪ Inside.unboundedOutside S := by
      rw [← Inside.compl_eq_inside_union_unboundedOutside]
      exact hxS
    rcases hxPartition with hxInside | hxOutside
    · exact False.elim (hx (Or.inr hxInside))
    · exact hxOutside
  · intro hxOutside hxFill
    rcases hxFill with hxS | hxInside
    · exact hxOutside.1 hxS
    · exact
        (Set.disjoint_left.mp
          (Inside.inside_disjoint_unboundedOutside S))
          hxInside hxOutside

/-- The fill of a bounded obstacle is bounded. -/
theorem isBounded_fill
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (fill S) := by
  exact hS.union (Helpers.isBounded_inside_of_isBounded hS)

/-- The fill of a closed obstacle is closed. -/
theorem isClosed_fill
    {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) :
    IsClosed (fill S) := by
  rw [← isOpen_compl_iff, compl_fill]
  exact Inside.isOpen_unboundedOutside_of_isClosed hS

/-- The fill of a closed bounded planar obstacle is compact. -/
theorem isCompact_fill
    {S : Set (ℝ × ℝ)}
    (hSclosed : IsClosed S)
    (hSbounded : Bornology.IsBounded S) :
    IsCompact (fill S) := by
  exact
    Metric.isCompact_of_isClosed_isBounded
      (isClosed_fill hSclosed)
      (isBounded_fill hSbounded)

/-- Filling can only remove frontier points; it cannot create frontier away
from the original obstacle. -/
theorem frontier_fill_subset
    {S : Set (ℝ × ℝ)}
    (hSclosed : IsClosed S) :
    frontier (fill S) ⊆ S := by
  intro x hxFrontier
  have hxClosure : x ∈ closure (fill S) :=
    frontier_subset_closure hxFrontier
  have hxFill : x ∈ fill S := by
    rw [(isClosed_fill hSclosed).closure_eq] at hxClosure
    exact hxClosure
  rcases hxFill with hxS | hxInside
  · exact hxS
  · have hxInterior :
        x ∈ interior (fill S) :=
      interior_maximal
        (fun _ hy => Or.inr hy)
        (Helpers.isOpen_inside_of_isClosed hSclosed)
        hxInside
    have hxFill' : x ∈ fill S :=
      Or.inr hxInside
    exact False.elim <|
      (mem_frontier_iff_notMem_interior hxFill').mp
        hxFrontier hxInterior

/-- A compact planar region whose complement is one unbounded connected
piece has the expected bounded-component interpretation of its frontier. -/
theorem inside_frontier_eq_interior
    {K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K)
    (hKcomplPreconnected : IsPreconnected Kᶜ)
    (hKcomplUnbounded : ¬ Bornology.IsBounded Kᶜ) :
    inside (frontier K) = interior K := by
  have hKclosed : IsClosed K :=
    hKcompact.isClosed
  apply Inside.inside_eq_of_open_partition
  · calc
      (frontier K)ᶜ =
          interior K ∪ interior Kᶜ :=
        compl_frontier_eq_union_interior
      _ = interior K ∪ Kᶜ := by
        rw [hKclosed.isOpen_compl.interior_eq]
  · exact isOpen_interior
  · exact hKclosed.isOpen_compl
  · rw [Set.disjoint_left]
    intro x hxInterior hxCompl
    exact hxCompl (interior_subset hxInterior)
  · exact
      hKcompact.isBounded.subset interior_subset
  · intro x hxCompl
    refine
      ⟨Kᶜ, hxCompl, hKcomplPreconnected, ?_,
        hKcomplUnbounded⟩
    intro y hyCompl hyFrontier
    exact
      hyCompl <|
        hKclosed.closure_eq ▸
          frontier_subset_closure hyFrontier

/-- The filled region of a bounded obstacle has a preconnected complement. -/
theorem isPreconnected_compl_fill
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    IsPreconnected (fill S)ᶜ := by
  rw [compl_fill]
  exact Exterior.isPreconnected_unboundedOutside hS

/-- The complement of the filled region of a bounded obstacle is unbounded. -/
theorem not_isBounded_compl_fill
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    ¬ Bornology.IsBounded (fill S)ᶜ := by
  obtain ⟨p, hpOutside, hpComponent⟩ :=
    Exterior.unboundedOutside_eq_connectedComponentIn hS
  rw [compl_fill, hpComponent]
  exact hpOutside.2

/-- Filling is monotone: enlarging the obstacle can only turn more bounded
complement components into filled points. -/
theorem fill_mono
    {S T : Set (ℝ × ℝ)}
    (hST : S ⊆ T) :
    fill S ⊆ fill T := by
  intro x hxFill
  rcases hxFill with hxS | hxInside
  · exact Or.inl (hST hxS)
  · by_cases hxT : x ∈ T
    · exact Or.inl hxT
    · refine Or.inr ⟨hxT, ?_⟩
      apply hxInside.2.subset
      apply
        isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn hxT)
      intro y hyComponent hyS
      have hyT :
          y ∈ Tᶜ :=
        connectedComponentIn_subset Tᶜ x hyComponent
      exact hyT (hST hyS)

/-- Once a bounded obstacle has been filled, it has no bounded complement
components left. -/
theorem inside_fill_eq_empty
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    inside (fill S) = ∅ := by
  apply Set.Subset.antisymm
  · intro x hxInside
    have hcomplComponent :
        (fill S)ᶜ ⊆
          connectedComponentIn (fill S)ᶜ x :=
      (isPreconnected_compl_fill hS).subset_connectedComponentIn
        (show x ∈ (fill S)ᶜ from hxInside.1)
        (Set.Subset.refl _)
    exact
      (not_isBounded_compl_fill hS)
        (hxInside.2.subset hcomplComponent)
  · exact Set.empty_subset _

/-- On bounded obstacles, `fill` is idempotent. -/
theorem fill_fill
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    fill (fill S) = fill S := by
  change fill S ∪ inside (fill S) = fill S
  rw [inside_fill_eq_empty hS, Set.union_empty]

/-- Any intermediate obstacle between a bounded set and its fill has the
same fill. -/
theorem fill_eq_of_subset_of_subset_fill
    {S T : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S)
    (hST : S ⊆ T)
    (hTfill : T ⊆ fill S) :
    fill T = fill S := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' :
        x ∈ fill (fill S) :=
      fill_mono hTfill hx
    rw [fill_fill hS] at hx'
    exact hx'
  · exact fill_mono hST

/-- In particular, adding a set already contained in a bounded fill does not
change that fill. -/
theorem fill_union_eq_fill
    {S U : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S)
    (hU : U ⊆ fill S) :
    fill (S ∪ U) = fill S := by
  apply
    fill_eq_of_subset_of_subset_fill hS
      Set.subset_union_left
  rintro x (hxS | hxU)
  · exact Or.inl hxS
  · exact hU hxU

/-- The bounded-component inside of the frontier of a fill is its ordinary
topological interior. -/
theorem inside_frontier_fill_eq_interior
    {S : Set (ℝ × ℝ)}
    (hSclosed : IsClosed S)
    (hSbounded : Bornology.IsBounded S) :
    inside (frontier (fill S)) = interior (fill S) := by
  exact
    inside_frontier_eq_interior
      (isCompact_fill hSclosed hSbounded)
      (isPreconnected_compl_fill hSbounded)
      (not_isBounded_compl_fill hSbounded)

end Submission.FilledRegion
