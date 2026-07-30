import Submission.Helpers

namespace Submission.Helpers

open Set

/-- Distinct connected components relative to a set are disjoint. -/
theorem connectedComponentIn_disjoint_of_ne {X : Type*} [TopologicalSpace X]
    {s : Set X} {x y : X}
    (hxy : connectedComponentIn s x ≠ connectedComponentIn s y) :
    Disjoint (connectedComponentIn s x) (connectedComponentIn s y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  apply hxy
  exact (connectedComponentIn_eq hzx).trans
    (connectedComponentIn_eq hzy).symm

/-- A nonempty set fails to be preconnected exactly when it contains points
in two distinct relative connected components. -/
theorem exists_two_connectedComponents_iff_not_isPreconnected
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : s.Nonempty) :
    (∃ x ∈ s, ∃ y ∈ s,
      connectedComponentIn s x ≠ connectedComponentIn s y) ↔
      ¬ IsPreconnected s := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩ hpreconnected
    exact hxy ((hpreconnected.connectedComponentIn hx).trans
      (hpreconnected.connectedComponentIn hy).symm)
  · intro hnotPreconnected
    by_contra htwo
    push Not at htwo
    obtain ⟨p, hp⟩ := hs
    apply hnotPreconnected
    have hcomponent : connectedComponentIn s p = s := by
      apply Set.Subset.antisymm (connectedComponentIn_subset s p)
      intro y hy
      have hyOwn : y ∈ connectedComponentIn s y :=
        mem_connectedComponentIn hy
      exact (htwo p hp y hy).symm ▸ hyOwn
    rw [← hcomponent]
    exact isPreconnected_connectedComponentIn

/-- In a locally connected ambient space, the frontier of a component of an
open set lies outside that open set. -/
theorem frontier_connectedComponentIn_subset_compl {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] {s : Set X}
    (hs : IsOpen s) (x : X) :
    frontier (connectedComponentIn s x) ⊆ sᶜ := by
  intro y hy
  have hcomponentOpen : IsOpen (connectedComponentIn s x) :=
    hs.connectedComponentIn
  have hyClosure : y ∈ closure (connectedComponentIn s x) :=
    frontier_subset_closure hy
  have hyNotComponent : y ∉ connectedComponentIn s x := by
    rw [hcomponentOpen.frontier_eq] at hy
    exact hy.2
  rw [mem_compl_iff]
  intro hys
  have hyOwn : y ∈ connectedComponentIn s y :=
    mem_connectedComponentIn hys
  have hne : connectedComponentIn s x ≠ connectedComponentIn s y := by
    intro hxy
    exact hyNotComponent (hxy.symm ▸ hyOwn)
  have hdisjoint :
      Disjoint (closure (connectedComponentIn s x))
        (connectedComponentIn s y) :=
    (connectedComponentIn_disjoint_of_ne hne).closure_left
      hs.connectedComponentIn
  exact Set.disjoint_left.mp hdisjoint hyClosure hyOwn

/-- The closure of a component of an open set adds points only from the
complement of that open set. -/
theorem closure_connectedComponentIn_subset_union_compl {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] {s : Set X}
    (hs : IsOpen s) (x : X) :
    closure (connectedComponentIn s x) ⊆
      connectedComponentIn s x ∪ sᶜ := by
  intro y hy
  by_cases hyComponent : y ∈ connectedComponentIn s x
  · exact Or.inl hyComponent
  · apply Or.inr
    apply frontier_connectedComponentIn_subset_compl hs x
    rw [(hs.connectedComponentIn).frontier_eq]
    exact ⟨hy, hyComponent⟩

/-- Relative to its defining open set, a component is already closed. -/
theorem closure_connectedComponentIn_inter {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] {s : Set X}
    (hs : IsOpen s) (x : X) :
    closure (connectedComponentIn s x) ∩ s =
      connectedComponentIn s x := by
  apply Set.Subset.antisymm
  · rintro y ⟨hyClosure, hys⟩
    rcases closure_connectedComponentIn_subset_union_compl hs x hyClosure with
      hyComponent | hyCompl
    · exact hyComponent
    · exact (hyCompl hys).elim
  · intro y hy
    exact ⟨subset_closure hy, connectedComponentIn_subset s x hy⟩

/-- The frontier of a component of an open set is exactly the part of its
closure outside that open set. -/
theorem frontier_connectedComponentIn_eq_inter_compl {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] {s : Set X}
    (hs : IsOpen s) (x : X) :
    frontier (connectedComponentIn s x) =
      closure (connectedComponentIn s x) ∩ sᶜ := by
  rw [(hs.connectedComponentIn).frontier_eq]
  ext y
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rcases closure_connectedComponentIn_subset_union_compl hs x hy.1 with
      hyComponent | hyCompl
    · exact (hy.2 hyComponent).elim
    · exact hyCompl
  · rintro ⟨hyClosure, hyCompl⟩
    refine ⟨hyClosure, ?_⟩
    intro hyComponent
    exact hyCompl (connectedComponentIn_subset s x hyComponent)

/-- Every component of a proper open subset of a connected ambient space has
a nonempty frontier. -/
theorem frontier_connectedComponentIn_nonempty_of_ne_univ
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {s : Set X} {x : X} (hx : x ∈ s) (hs : s ≠ Set.univ) :
    (frontier (connectedComponentIn s x)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨connectedComponentIn_nonempty_iff.mpr hx, ?_⟩
  intro hcomponent
  apply hs
  apply Set.eq_univ_of_univ_subset
  intro y _hy
  apply connectedComponentIn_subset s x
  rw [hcomponent]
  exact Set.mem_univ y

/-- Every bounded, nonempty component in a nontrivial real normed space has a
nonempty frontier. -/
theorem frontier_connectedComponentIn_nonempty_of_isBounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {s : Set E} {x : E} (hx : x ∈ s)
    (hbounded : Bornology.IsBounded (connectedComponentIn s x)) :
    (frontier (connectedComponentIn s x)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨connectedComponentIn_nonempty_iff.mpr hx, ?_⟩
  intro hcomponent
  apply NormedSpace.unbounded_univ ℝ E
  simpa only [hcomponent] using hbounded

/-- The frontier of a nonempty bounded open set separates a nontrivial real
normed space. -/
theorem not_isPreconnected_compl_frontier_of_isOpen_isBounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {s : Set E} (hsOpen : IsOpen s) (hsNonempty : s.Nonempty)
    (hsBounded : Bornology.IsBounded s) :
    ¬ IsPreconnected (frontier s)ᶜ := by
  intro hpreconnected
  have hcover : (frontier s)ᶜ ⊆ s ∪ (closure s)ᶜ := by
    intro y hy
    rw [Set.mem_compl_iff] at hy
    by_cases hys : y ∈ s
    · exact Or.inl hys
    · apply Or.inr
      rw [Set.mem_compl_iff]
      intro hyClosure
      apply hy
      rw [hsOpen.frontier_eq]
      exact ⟨hyClosure, hys⟩
  have hdisjoint : Disjoint s (closure s)ᶜ := by
    rw [Set.disjoint_left]
    intro y hys hyClosure
    exact hyClosure (subset_closure hys)
  have hsides :=
    isPreconnected_iff_subset_of_disjoint.mp hpreconnected s
      (closure s)ᶜ hsOpen isClosed_closure.isOpen_compl hcover
      (by simp only [hdisjoint.inter_eq, Set.inter_empty])
  have hclosureNe : closure s ≠ (Set.univ : Set E) := by
    intro hclosure
    apply NormedSpace.unbounded_univ ℝ E
    simpa only [hclosure] using hsBounded.closure
  obtain ⟨y, hyClosure⟩ :=
    (Set.ne_univ_iff_exists_notMem (closure s)).mp hclosureNe
  have hyFrontier : y ∈ (frontier s)ᶜ := by
    rw [Set.mem_compl_iff]
    exact fun hy ↦ hyClosure (frontier_subset_closure hy)
  rcases hsides with hsSubset | hclosureComplSubset
  · exact hyClosure (subset_closure (hsSubset hyFrontier))
  · obtain ⟨x, hxs⟩ := hsNonempty
    have hxFrontier : x ∈ (frontier s)ᶜ := by
      rw [Set.mem_compl_iff, hsOpen.frontier_eq]
      exact fun hx ↦ hx.2 hxs
    exact hclosureComplSubset hxFrontier (subset_closure hxs)

/-- In a locally connected normed space, the frontier of every nonempty
bounded component of an open set is itself a separator. -/
theorem not_isPreconnected_compl_frontier_connectedComponentIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [LocallyConnectedSpace E] {s : Set E} (hsOpen : IsOpen s)
    {x : E} (hx : x ∈ s)
    (hbounded : Bornology.IsBounded (connectedComponentIn s x)) :
    ¬ IsPreconnected (frontier (connectedComponentIn s x))ᶜ :=
  not_isPreconnected_compl_frontier_of_isOpen_isBounded
    hsOpen.connectedComponentIn
    (connectedComponentIn_nonempty_iff.mpr hx) hbounded

/-- In a proper metric space, the closure of a bounded relative component is
compact. -/
theorem isCompact_closure_connectedComponentIn_of_isBounded
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} {x : X}
    (hbounded : Bornology.IsBounded (connectedComponentIn s x)) :
    IsCompact (closure (connectedComponentIn s x)) :=
  hbounded.isCompact_closure

/-- In a proper metric space, the frontier of a bounded relative component is
compact. -/
theorem isCompact_frontier_connectedComponentIn_of_isBounded
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} {x : X}
    (hbounded : Bornology.IsBounded (connectedComponentIn s x)) :
    IsCompact (frontier (connectedComponentIn s x)) :=
  hbounded.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure

/-- A bounded component of an open complement accumulates on the deleted
closed set. -/
theorem exists_mem_frontier_of_bounded_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {a : Set E} (ha : IsClosed a) {x : E} (hx : x ∈ aᶜ)
    (hbounded : Bornology.IsBounded (connectedComponentIn aᶜ x)) :
    ∃ z ∈ a, z ∈ closure (connectedComponentIn aᶜ x) := by
  obtain ⟨z, hz⟩ :=
    frontier_connectedComponentIn_nonempty_of_isBounded hx hbounded
  refine ⟨z, ?_, frontier_subset_closure hz⟩
  have hzcompl : z ∈ (aᶜ)ᶜ :=
    frontier_connectedComponentIn_subset_compl ha.isOpen_compl x hz
  simpa only [compl_compl] using hzcompl

/-- Every complementary component of a nonempty closed set accumulates on
that closed set. -/
theorem exists_mem_frontier_of_complement_component
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    [PreconnectedSpace X] {a : Set X} (haClosed : IsClosed a)
    (haNonempty : a.Nonempty) {x : X} (hx : x ∈ aᶜ) :
    ∃ z ∈ a, z ∈ frontier (connectedComponentIn aᶜ x) := by
  have hcomplNe : aᶜ ≠ (Set.univ : Set X) := by
    intro hcompl
    obtain ⟨z, hz⟩ := haNonempty
    have : z ∈ aᶜ := hcompl.symm ▸ Set.mem_univ z
    exact this hz
  obtain ⟨z, hz⟩ :=
    frontier_connectedComponentIn_nonempty_of_ne_univ hx hcomplNe
  refine ⟨z, ?_, hz⟩
  have hzcompl : z ∈ (aᶜ)ᶜ :=
    frontier_connectedComponentIn_subset_compl haClosed.isOpen_compl x hz
  simpa only [compl_compl] using hzcompl

/-- For a sphere embedding, the frontier of each complementary component is
exactly its closure's intersection with the embedded sphere. -/
theorem frontier_sphere_complement_component_eq (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x : EuclideanSpace ℝ (Fin d)) :
    frontier (connectedComponentIn (Set.range r)ᶜ x) =
      closure (connectedComponentIn (Set.range r)ᶜ x) ∩ Set.range r := by
  simpa only [compl_compl] using
    frontier_connectedComponentIn_eq_inter_compl
      (isOpen_compl_range_sphere_embedding d r hcont hinj) x

/-- Every complementary component of an embedded sphere has an actual sphere
point on its frontier. -/
theorem exists_sphere_point_mem_component_frontier (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (Set.range r)ᶜ) :
    ∃ z, r z ∈ frontier (connectedComponentIn (Set.range r)ᶜ x) := by
  have hrangeNonempty : (Set.range r).Nonempty :=
    (sphere_range_connected d hd r hcont).nonempty
  obtain ⟨y, hyRange, hyFrontier⟩ :=
    exists_mem_frontier_of_complement_component
      (isClosed_range_sphere_embedding d r hcont hinj)
      hrangeNonempty hx
  obtain ⟨z, rfl⟩ := hyRange
  exact ⟨z, hyFrontier⟩

/-- Every bounded complementary component supplies a nonempty compact
separator contained in the embedded sphere, namely its frontier. -/
theorem exists_compact_separator_subset_sphere_of_bounded_component
    (d : ℕ) (hd : 2 ≤ d) (r : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1 → EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (Set.range r)ᶜ)
    (hbounded : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ x)) :
    ∃ k : Set (EuclideanSpace ℝ (Fin d)),
      k.Nonempty ∧ IsCompact k ∧ k ⊆ Set.range r ∧
        ¬ IsPreconnected kᶜ := by
  letI : Nonempty (Fin d) :=
    ⟨⟨0, lt_of_lt_of_le (by norm_num) hd⟩⟩
  let k := frontier (connectedComponentIn (Set.range r)ᶜ x)
  refine ⟨k,
    frontier_connectedComponentIn_nonempty_of_isBounded hx hbounded,
    isCompact_frontier_connectedComponentIn_of_isBounded hbounded, ?_, ?_⟩
  · simpa only [k, compl_compl] using
      frontier_connectedComponentIn_subset_compl
        (isOpen_compl_range_sphere_embedding d r hcont hinj) x
  · exact not_isPreconnected_compl_frontier_connectedComponentIn
      (isOpen_compl_range_sphere_embedding d r hcont hinj) hx hbounded

end Submission.Helpers
