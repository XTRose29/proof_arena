import Submission.Components

namespace Submission.Helpers

/-- There is a distinguished unbounded complementary component, and every
different complementary component is bounded. -/
theorem exists_exterior_component_bounded_others (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) :
    ∃ p ∈ (Set.range r)ᶜ,
      ¬ Bornology.IsBounded
        (connectedComponentIn (Set.range r)ᶜ p) ∧
      ∀ x ∈ (Set.range r)ᶜ,
        connectedComponentIn (Set.range r)ᶜ x ≠
          connectedComponentIn (Set.range r)ᶜ p →
        Bornology.IsBounded
          (connectedComponentIn (Set.range r)ᶜ x) := by
  obtain ⟨p, hp, hpUnbounded⟩ :=
    exists_unbounded_connectedComponentIn d hd r hcont
  refine ⟨p, hp, hpUnbounded, ?_⟩
  intro x _hx hxne
  by_contra hxUnbounded
  exact hxne
    (connectedComponentIn_eq_of_not_isBounded d hd r hcont
      hxUnbounded hpUnbounded)

/-- Once two distinct complementary components are exhibited, one of them is
automatically bounded. -/
theorem exists_bounded_component_of_two_components (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    (htwo : ∃ x ∈ (Set.range r)ᶜ, ∃ y ∈ (Set.range r)ᶜ,
      connectedComponentIn (Set.range r)ᶜ x ≠
        connectedComponentIn (Set.range r)ᶜ y) :
    ∃ x ∈ (Set.range r)ᶜ,
      Bornology.IsBounded
        (connectedComponentIn (Set.range r)ᶜ x) := by
  obtain ⟨p, hp, _hpUnbounded, hothers⟩ :=
    exists_exterior_component_bounded_others d hd r hcont
  obtain ⟨x, hx, y, hy, hxy⟩ := htwo
  by_cases hxp : connectedComponentIn (Set.range r)ᶜ x =
      connectedComponentIn (Set.range r)ᶜ p
  · refine ⟨y, hy, hothers y hy ?_⟩
    intro hyp
    exact hxy (hxp.trans hyp.symm)
  · exact ⟨x, hx, hothers x hx hxp⟩

/-- Once existence and uniqueness of the bounded complementary component are
known, the already-constructed exterior component completes the exact
Jordan--Brouwer cardinality statement. -/
theorem jordan_brouwer_of_bounded_component (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    (hbounded : ∃ x ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x))
    (hbounded_unique : ∀ x ∈ (Set.range r)ᶜ, ∀ y ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) →
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y) →
      connectedComponentIn (Set.range r)ᶜ x =
        connectedComponentIn (Set.range r)ᶜ y) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ :
          Set (EuclideanSpace ℝ (Fin d)))) = 2 := by
  apply natCard_connectedComponents_eq_two_of_bounded_partition
    (s := (Set.range r)ᶜ)
  · exact hbounded
  · exact exists_unbounded_connectedComponentIn d hd r hcont
  · exact hbounded_unique
  · intro x hx y hy
    exact connectedComponentIn_eq_of_not_isBounded d hd r hcont

/-- An explicit separation witness together with uniqueness of bounded
components is enough for the exact cardinality conclusion. -/
theorem jordan_brouwer_of_two_components (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    (htwo : ∃ x ∈ (Set.range r)ᶜ, ∃ y ∈ (Set.range r)ᶜ,
      connectedComponentIn (Set.range r)ᶜ x ≠
        connectedComponentIn (Set.range r)ᶜ y)
    (hbounded_unique : ∀ x ∈ (Set.range r)ᶜ, ∀ y ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) →
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y) →
      connectedComponentIn (Set.range r)ᶜ x =
        connectedComponentIn (Set.range r)ᶜ y) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ :
          Set (EuclideanSpace ℝ (Fin d)))) = 2 := by
  apply jordan_brouwer_of_bounded_component d hd r hcont
  · exact exists_bounded_component_of_two_components d hd r hcont htwo
  · exact hbounded_unique

/-- Equivalently, it is enough to prove that the complementary region is not
preconnected and that any two bounded complementary components coincide. -/
theorem jordan_brouwer_of_not_isPreconnected (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    (hseparates : ¬ IsPreconnected (Set.range r)ᶜ)
    (hbounded_unique : ∀ x ∈ (Set.range r)ᶜ, ∀ y ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) →
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y) →
      connectedComponentIn (Set.range r)ᶜ x =
        connectedComponentIn (Set.range r)ᶜ y) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ :
          Set (EuclideanSpace ℝ (Fin d)))) = 2 := by
  apply jordan_brouwer_of_two_components d hd r hcont
  · apply
      (exists_two_connectedComponents_iff_not_isPreconnected ?_).2
        hseparates
    obtain ⟨p, hp, _hpUnbounded⟩ :=
      exists_unbounded_connectedComponentIn d hd r hcont
    exact ⟨p, hp⟩
  · exact hbounded_unique

end Submission.Helpers
