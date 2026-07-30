import Submission.FilledRegion
import Submission.HalfspaceEscape

open LeanEval.Geometry.PicksTheorem

namespace Submission.FillHalfspace

/-- A supporting closed half-space that contains an obstacle also contains
all of its bounded complement components. -/
theorem fill_subset_halfSpace_le
    {B : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (d : ℝ × ℝ)
    (hd : 0 < f d)
    (hB : ∀ y ∈ B, f y ≤ c) :
    FilledRegion.fill B ⊆
      {x : ℝ × ℝ | f x ≤ c} := by
  intro x hx
  change f x ≤ c
  rcases hx with hxB | hxInside
  · exact hB x hxB
  · by_contra hxle
    have hxc : c < f x :=
      lt_of_not_ge hxle
    obtain ⟨W, hxW, hWpreconnected,
        hWcompl, hWunbounded⟩ :=
      HalfspaceEscape.exists_unbounded_escape_of_strictHalfspace
        f c hxc hd hB
    have hWcomponent :
        W ⊆ connectedComponentIn Bᶜ x :=
      hWpreconnected.subset_connectedComponentIn
        hxW hWcompl
    exact
      hWunbounded
        (hxInside.2.subset hWcomponent)

end Submission.FillHalfspace
