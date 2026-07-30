import Submission.Exterior
import Submission.HalfspaceEscape

namespace Submission.AttachmentExterior

/-!
The filled-region gluing arguments only need to rule out new bounded
components in the complement of an attached union.  The lemmas below reduce
that question to a concrete reachability statement: every exterior point
must be joinable, while staying exterior, to one strict supporting
half-space.  A forward ray then makes its component unbounded, and boundedness
of the obstacle identifies all such components with the unique exterior.
-/

/-- A path inside a set places its target in the source's connected
component. -/
theorem target_mem_connectedComponentIn_of_joinedIn
    {F : Set (ℝ × ℝ)} {x y : ℝ × ℝ}
    (hxy : JoinedIn F x y) :
    y ∈ connectedComponentIn F x := by
  let path := hxy.somePath
  have hpathPreconnected :
      IsPreconnected (Set.range path) :=
    isPreconnected_range path.continuous
  have hpathSubset : Set.range path ⊆ F := by
    rintro _ ⟨t, rfl⟩
    exact hxy.somePath_mem t
  have hxRange : x ∈ Set.range path := by
    refine ⟨0, ?_⟩
    simp [path]
  have hrangeComponent :
      Set.range path ⊆ connectedComponentIn F x :=
    hpathPreconnected.subset_connectedComponentIn
      hxRange hpathSubset
  apply hrangeComponent
  refine ⟨1, ?_⟩
  simp [path]

/-- If a point can reach a strict upper supporting half-space, its component
in the obstacle complement is unbounded. -/
theorem component_unbounded_of_joined_strictUpper
    {K : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (d : ℝ × ℝ) (hd : 0 < f d)
    (hK : ∀ z ∈ K, f z ≤ c)
    {x y : ℝ × ℝ}
    (hxy : JoinedIn Kᶜ x y)
    (hy : c < f y) :
    ¬ Bornology.IsBounded
      (connectedComponentIn Kᶜ x) := by
  have hyComponent :
      y ∈ connectedComponentIn Kᶜ x :=
    target_mem_connectedComponentIn_of_joinedIn hxy
  have hcomponents :
      connectedComponentIn Kᶜ x =
        connectedComponentIn Kᶜ y :=
    connectedComponentIn_eq hyComponent
  have hraySubset :
      HalfspaceEscape.forwardRay y d ⊆ Kᶜ :=
    HalfspaceEscape.forwardRay_subset_compl_of_strictHalfspace
      f c hy hd hK
  have hrayComponentY :
      HalfspaceEscape.forwardRay y d ⊆
        connectedComponentIn Kᶜ y :=
    IsPreconnected.subset_connectedComponentIn
      (HalfspaceEscape.isPreconnected_forwardRay y d)
      (HalfspaceEscape.self_mem_forwardRay y d)
      hraySubset
  have hrayComponentX :
      HalfspaceEscape.forwardRay y d ⊆
        connectedComponentIn Kᶜ x := by
    rw [hcomponents]
    exact hrayComponentY
  intro hcomponentBounded
  exact
    HalfspaceEscape.not_isBounded_forwardRay y
      (fun hdZero => by
        rw [hdZero, map_zero] at hd
        exact (lt_irrefl 0 hd))
      (hcomponentBounded.subset hrayComponentX)

/-- For a bounded obstacle lying below a supporting level, it is enough to
join every complement point to the strict upper half-space in order to prove
that the whole complement is preconnected. -/
theorem isPreconnected_compl_of_reaches_strictUpper
    {K : Set (ℝ × ℝ)}
    (hKbounded : Bornology.IsBounded K)
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (d : ℝ × ℝ) (hd : 0 < f d)
    (hK : ∀ z ∈ K, f z ≤ c)
    (hreach :
      ∀ x ∈ Kᶜ,
        ∃ y : ℝ × ℝ,
          c < f y ∧ JoinedIn Kᶜ x y) :
    IsPreconnected Kᶜ := by
  have hcompl :
      Kᶜ = Inside.unboundedOutside K := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := hreach x hx
      exact
        ⟨hx,
          component_unbounded_of_joined_strictUpper
            f c d hd hK hxy hy⟩
    · intro hx
      exact hx.1
  rw [hcompl]
  exact Exterior.isPreconnected_unboundedOutside hKbounded

/-- Points in one strict upper half-space are joined there, hence also in
the complement of every obstacle supported below its boundary level. -/
theorem joinedIn_compl_of_mem_strictUpper
    {K : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hK : ∀ z ∈ K, f z ≤ c)
    {x y : ℝ × ℝ}
    (hx : c < f x) (hy : c < f y) :
    JoinedIn Kᶜ x y := by
  let upper : Set (ℝ × ℝ) := {z | c < f z}
  have hupperConvex : Convex ℝ upper := by
    exact convex_halfSpace_gt f.toLinearMap.isLinear c
  have hjoined : JoinedIn upper x y :=
    (hupperConvex.isPathConnected ⟨x, hx⟩).joinedIn
      x hx y hy
  apply hjoined.mono
  intro z hz hzK
  exact (not_lt_of_ge (hK z hzK)) hz

end Submission.AttachmentExterior
