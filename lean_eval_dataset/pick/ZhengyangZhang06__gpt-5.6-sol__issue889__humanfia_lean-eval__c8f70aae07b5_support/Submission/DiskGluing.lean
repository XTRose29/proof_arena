import Submission.FillFrontier
import Submission.AttachmentExterior

open LeanEval.Geometry.PicksTheorem

namespace Submission.DiskGluing

/-- A closed region can be attached along `E` to any closed region with a
one-component exterior that meets it exactly in `E`. -/
def EdgeAttachable
    (K E : Set (ℝ × ℝ)) : Prop :=
  ∀ ⦃R : Set (ℝ × ℝ)⦄,
    IsClosed R →
      IsPreconnected Rᶜ →
        R ∩ K = E →
          IsPreconnected (R ∪ K)ᶜ

/-- Membership in a filled region does not change along paths in the obstacle
complement: a path to a point outside the fill certifies that its source is
outside the fill as well. -/
theorem not_mem_fill_of_joined_not_mem_fill
    {B : Set (ℝ × ℝ)} {x y : ℝ × ℝ}
    (hxy : JoinedIn Bᶜ x y)
    (hy : y ∉ FilledRegion.fill B) :
    x ∉ FilledRegion.fill B := by
  intro hx
  rcases hx with hxBoundary | hxInside
  · exact hxy.source_mem hxBoundary
  · have hyComponent :
        y ∈ connectedComponentIn Bᶜ x :=
      AttachmentExterior.target_mem_connectedComponentIn_of_joinedIn
        hxy
    have hyInside : y ∈ inside B := by
      refine ⟨hxy.target_mem, ?_⟩
      rw [← connectedComponentIn_eq hyComponent]
      exact hxInside.2
    exact hy (Or.inr hyInside)

/-- A preconnected set which avoids the frontier of a closed region cannot
move from the exterior to the interior of that region. -/
theorem subset_compl_of_preconnected_of_disjoint_frontier
    {K C : Set (ℝ × ℝ)}
    (hKclosed : IsClosed K)
    (hC : IsPreconnected C)
    (hCfrontier : Disjoint C (frontier K))
    {x : ℝ × ℝ}
    (hxC : x ∈ C)
    (hxK : x ∉ K) :
    C ⊆ Kᶜ := by
  apply
    hC.subset_left_of_subset_union
      hKclosed.isOpen_compl isOpen_interior
  · rw [Set.disjoint_left]
    intro y hyCompl hyInterior
    exact hyCompl (interior_subset hyInterior)
  · intro y hyC
    have hyNotFrontier : y ∉ frontier K := by
      exact
        Set.disjoint_left.mp hCfrontier hyC
    have hySides :
        y ∈ interior K ∪ interior Kᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact hyNotFrontier
    rcases hySides with hyInterior | hyExterior
    · exact Or.inr hyInterior
    · left
      simpa [hKclosed.isOpen_compl.interior_eq] using
        hyExterior
  · exact ⟨x, hxC, hxK⟩

/-- The corresponding inside-side propagation principle. -/
theorem subset_interior_of_preconnected_of_disjoint_frontier
    {K C : Set (ℝ × ℝ)}
    (hKclosed : IsClosed K)
    (hC : IsPreconnected C)
    (hCfrontier : Disjoint C (frontier K))
    {x : ℝ × ℝ}
    (hxC : x ∈ C)
    (hxInterior : x ∈ interior K) :
    C ⊆ interior K := by
  apply
    hC.subset_right_of_subset_union
      hKclosed.isOpen_compl isOpen_interior
  · rw [Set.disjoint_left]
    intro y hyCompl hyInterior
    exact hyCompl (interior_subset hyInterior)
  · intro y hyC
    have hyNotFrontier : y ∉ frontier K := by
      exact
        Set.disjoint_left.mp hCfrontier hyC
    have hySides :
        y ∈ interior K ∪ interior Kᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact hyNotFrontier
    rcases hySides with hyInterior | hyExterior
    · exact Or.inr hyInterior
    · left
      simpa [hKclosed.isOpen_compl.interior_eq] using
        hyExterior
  · exact ⟨x, hxC, hxInterior⟩

/-- If one root-deleted side is preconnected, avoids the other frontier,
and contains an exterior point of the other side, then the two closed
regions meet exactly in their common root. -/
theorem inter_eq_root_of_one_preconnected_side
    {A B D : Set (ℝ × ℝ)}
    (hBclosed : IsClosed B)
    (hDsubsetA : D ⊆ A)
    (hDsubsetB : D ⊆ B)
    (hAside : IsPreconnected (A \ D))
    (hAsideFrontier :
      Disjoint (A \ D) (frontier B))
    {x : ℝ × ℝ}
    (hxAside : x ∈ A \ D)
    (hxB : x ∉ B) :
    A ∩ B = D := by
  have hAsideCompl : A \ D ⊆ Bᶜ :=
    subset_compl_of_preconnected_of_disjoint_frontier
      hBclosed hAside hAsideFrontier hxAside hxB
  apply Set.Subset.antisymm
  · rintro y ⟨hyA, hyB⟩
    by_contra hyD
    exact (hAsideCompl ⟨hyA, hyD⟩) hyB
  · intro y hyD
    exact ⟨hDsubsetA hyD, hDsubsetB hyD⟩

/-- Regularity and preconnectedness of the ordinary interior imply that
deleting an arbitrary subset of the frontier preserves preconnectedness. -/
theorem isPreconnected_sdiff_frontier_subset
    {K E : Set (ℝ × ℝ)}
    (hregular : closure (interior K) = K)
    (hinterior : IsPreconnected (interior K))
    (hE : E ⊆ frontier K) :
    IsPreconnected (K \ E) := by
  apply hinterior.subset_closure
  · intro x hxInterior
    refine ⟨interior_subset hxInterior, ?_⟩
    intro hxE
    exact
      Set.disjoint_left.mp disjoint_interior_frontier
        hxInterior (hE hxE)
  · intro x hx
    rw [hregular]
    exact hx.1

/-- A seam point which is interior after gluing connects the two child
interiors.  If both children are regular closed with preconnected interiors,
then the glued union also has preconnected interior. -/
theorem isPreconnected_interior_union
    {A B : Set (ℝ × ℝ)}
    (hAregular : closure (interior A) = A)
    (hBregular : closure (interior B) = B)
    (hAinterior : IsPreconnected (interior A))
    (hBinterior : IsPreconnected (interior B))
    {p : ℝ × ℝ}
    (hpA : p ∈ A)
    (hpB : p ∈ B)
    (hpInterior : p ∈ interior (A ∪ B)) :
    IsPreconnected (interior (A ∪ B)) := by
  let Ap : Set (ℝ × ℝ) :=
    interior A ∪ {p}
  let Bp : Set (ℝ × ℝ) :=
    {p} ∪ interior B
  have hpClosureA : p ∈ closure (interior A) := by
    rw [hAregular]
    exact hpA
  have hpClosureB : p ∈ closure (interior B) := by
    rw [hBregular]
    exact hpB
  have hAp : IsPreconnected Ap := by
    apply hAinterior.subset_closure
    · exact Set.subset_union_left
    · rintro x (hx | rfl)
      · exact subset_closure hx
      · exact hpClosureA
  have hBp : IsPreconnected Bp := by
    apply hBinterior.subset_closure
    · exact Set.subset_union_right
    · rintro x (rfl | hx)
      · exact hpClosureB
      · exact subset_closure hx
  have hApBp : (Ap ∩ Bp).Nonempty := by
    refine ⟨p, ?_, ?_⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hcore : IsPreconnected (Ap ∪ Bp) :=
    hAp.union' hApBp hBp
  apply hcore.subset_closure
  · rintro x (hxAp | hxBp)
    · rcases hxAp with hxA | rfl
      · exact
          interior_mono Set.subset_union_left hxA
      · exact hpInterior
    · rcases hxBp with rfl | hxB
      · exact hpInterior
      · exact
          interior_mono Set.subset_union_right hxB
  · intro x hxInterior
    have hxUnion : x ∈ A ∪ B :=
      interior_subset hxInterior
    rcases hxUnion with hxA | hxB
    · have hxClosure : x ∈ closure (interior A) := by
        rw [hAregular]
        exact hxA
      exact
        closure_mono
          (fun y hy =>
            Or.inl (Or.inl hy))
          hxClosure
    · have hxClosure : x ∈ closure (interior B) := by
        rw [hBregular]
        exact hxB
      exact
        closure_mono
          (fun y hy =>
            Or.inr (Or.inr hy))
          hxClosure

/-- Two regular closed regions which meet exactly on a locally straight
seam cover a neighborhood of every interior seam point. -/
theorem mem_interior_union_of_local_zero
    {A B D : Set (ℝ × ℝ)}
    (g : (ℝ × ℝ) →ᵃ[ℝ] ℝ)
    {p : ℝ × ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hAclosed : IsClosed A)
    (hBclosed : IsClosed B)
    (hAregular : closure (interior A) = A)
    (hBregular : closure (interior B) = B)
    (hinter : A ∩ B = D)
    (hDfrontierA : D ⊆ frontier A)
    (hDfrontierB : D ⊆ frontier B)
    (hpD : p ∈ D)
    (hzero :
      ∀ z ∈ Metric.ball p ρ,
        g z = 0 → z ∈ D)
    (hfrontierA :
      ∀ z ∈ Metric.ball p ρ,
        z ∈ frontier A → g z = 0)
    (hfrontierB :
      ∀ z ∈ Metric.ball p ρ,
        z ∈ frontier B → g z = 0) :
    p ∈ interior (A ∪ B) := by
  have hpA : p ∈ A :=
    hAclosed.frontier_subset
      (hDfrontierA hpD)
  have hpB : p ∈ B :=
    hBclosed.frontier_subset
      (hDfrontierB hpD)
  have hpClosureA : p ∈ closure (interior A) := by
    rw [hAregular]
    exact hpA
  have hpClosureB : p ∈ closure (interior B) := by
    rw [hBregular]
    exact hpB
  obtain ⟨a, haBall, haInterior⟩ :=
    (mem_closure_iff.mp hpClosureA)
      (Metric.ball p ρ) Metric.isOpen_ball
      (Metric.mem_ball_self hρ)
  obtain ⟨b, hbBall, hbInterior⟩ :=
    (mem_closure_iff.mp hpClosureB)
      (Metric.ball p ρ) Metric.isOpen_ball
      (Metric.mem_ball_self hρ)
  have hga : g a ≠ 0 := by
    intro hgaZero
    have haD : a ∈ D :=
      hzero a haBall hgaZero
    exact
      Set.disjoint_left.mp disjoint_interior_frontier
        haInterior (hDfrontierA haD)
  have hgb : g b ≠ 0 := by
    intro hgbZero
    have hbD : b ∈ D :=
      hzero b hbBall hgbZero
    exact
      Set.disjoint_left.mp disjoint_interior_frontier
        hbInterior (hDfrontierB hbD)
  have hbNotA : b ∉ A := by
    intro hbA
    have hbBoth : b ∈ A ∩ B :=
      ⟨hbA, interior_subset hbInterior⟩
    rw [hinter] at hbBoth
    exact
      Set.disjoint_left.mp disjoint_interior_frontier
        hbInterior (hDfrontierB hbBoth)
  let negSide : Set (ℝ × ℝ) :=
    Metric.ball p ρ ∩ {z : ℝ × ℝ | g z < 0}
  let posSide : Set (ℝ × ℝ) :=
    Metric.ball p ρ ∩ {z : ℝ × ℝ | 0 < g z}
  have hnegPreconnected :
      IsPreconnected negSide := by
    exact
      ((convex_ball p ρ).inter
        ((convex_Iio (0 : ℝ)).affine_preimage g)).isPreconnected
  have hposPreconnected :
      IsPreconnected posSide := by
    exact
      ((convex_ball p ρ).inter
        ((convex_Ioi (0 : ℝ)).affine_preimage g)).isPreconnected
  have hnegDisjointA :
      Disjoint negSide (frontier A) := by
    rw [Set.disjoint_left]
    intro z hzNeg hzFrontier
    have hzZero :=
      hfrontierA z hzNeg.1 hzFrontier
    have hzLt : g z < 0 := hzNeg.2
    rw [hzZero] at hzLt
    exact (lt_irrefl 0 hzLt)
  have hposDisjointA :
      Disjoint posSide (frontier A) := by
    rw [Set.disjoint_left]
    intro z hzPos hzFrontier
    have hzZero :=
      hfrontierA z hzPos.1 hzFrontier
    have hzLt : 0 < g z := hzPos.2
    rw [hzZero] at hzLt
    exact (lt_irrefl 0 hzLt)
  have hnegDisjointB :
      Disjoint negSide (frontier B) := by
    rw [Set.disjoint_left]
    intro z hzNeg hzFrontier
    have hzZero :=
      hfrontierB z hzNeg.1 hzFrontier
    have hzLt : g z < 0 := hzNeg.2
    rw [hzZero] at hzLt
    exact (lt_irrefl 0 hzLt)
  have hposDisjointB :
      Disjoint posSide (frontier B) := by
    rw [Set.disjoint_left]
    intro z hzPos hzFrontier
    have hzZero :=
      hfrontierB z hzPos.1 hzFrontier
    have hzLt : 0 < g z := hzPos.2
    rw [hzZero] at hzLt
    exact (lt_irrefl 0 hzLt)
  have hnegSubsetA
      (haNeg : g a < 0) :
      negSide ⊆ interior A :=
    subset_interior_of_preconnected_of_disjoint_frontier
      hAclosed hnegPreconnected hnegDisjointA
        ⟨haBall, haNeg⟩ haInterior
  have hposSubsetA
      (haPos : 0 < g a) :
      posSide ⊆ interior A :=
    subset_interior_of_preconnected_of_disjoint_frontier
      hAclosed hposPreconnected hposDisjointA
        ⟨haBall, haPos⟩ haInterior
  have hnegSubsetB
      (hbNeg : g b < 0) :
      negSide ⊆ interior B :=
    subset_interior_of_preconnected_of_disjoint_frontier
      hBclosed hnegPreconnected hnegDisjointB
        ⟨hbBall, hbNeg⟩ hbInterior
  have hposSubsetB
      (hbPos : 0 < g b) :
      posSide ⊆ interior B :=
    subset_interior_of_preconnected_of_disjoint_frontier
      hBclosed hposPreconnected hposDisjointB
        ⟨hbBall, hbPos⟩ hbInterior
  have hcover :
      Metric.ball p ρ ⊆ A ∪ B := by
    intro z hzBall
    rcases lt_trichotomy (g z) 0 with
      hzNeg | hzZero | hzPos
    · by_cases haNeg : g a < 0
      · exact
          Or.inl <|
            interior_subset <|
              hnegSubsetA haNeg ⟨hzBall, hzNeg⟩
      · have haPos : 0 < g a :=
          lt_of_le_of_ne
            (le_of_not_gt haNeg) hga.symm
        have hbNeg : g b < 0 := by
          by_contra hbNotNeg
          have hbPos : 0 < g b :=
            lt_of_le_of_ne
              (le_of_not_gt hbNotNeg) hgb.symm
          exact hbNotA <|
            interior_subset <|
              hposSubsetA haPos ⟨hbBall, hbPos⟩
        exact
          Or.inr <|
            interior_subset <|
              hnegSubsetB hbNeg ⟨hzBall, hzNeg⟩
    · have hzD : z ∈ D :=
        hzero z hzBall hzZero
      exact Or.inl <|
        hAclosed.frontier_subset
          (hDfrontierA hzD)
    · by_cases haPos : 0 < g a
      · exact
          Or.inl <|
            interior_subset <|
              hposSubsetA haPos ⟨hzBall, hzPos⟩
      · have haNeg : g a < 0 := by
          have hle : g a ≤ 0 :=
            le_of_not_gt haPos
          exact lt_of_le_of_ne hle hga
        have hbPos : 0 < g b := by
          by_contra hbNotPos
          have hbNeg : g b < 0 := by
            have hle : g b ≤ 0 :=
              le_of_not_gt hbNotPos
            exact lt_of_le_of_ne hle hgb
          exact hbNotA <|
            interior_subset <|
              hnegSubsetA haNeg ⟨hbBall, hbNeg⟩
        exact
          Or.inr <|
            interior_subset <|
              hposSubsetB hbPos ⟨hzBall, hzPos⟩
  rw [mem_interior_iff_mem_nhds]
  exact
    Filter.mem_of_superset
      (Metric.ball_mem_nhds p hρ) hcover

/-- A frontier point of one closed child remains a frontier point of the
union when it is outside the other closed child. -/
theorem mem_frontier_union_of_notMem_right
    {A B : Set (ℝ × ℝ)}
    (hAclosed : IsClosed A)
    (hBclosed : IsClosed B)
    {x : ℝ × ℝ}
    (hxFrontier : x ∈ frontier A)
    (hxB : x ∉ B) :
    x ∈ frontier (A ∪ B) := by
  have hxA : x ∈ A :=
    hAclosed.frontier_subset hxFrontier
  apply
    (mem_frontier_iff_notMem_interior
      (show x ∈ A ∪ B from Or.inl hxA)).2
  intro hxInterior
  have hopen :
      IsOpen (interior (A ∪ B) ∩ Bᶜ) :=
    isOpen_interior.inter hBclosed.isOpen_compl
  have hsubset :
      interior (A ∪ B) ∩ Bᶜ ⊆ A := by
    rintro y ⟨hyInterior, hyB⟩
    rcases interior_subset hyInterior with hyA | hyB'
    · exact hyA
    · exact False.elim (hyB hyB')
  have hxInteriorA : x ∈ interior A :=
    interior_maximal hsubset hopen ⟨hxInterior, hxB⟩
  exact
    (mem_frontier_iff_notMem_interior hxA).mp
      hxFrontier hxInteriorA

/-- An attachable child can be glued to any closed child with a
preconnected exterior once their intersection is exactly the attaching
edge. -/
theorem isPreconnected_compl_union_of_attachable
    {A B D : Set (ℝ × ℝ)}
    (hattach : EdgeAttachable A D)
    (hBclosed : IsClosed B)
    (hBcompl : IsPreconnected Bᶜ)
    (hinter : A ∩ B = D) :
    IsPreconnected (A ∪ B)ᶜ := by
  rw [Set.union_comm]
  apply hattach hBclosed hBcompl
  rw [Set.inter_comm]
  exact hinter

/-- Edge attachability composes across an exact child intersection. -/
theorem EdgeAttachable.union_of_left
    {A B D E : Set (ℝ × ℝ)}
    (hattachA : EdgeAttachable A E)
    (hattachB : EdgeAttachable B D)
    (hAclosed : IsClosed A)
    (hinter : A ∩ B = D)
    (hEsubsetA : E ⊆ A)
    (hEinterB : E ∩ B ⊆ D) :
    EdgeAttachable (A ∪ B) E := by
  intro R hRclosed hRcompl hRinter
  have hRinterA : R ∩ A = E := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxR, hxA⟩
      have hxRK : x ∈ R ∩ (A ∪ B) :=
        ⟨hxR, Or.inl hxA⟩
      rwa [hRinter] at hxRK
    · intro x hxE
      have hxRK : x ∈ R ∩ (A ∪ B) := by
        rw [hRinter]
        exact hxE
      exact ⟨hxRK.1, hEsubsetA hxE⟩
  have hRAcompl :
      IsPreconnected (R ∪ A)ᶜ :=
    hattachA hRclosed hRcompl hRinterA
  have hRAclosed : IsClosed (R ∪ A) := by
    exact hRclosed.union hAclosed
  have hRAinterB : (R ∪ A) ∩ B = D := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxRorA, hxB⟩
      rcases hxRorA with hxR | hxA
      · have hxRK : x ∈ R ∩ (A ∪ B) :=
          ⟨hxR, Or.inr hxB⟩
        have hxE : x ∈ E := by
          rwa [hRinter] at hxRK
        exact hEinterB ⟨hxE, hxB⟩
      · rw [← hinter]
        exact ⟨hxA, hxB⟩
    · intro x hxD
      have hxAB : x ∈ A ∩ B := by
        rw [hinter]
        exact hxD
      exact ⟨Or.inr hxAB.1, hxAB.2⟩
  have hfinal :
      IsPreconnected ((R ∪ A) ∪ B)ᶜ :=
    hattachB hRAclosed hRAcompl hRAinterB
  simpa [Set.union_assoc] using hfinal

end Submission.DiskGluing
