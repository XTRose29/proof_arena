import Submission.PolygonIncidence

open LeanEval.Geometry.PicksTheorem

namespace Submission.PolygonLocal

/-- The relative interior of one polygon edge. -/
def openEdge
    {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (i : Fin n) :
    Set (ℝ × ℝ) :=
  openSegment ℝ (poly i) (poly (finRotate n i))

theorem openEdge_subset_edgeSet
    {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (i : Fin n) :
    openEdge poly i ⊆ poly.edgeSet ℝ i := by
  intro x hx
  simpa [openEdge, Polygon.edgeSet,
    affineSegment_eq_segment] using
    openSegment_subset_segment ℝ
      (poly i) (poly (finRotate n i)) hx

/-- In a simple polygon, the open part of an edge is disjoint from every
other edge, including the two adjacent edges. -/
theorem openEdge_disjoint_edgeSet
    {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (hsimple : IsSimple poly)
    (i j : Fin n)
    (hij : i ≠ j) :
    Disjoint (openEdge poly i) (poly.edgeSet ℝ j) := by
  rw [Set.disjoint_left]
  intro x hxOpen hxEdge
  have hxOwn : x ∈ poly.edgeSet ℝ i :=
    openEdge_subset_edgeSet poly i hxOpen
  by_cases hadj : Adjacent i j
  · rcases hadj with hforward | hbackward
    · have hinter :=
        hsimple.2.2 i
      rw [hforward] at hinter
      have hxVertex : x = poly j := by
        exact Set.mem_singleton_iff.mp <|
          hinter ▸ ⟨hxOwn, hxEdge⟩
      subst x
      have hcollapse :
          poly i = poly (finRotate n i) := by
        apply
          (right_mem_openSegment_iff
            (𝕜 := ℝ)).mp
        simpa [openEdge, hforward] using hxOpen
      exact hsimple.1 i hcollapse
    · have hinter :=
        hsimple.2.2 j
      rw [hbackward] at hinter
      have hxVertex : x = poly i := by
        exact Set.mem_singleton_iff.mp <|
          hinter ▸ ⟨hxEdge, hxOwn⟩
      subst x
      have hcollapse :
          poly i = poly (finRotate n i) := by
        apply
          (left_mem_openSegment_iff
            (𝕜 := ℝ)).mp
        simpa [openEdge] using hxOpen
      exact hsimple.1 i hcollapse
  · exact
      Set.disjoint_left.mp
        (hsimple.2.1 i j hij hadj)
        hxOwn hxEdge

/-- Near a relative-interior point of a simple polygon edge, no other
polygon edge occurs. -/
theorem exists_ball_boundary_subset_edge
    {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (hsimple : IsSimple poly)
    (i : Fin n)
    {p : ℝ × ℝ}
    (hp : p ∈ openEdge poly i) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ q ∈ Metric.ball p ρ,
        q ∈ poly.boundary (R := ℝ) →
          q ∈ poly.edgeSet ℝ i := by
  classical
  let otherEdges : Set (ℝ × ℝ) :=
    ⋃ j ∈ Finset.univ.erase i,
      poly.edgeSet ℝ j
  have hOtherClosed : IsClosed otherEdges := by
    dsimp [otherEdges]
    apply isClosed_biUnion_finset
    intro j hj
    rw [Polygon.edgeSet, affineSegment_eq_segment,
      segment_eq_image_lineMap]
    exact
      (isCompact_Icc.image
        AffineMap.lineMap_continuous).isClosed
  have hpOther : p ∈ otherEdgesᶜ := by
    intro hpUnion
    rcases Set.mem_iUnion.mp hpUnion with ⟨j, hpUnion⟩
    rcases Set.mem_iUnion.mp hpUnion with ⟨hj, hpEdge⟩
    have hji : j ≠ i :=
      (Finset.mem_erase.mp hj).1
    exact
      Set.disjoint_left.mp
        (openEdge_disjoint_edgeSet
          poly hsimple i j hji.symm)
        hp hpEdge
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.mp hOtherClosed.isOpen_compl
      p hpOther
  refine ⟨ρ, hρ, ?_⟩
  intro q hqBall hqBoundary
  rw [Polygon.boundary] at hqBoundary
  rcases Set.mem_iUnion.mp hqBoundary with
    ⟨j, hqEdge⟩
  by_cases hji : j = i
  · simpa [hji] using hqEdge
  · have hqOther : q ∈ otherEdges := by
      dsimp [otherEdges]
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, hqEdge⟩
      exact Finset.mem_erase.mpr
        ⟨hji, Finset.mem_univ j⟩
    exact False.elim <|
      (hball hqBall) hqOther

/-- Near a vertex of a simple polygon, the boundary consists only of the
two incident edges. -/
theorem exists_ball_boundary_subset_incident
    {n : ℕ} [NeZero n]
    (poly : Polygon (ℝ × ℝ) n)
    (hsimple : IsSimple poly)
    (i : Fin n) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ q ∈ Metric.ball (poly i) ρ,
        q ∈ poly.boundary (R := ℝ) →
          q ∈ poly.edgeSet ℝ i ∪
            poly.edgeSet ℝ ((finRotate n).symm i) := by
  classical
  let previous : Fin n :=
    (finRotate n).symm i
  let otherEdges : Set (ℝ × ℝ) :=
    ⋃ j ∈
        (Finset.univ.erase i).erase previous,
      poly.edgeSet ℝ j
  have hOtherClosed : IsClosed otherEdges := by
    dsimp [otherEdges]
    apply isClosed_biUnion_finset
    intro j hj
    rw [Polygon.edgeSet, affineSegment_eq_segment,
      segment_eq_image_lineMap]
    exact
      (isCompact_Icc.image
        AffineMap.lineMap_continuous).isClosed
  have hiOther : poly i ∈ otherEdgesᶜ := by
    intro hiUnion
    rcases Set.mem_iUnion.mp hiUnion with ⟨j, hiUnion⟩
    rcases Set.mem_iUnion.mp hiUnion with ⟨hj, hiEdge⟩
    have hjData :=
      Finset.mem_erase.mp hj
    have hjPrevious : j ≠ previous :=
      hjData.1
    have hji : j ≠ i :=
      (Finset.mem_erase.mp hjData.2).1
    have hiNext : i ≠ finRotate n j := by
      intro hnext
      have hprev : (finRotate n).symm i = j := by
        have h :=
          congrArg (finRotate n).symm hnext
        simpa using h
      exact hjPrevious hprev.symm
    exact
      PolygonIncidence.vertex_not_mem_edgeSet
        poly hsimple i j hji.symm hiNext hiEdge
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.mp hOtherClosed.isOpen_compl
      (poly i) hiOther
  refine ⟨ρ, hρ, ?_⟩
  intro q hqBall hqBoundary
  rw [Polygon.boundary] at hqBoundary
  rcases Set.mem_iUnion.mp hqBoundary with
    ⟨j, hqEdge⟩
  by_cases hji : j = i
  · exact Or.inl (by simpa [hji] using hqEdge)
  by_cases hjPrevious : j = previous
  · exact Or.inr (by simpa [hjPrevious, previous] using hqEdge)
  · have hqOther : q ∈ otherEdges := by
      dsimp [otherEdges]
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, hqEdge⟩
      exact Finset.mem_erase.mpr
        ⟨hjPrevious,
          Finset.mem_erase.mpr
            ⟨hji, Finset.mem_univ j⟩⟩
    exact False.elim <|
      (hball hqBall) hqOther

/-- Removing the left endpoint from a nondegenerate closed segment leaves a
preconnected set. -/
theorem isPreconnected_segment_sdiff_left
    {a b : ℝ × ℝ} (hab : a ≠ b) :
  IsPreconnected (segment ℝ a b \ {a}) := by
  apply
    (convex_openSegment (𝕜 := ℝ) a b).isPreconnected.subset_closure
  · intro x hx
    refine ⟨openSegment_subset_segment ℝ a b hx, ?_⟩
    intro hxa
    have : x = a := Set.mem_singleton_iff.mp hxa
    subst x
    exact hab (left_mem_openSegment_iff.mp hx)
  · intro x hx
    exact segment_subset_closure_openSegment hx.1

/-- Removing the right endpoint from a nondegenerate closed segment leaves a
preconnected set. -/
theorem isPreconnected_segment_sdiff_right
    {a b : ℝ × ℝ} (hab : a ≠ b) :
  IsPreconnected (segment ℝ a b \ {b}) := by
  apply
    (convex_openSegment (𝕜 := ℝ) a b).isPreconnected.subset_closure
  · intro x hx
    refine ⟨openSegment_subset_segment ℝ a b hx, ?_⟩
    intro hxb
    have : x = b := Set.mem_singleton_iff.mp hxb
    subst x
    exact hab (right_mem_openSegment_iff.mp hx)
  · intro x hx
    exact segment_subset_closure_openSegment hx.1

/-- For a simple polygon with at least three vertices, deleting its closing
edge leaves the open polygonal chain, which is preconnected. -/
theorem isPreconnected_boundary_sdiff_last
    {k : ℕ}
    (poly : Polygon (ℝ × ℝ) (k + 3))
    (hsimple : IsSimple poly) :
    IsPreconnected
      (poly.boundary (R := ℝ) \
        poly.edgeSet ℝ (Fin.last (k + 2))) := by
  let last : Fin (k + 3) :=
    Fin.last (k + 2)
  let piece :
      Fin (k + 2) → Set (ℝ × ℝ) :=
    fun i =>
      poly.edgeSet ℝ i.castSucc \
        poly.edgeSet ℝ last
  have hcastNeLast :
      ∀ i : Fin (k + 2),
        i.castSucc ≠ last := by
    intro i h
    have hval := congrArg Fin.val h
    dsimp [last] at hval
    omega
  have hpiecePreconnected :
      ∀ i : Fin (k + 2),
        IsPreconnected (piece i) := by
    intro i
    let j : Fin (k + 3) := i.castSucc
    have hjlast : j ≠ last :=
      hcastNeLast i
    by_cases hadj : Adjacent last j
    · rcases hadj with hforward | hbackward
      · have hinter :
            poly.edgeSet ℝ last ∩
                poly.edgeSet ℝ j =
              {poly j} := by
          have h := hsimple.2.2 last
          rw [hforward] at h
          exact h
        have hdiff :
            poly.edgeSet ℝ j \
                poly.edgeSet ℝ last =
              poly.edgeSet ℝ j \ {poly j} := by
          ext x
          constructor
          · rintro ⟨hxEdge, hxLast⟩
            refine ⟨hxEdge, ?_⟩
            intro hxVertex
            apply hxLast
            have hxBoth :
                x ∈
                  poly.edgeSet ℝ last ∩
                    poly.edgeSet ℝ j := by
              rw [hinter]
              exact hxVertex
            exact hxBoth.1
          · rintro ⟨hxEdge, hxVertex⟩
            refine ⟨hxEdge, ?_⟩
            intro hxLast
            apply hxVertex
            have hxBoth :
                x ∈
                  poly.edgeSet ℝ last ∩
                    poly.edgeSet ℝ j :=
              ⟨hxLast, hxEdge⟩
            rw [hinter] at hxBoth
            exact hxBoth
        change
          IsPreconnected
            (poly.edgeSet ℝ j \
              poly.edgeSet ℝ last)
        rw [hdiff, Polygon.edgeSet,
          affineSegment_eq_segment]
        exact
          isPreconnected_segment_sdiff_left
            (hsimple.1 j)
      · have hinter :
            poly.edgeSet ℝ j ∩
                poly.edgeSet ℝ last =
              {poly last} := by
          have h := hsimple.2.2 j
          rw [hbackward] at h
          exact h
        have hdiff :
            poly.edgeSet ℝ j \
                poly.edgeSet ℝ last =
              poly.edgeSet ℝ j \ {poly last} := by
          ext x
          constructor
          · rintro ⟨hxEdge, hxLast⟩
            refine ⟨hxEdge, ?_⟩
            intro hxVertex
            apply hxLast
            have hxBoth :
                x ∈
                  poly.edgeSet ℝ j ∩
                    poly.edgeSet ℝ last := by
              rw [hinter]
              exact hxVertex
            exact hxBoth.2
          · rintro ⟨hxEdge, hxVertex⟩
            refine ⟨hxEdge, ?_⟩
            intro hxLast
            apply hxVertex
            have hxBoth :
                x ∈
                  poly.edgeSet ℝ j ∩
                    poly.edgeSet ℝ last :=
              ⟨hxEdge, hxLast⟩
            rw [hinter] at hxBoth
            exact hxBoth
        change
          IsPreconnected
            (poly.edgeSet ℝ j \
              poly.edgeSet ℝ last)
        rw [hdiff, Polygon.edgeSet,
          affineSegment_eq_segment, hbackward]
        have hne := hsimple.1 j
        rw [hbackward] at hne
        exact
          isPreconnected_segment_sdiff_right
            hne
    · have hdisjoint :
          Disjoint
            (poly.edgeSet ℝ j)
            (poly.edgeSet ℝ last) :=
        (hsimple.2.1 last j hjlast.symm hadj).symm
      have hdiff :
          poly.edgeSet ℝ j \
              poly.edgeSet ℝ last =
            poly.edgeSet ℝ j := by
        ext x
        constructor
        · exact fun hx => hx.1
        · intro hx
          refine ⟨hx, ?_⟩
          exact
            Set.disjoint_left.mp hdisjoint hx
      change
        IsPreconnected
          (poly.edgeSet ℝ j \
            poly.edgeSet ℝ last)
      rw [hdiff, Polygon.edgeSet,
        affineSegment_eq_segment]
      exact (convex_segment _ _).isPreconnected
  have hpieceChain :
      ∀ i : Fin (k + 2),
        (piece i ∩ piece (Order.succ i)).Nonempty := by
    intro i
    by_cases hilast : i = Fin.last (k + 1)
    · subst i
      rw [Fin.orderSucc_last]
      let j : Fin (k + 3) :=
        (Fin.last (k + 1)).castSucc
      have hjNotClosing :
          poly j ∉ poly.edgeSet ℝ last := by
        apply
          PolygonIncidence.vertex_not_mem_edgeSet
            poly hsimple j last
        · intro h
          have hval := congrArg Fin.val h
          dsimp [j, last] at hval
          omega
        · rw [finRotate_last]
          intro h
          have hval := congrArg Fin.val h
          dsimp [j] at hval
          omega
      refine
        ⟨poly j, ?_, ?_⟩
      · exact
          ⟨left_mem_affineSegment ℝ _ _,
            hjNotClosing⟩
      · exact
          ⟨left_mem_affineSegment ℝ _ _,
            hjNotClosing⟩
    · obtain ⟨r, rfl⟩ :=
        Fin.eq_castSucc_of_ne_last hilast
      let j : Fin (k + 3) :=
        r.castSucc.castSucc
      let jnext : Fin (k + 3) :=
        r.succ.castSucc
      have hrotate :
          finRotate (k + 3) j = jnext := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last]
        · rfl
        · intro h
          have hval := congrArg Fin.val h
          dsimp [j] at hval
          omega
      have hjnextNotClosing :
          poly jnext ∉ poly.edgeSet ℝ last := by
        apply
          PolygonIncidence.vertex_not_mem_edgeSet
            poly hsimple jnext last
        · intro h
          have hval := congrArg Fin.val h
          dsimp [jnext, last] at hval
          omega
        · rw [finRotate_last]
          intro h
          have hval := congrArg Fin.val h
          dsimp [jnext] at hval
          omega
      refine
        ⟨poly jnext, ?_, ?_⟩
      · refine
          ⟨?_, hjnextNotClosing⟩
        change
          poly jnext ∈
            affineSegment ℝ (poly j)
              (poly (finRotate (k + 3) j))
        rw [hrotate]
        exact right_mem_affineSegment ℝ _ _
      · refine
          ⟨?_, hjnextNotClosing⟩
        have hsucc :
            (Order.succ r.castSucc).castSucc =
              jnext := by
          apply Fin.ext
          simp [jnext]
        rw [hsucc]
        exact left_mem_affineSegment ℝ _ _
  have hunion :
      IsPreconnected (⋃ i, piece i) :=
    IsPreconnected.iUnion_of_chain
      hpiecePreconnected hpieceChain
  have hboundary :
      poly.boundary (R := ℝ) \
          poly.edgeSet ℝ last =
        ⋃ i, piece i := by
    ext x
    constructor
    · rintro ⟨hxBoundary, hxLast⟩
      rw [Polygon.boundary] at hxBoundary
      rcases Set.mem_iUnion.mp hxBoundary with
        ⟨j, hxEdge⟩
      have hjNotLast : j ≠ last := by
        intro h
        subst j
        exact hxLast hxEdge
      have hjlt : j.val < k + 2 := by
        by_contra h
        apply hjNotLast
        apply Fin.ext
        dsimp [last]
        omega
      let i : Fin (k + 2) :=
        ⟨j.val, hjlt⟩
      have hij : i.castSucc = j := by
        apply Fin.ext
        rfl
      exact
        Set.mem_iUnion.mpr
          ⟨i, by
            change
              x ∈
                poly.edgeSet ℝ i.castSucc \
                  poly.edgeSet ℝ last
            rw [hij]
            exact ⟨hxEdge, hxLast⟩⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with
        ⟨i, hxPiece⟩
      refine ⟨?_, hxPiece.2⟩
      rw [Polygon.boundary]
      exact
        Set.mem_iUnion.mpr
          ⟨i.castSucc, hxPiece.1⟩
  rw [hboundary]
  exact hunion

/-- Size-independent form of
`isPreconnected_boundary_sdiff_last`. -/
theorem isPreconnected_boundary_sdiff_last_of_three_le
    {m : ℕ} (hm : 3 ≤ m)
    (poly : Polygon (ℝ × ℝ) m)
    (hsimple : IsSimple poly) :
    IsPreconnected
      (poly.boundary (R := ℝ) \
        poly.edgeSet ℝ
          (⟨m - 1, by omega⟩ : Fin m)) := by
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_le hm
  have hk' : m = k + 3 := by
    omega
  clear hk
  subst m
  have hlast :
      (⟨k + 3 - 1, by omega⟩ : Fin (k + 3)) =
        Fin.last (k + 2) := by
    apply Fin.ext
    simp
  rw [hlast]
  exact
    isPreconnected_boundary_sdiff_last
      (k := k) poly hsimple

end Submission.PolygonLocal
