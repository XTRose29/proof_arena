import Submission.DiskDataGluing
import Submission.VisibleSeam

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleDisk

/-- The free child boundary chains are dense in the parent boundary. -/
theorem parentBoundary_subset_closure_free
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (visible :
      VisibleDiagonal.Witness hn v htriangle)
    (hq : 3 ≤ visible.q.val) :
    (latPoly v).boundary (R := ℝ) ⊆
      closure
        (((latPoly
              (FrontSubpolygon.vertices
                v visible.q)).boundary (R := ℝ) \
            segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v visible.q))) ∪
          ((latPoly
              (BackSubpolygon.vertices
                v visible.q hq)).boundary (R := ℝ) \
            segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v visible.q)))) := by
  let tip : ℝ × ℝ :=
    toPlane
      (v
        (⟨1, by omega⟩ :
          Fin (n + 1)))
  let two : ℝ × ℝ :=
    toPlane
      (v
        (⟨2, by omega⟩ :
          Fin (n + 1)))
  let qPoint : ℝ × ℝ :=
    toPlane (v visible.q)
  let D : Set (ℝ × ℝ) :=
    segment ℝ tip qPoint
  let L : Set (ℝ × ℝ) :=
    (latPoly
      (FrontSubpolygon.vertices
        v visible.q)).boundary (R := ℝ)
  let R : Set (ℝ × ℝ) :=
    (latPoly
      (BackSubpolygon.vertices
        v visible.q hq)).boundary (R := ℝ)
  let C : Set (ℝ × ℝ) :=
    (L \ D) ∪ (R \ D)
  have htipTwo : tip ≠ two := by
    have hindices :
        (⟨1, by omega⟩ : Fin (n + 1)) ≠
          (⟨2, by omega⟩ : Fin (n + 1)) := by
      intro h
      have hval : 1 = 2 :=
        congrArg Fin.val h
      omega
    simpa [tip, two, latPoly] using
      (Helpers.vertex_injective_of_isSimple hsimple).ne
        hindices
  have hopenTip : openSegment ℝ tip two ⊆ C := by
    intro z hzOpen
    have hzEdge :
        z ∈
          (latPoly v).edgeSet ℝ
            (⟨1, by omega⟩ :
              Fin (n + 1)) := by
      simpa [Polygon.edgeSet, latPoly,
        affineSegment_eq_segment, tip, two,
        CleanEar.finRotate_one hn] using
          openSegment_subset_segment ℝ tip two hzOpen
    have hzFront : z ∈ L := by
      dsimp [L]
      rw [Polygon.boundary]
      refine
        Set.mem_iUnion.mpr
          ⟨(⟨0, by omega⟩ :
            Fin visible.q.val), ?_⟩
      rw [FrontSubpolygon.edge_zero
        v visible.q hq]
      exact hzEdge
    have hzNotD : z ∉ D := by
      intro hzD
      have hzBoth :
          z ∈
            segment ℝ
                (toPlane
                  (v
                    (⟨1, by omega⟩ :
                      Fin (n + 1))))
                (toPlane (v visible.q)) ∩
              (latPoly v).edgeSet ℝ
                (⟨1, by omega⟩ :
                  Fin (n + 1)) := by
        simpa [D, tip, qPoint] using
          And.intro hzD hzEdge
      rw [FrontSubpolygon.diagonal_inter_first_edge
        v hsimple visible.q hq visible.boundary_inter] at hzBoth
      have hztip : z = tip := by
        simpa [tip] using hzBoth
      subst z
      exact htipTwo
        (left_mem_openSegment_iff.mp hzOpen)
    change
      (z ∈ L ∧ z ∉ D) ∨
        (z ∈ R ∧ z ∉ D)
    exact Or.inl ⟨hzFront, hzNotD⟩
  have htipClosure : tip ∈ closure C := by
    exact
      closure_mono hopenTip <|
        segment_subset_closure_openSegment <|
          left_mem_segment ℝ tip two
  let pred : Fin visible.q.val :=
    ⟨visible.q.val - 2, by omega⟩
  let predIndex : Fin (n + 1) :=
    FrontSubpolygon.frontIndex visible.q pred
  let predPoint : ℝ × ℝ :=
    toPlane (v predIndex)
  have hpredIndexNe : predIndex ≠ visible.q := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [predIndex, pred,
      FrontSubpolygon.frontIndex] at hval
    omega
  have hpredQ : predPoint ≠ qPoint := by
    simpa [predPoint, qPoint, latPoly] using
      (Helpers.vertex_injective_of_isSimple hsimple).ne
        hpredIndexNe
  have hpredLt : pred.val + 1 < visible.q.val := by
    dsimp [pred]
    omega
  have hopenQ :
      openSegment ℝ predPoint qPoint ⊆ C := by
    intro z hzOpen
    have hzEdge :
        z ∈ (latPoly v).edgeSet ℝ predIndex := by
      have hrotate :
          finRotate (n + 1) predIndex =
            visible.q := by
        rw [← FrontSubpolygon.frontIndex_rotate_of_lt
          visible.q pred hpredLt]
        apply Fin.ext
        rw [FrontSubpolygon.frontIndex_val,
          FrontSubpolygon.finRotate_val_of_lt
            visible.q pred hpredLt]
        dsimp [pred]
        omega
      simpa [Polygon.edgeSet, latPoly,
        affineSegment_eq_segment, predPoint, qPoint,
        predIndex, hrotate] using
          openSegment_subset_segment ℝ
            predPoint qPoint hzOpen
    have hzFront : z ∈ L := by
      dsimp [L]
      rw [Polygon.boundary]
      refine Set.mem_iUnion.mpr ⟨pred, ?_⟩
      rw [FrontSubpolygon.edge_of_lt
        v visible.q pred hpredLt]
      exact hzEdge
    have hzNotD : z ∉ D := by
      intro hzD
      have hzBoth :
          z ∈
            (latPoly v).edgeSet ℝ predIndex ∩
              segment ℝ
                (toPlane
                  (v
                    (⟨1, by omega⟩ :
                      Fin (n + 1))))
                (toPlane (v visible.q)) := by
        simpa [D, tip, qPoint] using
          And.intro hzEdge hzD
      rw [FrontSubpolygon.predecessor_edge_inter_diagonal
        v hsimple visible.q hq visible.boundary_inter] at hzBoth
      have hzq : z = qPoint := by
        simpa [qPoint] using hzBoth
      subst z
      exact hpredQ
        (right_mem_openSegment_iff.mp hzOpen)
    change
      (z ∈ L ∧ z ∉ D) ∨
        (z ∈ R ∧ z ∉ D)
    exact Or.inl ⟨hzFront, hzNotD⟩
  have hqClosure : qPoint ∈ closure C := by
    exact
      closure_mono hopenQ <|
        segment_subset_closure_openSegment <|
          right_mem_segment ℝ predPoint qPoint
  have hunion :
      L ∪ R =
        (latPoly v).boundary (R := ℝ) ∪ D := by
    simpa [L, R, D, tip, qPoint] using
      VisibleBoundary.childBoundaries_union
        v visible.q hq
  have hinter :
      (latPoly v).boundary (R := ℝ) ∩ D =
        {tip, qPoint} := by
    simpa [D, tip, qPoint] using
      visible.boundary_inter
  simpa [C, L, R, D, tip, qPoint] using
    DiskDataGluing.parent_subset_closure_free
      hunion hinter htipClosure hqClosure

/-- The parent filled region is the union of the two filled regions cut out
by a visible clean chord. -/
theorem parentRegion_eq_union
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (M : ℤ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          ExtremeVertex.exposingFunctional M
              (toPlane (v j)) <
            ExtremeVertex.exposingFunctional M
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1)))))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (visible :
      VisibleDiagonal.Witness hn v htriangle)
    (hq : 3 ≤ visible.q.val)
    (hfront :
      IsSimple
        (latPoly
          (FrontSubpolygon.vertices v visible.q)))
    (hback :
      IsSimple
        (latPoly
          (BackSubpolygon.vertices v visible.q hq)))
    (frontData :
      DiskData.Holds
        (FrontSubpolygon.vertices v visible.q))
    (backData :
      DiskData.Holds
        (BackSubpolygon.vertices v visible.q hq)) :
    DiskData.region v =
      DiskData.region
          (FrontSubpolygon.vertices v visible.q) ∪
        DiskData.region
          (BackSubpolygon.vertices v visible.q hq) := by
  let frontVertices :=
    FrontSubpolygon.vertices v visible.q
  let backVertices :=
    BackSubpolygon.vertices v visible.q hq
  let A := DiskData.region frontVertices
  let B := DiskData.region backVertices
  let D :=
    segment ℝ
      (toPlane
        (v
          (⟨1, by omega⟩ :
            Fin (n + 1))))
      (toPlane (v visible.q))
  have hinter : A ∩ B = D := by
    simpa [A, B, D, frontVertices, backVertices] using
      VisibleFillIntersection.childFills_inter
        hn v hsimple M hvertices htriangle visible hq
          hfront hback frontData backData
  let frontLast : Fin visible.q.val :=
    ⟨visible.q.val - 1, by omega⟩
  have hattachFront :
      DiskGluing.EdgeAttachable A D := by
    have h :=
      frontData.edgeAttachable frontLast
    rw [FrontSubpolygon.edge_last
      v visible.q (by omega)] at h
    simpa [A, D, frontVertices, frontLast] using h
  have hBclosed : IsClosed B := by
    dsimp [B, DiskData.region, backVertices]
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly
            (BackSubpolygon.vertices
              v visible.q hq))).isClosed
  have hBcompl : IsPreconnected Bᶜ := by
    dsimp [B, DiskData.region, backVertices]
    exact
      FilledRegion.isPreconnected_compl_fill
        (Helpers.isBounded_boundary
          (latPoly
            (BackSubpolygon.vertices
              v visible.q hq)))
  have hcompl : IsPreconnected (A ∪ B)ᶜ :=
    DiskGluing.isPreconnected_compl_union_of_attachable
      hattachFront hBclosed hBcompl hinter
  have hboundaryUnion :
      (latPoly frontVertices).boundary (R := ℝ) ∪
          (latPoly backVertices).boundary (R := ℝ) =
        (latPoly v).boundary (R := ℝ) ∪ D := by
    simpa [frontVertices, backVertices, D] using
      VisibleBoundary.childBoundaries_union
        v visible.q hq
  have hseam :
      D \ (latPoly v).boundary (R := ℝ) ⊆
        interior (A ∪ B) := by
    simpa [A, B, D, frontVertices, backVertices] using
      VisibleSeam.chord_sdiff_parent_subset_interior
        hn v hsimple htriangle visible hq hfront hback
          frontData backData
          (by
            simpa [A, B, D, frontVertices, backVertices]
              using hinter)
  change
    FilledRegion.fill
        ((latPoly v).boundary (R := ℝ)) =
      FilledRegion.fill
          ((latPoly frontVertices).boundary (R := ℝ)) ∪
        FilledRegion.fill
          ((latPoly backVertices).boundary (R := ℝ))
  apply
    FillFrontier.parentFill_eq_childFill_union
      (Helpers.isCompact_boundary
        (latPoly frontVertices)).isClosed
      (Helpers.isCompact_boundary
        (latPoly backVertices)).isClosed
      (Helpers.isBounded_boundary
        (latPoly frontVertices))
      (Helpers.isBounded_boundary
        (latPoly backVertices))
      hboundaryUnion hseam
  simpa [A, B, DiskData.region, frontVertices,
    backVertices] using hcompl

/-- Disk data is preserved by a visible clean-diagonal split. -/
theorem holds
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (M : ℤ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          ExtremeVertex.exposingFunctional M
              (toPlane (v j)) <
            ExtremeVertex.exposingFunctional M
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1)))))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (visible :
      VisibleDiagonal.Witness hn v htriangle)
    (hq : 3 ≤ visible.q.val)
    (hfront :
      IsSimple
        (latPoly
          (FrontSubpolygon.vertices v visible.q)))
    (hback :
      IsSimple
        (latPoly
          (BackSubpolygon.vertices v visible.q hq)))
    (frontData :
      DiskData.Holds
        (FrontSubpolygon.vertices v visible.q))
    (backData :
      DiskData.Holds
        (BackSubpolygon.vertices v visible.q hq)) :
    DiskData.Holds v := by
  let frontVertices :=
    FrontSubpolygon.vertices v visible.q
  let backVertices :=
    BackSubpolygon.vertices v visible.q hq
  let A := DiskData.region frontVertices
  let B := DiskData.region backVertices
  let tip :=
    toPlane
      (v
        (⟨1, by omega⟩ :
          Fin (n + 1)))
  let qPoint := toPlane (v visible.q)
  let D : Set (ℝ × ℝ) :=
    segment ℝ tip qPoint
  have hinter : A ∩ B = D := by
    simpa [A, B, D, tip, qPoint,
      frontVertices, backVertices] using
      VisibleFillIntersection.childFills_inter
        hn v hsimple M hvertices htriangle visible hq
          hfront hback frontData backData
  have hunion :
      DiskData.region v = A ∪ B := by
    simpa [A, B, frontVertices, backVertices] using
      parentRegion_eq_union hn v hsimple M hvertices
        htriangle visible hq hfront hback frontData backData
  let p :=
    AffineMap.lineMap tip qPoint (1 / 2 : ℝ)
  have hpOpen :
      p ∈ openSegment ℝ tip qPoint := by
    apply lineMap_mem_openSegment
    constructor <;> norm_num
  have hpD : p ∈ D := by
    exact
      openSegment_subset_segment ℝ tip qPoint hpOpen
  have htipNeQ : tip ≠ qPoint := by
    intro h
    apply visible.q_ne_one
    apply
      Helpers.vertex_injective_of_isSimple hsimple
    simpa [tip, qPoint, latPoly] using h.symm
  have hpNotParent :
      p ∉ (latPoly v).boundary (R := ℝ) := by
    intro hpParent
    have hpBoth :
        p ∈
          (latPoly v).boundary (R := ℝ) ∩
            segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v visible.q)) := by
      simpa [D, tip, qPoint] using
        And.intro hpParent hpD
    rw [visible.boundary_inter] at hpBoth
    rcases hpBoth with hptip | hpq
    · have hpEq : p = tip := by
        simpa [tip] using hptip
      have hpTip :
          tip ∈ openSegment ℝ tip qPoint :=
        hpEq ▸ hpOpen
      exact htipNeQ
        (left_mem_openSegment_iff.mp hpTip)
    · have hpEq : p = qPoint := by
        simpa [qPoint] using hpq
      have hpQ :
          qPoint ∈ openSegment ℝ tip qPoint :=
        hpEq ▸ hpOpen
      exact htipNeQ
        (right_mem_openSegment_iff.mp hpQ)
  have hseam :
      D \ (latPoly v).boundary (R := ℝ) ⊆
        interior (A ∪ B) := by
    simpa [A, B, D, tip, qPoint,
      frontVertices, backVertices] using
      VisibleSeam.chord_sdiff_parent_subset_interior
        hn v hsimple htriangle visible hq hfront hback
          frontData backData
          (by
            simpa [A, B, D, tip, qPoint,
              frontVertices, backVertices] using hinter)
  have hpBoth : p ∈ A ∩ B := by
    rw [hinter]
    exact hpD
  have hseamPoint :
      ∃ p,
        p ∈ A ∧ p ∈ B ∧ p ∈ interior (A ∪ B) :=
    ⟨p, hpBoth.1, hpBoth.2,
      hseam ⟨hpD, hpNotParent⟩⟩
  have hdense :
      (latPoly v).boundary (R := ℝ) ⊆
        closure
          (((latPoly frontVertices).boundary (R := ℝ) \ D) ∪
            ((latPoly backVertices).boundary (R := ℝ) \ D)) := by
    simpa [frontVertices, backVertices, D, tip, qPoint] using
      parentBoundary_subset_closure_free
        hn v hsimple htriangle visible hq
  have hAclosed : IsClosed A := by
    dsimp [A, DiskData.region, frontVertices]
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly
            (FrontSubpolygon.vertices
              v visible.q))).isClosed
  have hBclosed : IsClosed B := by
    dsimp [B, DiskData.region, backVertices]
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly
            (BackSubpolygon.vertices
              v visible.q hq))).isClosed
  let frontLast : Fin visible.q.val :=
    ⟨visible.q.val - 1, by omega⟩
  let backLast : Fin (BackSubpolygon.size visible.q) :=
    ⟨BackSubpolygon.size visible.q - 1, by
      have :=
        BackSubpolygon.three_le_size visible.q hq
      omega⟩
  have hattachFrontChord :
      DiskGluing.EdgeAttachable A D := by
    have h :=
      frontData.edgeAttachable frontLast
    rw [FrontSubpolygon.edge_last
      v visible.q (by omega)] at h
    simpa [A, D, tip, qPoint,
      frontVertices, frontLast] using h
  have hattachBackChord :
      DiskGluing.EdgeAttachable B D := by
    have h :=
      backData.edgeAttachable backLast
    rw [BackSubpolygon.edge_last
      v visible.q hq] at h
    simpa [B, D, tip, qPoint,
      backVertices, backLast] using h
  have hinter' : B ∩ A = D := by
    rw [Set.inter_comm]
    exact hinter
  have hedges :
      ∀ i : Fin (n + 1),
        DiskGluing.EdgeAttachable
          (A ∪ B) ((latPoly v).edgeSet ℝ i) := by
    intro i
    by_cases hfrontIndex :
        1 ≤ i.val ∧ i.val < visible.q.val
    · let j : Fin visible.q.val :=
        ⟨i.val - 1, by omega⟩
      have hj : j.val + 1 < visible.q.val := by
        dsimp [j]
        omega
      have hindex :
          FrontSubpolygon.frontIndex visible.q j = i := by
        apply Fin.ext
        dsimp [FrontSubpolygon.frontIndex, j]
        omega
      have hattach :
          DiskGluing.EdgeAttachable A
            ((latPoly v).edgeSet ℝ i) := by
        have h := frontData.edgeAttachable j
        rw [FrontSubpolygon.edge_of_lt
          v visible.q j hj, hindex] at h
        simpa [A, frontVertices] using h
      have hsubset :
          (latPoly v).edgeSet ℝ i ⊆ A := by
        intro x hxEdge
        change
          x ∈
            FilledRegion.fill
              ((latPoly frontVertices).boundary
                (R := ℝ))
        left
        rw [Polygon.boundary]
        refine Set.mem_iUnion.mpr ⟨j, ?_⟩
        rw [FrontSubpolygon.edge_of_lt
          v visible.q j hj, hindex]
        exact hxEdge
      exact
        DiskDataGluing.edgeAttachable_union_of_left
          hattach hattachBackChord hAclosed hinter
            hsubset
    · have hbackResult :
          DiskGluing.EdgeAttachable
            (B ∪ A) ((latPoly v).edgeSet ℝ i) := by
        by_cases hizero : i.val = 0
        · let j : Fin (BackSubpolygon.size visible.q) :=
            ⟨n + 1 - visible.q.val, by
              dsimp [BackSubpolygon.size]
              omega⟩
          have hj :
              j.val + 1 <
                BackSubpolygon.size visible.q := by
            dsimp [j, BackSubpolygon.size]
            omega
          have hindex :
              BackSubpolygon.parentIndex visible.q j = i := by
            apply Fin.ext
            simp [BackSubpolygon.parentIndex, j, hizero]
          have hattach :
              DiskGluing.EdgeAttachable B
                ((latPoly v).edgeSet ℝ i) := by
            have h := backData.edgeAttachable j
            rw [BackSubpolygon.edge_of_lt
              v visible.q hq j hj, hindex] at h
            simpa [B, backVertices] using h
          have hsubset :
              (latPoly v).edgeSet ℝ i ⊆ B := by
            intro x hxEdge
            change
              x ∈
                FilledRegion.fill
                  ((latPoly backVertices).boundary
                    (R := ℝ))
            left
            rw [Polygon.boundary]
            refine Set.mem_iUnion.mpr ⟨j, ?_⟩
            rw [BackSubpolygon.edge_of_lt
              v visible.q hq j hj, hindex]
            exact hxEdge
          exact
            DiskDataGluing.edgeAttachable_union_of_left
              hattach hattachFrontChord hBclosed
                hinter' hsubset
        · have hiq : visible.q.val ≤ i.val := by
            omega
          let j : Fin (BackSubpolygon.size visible.q) :=
            ⟨i.val - visible.q.val, by
              dsimp [BackSubpolygon.size]
              omega⟩
          have hj :
              j.val + 1 <
                BackSubpolygon.size visible.q := by
            dsimp [j, BackSubpolygon.size]
            omega
          have hindex :
              BackSubpolygon.parentIndex visible.q j = i := by
            apply Fin.ext
            simp [BackSubpolygon.parentIndex, j]
            rw [Nat.mod_eq_of_lt] <;> omega
          have hattach :
              DiskGluing.EdgeAttachable B
                ((latPoly v).edgeSet ℝ i) := by
            have h := backData.edgeAttachable j
            rw [BackSubpolygon.edge_of_lt
              v visible.q hq j hj, hindex] at h
            simpa [B, backVertices] using h
          have hsubset :
              (latPoly v).edgeSet ℝ i ⊆ B := by
            intro x hxEdge
            change
              x ∈
                FilledRegion.fill
                  ((latPoly backVertices).boundary
                    (R := ℝ))
            left
            rw [Polygon.boundary]
            refine Set.mem_iUnion.mpr ⟨j, ?_⟩
            rw [BackSubpolygon.edge_of_lt
              v visible.q hq j hj, hindex]
            exact hxEdge
          exact
            DiskDataGluing.edgeAttachable_union_of_left
              hattach hattachFrontChord hBclosed
                hinter' hsubset
      simpa [Set.union_comm] using hbackResult
  apply
    DiskDataGluing.holds_of_gluing
      v frontVertices backVertices D frontData backData
        (by simpa [A, B] using hinter)
        (by simpa [A, B] using hunion)
        (by simpa [A, B] using hseamPoint)
        hdense
  simpa [A, B] using hedges

end Submission.VisibleDisk
