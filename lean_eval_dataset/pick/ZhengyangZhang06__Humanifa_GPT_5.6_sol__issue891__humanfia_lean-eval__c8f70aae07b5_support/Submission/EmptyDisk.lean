import Submission.DiskDataGluing
import Submission.EmptyEar
import Submission.EmptyEarExterior
import Submission.EmptyEarSeam

open LeanEval.Geometry.PicksTheorem

namespace Submission.EmptyDisk

/-- The two free child boundaries are dense in the parent boundary for an
empty-ear split. -/
theorem parentBoundary_subset_closure_free
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (_hsimple : IsSimple (latPoly v))
    (htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)))
    (houter :
      (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v =
        {toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)}) :
    (latPoly v).boundary (R := ℝ) ⊆
      closure
        (((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ) \
            CleanEar.diagonal hn v) ∪
          ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ) \
            CleanEar.diagonal hn v)) := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let P := (latPoly v).boundary (R := ℝ)
  let L := (latPoly ear).boundary (R := ℝ)
  let R := (latPoly reduced).boundary (R := ℝ)
  let D := CleanEar.diagonal hn v
  let p0 := toPlane (v 0)
  let p1 :=
    toPlane
      (v
        (⟨1, by omega⟩ :
          Fin (n + 1)))
  let p2 :=
    toPlane
      (v
        (⟨2, by omega⟩ :
          Fin (n + 1)))
  let C := (L \ D) ∪ (R \ D)
  have hopenZeroOne :
      openSegment ℝ p0 p1 ⊆ C := by
    intro z hzOpen
    have hzEdge :
        z ∈
          (latPoly ear).edgeSet ℝ
            (0 : Fin 3) := by
      rw [EarRemoval.ear_edge_zero hn v]
      change
        z ∈ affineSegment ℝ
          (toPlane (v 0))
          (toPlane
            (v (finRotate (n + 1) 0)))
      rw [CleanEar.finRotate_zero hn,
        affineSegment_eq_segment]
      change z ∈ segment ℝ p0 p1
      exact openSegment_subset_segment ℝ p0 p1 hzOpen
    have hzL : z ∈ L := by
      dsimp [L]
      rw [Polygon.boundary]
      exact Set.mem_iUnion.mpr ⟨0, hzEdge⟩
    have hzNotD : z ∉ D := by
      intro hzD
      have hzEdgeTwo :
          z ∈
            (latPoly ear).edgeSet ℝ
              (2 : Fin 3) := by
        rw [EarRemoval.ear_edge_two hn v]
        exact hzD
      have hzInter :
          z ∈
            (latPoly ear).edgeSet ℝ (2 : Fin 3) ∩
              (latPoly ear).edgeSet ℝ (0 : Fin 3) :=
        ⟨hzEdgeTwo, hzEdge⟩
      have hinter := htriangle.2.2 (2 : Fin 3)
      have hrotate :
          finRotate 3 (2 : Fin 3) = (0 : Fin 3) := by
        decide
      rw [hrotate] at hinter
      rw [hinter] at hzInter
      have hzp0 : z = p0 := by
        simpa [ear, p0, latPoly] using
          Set.mem_singleton_iff.mp hzInter
      subst z
      have hp0p1 : p0 ≠ p1 := by
        simpa [p0, p1, ear, latPoly] using
          htriangle.1 (0 : Fin 3)
      exact hp0p1
        (left_mem_openSegment_iff.mp hzOpen)
    exact Or.inl ⟨hzL, hzNotD⟩
  have hp0Closure : p0 ∈ closure C := by
    exact
      closure_mono hopenZeroOne <|
        segment_subset_closure_openSegment <|
          left_mem_segment ℝ p0 p1
  have hopenOneTwo :
      openSegment ℝ p1 p2 ⊆ C := by
    intro z hzOpen
    have hzEdge :
        z ∈
          (latPoly ear).edgeSet ℝ
            (1 : Fin 3) := by
      rw [EarRemoval.ear_edge_one hn v]
      change
        z ∈ affineSegment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane
            (v
              (finRotate (n + 1)
                (⟨1, by omega⟩ :
                  Fin (n + 1)))))
      rw [CleanEar.finRotate_one hn,
        affineSegment_eq_segment]
      change z ∈ segment ℝ p1 p2
      exact openSegment_subset_segment ℝ p1 p2 hzOpen
    have hzL : z ∈ L := by
      dsimp [L]
      rw [Polygon.boundary]
      exact Set.mem_iUnion.mpr ⟨1, hzEdge⟩
    have hzNotD : z ∉ D := by
      intro hzD
      have hzEdgeTwo :
          z ∈
            (latPoly ear).edgeSet ℝ
              (2 : Fin 3) := by
        rw [EarRemoval.ear_edge_two hn v]
        exact hzD
      have hzInter :
          z ∈
            (latPoly ear).edgeSet ℝ (1 : Fin 3) ∩
              (latPoly ear).edgeSet ℝ (2 : Fin 3) :=
        ⟨hzEdge, hzEdgeTwo⟩
      have hinter := htriangle.2.2 (1 : Fin 3)
      have hrotate :
          finRotate 3 (1 : Fin 3) = (2 : Fin 3) := by
        decide
      rw [hrotate] at hinter
      rw [hinter] at hzInter
      have hzp2 : z = p2 := by
        simpa [ear, p2, latPoly] using
          Set.mem_singleton_iff.mp hzInter
      subst z
      have hp1p2 : p1 ≠ p2 := by
        simpa [p1, p2, ear, latPoly] using
          htriangle.1 (1 : Fin 3)
      exact hp1p2
        (right_mem_openSegment_iff.mp hzOpen)
    exact Or.inl ⟨hzL, hzNotD⟩
  have hp2Closure : p2 ∈ closure C := by
    exact
      closure_mono hopenOneTwo <|
        segment_subset_closure_openSegment <|
          right_mem_segment ℝ p1 p2
  have hunion :
      L ∪ R = P ∪ D := by
    simpa [L, R, P, D, ear, reduced,
      CleanEar.diagonal] using
      EarRemoval.child_boundaries_union hn v
  have hinter :
      P ∩ D = {p0, p2} := by
    simpa [P, D, p0, p2] using houter
  simpa [C, L, R, P, D, p0, p2, ear, reduced] using
    DiskDataGluing.parent_subset_closure_free
      hunion hinter hp0Closure hp2Closure

/-- Disk data is preserved by removing and reattaching a strictly exposed,
vertex-empty ear. -/
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
    (hempty :
      EmptyCap.VertexEmptyAtOne hn v htriangle)
    (houter :
      (latPoly v).boundary (R := ℝ) ∩
          CleanEar.diagonal hn v =
        {toPlane (v 0),
          toPlane (v ⟨2, by omega⟩)})
    (reducedData :
      DiskData.Holds (EarRemoval.removeSecond v)) :
    DiskData.Holds v := by
  let ear := EarRemoval.earTriangle hn v
  let reduced := EarRemoval.removeSecond v
  let A := DiskData.region ear
  let B := DiskData.region reduced
  let D := CleanEar.diagonal hn v
  let p0 := toPlane (v 0)
  let p2 :=
    toPlane
      (v
        (⟨2, by omega⟩ :
          Fin (n + 1)))
  let triangleData : DiskData.Holds ear :=
    DiskData.triangle ear htriangle
  have hinter : A ∩ B = D := by
    simpa [A, B, D, ear, reduced, DiskData.region] using
      EmptyEarFill.childFill_inter_eq_diagonal
        hn v hsimple M hvertices htriangle hempty
  have hseam :
      D \ (latPoly v).boundary (R := ℝ) ⊆
        interior (A ∪ B) := by
    simpa [A, B, D, ear, reduced, DiskData.region] using
      EmptyEarSeam.diagonal_sdiff_parent_subset_interior
        hn v hsimple M hvertices htriangle hempty houter
          reducedData.regular
  have hcompl :
      IsPreconnected (A ∪ B)ᶜ := by
    simpa [A, B, ear, reduced, DiskData.region] using
      EmptyEarExterior.childFill_compl_isPreconnected
        hn v hsimple M hvertices htriangle hempty
  have hunion :
      DiskData.region v = A ∪ B := by
    simpa [A, B, ear, reduced, DiskData.region] using
      EmptyEar.parentFill_eq_childFill_union_of_local
        hn v
          (by
            simpa [A, B, D, ear, reduced,
              DiskData.region] using hseam)
          (by
            simpa [A, B, ear, reduced,
              DiskData.region] using hcompl)
  let p := AffineMap.lineMap p0 p2 (1 / 2 : ℝ)
  have hpOpen : p ∈ openSegment ℝ p0 p2 := by
    apply lineMap_mem_openSegment
    constructor <;> norm_num
  have hpD : p ∈ D := by
    simpa [D, p0, p2, CleanEar.diagonal] using
      openSegment_subset_segment ℝ p0 p2 hpOpen
  have hp0p2 : p0 ≠ p2 := by
    have hindices :
        (0 : Fin (n + 1)) ≠
          (⟨2, by omega⟩ : Fin (n + 1)) := by
      intro h
      have := congrArg Fin.val h
      norm_num at this
    simpa [p0, p2, latPoly] using
      (Helpers.vertex_injective_of_isSimple hsimple).ne
        hindices
  have hpNotParent :
      p ∉ (latPoly v).boundary (R := ℝ) := by
    intro hpParent
    have hpBoth :
        p ∈
          (latPoly v).boundary (R := ℝ) ∩
            CleanEar.diagonal hn v :=
      ⟨hpParent, hpD⟩
    rw [houter] at hpBoth
    rcases hpBoth with hpZero | hpTwo
    · have hpEq : p = p0 := by
        simpa [p0] using hpZero
      rw [hpEq] at hpOpen
      exact hp0p2
        (left_mem_openSegment_iff.mp hpOpen)
    · have hpEq : p = p2 := by
        simpa [p2] using hpTwo
      rw [hpEq] at hpOpen
      exact hp0p2
        (right_mem_openSegment_iff.mp hpOpen)
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
          (((latPoly ear).boundary (R := ℝ) \ D) ∪
            ((latPoly reduced).boundary (R := ℝ) \ D)) := by
    simpa [ear, reduced, D] using
      parentBoundary_subset_closure_free
        hn v hsimple htriangle houter
  have hAclosed : IsClosed A := by
    dsimp [A, DiskData.region, ear]
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly (EarRemoval.earTriangle hn v))).isClosed
  have hBclosed : IsClosed B := by
    dsimp [B, DiskData.region, reduced]
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly (EarRemoval.removeSecond v))).isClosed
  have hattachTriangleD :
      DiskGluing.EdgeAttachable A D := by
    have h := triangleData.edgeAttachable (2 : Fin 3)
    rw [EarRemoval.ear_edge_two hn v] at h
    simpa [A, D, ear, CleanEar.diagonal] using h
  have hattachReducedD :
      DiskGluing.EdgeAttachable B D := by
    have h :=
      reducedData.edgeAttachable
        (⟨0, by omega⟩ : Fin n)
    rw [EarRemoval.reduced_edge_zero hn v] at h
    simpa [B, D, reduced, CleanEar.diagonal] using h
  have hinter' : B ∩ A = D := by
    rw [Set.inter_comm]
    exact hinter
  have hedges :
      ∀ i : Fin (n + 1),
        DiskGluing.EdgeAttachable
          (A ∪ B) ((latPoly v).edgeSet ℝ i) := by
    intro i
    by_cases hizero : i.val = 0
    · have hi : i = (0 : Fin (n + 1)) :=
        Fin.ext hizero
      subst i
      have hattach :
          DiskGluing.EdgeAttachable A
            ((latPoly v).edgeSet ℝ
              (0 : Fin (n + 1))) := by
        have h := triangleData.edgeAttachable (0 : Fin 3)
        rw [EarRemoval.ear_edge_zero hn v] at h
        simpa [A, ear] using h
      have hsubset :
          (latPoly v).edgeSet ℝ
              (0 : Fin (n + 1)) ⊆ A := by
        intro x hx
        change
          x ∈
            FilledRegion.fill
              ((latPoly ear).boundary (R := ℝ))
        left
        rw [Polygon.boundary]
        refine Set.mem_iUnion.mpr ⟨(0 : Fin 3), ?_⟩
        rw [EarRemoval.ear_edge_zero hn v]
        exact hx
      exact
        DiskDataGluing.edgeAttachable_union_of_left
          hattach hattachReducedD hAclosed hinter hsubset
    · by_cases hione : i.val = 1
      · have hi :
            i =
              (⟨1, by omega⟩ :
                Fin (n + 1)) :=
          Fin.ext hione
        rw [hi]
        have hattach :
            DiskGluing.EdgeAttachable A
              ((latPoly v).edgeSet ℝ
                (⟨1, by omega⟩ :
                  Fin (n + 1))) := by
          have h := triangleData.edgeAttachable (1 : Fin 3)
          rw [EarRemoval.ear_edge_one hn v] at h
          simpa [A, ear] using h
        have hsubset :
            (latPoly v).edgeSet ℝ
                (⟨1, by omega⟩ :
                  Fin (n + 1)) ⊆ A := by
          intro x hx
          change
            x ∈
              FilledRegion.fill
                ((latPoly ear).boundary (R := ℝ))
          left
          rw [Polygon.boundary]
          refine Set.mem_iUnion.mpr ⟨(1 : Fin 3), ?_⟩
          rw [EarRemoval.ear_edge_one hn v]
          exact hx
        exact
          DiskDataGluing.edgeAttachable_union_of_left
            hattach hattachReducedD hAclosed hinter hsubset
      · have hiTwo : 2 ≤ i.val := by
          omega
        let j : Fin n :=
          ⟨i.val - 1, by omega⟩
        have hjzero : j.val ≠ 0 := by
          dsimp [j]
          omega
        have hindex :
            EarRemoval.reducedIndex j = i := by
          apply Fin.ext
          simp [EarRemoval.reducedIndex, j, hjzero]
          omega
        have hattach :
            DiskGluing.EdgeAttachable B
              ((latPoly v).edgeSet ℝ i) := by
          have h := reducedData.edgeAttachable j
          rw [EarRemoval.reduced_edge_of_ne_zero
            hn v j hjzero, hindex] at h
          simpa [B, reduced] using h
        have hsubset :
            (latPoly v).edgeSet ℝ i ⊆ B := by
          intro x hx
          change
            x ∈
              FilledRegion.fill
                ((latPoly reduced).boundary (R := ℝ))
          left
          rw [Polygon.boundary]
          refine Set.mem_iUnion.mpr ⟨j, ?_⟩
          rw [EarRemoval.reduced_edge_of_ne_zero
            hn v j hjzero, hindex]
          exact hx
        have hback :
            DiskGluing.EdgeAttachable
              (B ∪ A) ((latPoly v).edgeSet ℝ i) :=
          DiskDataGluing.edgeAttachable_union_of_left
            hattach hattachTriangleD hBclosed hinter' hsubset
        simpa [Set.union_comm] using hback
  apply
    DiskDataGluing.holds_of_gluing
      v ear reduced D triangleData reducedData
        (by simpa [A, B] using hinter)
        (by simpa [A, B] using hunion)
        (by simpa [A, B] using hseamPoint)
        hdense
  simpa [A, B] using hedges

end Submission.EmptyDisk
