import Submission.DiskData
import Submission.VisibleBoundary

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleFillIntersection

/-- Disk data for the two visible children, together with the local
opposite-side witnesses, forces their filled regions to meet exactly in the
clean chord. -/
theorem childFills_inter
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
    DiskData.region
          (FrontSubpolygon.vertices v visible.q) ∩
        DiskData.region
          (BackSubpolygon.vertices v visible.q hq) =
      segment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v visible.q)) := by
  let frontVertices :=
    FrontSubpolygon.vertices v visible.q
  let backVertices :=
    BackSubpolygon.vertices v visible.q hq
  let frontBoundary :=
    (latPoly frontVertices).boundary (R := ℝ)
  let backBoundary :=
    (latPoly backVertices).boundary (R := ℝ)
  let A := DiskData.region frontVertices
  let B := DiskData.region backVertices
  let D :=
    segment ℝ
      (toPlane
        (v
          (⟨1, by omega⟩ :
            Fin (n + 1))))
      (toPlane (v visible.q))
  have hAclosed : IsClosed A := by
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly frontVertices)).isClosed
  have hBclosed : IsClosed B := by
    exact
      FilledRegion.isClosed_fill
        (Helpers.isCompact_boundary
          (latPoly backVertices)).isClosed
  have hboundaryInter :
      frontBoundary ∩ backBoundary = D := by
    simpa [frontBoundary, backBoundary, D,
      frontVertices, backVertices] using
        VisibleBoundary.childBoundaries_inter
          hn v hsimple visible.q hq
  have hDfrontBoundary :
      D ⊆ frontBoundary := by
    intro x hxD
    have hxBoth :
        x ∈ frontBoundary ∩ backBoundary := by
      rw [hboundaryInter]
      exact hxD
    exact hxBoth.1
  have hDbackBoundary :
      D ⊆ backBoundary := by
    intro x hxD
    have hxBoth :
        x ∈ frontBoundary ∩ backBoundary := by
      rw [hboundaryInter]
      exact hxD
    exact hxBoth.2
  have hfreeBack :
      IsPreconnected (backBoundary \ D) := by
    have h :=
      PolygonLocal.isPreconnected_boundary_sdiff_last_of_three_le
        (BackSubpolygon.three_le_size visible.q hq)
        (latPoly backVertices) hback
    rw [BackSubpolygon.edge_last
      v visible.q hq] at h
    simpa [backBoundary, backVertices, D] using h
  obtain ⟨x, hxFreeFront, hxOutsideBack⟩ :=
    VisibleOutside.exists_front_point_outside_back
      hn v M hvertices htriangle visible hq hback
  have hxFreeFront' :
      x ∈ frontBoundary \ D := by
    simpa [frontBoundary, frontVertices, D] using
      hxFreeFront
  have hxOutsideBack' : x ∉ B := by
    simpa [B, backVertices, DiskData.region] using
      hxOutsideBack
  obtain ⟨y, hyFreeBack, hyOutsideFront⟩ :=
    VisibleOutside.exists_back_point_outside_front
      hn v M hvertices htriangle visible hq hfront
  have hyFreeBack' :
      y ∈ backBoundary \ D := by
    simpa [backBoundary, backVertices, D] using
      hyFreeBack
  have hyOutsideFront' : y ∉ A := by
    simpa [A, frontVertices, DiskData.region] using
      hyOutsideFront
  have hfreeBackFrontier :
      Disjoint (backBoundary \ D) (frontier A) := by
    rw [← frontData.boundary_eq_frontier,
      Set.disjoint_left]
    intro z hzBack hzFront
    have hzBoth :
        z ∈ frontBoundary ∩ backBoundary :=
      ⟨hzFront, hzBack.1⟩
    rw [hboundaryInter] at hzBoth
    exact hzBack.2 hzBoth
  have hfreeBackCompl :
      backBoundary \ D ⊆ Aᶜ :=
    DiskGluing.subset_compl_of_preconnected_of_disjoint_frontier
      hAclosed hfreeBack hfreeBackFrontier
        hyFreeBack' hyOutsideFront'
  have hAsideFrontier :
      Disjoint (A \ D) (frontier B) := by
    rw [← backData.boundary_eq_frontier,
      Set.disjoint_left]
    intro z hzA hzBack
    have hzFreeBack :
        z ∈ backBoundary \ D :=
      ⟨hzBack, hzA.2⟩
    exact (hfreeBackCompl hzFreeBack) hzA.1
  have hDfrontierA :
      D ⊆ frontier A := by
    rw [← frontData.boundary_eq_frontier]
    exact hDfrontBoundary
  have hAside :
      IsPreconnected (A \ D) :=
    DiskGluing.isPreconnected_sdiff_frontier_subset
      frontData.regular
      frontData.interiorPreconnected
      hDfrontierA
  have hDsubsetA : D ⊆ A := by
    intro z hzD
    exact Or.inl (hDfrontBoundary hzD)
  have hDsubsetB : D ⊆ B := by
    intro z hzD
    exact Or.inl (hDbackBoundary hzD)
  have hxAside : x ∈ A \ D :=
    ⟨Or.inl hxFreeFront'.1, hxFreeFront'.2⟩
  have hinter :
      A ∩ B = D :=
    DiskGluing.inter_eq_root_of_one_preconnected_side
      hBclosed hDsubsetA hDsubsetB hAside
        hAsideFrontier hxAside hxOutsideBack'
  simpa [A, B, D, frontVertices, backVertices] using
    hinter

end Submission.VisibleFillIntersection
