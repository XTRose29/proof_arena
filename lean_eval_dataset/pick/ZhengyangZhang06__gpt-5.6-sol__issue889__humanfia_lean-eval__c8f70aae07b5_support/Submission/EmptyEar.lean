import Submission.EmptyEarFill
import Submission.FillFrontier

open LeanEval.Geometry.PicksTheorem

namespace Submission.EmptyEar

/-- For an ear attachment, boundedness and the child-boundary union reduce
the parent-fill equality to two geometric facts: the diagonal is in the
parent fill and the union of the child fills has preconnected complement. -/
theorem parentFill_eq_childFill_union
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hdiagonal :
      CleanEar.diagonal hn v ⊆
        FilledRegion.fill
          ((latPoly v).boundary (R := ℝ)))
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill
              ((latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ)))ᶜ) :
    FilledRegion.fill
          ((latPoly v).boundary (R := ℝ)) =
        FilledRegion.fill
            ((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ)) ∪
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)) := by
  apply
    FillUnion.parentFill_eq_childFill_union_of_bounded
      (Helpers.isBounded_boundary (latPoly v))
      (Helpers.isBounded_boundary
        (latPoly (EarRemoval.earTriangle hn v)))
      (Helpers.isBounded_boundary
        (latPoly (EarRemoval.removeSecond v)))
      (EarRemoval.child_boundaries_union hn v)
      hdiagonal hcomplPreconnected

/-- A local two-sided seam and a one-component exterior give the same
parent-fill equality without separately assuming that the diagonal already
belongs to the parent fill. -/
theorem parentFill_eq_childFill_union_of_local
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hseamInterior :
      CleanEar.diagonal hn v \
          (latPoly v).boundary (R := ℝ) ⊆
        interior
          (FilledRegion.fill
                ((latPoly
                  (EarRemoval.earTriangle hn v)).boundary
                    (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ))))
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill
              ((latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ)))ᶜ) :
    FilledRegion.fill
          ((latPoly v).boundary (R := ℝ)) =
        FilledRegion.fill
            ((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ)) ∪
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)) := by
  apply
    FillFrontier.parentFill_eq_childFill_union
      (Helpers.isCompact_boundary
        (latPoly (EarRemoval.earTriangle hn v))).isClosed
      (Helpers.isCompact_boundary
        (latPoly (EarRemoval.removeSecond v))).isClosed
      (Helpers.isBounded_boundary
        (latPoly (EarRemoval.earTriangle hn v)))
      (Helpers.isBounded_boundary
        (latPoly (EarRemoval.removeSecond v)))
      (EarRemoval.child_boundaries_union hn v)
      hseamInterior hcomplPreconnected

/-- The local empty-cap construction produces a core ear once the diagonal
has been identified as internal and the attached child-fill exterior is
preconnected. -/
theorem coreIsEarAtOne_of_vertexEmpty
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
    (hdiagonal :
      CleanEar.diagonal hn v ⊆
        FilledRegion.fill
          ((latPoly v).boundary (R := ℝ)))
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill
              ((latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ)))ᶜ) :
    CleanEar.CoreIsEarAtOne hn v := by
  have hfillUnion :=
    parentFill_eq_childFill_union
      hn v hdiagonal hcomplPreconnected
  have hfillInter :=
    EmptyEarFill.childFill_inter_eq_diagonal
      hn v hsimple M hvertices htriangle hempty
  exact
    FillEar.coreIsEarAtOne_of_fill_gluing
      hn v hsimple houter hfillUnion hfillInter

/-- Local seam interior and exterior reachability are sufficient for the
same empty-ear certificate. -/
theorem coreIsEarAtOne_of_vertexEmpty_of_local
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
    (hseamInterior :
      CleanEar.diagonal hn v \
          (latPoly v).boundary (R := ℝ) ⊆
        interior
          (FilledRegion.fill
                ((latPoly
                  (EarRemoval.earTriangle hn v)).boundary
                    (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ))))
    (hcomplPreconnected :
      IsPreconnected
        (FilledRegion.fill
              ((latPoly
                (EarRemoval.earTriangle hn v)).boundary
                  (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond v)).boundary
                  (R := ℝ)))ᶜ) :
    CleanEar.CoreIsEarAtOne hn v := by
  have hfillUnion :=
    parentFill_eq_childFill_union_of_local
      hn v hseamInterior hcomplPreconnected
  have hfillInter :=
    EmptyEarFill.childFill_inter_eq_diagonal
      hn v hsimple M hvertices htriangle hempty
  exact
    FillEar.coreIsEarAtOne_of_fill_gluing
      hn v hsimple houter hfillUnion hfillInter

/-- The finite/local data isolated by the empty-cap reduction. -/
structure Witness
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) : Type where
  M : ℤ
  strictlyExposed :
    ∀ j : Fin (n + 1),
      j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
        ExtremeVertex.exposingFunctional M
            (toPlane (v j)) <
          ExtremeVertex.exposingFunctional M
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
  triangleSimple :
    IsSimple
      (latPoly (EarRemoval.earTriangle hn v))
  vertexEmpty :
    EmptyCap.VertexEmptyAtOne hn v triangleSimple
  outerBoundaryInter :
    (latPoly v).boundary (R := ℝ) ∩
        CleanEar.diagonal hn v =
      {toPlane (v 0),
        toPlane (v ⟨2, by omega⟩)}
  diagonalInParentFill :
    CleanEar.diagonal hn v ⊆
      FilledRegion.fill
        ((latPoly v).boundary (R := ℝ))
  childFillComplPreconnected :
    IsPreconnected
      (FilledRegion.fill
            ((latPoly
              (EarRemoval.earTriangle hn v)).boundary
                (R := ℝ)) ∪
          FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)))ᶜ

/-- A local witness supplies the exact core ear certificate. -/
theorem Witness.toCoreIsEarAtOne
    {n : ℕ} {hn : 3 ≤ n}
    {v : Fin (n + 1) → ℤ × ℤ}
    (w : Witness hn v)
    (hsimple : IsSimple (latPoly v)) :
    CleanEar.CoreIsEarAtOne hn v :=
  coreIsEarAtOne_of_vertexEmpty
    hn v hsimple w.M w.strictlyExposed
      w.triangleSimple w.vertexEmpty
      w.outerBoundaryInter w.diagonalInParentFill
      w.childFillComplPreconnected

end Submission.EmptyEar
