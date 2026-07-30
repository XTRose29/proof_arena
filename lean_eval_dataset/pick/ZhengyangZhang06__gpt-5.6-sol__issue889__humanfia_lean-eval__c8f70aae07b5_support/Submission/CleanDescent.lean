import Submission.BackSubpolygon

open LeanEval.Geometry.PicksTheorem

namespace Submission.CleanDescent

/-- Data for the two possible strictly decreasing moves at a normalized
strictly exposed vertex.  An empty candidate removes the exposed vertex;
otherwise a visible chord cuts the polygon into the two consecutive
subpolygons. -/
inductive Step
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) : Type
  | ear
      (M : ℤ)
      (strictlyExposed :
        ∀ j : Fin (n + 1),
          j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
            ExtremeVertex.exposingFunctional M
                (toPlane (v j)) <
              ExtremeVertex.exposingFunctional M
                (toPlane
                  (v
                    (⟨1, by omega⟩ :
                      Fin (n + 1)))))
      (triangleSimple :
        IsSimple
          (latPoly (EarRemoval.earTriangle hn v)))
      (vertexEmpty :
        EmptyCap.VertexEmptyAtOne hn v triangleSimple)
      (outerBoundaryInter :
        (latPoly v).boundary (R := ℝ) ∩
            CleanEar.diagonal hn v =
          {toPlane (v 0),
            toPlane (v ⟨2, by omega⟩)})
      (reducedSimple :
        IsSimple
          (latPoly (EarRemoval.removeSecond v))) :
      Step hn v hsimple
  | diagonal
      (M : ℤ)
      (strictlyExposed :
        ∀ j : Fin (n + 1),
          j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
            ExtremeVertex.exposingFunctional M
                (toPlane (v j)) <
              ExtremeVertex.exposingFunctional M
                (toPlane
                  (v
                    (⟨1, by omega⟩ :
                      Fin (n + 1)))))
      (triangleSimple :
        IsSimple
          (latPoly (EarRemoval.earTriangle hn v)))
      (visible :
        VisibleDiagonal.Witness hn v triangleSimple)
      (three_le_q : 3 ≤ visible.q.val)
      (frontSimple :
        IsSimple
          (latPoly
            (FrontSubpolygon.vertices v visible.q)))
      (backSimple :
        IsSimple
          (latPoly
            (BackSubpolygon.vertices v visible.q
              three_le_q))) :
      Step hn v hsimple

/-- Every normalized simple polygon with at least four vertices admits a
strictly decreasing clean move. -/
theorem exists_step
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
                    Fin (n + 1))))) :
    Nonempty (Step hn v hsimple) := by
  have htriangle :
      IsSimple
        (latPoly (EarRemoval.earTriangle hn v)) :=
    ExposedTriangle.earTriangle_simple_of_strictlyExposed
      hn v hsimple
        (ExtremeVertex.exposingFunctional M)
        hvertices
  rcases
      VisibleDiagonal.vertexEmpty_or_visibleDiagonal
        hn v hsimple htriangle with
    hempty | hvisible
  · have houter :=
      EmptyCap.parentBoundary_inter_diagonal_of_vertexEmpty
        hn v hsimple htriangle hempty
    have hreduced :=
      CleanEar.reducedSimple_of_outerBoundaryInter
        hn v hsimple houter
    exact
      ⟨Step.ear M hvertices htriangle hempty
        houter hreduced⟩
  · obtain ⟨hvisible⟩ := hvisible
    have hqzero : hvisible.q.val ≠ 0 := by
      intro h
      exact hvisible.q_ne_zero (Fin.ext h)
    have hqone : hvisible.q.val ≠ 1 := by
      intro h
      exact hvisible.q_ne_one (Fin.ext h)
    have hqtwo : hvisible.q.val ≠ 2 := by
      intro h
      exact hvisible.q_ne_two (Fin.ext h)
    have hq : 3 ≤ hvisible.q.val := by
      omega
    have hfront :
        IsSimple
          (latPoly
            (FrontSubpolygon.vertices v hvisible.q)) :=
      FrontSubpolygon.isSimple_vertices_of_clean
        v hsimple hvisible.q hq hvisible.boundary_inter
    have hback :
        IsSimple
          (latPoly
            (BackSubpolygon.vertices v hvisible.q hq)) :=
      BackSubpolygon.isSimple_vertices_of_clean
        v hsimple hvisible.q hq hvisible.boundary_inter
    exact
      ⟨Step.diagonal M hvertices htriangle
        hvisible hq hfront hback⟩

/-- A property that is invariant under cyclic reindexing and is closed under
both clean reduction moves holds for every simple lattice polygon.  This is
the well-founded combinatorial core of the diagonal descent; topology enters
only when the two reduction hypotheses are instantiated. -/
theorem all_of_reduction_steps
    (P :
      {m : ℕ} → (Fin m → ℤ × ℤ) → Prop)
    (triangle :
      ∀ (v : Fin 3 → ℤ × ℤ),
        IsSimple (latPoly v) →
          P v)
    (unrotate :
      ∀ {m : ℕ} (k : ℕ)
        (v : Fin m → ℤ × ℤ),
        P (Rotate.rotatePow k v) →
          P v)
    (removeExposed :
      ∀ {n : ℕ} (hn : 3 ≤ n)
        (v : Fin (n + 1) → ℤ × ℤ)
        (_hsimple : IsSimple (latPoly v))
        (M : ℤ)
        (_hvertices :
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
        (_hempty :
          EmptyCap.VertexEmptyAtOne hn v htriangle)
        (_houter :
          (latPoly v).boundary (R := ℝ) ∩
              CleanEar.diagonal hn v =
            {toPlane (v 0),
              toPlane (v ⟨2, by omega⟩)}),
        P (EarRemoval.removeSecond v) →
          P v)
    (splitVisible :
      ∀ {n : ℕ} (hn : 3 ≤ n)
        (v : Fin (n + 1) → ℤ × ℤ)
        (_hsimple : IsSimple (latPoly v))
        (M : ℤ)
        (_hvertices :
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
        (hq : 3 ≤ visible.q.val),
        P (FrontSubpolygon.vertices v visible.q) →
          P (BackSubpolygon.vertices v visible.q hq) →
            P v) :
    ∀ {m : ℕ} (_hm : 3 ≤ m)
      (v : Fin m → ℤ × ℤ),
      IsSimple (latPoly v) →
        P v := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm v hsimple
      by_cases hmthree : m = 3
      · subst m
        exact triangle v hsimple
      · obtain ⟨n, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hn : 3 ≤ n := by
          omega
        letI : NeZero (n + 1) := ⟨by omega⟩
        obtain ⟨k, M, _, hvertices⟩ :=
          ExtremeVertex.exists_rotation_strictly_exposed_at_one
            (n := n + 1) (by omega) v
              (Helpers.lattice_vertex_injective_of_isSimple
                hsimple)
        let w := Rotate.rotatePow k v
        have hsimpleW : IsSimple (latPoly w) := by
          simpa [w] using
            Rotate.isSimple_rotatePow k hsimple
        obtain ⟨step⟩ :=
          exists_step hn w hsimpleW M
            (by simpa [w] using hvertices)
        apply unrotate k v
        change P w
        cases step with
        | ear M hvertices htriangle hempty houter hreduced =>
            apply
              removeExposed hn w hsimpleW M hvertices
                htriangle hempty houter
            exact
              ih n (by omega) hn
                (EarRemoval.removeSecond w) hreduced
        | diagonal M hvertices htriangle visible hq
            hfront hback =>
            apply
              splitVisible hn w hsimpleW M hvertices
                htriangle visible hq
            · exact
                ih visible.q.val visible.q.isLt hq
                  (FrontSubpolygon.vertices w visible.q)
                  hfront
            · exact
                ih (BackSubpolygon.size visible.q)
                  (BackSubpolygon.size_lt_parent
                    visible.q hq)
                  (BackSubpolygon.three_le_size
                    visible.q hq)
                  (BackSubpolygon.vertices w visible.q hq)
                  hback

end Submission.CleanDescent
