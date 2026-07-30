import Submission.BackSubpolygon
import Submission.ReducedSupport

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleSupport

private theorem exposed_le
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (hn : 1 ≤ n)
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
    (j : Fin (n + 1)) :
    ExtremeVertex.exposingFunctional M
        (toPlane (v j)) ≤
      ExtremeVertex.exposingFunctional M
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1)))) := by
  by_cases hj :
      j =
        (⟨1, by omega⟩ :
          Fin (n + 1))
  · subst j
    exact le_rfl
  · exact (hvertices j hj).le

/-- The boundary of the front visible subpolygon remains below the
strictly exposed parent tip. -/
theorem frontBoundary_le
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (hn : 1 ≤ n)
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
    (q : Fin (n + 1)) :
    ∀ x ∈
        (latPoly
          (FrontSubpolygon.vertices v q)).boundary
            (R := ℝ),
      ExtremeVertex.exposingFunctional M x ≤
        ExtremeVertex.exposingFunctional M
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1)))) := by
  apply
    ReducedSupport.continuousLinearMap_le_on_boundary
  intro i
  exact
    exposed_le v hn M hvertices
      (FrontSubpolygon.frontIndex q i)

/-- Consequently the complete filled front child remains below the exposed
supporting line. -/
theorem frontFill_subset_halfspace
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (hn : 1 ≤ n)
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
    (q : Fin (n + 1)) :
    FilledRegion.fill
        ((latPoly
          (FrontSubpolygon.vertices v q)).boundary
            (R := ℝ)) ⊆
      {x : ℝ × ℝ |
        ExtremeVertex.exposingFunctional M x ≤
          ExtremeVertex.exposingFunctional M
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))} := by
  let d : ℝ × ℝ := (0, -1)
  have hd :
      0 <
        ExtremeVertex.exposingFunctional M d := by
    simp [d, ExtremeVertex.exposingFunctional]
  exact
    FillHalfspace.fill_subset_halfSpace_le
      (ExtremeVertex.exposingFunctional M)
      (ExtremeVertex.exposingFunctional M
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1)))))
      d hd (frontBoundary_le v hn M hvertices q)

/-- The boundary of the complementary visible subpolygon also remains below
the strictly exposed parent tip. -/
theorem backBoundary_le
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (hn : 1 ≤ n)
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
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    ∀ x ∈
        (latPoly
          (BackSubpolygon.vertices v q hq)).boundary
            (R := ℝ),
      ExtremeVertex.exposingFunctional M x ≤
        ExtremeVertex.exposingFunctional M
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1)))) := by
  apply
    ReducedSupport.continuousLinearMap_le_on_boundary
  intro i
  let j : Fin (n + 1) :=
    ((finRotate (n + 1))^[q.val - 1])
      (FrontSubpolygon.frontIndex
        (BackSubpolygon.endpoint q hq) i)
  have hvertex :
      BackSubpolygon.vertices v q hq i =
        v j := by
    change
      BackSubpolygon.rotated v q
          (FrontSubpolygon.frontIndex
            (BackSubpolygon.endpoint q hq) i) =
        v j
    rw [BackSubpolygon.rotated,
      Rotate.rotatePow_apply]
  rw [hvertex]
  exact exposed_le v hn M hvertices j

/-- Consequently the complete filled complementary child remains below the
same exposed supporting line. -/
theorem backFill_subset_halfspace
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (hn : 1 ≤ n)
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
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    FilledRegion.fill
        ((latPoly
          (BackSubpolygon.vertices v q hq)).boundary
            (R := ℝ)) ⊆
      {x : ℝ × ℝ |
        ExtremeVertex.exposingFunctional M x ≤
          ExtremeVertex.exposingFunctional M
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))} := by
  let d : ℝ × ℝ := (0, -1)
  have hd :
      0 <
        ExtremeVertex.exposingFunctional M d := by
    simp [d, ExtremeVertex.exposingFunctional]
  exact
    FillHalfspace.fill_subset_halfSpace_le
      (ExtremeVertex.exposingFunctional M)
      (ExtremeVertex.exposingFunctional M
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1)))))
      d hd (backBoundary_le v hn M hvertices q hq)

end Submission.VisibleSupport
