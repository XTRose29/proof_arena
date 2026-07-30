import Submission.ExtremeVertex
import Submission.FillHalfspace

open LeanEval.Geometry.PicksTheorem

namespace Submission.ReducedSupport

/-- A weak linear-functional bound at all vertices extends to every polygon
edge. -/
theorem continuousLinearMap_le_on_boundary
    {n : ℕ}
    (v : Fin n → ℤ × ℤ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (c : ℝ)
    (hvertices :
      ∀ i : Fin n, L (toPlane (v i)) ≤ c) :
    ∀ x ∈ (latPoly v).boundary (R := ℝ),
      L x ≤ c := by
  intro x hx
  rw [Polygon.boundary] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hhalfspace :
      Convex ℝ {y : ℝ × ℝ | L y ≤ c} :=
    convex_halfSpace_le L.toLinearMap.isLinear c
  exact
    hhalfspace.segment_subset
      (hvertices i)
      (hvertices (finRotate n i))
      (by
        simpa only [Polygon.edgeSet,
          affineSegment_eq_segment, latPoly] using hi)

/-- The finitely many reduced vertices have a maximum support level, and
strict exposure keeps that maximum below the deleted vertex. -/
theorem exists_strict_reduced_support_level
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (M : ℤ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          ExtremeVertex.exposingFunctional M
              (toPlane (v j)) <
            ExtremeVertex.exposingFunctional M
              (toPlane
                (v (⟨1, by omega⟩ :
                  Fin (n + 1))))) :
    ∃ c : ℝ,
      c <
          ExtremeVertex.exposingFunctional M
            (toPlane
              (v (⟨1, by omega⟩ :
                Fin (n + 1)))) ∧
        ∀ x ∈
          (latPoly
            (EarRemoval.removeSecond v)).boundary
              (R := ℝ),
          ExtremeVertex.exposingFunctional M x ≤ c := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_max_image
      Finset.univ
      (fun j : Fin n =>
        ExtremeVertex.exposingFunctional M
          (toPlane (EarRemoval.removeSecond v j)))
      Finset.univ_nonempty
  let c :=
    ExtremeVertex.exposingFunctional M
      (toPlane (EarRemoval.removeSecond v i))
  refine ⟨c, ?_, ?_⟩
  · exact
      hvertices (EarRemoval.reducedIndex i)
        (EarRemoval.reducedIndex_ne_one
          (by omega) i)
  · apply continuousLinearMap_le_on_boundary
    intro j
    exact hi j (Finset.mem_univ j)

/-- Consequently the entire filled reduced polygon remains below a level
that is strictly lower than the exposed vertex. -/
theorem exists_fill_reduced_support_level
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (M : ℤ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          ExtremeVertex.exposingFunctional M
              (toPlane (v j)) <
            ExtremeVertex.exposingFunctional M
              (toPlane
                (v (⟨1, by omega⟩ :
                  Fin (n + 1))))) :
    ∃ c : ℝ,
      c <
          ExtremeVertex.exposingFunctional M
            (toPlane
              (v (⟨1, by omega⟩ :
                Fin (n + 1)))) ∧
        FilledRegion.fill
            ((latPoly
              (EarRemoval.removeSecond v)).boundary
                (R := ℝ)) ⊆
          {x : ℝ × ℝ |
            ExtremeVertex.exposingFunctional M x ≤ c} := by
  obtain ⟨c, hc, hboundary⟩ :=
    exists_strict_reduced_support_level
      hn v M hvertices
  let d : ℝ × ℝ := (0, -1)
  have hd :
      0 <
        ExtremeVertex.exposingFunctional M d := by
    simp [d, ExtremeVertex.exposingFunctional]
  exact
    ⟨c, hc,
      FillHalfspace.fill_subset_halfSpace_le
        (ExtremeVertex.exposingFunctional M)
        c d hd hboundary⟩

end Submission.ReducedSupport
