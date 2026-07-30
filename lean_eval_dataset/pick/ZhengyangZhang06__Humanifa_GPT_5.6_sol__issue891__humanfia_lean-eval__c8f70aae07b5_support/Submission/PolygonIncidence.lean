import Submission.ExposedTriangle

open LeanEval.Geometry.PicksTheorem

namespace Submission.PolygonIncidence

/-- In a simple polygon, the only vertices lying on an edge are its two
endpoints. -/
theorem vertex_mem_edgeSet_iff
    {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (hsimple : IsSimple poly)
    (i j : Fin n) :
    poly i ∈ poly.edgeSet ℝ j ↔
      i = j ∨ i = finRotate n j := by
  constructor
  · intro hi
    by_cases hij : i = j
    · exact Or.inl hij
    by_cases hisucc : i = finRotate n j
    · exact Or.inr hisucc
    have hnotAdjacent : ¬ Adjacent i j := by
      intro hadj
      rcases hadj with hforward | hbackward
      · have hiNext :
            poly i ∈ poly.edgeSet ℝ
              (finRotate n i) := by
          rw [hforward]
          exact hi
        have hiInter :
            poly i ∈
              poly.edgeSet ℝ i ∩
                poly.edgeSet ℝ (finRotate n i) :=
          ⟨left_mem_affineSegment ℝ _ _, hiNext⟩
        rw [hsimple.2.2 i] at hiInter
        exact
          hsimple.1 i
            (Set.mem_singleton_iff.mp hiInter)
      · exact hisucc hbackward.symm
    have hdisjoint :=
      hsimple.2.1 i j hij hnotAdjacent
    exact
      (Set.disjoint_left.mp hdisjoint
        (left_mem_affineSegment ℝ _ _) hi).elim
  · rintro (rfl | rfl)
    · exact left_mem_affineSegment ℝ _ _
    · exact right_mem_affineSegment ℝ _ _

/-- A vertex whose index is neither endpoint of an edge is disjoint from
that edge. -/
theorem vertex_not_mem_edgeSet
    {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (hsimple : IsSimple poly)
    (i j : Fin n)
    (hij : i ≠ j)
    (hisucc : i ≠ finRotate n j) :
    poly i ∉ poly.edgeSet ℝ j := by
  rw [vertex_mem_edgeSet_iff poly hsimple i j]
  exact not_or_intro hij hisucc

end Submission.PolygonIncidence
