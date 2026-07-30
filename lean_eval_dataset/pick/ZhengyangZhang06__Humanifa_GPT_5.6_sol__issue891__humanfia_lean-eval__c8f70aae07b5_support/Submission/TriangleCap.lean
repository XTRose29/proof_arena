import Submission.FilledRegion
import Submission.TriangleCoords

namespace Submission.TriangleCap

/-- The closed triangle with its base opposite vertex `1` removed, expressed
as a convex barycentric half-space. -/
def openCap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Set (ℝ × ℝ) :=
  t.closedInterior ∩
    (Submission.Triangle.affineBasis t).coord 1 ⁻¹'
      Set.Ioi 0

/-- The open cap is convex. -/
theorem convex_openCap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Convex ℝ (openCap t) := by
  exact
    (Submission.Triangle.convex_closedInterior t).inter <|
      Convex.affine_preimage
        ((Submission.Triangle.affineBasis t).coord 1)
        (convex_Ioi 0)

/-- The distinguished vertex belongs to its open cap. -/
theorem point_one_mem_openCap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    t.points 1 ∈ openCap t := by
  refine ⟨t.point_mem_closedInterior 1, ?_⟩
  simp

/-- If a triangle cap avoids an obstacle and its tip is outside the
obstacle's fill, the whole cap belongs to an unbounded complement component.
When the base already lies in the fill, this identifies the exact
triangle/fill intersection. -/
theorem closedInterior_inter_fill_eq_faceOpposite_one
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {B : Set (ℝ × ℝ)}
    (hcapCompl : openCap t ⊆ Bᶜ)
    (htip : t.points 1 ∉ FilledRegion.fill B)
    (hfaceFill :
      (t.faceOpposite 1).closedInterior ⊆
        FilledRegion.fill B) :
    t.closedInterior ∩ FilledRegion.fill B =
      (t.faceOpposite 1).closedInterior := by
  have htipCap :
      t.points 1 ∈ openCap t :=
    point_one_mem_openCap t
  have htipCompl :
      t.points 1 ∈ Bᶜ :=
    hcapCompl htipCap
  have htipComponentUnbounded :
      ¬ Bornology.IsBounded
        (connectedComponentIn Bᶜ (t.points 1)) := by
    intro hbounded
    exact
      htip <|
        Or.inr ⟨htipCompl, hbounded⟩
  have hcapComponent :
      openCap t ⊆
        connectedComponentIn Bᶜ (t.points 1) :=
    (convex_openCap t).isPreconnected.subset_connectedComponentIn
        htipCap hcapCompl
  have hcapFillDisjoint :
      ∀ x ∈ openCap t,
        x ∉ FilledRegion.fill B := by
    intro x hxCap hxFill
    rcases hxFill with hxB | hxInside
    · exact hcapCompl hxCap hxB
    · have htipComponentSubset :
          connectedComponentIn Bᶜ (t.points 1) ⊆
            connectedComponentIn Bᶜ x :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn
            (hcapComponent hxCap)
            (connectedComponentIn_subset Bᶜ
              (t.points 1))
      exact
        htipComponentUnbounded
          (hxInside.2.subset htipComponentSubset)
  apply Set.Subset.antisymm
  · intro x hx
    have hxClosed :
        x ∈ t.closedInterior :=
      hx.1
    by_cases hxCap : x ∈ openCap t
    · exact False.elim <|
        hcapFillDisjoint x hxCap hx.2
    · have hcoordNonneg :
          0 ≤
            (Submission.Triangle.affineBasis t).coord
              1 x :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t x).mp hxClosed 1
      have hcoordNotPos :
          ¬ 0 <
            (Submission.Triangle.affineBasis t).coord
              1 x := by
        intro hpos
        exact hxCap ⟨hxClosed, hpos⟩
      have hcoordZero :
          (Submission.Triangle.affineBasis t).coord
              1 x =
            0 :=
        le_antisymm (le_of_not_gt hcoordNotPos)
          hcoordNonneg
      exact
        (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
          t hxClosed 1).mp hcoordZero
  · intro x hxFace
    exact
      ⟨t.closedInterior_faceOpposite_subset_closedInterior
          1 hxFace,
        hfaceFill hxFace⟩

end Submission.TriangleCap
