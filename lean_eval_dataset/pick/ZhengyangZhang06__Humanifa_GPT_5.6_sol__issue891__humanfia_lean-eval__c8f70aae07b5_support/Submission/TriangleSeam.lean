import Submission.AttachmentExterior
import Submission.FilledRegion
import Submission.TriangleCoords

open LeanEval.Geometry.PicksTheorem
open Filter
open scoped Topology

namespace Submission.TriangleSeam

/-- A point on a triangle face is locally interior after attachment when a
small ball has no obstacle off the face and the filled obstacle reaches the
opposite side. -/
theorem mem_interior_union_closedInterior_of_opposite_fill_point
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {B : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hside :
      ∀ q ∈ Metric.ball p ρ,
        0 <
            (Submission.Triangle.affineBasis t).coord 0 q ∧
          0 <
            (Submission.Triangle.affineBasis t).coord 2 q)
    (hboundary :
      ∀ q ∈ Metric.ball p ρ,
        q ∈ B →
          (Submission.Triangle.affineBasis t).coord 1 q = 0)
    (hopposite :
      ∃ z ∈ Metric.ball p ρ,
        (Submission.Triangle.affineBasis t).coord 1 z < 0 ∧
          z ∈ FilledRegion.fill B) :
    p ∈
      interior
        (FilledRegion.fill B ∪
          t.closedInterior) := by
  obtain ⟨z, hzBall, hzNeg, hzFill⟩ :=
    hopposite
  have hzNotB : z ∉ B := by
    intro hzB
    exact
      (ne_of_lt hzNeg)
        (hboundary z hzBall hzB)
  have hzInside : z ∈ inside B := by
    rcases hzFill with hzB | hzInside
    · exact False.elim (hzNotB hzB)
    · exact hzInside
  let H : Set (ℝ × ℝ) :=
    Metric.ball p ρ ∩
      {q |
        (Submission.Triangle.affineBasis t).coord 1 q < 0}
  have hHconvex : Convex ℝ H := by
    exact
      (convex_ball p ρ).inter <|
        (convex_Iio (0 : ℝ)).affine_preimage
          ((Submission.Triangle.affineBasis t).coord 1)
  have hzH : z ∈ H :=
    ⟨hzBall, hzNeg⟩
  have hHsubset : H ⊆ Bᶜ := by
    rintro q ⟨hqBall, hqNeg⟩ hqB
    exact
      (ne_of_lt hqNeg)
        (hboundary q hqBall hqB)
  have hcover :
      Metric.ball p ρ ⊆
        FilledRegion.fill B ∪
          t.closedInterior := by
    intro q hqBall
    by_cases hqNeg :
        (Submission.Triangle.affineBasis t).coord 1 q < 0
    · have hqH : q ∈ H :=
        ⟨hqBall, hqNeg⟩
      have hzq :
          JoinedIn Bᶜ z q := by
        apply
          (hHconvex.isPathConnected ⟨z, hzH⟩).joinedIn
            z hzH q hqH |>.mono
        exact hHsubset
      have hqComponent :
          q ∈ connectedComponentIn Bᶜ z :=
        AttachmentExterior.target_mem_connectedComponentIn_of_joinedIn
          hzq
      have hcomponents :
          connectedComponentIn Bᶜ z =
            connectedComponentIn Bᶜ q :=
        connectedComponentIn_eq hqComponent
      have hqInside : q ∈ inside B := by
        refine ⟨hHsubset hqH, ?_⟩
        rw [← hcomponents]
        exact hzInside.2
      exact Or.inl (Or.inr hqInside)
    · right
      rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
      intro i
      have hqSide := hside q hqBall
      fin_cases i
      · exact hqSide.1.le
      · exact le_of_not_gt hqNeg
      · exact hqSide.2.le
  rw [mem_interior_iff_mem_nhds]
  exact
    Filter.mem_of_superset
      (Metric.ball_mem_nhds p hρ) hcover

/-- Regularity of the filled obstacle supplies the opposite-side point
required by the local seam lemma. -/
theorem exists_opposite_fill_point_of_regular
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {B : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hside :
      ∀ q ∈ Metric.ball p ρ,
        0 <
            (Submission.Triangle.affineBasis t).coord 0 q ∧
          0 <
            (Submission.Triangle.affineBasis t).coord 2 q)
    (hregular :
      closure (interior (FilledRegion.fill B)) =
        FilledRegion.fill B)
    (hinter :
      FilledRegion.fill B ∩ t.closedInterior =
        (t.faceOpposite 1).closedInterior)
    (hpFace :
      p ∈ (t.faceOpposite 1).closedInterior) :
    ∃ z ∈ Metric.ball p ρ,
      (Submission.Triangle.affineBasis t).coord 1 z < 0 ∧
        z ∈ FilledRegion.fill B := by
  have hpClosed :
      p ∈ t.closedInterior :=
    t.closedInterior_faceOpposite_subset_closedInterior
      1 hpFace
  have hpFill : p ∈ FilledRegion.fill B := by
    have hpBoth :
        p ∈
          FilledRegion.fill B ∩
            t.closedInterior := by
      rw [hinter]
      exact hpFace
    exact hpBoth.1
  have hpClosure :
      p ∈
        closure
          (interior (FilledRegion.fill B)) := by
    rw [hregular]
    exact hpFill
  obtain ⟨z, hzBall, hzInterior⟩ :=
    (mem_closure_iff.mp hpClosure)
      (Metric.ball p ρ) Metric.isOpen_ball
      (Metric.mem_ball_self hρ)
  have hzNeg :
      (Submission.Triangle.affineBasis t).coord 1 z < 0 := by
    by_contra hzNotNeg
    have hzOneNonneg :
        0 ≤
          (Submission.Triangle.affineBasis t).coord 1 z :=
      le_of_not_gt hzNotNeg
    have hzSide := hside z hzBall
    have hzClosed :
        z ∈ t.closedInterior := by
      rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
      intro i
      fin_cases i
      · exact hzSide.1.le
      · exact hzOneNonneg
      · exact hzSide.2.le
    have hzFace :
        z ∈ (t.faceOpposite 1).closedInterior := by
      rw [← hinter]
      exact
        ⟨interior_subset hzInterior, hzClosed⟩
    have hzOneZero :
        (Submission.Triangle.affineBasis t).coord 1 z = 0 :=
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hzClosed 1).mpr hzFace
    have hnear :
        ∀ᶠ δ : ℝ in 𝓝[>] 0,
          AffineMap.lineMap z (t.points 1) δ ∈
            interior (FilledRegion.fill B) :=
      AffineMap.lineMap_continuous.continuousWithinAt.eventually_mem
        (by
          simpa using
            isOpen_interior.mem_nhds hzInterior)
    have hsmall :
        ∀ᶠ δ : ℝ in 𝓝[>] 0,
          AffineMap.lineMap z (t.points 1) δ ∈
              interior (FilledRegion.fill B) ∧
            δ ∈ Set.Ioo (0 : ℝ) 1 :=
      hnear.and (Ioo_mem_nhdsGT zero_lt_one)
    obtain ⟨δ, hδInterior, hδ⟩ :=
      hsmall.exists
    let q :=
      AffineMap.lineMap z (t.points 1) δ
    have hqCoords :
        ∀ i : Fin 3,
          0 <
            (Submission.Triangle.affineBasis t).coord i q := by
      intro i
      fin_cases i
      · simp [q]
        exact mul_pos (sub_pos.mpr hδ.2) hzSide.1
      · simp [q, hzOneZero]
        exact hδ.1
      · simp [q]
        exact mul_pos (sub_pos.mpr hδ.2) hzSide.2
    have hqClosed :
        q ∈ t.closedInterior := by
      rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
      intro i
      exact (hqCoords i).le
    have hqFace :
        q ∈ (t.faceOpposite 1).closedInterior := by
      rw [← hinter]
      exact
        ⟨interior_subset hδInterior, hqClosed⟩
    have hqOneZero :
        (Submission.Triangle.affineBasis t).coord 1 q = 0 :=
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hqClosed 1).mpr hqFace
    exact (ne_of_gt (hqCoords 1)) hqOneZero
  exact
    ⟨z, hzBall, hzNeg,
      interior_subset hzInterior⟩

end Submission.TriangleSeam
