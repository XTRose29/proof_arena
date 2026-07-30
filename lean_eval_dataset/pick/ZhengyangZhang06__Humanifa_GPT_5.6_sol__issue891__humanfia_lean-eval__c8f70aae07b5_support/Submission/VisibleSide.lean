import Submission.VisibleSupport
import Submission.DiskGluing
import Submission.PolygonLocal

namespace Submission.VisibleSide

/-- An affine functional vanishing on the line through triangle vertex `1`
and `q`. Its sign distinguishes the two incident sides of the triangle. -/
noncomputable def sideMap
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ) :
    (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  (Submission.Triangle.affineBasis t).coord 2 q •
      (Submission.Triangle.affineBasis t).coord 0 -
    (Submission.Triangle.affineBasis t).coord 0 q •
      (Submission.Triangle.affineBasis t).coord 2

@[simp]
theorem sideMap_apply
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q x : ℝ × ℝ) :
    sideMap t q x =
      (Submission.Triangle.affineBasis t).coord 2 q *
          (Submission.Triangle.affineBasis t).coord 0 x -
        (Submission.Triangle.affineBasis t).coord 0 q *
          (Submission.Triangle.affineBasis t).coord 2 x :=
  rfl

@[simp]
theorem sideMap_point_one
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ) :
    sideMap t q (t.points 1) = 0 := by
  simp [sideMap, TriangleCoords.coord_point]

@[simp]
theorem sideMap_point_zero
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ) :
    sideMap t q (t.points 0) =
      (Submission.Triangle.affineBasis t).coord 2 q := by
  simp [sideMap, TriangleCoords.coord_point]

@[simp]
theorem sideMap_point_two
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ) :
    sideMap t q (t.points 2) =
      -(Submission.Triangle.affineBasis t).coord 0 q := by
  simp [sideMap, TriangleCoords.coord_point]

@[simp]
theorem sideMap_self
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ) :
    sideMap t q q = 0 := by
  simp [sideMap]
  ring

/-- The chord from vertex `1` to `q` lies on the zero level of the side
functional. -/
theorem sideMap_eq_zero_on_segment_one
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (t.points 1) q) :
    sideMap t q x = 0 := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring]
  simp
  right
  ring

/-- The triangle side from vertex `0` to the tip lies in the nonnegative
side of the chord line. -/
theorem sideMap_nonneg_on_segment_zero_one
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    (hqTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 q)
    {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (t.points 0) (t.points 1)) :
    0 ≤ sideMap t q x := by
  have hconvex :
      Convex ℝ
        {z : ℝ × ℝ | 0 ≤ sideMap t q z} :=
    (convex_Ici (0 : ℝ)).affine_preimage
      (sideMap t q)
  exact
    hconvex.segment_subset
      (by simpa using hqTwo.le)
      (by simp)
      hx

/-- The triangle side from the tip to vertex `2` lies in the nonpositive
side of the chord line. -/
theorem sideMap_nonpos_on_segment_one_two
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    (hqZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 q)
    {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (t.points 1) (t.points 2)) :
    sideMap t q x ≤ 0 := by
  have hconvex :
      Convex ℝ
        {z : ℝ × ℝ | sideMap t q z ≤ 0} :=
    (convex_Iic (0 : ℝ)).affine_preimage
      (sideMap t q)
  exact
    hconvex.segment_subset
      (by simp)
      (by simpa using neg_nonpos.mpr hqZero.le)
      hx

/-- The relative interior of the `1`--`2` side is strictly on the negative
side of the chord. -/
theorem sideMap_neg_on_openSegment_one_two
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    (hqZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 q)
    {x : ℝ × ℝ}
    (hx :
      x ∈ openSegment ℝ (t.points 1) (t.points 2)) :
    sideMap t q x < 0 := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring]
  simp
  nlinarith [mul_pos hqZero hr.1]

/-- The relative interior of the `0`--`1` side is strictly on the positive
side of the chord. -/
theorem sideMap_pos_on_openSegment_zero_one
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    (hqTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 q)
    {x : ℝ × ℝ}
    (hx :
      x ∈ openSegment ℝ (t.points 0) (t.points 1)) :
    0 < sideMap t q x := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring]
  simp
  nlinarith [mul_pos hqTwo (sub_pos.mpr hr.2)]

/-- Around a relative-interior point of the chord, the zero level of
`sideMap` is contained in the chord segment itself. -/
theorem exists_ball_zero_subset_segment
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q p : ℝ × ℝ)
    (hqZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 q)
    (_hqTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 q)
    (hp :
      p ∈ openSegment ℝ (t.points 1) q) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ Metric.ball p ρ,
        sideMap t q z = 0 →
          z ∈ segment ℝ (t.points 1) q := by
  let b := Submission.Triangle.affineBasis t
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  have hpZero :
      0 <
        b.coord 0
          (AffineMap.lineMap (t.points 1) q s) := by
    dsimp [b]
    rw [TriangleCoords.coord_lineMap]
    simp [TriangleCoords.coord_point]
    exact mul_pos hs.1 hqZero
  have hpZeroLt :
      b.coord 0
          (AffineMap.lineMap (t.points 1) q s) <
        b.coord 0 q := by
    dsimp [b] at hpZero ⊢
    rw [TriangleCoords.coord_lineMap]
    simp [TriangleCoords.coord_point]
    nlinarith [mul_pos (sub_pos.mpr hs.2) hqZero]
  let O : Set (ℝ × ℝ) :=
    b.coord 0 ⁻¹'
      Set.Ioo 0 (b.coord 0 q)
  have hOopen : IsOpen O := by
    exact
      isOpen_Ioo.preimage <|
        AffineMap.continuous_of_finiteDimensional
          (b.coord 0)
  have hpO :
      AffineMap.lineMap (t.points 1) q s ∈ O :=
    ⟨hpZero, hpZeroLt⟩
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.mp hOopen
      (AffineMap.lineMap (t.points 1) q s) hpO
  refine ⟨ρ, hρ, ?_⟩
  intro z hzBall hzSide
  have hzO := hball hzBall
  let r : ℝ := b.coord 0 z / b.coord 0 q
  have hqZeroNe : b.coord 0 q ≠ 0 :=
    ne_of_gt hqZero
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hzO.1.le hqZero.le
    · exact
        (div_le_one hqZero).mpr hzO.2.le
  have hcoordZero :
      b.coord 0
          (AffineMap.lineMap (t.points 1) q r) =
        b.coord 0 z := by
    rw [TriangleCoords.coord_lineMap]
    simp [TriangleCoords.coord_point, r]
    field_simp
    rfl
  have hcoordTwo :
      b.coord 2
          (AffineMap.lineMap (t.points 1) q r) =
        b.coord 2 z := by
    have hside :
        b.coord 2 q * b.coord 0 z -
            b.coord 0 q * b.coord 2 z =
          0 := by
      simpa [sideMap, b] using hzSide
    rw [TriangleCoords.coord_lineMap]
    simp [TriangleCoords.coord_point, r]
    field_simp
    nlinarith
  have hcoordOne :
      b.coord 1
          (AffineMap.lineMap (t.points 1) q r) =
        b.coord 1 z := by
    have hsumLine :=
      b.sum_coord_apply_eq_one
        (AffineMap.lineMap (t.points 1) q r)
    have hsumZ :=
      b.sum_coord_apply_eq_one z
    rw [Fin.sum_univ_three] at hsumLine hsumZ
    linarith
  have hzLine :
      z =
        AffineMap.lineMap (t.points 1) q r := by
    symm
    apply b.ext_elem
    intro i
    fin_cases i
    · exact hcoordZero
    · exact hcoordOne
    · exact hcoordTwo
  rw [hzLine]
  exact lineMap_mem_segment ℝ _ _ hr

end Submission.VisibleSide
