import Submission.PolygonIncidence

namespace Submission.TriangleCoords

/-- Barycentric coordinates take the expected Kronecker-delta values on
the triangle vertices. -/
@[simp]
theorem coord_point
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i j : Fin 3) :
    (Submission.Triangle.affineBasis t).coord i
        (t.points j) =
      if i = j then 1 else 0 := by
  rw [← Submission.Triangle.affineBasis_apply]
  exact
    (Submission.Triangle.affineBasis t).coord_apply i j

/-- Scalar line maps over the reals expand to their affine combination. -/
@[simp]
theorem real_lineMap (a b r : ℝ) :
    AffineMap.lineMap a b r = (1 - r) * a + r * b :=
  AffineMap.lineMap_apply_ring a b r

/-- Barycentric coordinates preserve affine interpolation. -/
@[simp]
theorem coord_lineMap
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) (x y : ℝ × ℝ) (r : ℝ) :
    (Submission.Triangle.affineBasis t).coord i
        (AffineMap.lineMap x y r) =
      (1 - r) *
          (Submission.Triangle.affineBasis t).coord i x +
        r *
          (Submission.Triangle.affineBasis t).coord i y := by
  rw [AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring]

/-- Closed-triangle membership is equivalent to nonnegativity of all three
barycentric coordinates. -/
theorem mem_closedInterior_iff_coord_nonneg
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) :
    x ∈ t.closedInterior ↔
      ∀ i : Fin 3,
        0 ≤ (Submission.Triangle.affineBasis t).coord i x := by
  let b :=
    Submission.Triangle.affineBasis t
  constructor
  · rintro ⟨w, hw, hwIcc, hx⟩ i
    have hcoord :
        b.coord i
            (Finset.univ.affineCombination ℝ t.points w) =
          w i := by
      change
        b.coord i
            (Finset.univ.affineCombination ℝ b w) =
          w i
      exact
        b.coord_apply_combination_of_mem
          (Finset.mem_univ i) hw
    rw [← hx, hcoord]
    exact (hwIcc i).1
  · intro hcoord
    let w : Fin 3 → ℝ :=
      fun i => b.coord i x
    refine
      ⟨w, b.sum_coord_apply_eq_one x, ?_, ?_⟩
    · intro i
      refine ⟨hcoord i, ?_⟩
      have hle :
          b.coord i x ≤
            ∑ k : Fin 3, b.coord k x :=
        Finset.single_le_sum
          (fun k _ => hcoord k)
          (Finset.mem_univ i)
      simpa using hle
    · change
        Finset.univ.affineCombination ℝ b
            (fun i => b.coord i x) =
          x
      exact b.affineCombination_coord_eq_self x

/-- On the closed triangle, a barycentric coordinate vanishes exactly on
the opposite edge. -/
theorem coord_eq_zero_iff_mem_faceOpposite
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {x : ℝ × ℝ}
    (hx : x ∈ t.closedInterior)
    (i : Fin 3) :
    (Submission.Triangle.affineBasis t).coord i x = 0 ↔
      x ∈ (t.faceOpposite i).closedInterior := by
  let b :=
    Submission.Triangle.affineBasis t
  have hnonneg :
      ∀ j : Fin 3, 0 ≤ b.coord j x := by
    simpa [b] using
      (mem_closedInterior_iff_coord_nonneg t x).mp hx
  have hsum :
      b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
    have h := b.sum_coord_apply_eq_one x
    simpa only [Fin.sum_univ_three] using h
  rcases Triangle.fin_three_eq_zero_or_one_or_two i with
    rfl | rfl | rfl
  · constructor
    · intro hzero
      have htwoIcc :
          b.coord 2 x ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact hnonneg 2
        · linarith [hnonneg 1]
      have hpoint :
          AffineMap.lineMap (t.points 1) (t.points 2)
              (b.coord 2 x) =
            x := by
        apply b.ext_elem
        intro j
        rcases Triangle.fin_three_eq_zero_or_one_or_two j with
          rfl | rfl | rfl
        · simp [b, hzero]
        · simp [b]
          linarith
        · simp [b]
      rw [Submission.Triangle.closedInterior_faceOpposite_zero,
        affineSegment_eq_segment, ← hpoint]
      exact
        lineMap_mem_segment ℝ _ _ htwoIcc
    · intro hface
      rw [Submission.Triangle.closedInterior_faceOpposite_zero,
        affineSegment_eq_segment,
        segment_eq_image_lineMap] at hface
      obtain ⟨r, hr, rfl⟩ := hface
      simp
  · constructor
    · intro hone
      have htwoIcc :
          b.coord 2 x ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact hnonneg 2
        · linarith [hnonneg 0]
      have hpoint :
          AffineMap.lineMap (t.points 0) (t.points 2)
              (b.coord 2 x) =
            x := by
        apply b.ext_elem
        intro j
        rcases Triangle.fin_three_eq_zero_or_one_or_two j with
          rfl | rfl | rfl
        · simp [b]
          linarith
        · simp [b, hone]
        · simp [b]
      rw [Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_eq_segment, ← hpoint]
      exact
        lineMap_mem_segment ℝ _ _ htwoIcc
    · intro hface
      rw [Submission.Triangle.closedInterior_faceOpposite_one,
        affineSegment_eq_segment,
        segment_eq_image_lineMap] at hface
      obtain ⟨r, hr, rfl⟩ := hface
      simp
  · constructor
    · intro htwo
      have honeIcc :
          b.coord 1 x ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact hnonneg 1
        · linarith [hnonneg 0]
      have hpoint :
          AffineMap.lineMap (t.points 0) (t.points 1)
              (b.coord 1 x) =
            x := by
        apply b.ext_elem
        intro j
        rcases Triangle.fin_three_eq_zero_or_one_or_two j with
          rfl | rfl | rfl
        · simp [b]
          linarith
        · simp [b]
        · simp [b, htwo]
      rw [Submission.Triangle.closedInterior_faceOpposite_two,
        affineSegment_eq_segment, ← hpoint]
      exact
        lineMap_mem_segment ℝ _ _ honeIcc
    · intro hface
      rw [Submission.Triangle.closedInterior_faceOpposite_two,
        affineSegment_eq_segment,
        segment_eq_image_lineMap] at hface
      obtain ⟨r, hr, rfl⟩ := hface
      simp

/-- The parameter where the affine interpolation from a negative real value
to a positive one first reaches zero. -/
noncomputable def crossingParameter (a b : ℝ) : ℝ :=
  -a / (b - a)

/-- The crossing parameter lies strictly between the endpoints and really
does give value zero. -/
theorem crossingParameter_spec
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    crossingParameter a b ∈ Set.Ioo (0 : ℝ) 1 ∧
      (1 - crossingParameter a b) * a +
          crossingParameter a b * b =
        0 := by
  have hden : 0 < b - a := by
    linarith
  constructor
  · constructor
    · exact div_pos (neg_pos.mpr ha) hden
    · change -a / (b - a) < 1
      rw [div_lt_one hden]
      linarith
  · dsimp [crossingParameter]
    field_simp [ne_of_gt hden]
    ring

/-- After a negative-to-positive affine interpolation has crossed zero, its
value stays nonnegative. -/
theorem lineValue_nonneg_of_crossingParameter_le
    {a b s : ℝ} (ha : a < 0) (hb : 0 < b)
    (hs : crossingParameter a b ≤ s) :
    0 ≤ (1 - s) * a + s * b := by
  have hden : 0 ≤ b - a := by
    linarith
  have hzero :=
    (crossingParameter_spec ha hb).2
  have hdiff :
      ((1 - s) * a + s * b) -
          ((1 - crossingParameter a b) * a +
            crossingParameter a b * b) =
        (s - crossingParameter a b) * (b - a) := by
    ring
  rw [hzero, sub_zero] at hdiff
  rw [hdiff]
  exact
    mul_nonneg (sub_nonneg.mpr hs) hden

/-- If the two side coordinates of one endpoint do not both have the right
sign, while coordinate `1` and all coordinates of the other endpoint are
positive, the joining segment crosses one of the two faces incident to
vertex `1`.  This is the scalar core of the visibility argument. -/
theorem exists_side_crossing_parameter
    {a0 a1 a2 y0 y1 y2 : ℝ}
    (ha1 : 0 < a1)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hside : a0 < 0 ∨ a2 < 0) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ (1 - r) * a0 + r * y0 ∧
      0 < (1 - r) * a1 + r * y1 ∧
      0 ≤ (1 - r) * a2 + r * y2 ∧
      ((1 - r) * a0 + r * y0 = 0 ∨
        (1 - r) * a2 + r * y2 = 0) := by
  by_cases ha0 : a0 < 0
  · by_cases ha2' : a2 < 0
    · rcases le_total
        (crossingParameter a0 y0)
        (crossingParameter a2 y2) with hroots | hroots
      · refine
          ⟨crossingParameter a2 y2,
            (crossingParameter_spec ha2' hy2).1,
            lineValue_nonneg_of_crossingParameter_le
              ha0 hy0 hroots, ?_,
            (crossingParameter_spec ha2' hy2).2.ge,
            ?_⟩
        · have hr :=
            (crossingParameter_spec ha2' hy2).1
          nlinarith [
            mul_pos (sub_pos.mpr hr.2) ha1,
            mul_pos hr.1 hy1]
        · exact
            Or.inr (crossingParameter_spec ha2' hy2).2
      · refine
          ⟨crossingParameter a0 y0,
            (crossingParameter_spec ha0 hy0).1,
            (crossingParameter_spec ha0 hy0).2.ge,
            ?_,
            lineValue_nonneg_of_crossingParameter_le
              ha2' hy2 hroots, ?_⟩
        · have hr :=
            (crossingParameter_spec ha0 hy0).1
          nlinarith [
            mul_pos (sub_pos.mpr hr.2) ha1,
            mul_pos hr.1 hy1]
        · exact
            Or.inl (crossingParameter_spec ha0 hy0).2
    · have ha2nonneg : 0 ≤ a2 :=
        le_of_not_gt ha2'
      refine
        ⟨crossingParameter a0 y0,
          (crossingParameter_spec ha0 hy0).1,
          (crossingParameter_spec ha0 hy0).2.ge,
          ?_, ?_, ?_⟩
      · have hr :=
          (crossingParameter_spec ha0 hy0).1
        nlinarith [
          mul_pos (sub_pos.mpr hr.2) ha1,
          mul_pos hr.1 hy1]
      · have hr :=
          (crossingParameter_spec ha0 hy0).1
        exact
          add_nonneg
            (mul_nonneg
              (sub_nonneg.mpr hr.2.le) ha2nonneg)
            (mul_nonneg hr.1.le hy2.le)
      · exact
          Or.inl (crossingParameter_spec ha0 hy0).2
  · have ha2 : a2 < 0 :=
      hside.resolve_left ha0
    have ha0nonneg : 0 ≤ a0 :=
      le_of_not_gt ha0
    refine
      ⟨crossingParameter a2 y2,
        (crossingParameter_spec ha2 hy2).1,
        ?_, ?_,
        (crossingParameter_spec ha2 hy2).2.ge,
        ?_⟩
    · have hr :=
        (crossingParameter_spec ha2 hy2).1
      exact
        add_nonneg
          (mul_nonneg
            (sub_nonneg.mpr hr.2.le) ha0nonneg)
          (mul_nonneg hr.1.le hy0.le)
    · have hr :=
        (crossingParameter_spec ha2 hy2).1
      nlinarith [
        mul_pos (sub_pos.mpr hr.2) ha1,
        mul_pos hr.1 hy1]
    · exact
        Or.inr (crossingParameter_spec ha2 hy2).2

/-- A segment from a point outside a closed triangle but on the positive
`1`-coordinate side to a point in the triangle interior must cross one of
the two triangle faces incident to vertex `1`. -/
theorem exists_mem_incidentFace_on_segment
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {a y : ℝ × ℝ}
    (ha : a ∉ t.closedInterior)
    (haone :
      0 <
        (Submission.Triangle.affineBasis t).coord 1 a)
    (hy : y ∈ t.interior) :
    ∃ z ∈ segment ℝ a y,
      0 <
          (Submission.Triangle.affineBasis t).coord 1 z ∧
        z ∈ (t.faceOpposite 0).closedInterior ∪
          (t.faceOpposite 2).closedInterior := by
  let b :=
    Submission.Triangle.affineBasis t
  have hycoord :
      ∀ i : Fin 3, 0 < b.coord i y := by
    simpa [b] using
      (Submission.Triangle.mem_interior_iff_coord_pos
        t y).mp hy
  have hside :
      b.coord 0 a < 0 ∨ b.coord 2 a < 0 := by
    by_contra h
    simp only [not_or, not_lt] at h
    apply ha
    apply
      (mem_closedInterior_iff_coord_nonneg t a).mpr
    intro i
    rcases Triangle.fin_three_eq_zero_or_one_or_two i with
      rfl | rfl | rfl
    · exact h.1
    · simpa [b] using haone.le
    · exact h.2
  obtain ⟨r, hr, hrzero, hrone, hrtwo,
      hface⟩ :=
    exists_side_crossing_parameter
      (by simpa [b] using haone)
      (hycoord 0) (hycoord 1) (hycoord 2)
      hside
  let z :=
    AffineMap.lineMap a y r
  have hzclosed :
      z ∈ t.closedInterior := by
    apply
      (mem_closedInterior_iff_coord_nonneg t z).mpr
    intro i
    rcases Triangle.fin_three_eq_zero_or_one_or_two i with
      rfl | rfl | rfl
    · simpa [z, b] using
        hrzero
    · exact
        (by
          simpa [z, b] using
            hrone.le)
    · simpa [z, b] using
        hrtwo
  refine
    ⟨z, lineMap_mem_segment ℝ _ _
      ⟨hr.1.le, hr.2.le⟩, ?_, ?_⟩
  · simpa [z, b] using
      hrone
  rcases hface with hzero | htwo
  · exact Or.inl <|
      (coord_eq_zero_iff_mem_faceOpposite
        t hzclosed 0).mp <|
        by
          simpa [z, b] using
            hzero
  · exact Or.inr <|
      (coord_eq_zero_iff_mem_faceOpposite
        t hzclosed 2).mp <|
        by
          simpa [z, b] using
            htwo

/-- Barycentric depth from vertex `1`: it is zero at that vertex and one on
the opposite edge. -/
noncomputable def depth
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) : ℝ :=
  1 -
    (Submission.Triangle.affineBasis t).coord 1 x

@[simp]
theorem depth_point_one
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    depth t (t.points 1) = 0 := by
  simp [depth]

@[simp]
theorem depth_point_zero
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    depth t (t.points 0) = 1 := by
  simp [depth]

@[simp]
theorem depth_point_two
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    depth t (t.points 2) = 1 := by
  simp [depth]

/-- Depth scales linearly along every ray from vertex `1`. -/
theorem depth_lineMap
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) (r : ℝ) :
    depth t
        (AffineMap.lineMap (t.points 1) x r) =
      r * depth t x := by
  simp [depth]
  ring

/-- Depth is nonnegative throughout the closed triangle. -/
theorem depth_nonneg_of_mem_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {x : ℝ × ℝ}
    (hx : x ∈ t.closedInterior) :
    0 ≤ depth t x := by
  have hcoord :=
    (mem_closedInterior_iff_coord_nonneg t x).mp hx
  have hsum :=
    (Submission.Triangle.affineBasis t).sum_coord_apply_eq_one x
  have hsingle :
      (Submission.Triangle.affineBasis t).coord 1 x ≤
        ∑ i : Fin 3,
          (Submission.Triangle.affineBasis t).coord i x :=
    Finset.single_le_sum
      (fun i _ => hcoord i)
      (Finset.mem_univ 1)
  rw [hsum] at hsingle
  dsimp [depth]
  linarith

/-- The exposed vertex is the unique closed-triangle point of depth zero. -/
theorem depth_pos_of_mem_closedInterior_of_ne
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {x : ℝ × ℝ}
    (hx : x ∈ t.closedInterior)
    (hxne : x ≠ t.points 1) :
    0 < depth t x := by
  have hdepthNonneg :=
    depth_nonneg_of_mem_closedInterior t hx
  by_contra hnot
  have hdepthZero :
      depth t x = 0 :=
    le_antisymm (le_of_not_gt hnot) hdepthNonneg
  let b :=
    Submission.Triangle.affineBasis t
  have hcoord :=
    (mem_closedInterior_iff_coord_nonneg t x).mp hx
  have hsum :=
    b.sum_coord_apply_eq_one x
  rw [Fin.sum_univ_three] at hsum
  have hone :
      b.coord 1 x = 1 := by
    dsimp [depth, b] at hdepthZero
    linarith
  have hzero :
      b.coord 0 x = 0 := by
    have h0 : 0 ≤ b.coord 0 x := by
      simpa [b] using hcoord 0
    have h2 : 0 ≤ b.coord 2 x := by
      simpa [b] using hcoord 2
    linarith
  have htwo :
      b.coord 2 x = 0 := by
    have h0 : 0 ≤ b.coord 0 x := by
      simpa [b] using hcoord 0
    have h2 : 0 ≤ b.coord 2 x := by
      simpa [b] using hcoord 2
    linarith
  apply hxne
  apply b.ext_elem
  intro i
  rcases Triangle.fin_three_eq_zero_or_one_or_two i with
    rfl | rfl | rfl
  · simpa [b] using
      hzero
  · simpa [b] using
      hone
  · simpa [b] using
      htwo

/-- If the endpoint has positive coordinates toward both sides incident to
vertex `1`, the whole open radial segment from vertex `1` lies in the open
triangle. -/
theorem openSegment_pointOne_subset_interior
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {x : ℝ × ℝ}
    (hx : x ∈ t.closedInterior)
    (hxzero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 x)
    (hxtwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 x) :
    openSegment ℝ (t.points 1) x ⊆
      t.interior := by
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  apply
    (Submission.Triangle.mem_interior_iff_coord_pos
      t _).mpr
  intro i
  have hcoordNonneg :=
    (mem_closedInterior_iff_coord_nonneg t x).mp hx
  rcases Triangle.fin_three_eq_zero_or_one_or_two i with
    rfl | rfl | rfl
  · simp
    exact mul_pos hr.1 hxzero
  · have hproduct :
        0 ≤ r *
          (Submission.Triangle.affineBasis t).coord 1 x :=
      mul_nonneg (le_of_lt hr.1) (hcoordNonneg 1)
    simp
    exact
      add_pos_of_pos_of_nonneg
        (sub_pos.mpr hr.2) hproduct
  · simp
    exact mul_pos hr.1 hxtwo

end Submission.TriangleCoords
