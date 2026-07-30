import Submission.VisibleSide

namespace Submission.VisibleLocal

/-- On the negative side of a chord through vertex `1`, a short point of
the `1`--`2` side can escape past the tip along the continuation of the
`0`--`1` side. -/
theorem exists_one_two_point_not_mem_fill
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    (B : Set (ℝ × ℝ))
    (f : (ℝ × ℝ) →L[ℝ] ℝ)
    (hqZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 q)
    (hqTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 q)
    (hfZero :
      f (t.points 0) < f (t.points 1))
    (hfill :
      FilledRegion.fill B ⊆
        {z : ℝ × ℝ | f z ≤ f (t.points 1)})
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hboundary :
      ∀ z ∈ Metric.ball (t.points 1) ρ,
        z ∈ B →
          0 ≤ VisibleSide.sideMap t q z) :
    ∃ x ∈ openSegment ℝ (t.points 1) (t.points 2),
      x ∉ FilledRegion.fill B := by
  let δ : ℝ := min ρ 1
  let D : ℝ :=
    dist (t.points 1) (t.points 2) +
      dist (t.points 0) (t.points 1) + 1
  let r : ℝ := δ / (2 * D)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hden : 1 < 2 * D := by
    dsimp [D]
    have h₀ :
        0 ≤ dist (t.points 1) (t.points 2) :=
      dist_nonneg
    have h₁ :
        0 ≤ dist (t.points 0) (t.points 1) :=
      dist_nonneg
    linarith
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrδ : r < δ := by
    dsimp [r]
    exact div_lt_self hδ hden
  have hrOne : r < 1 := by
    exact hrδ.trans_le (min_le_right ρ 1)
  let x :=
    AffineMap.lineMap
      (t.points 1) (t.points 2) r
  let y :=
    AffineMap.lineMap
      (t.points 0) (t.points 1) (1 + r)
  have hrDistTwo :
      r * dist (t.points 1) (t.points 2) <
        δ / 2 := by
    calc
      r * dist (t.points 1) (t.points 2) <
          r * D := by
        apply mul_lt_mul_of_pos_left _ hr
        dsimp [D]
        have h :
            0 ≤ dist (t.points 0) (t.points 1) :=
          dist_nonneg
        linarith
      _ = δ / 2 := by
        dsimp [r]
        field_simp
  have hrDistZero :
      r * dist (t.points 0) (t.points 1) <
        δ / 2 := by
    calc
      r * dist (t.points 0) (t.points 1) <
          r * D := by
        apply mul_lt_mul_of_pos_left _ hr
        dsimp [D]
        have h :
            0 ≤ dist (t.points 1) (t.points 2) :=
          dist_nonneg
        linarith
      _ = δ / 2 := by
        dsimp [r]
        field_simp
  have hxBall :
      x ∈ Metric.ball (t.points 1) ρ := by
    rw [Metric.mem_ball]
    dsimp [x]
    rw [dist_lineMap_left,
      Real.norm_eq_abs, abs_of_pos hr]
    calc
      r * dist (t.points 1) (t.points 2) <
          δ / 2 :=
        hrDistTwo
      _ ≤ ρ / 2 := by
        gcongr
        exact min_le_left ρ 1
      _ < ρ := by linarith
  have hyBall :
      y ∈ Metric.ball (t.points 1) ρ := by
    rw [Metric.mem_ball]
    dsimp [y]
    rw [dist_lineMap_right,
      Real.norm_eq_abs]
    have habs : |1 - (1 + r)| = r := by
      rw [show 1 - (1 + r) = -r by ring,
        abs_neg, abs_of_pos hr]
    rw [habs]
    calc
      r * dist (t.points 0) (t.points 1) <
          δ / 2 :=
        hrDistZero
      _ ≤ ρ / 2 := by
        gcongr
        exact min_le_left ρ 1
      _ < ρ := by linarith
  have hxOpen :
      x ∈ openSegment ℝ (t.points 1) (t.points 2) := by
    dsimp [x]
    exact
      lineMap_mem_openSegment
        ℝ (t.points 1) (t.points 2)
        ⟨hr, hrOne⟩
  have hxSide :
      VisibleSide.sideMap t q x < 0 := by
    dsimp [x]
    rw [AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring]
    simp
    nlinarith [mul_pos hqZero hr]
  have hySide :
      VisibleSide.sideMap t q y < 0 := by
    dsimp [y]
    rw [AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring]
    simp
    nlinarith [mul_pos hqTwo hr]
  have hyAbove :
      f (t.points 1) < f y := by
    dsimp [y]
    simp only [AffineMap.lineMap_apply_module,
      map_add, map_smul, smul_eq_mul]
    nlinarith
  let C : Set (ℝ × ℝ) :=
    Metric.ball (t.points 1) ρ ∩
      {z : ℝ × ℝ |
        VisibleSide.sideMap t q z < 0}
  have hCconvex : Convex ℝ C := by
    exact
      (convex_ball (t.points 1) ρ).inter <|
        (convex_Iio (0 : ℝ)).affine_preimage
          (VisibleSide.sideMap t q)
  have hxC : x ∈ C :=
    ⟨hxBall, hxSide⟩
  have hyC : y ∈ C :=
    ⟨hyBall, hySide⟩
  have hCsubset : C ⊆ Bᶜ := by
    rintro z ⟨hzBall, hzSide⟩ hzB
    exact
      (not_lt_of_ge
        (hboundary z hzBall hzB)) hzSide
  have hxy :
      JoinedIn Bᶜ x y := by
    apply
      (hCconvex.isPathConnected ⟨x, hxC⟩).joinedIn
        x hxC y hyC |>.mono
    exact hCsubset
  have hyNotFill :
      y ∉ FilledRegion.fill B := by
    intro hyFill
    exact
      (not_lt_of_ge (hfill hyFill)) hyAbove
  exact
    ⟨x, hxOpen,
      DiskGluing.not_mem_fill_of_joined_not_mem_fill
        hxy hyNotFill⟩

/-- The symmetric positive-side construction gives a short point of the
`0`--`1` side outside an obstacle whose local boundary lies on the
nonpositive side of the chord. -/
theorem exists_zero_one_point_not_mem_fill
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (q : ℝ × ℝ)
    (B : Set (ℝ × ℝ))
    (f : (ℝ × ℝ) →L[ℝ] ℝ)
    (hqZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 q)
    (hqTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 q)
    (hfTwo :
      f (t.points 2) < f (t.points 1))
    (hfill :
      FilledRegion.fill B ⊆
        {z : ℝ × ℝ | f z ≤ f (t.points 1)})
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hboundary :
      ∀ z ∈ Metric.ball (t.points 1) ρ,
        z ∈ B →
          VisibleSide.sideMap t q z ≤ 0) :
    ∃ x ∈ openSegment ℝ (t.points 0) (t.points 1),
      x ∉ FilledRegion.fill B := by
  let δ : ℝ := min ρ 1
  let D : ℝ :=
    dist (t.points 0) (t.points 1) +
      dist (t.points 1) (t.points 2) + 1
  let r : ℝ := δ / (2 * D)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hden : 1 < 2 * D := by
    dsimp [D]
    have h₀ :
        0 ≤ dist (t.points 0) (t.points 1) :=
      dist_nonneg
    have h₁ :
        0 ≤ dist (t.points 1) (t.points 2) :=
      dist_nonneg
    linarith
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrδ : r < δ := by
    dsimp [r]
    exact div_lt_self hδ hden
  have hrOne : r < 1 := by
    exact hrδ.trans_le (min_le_right ρ 1)
  let x :=
    AffineMap.lineMap
      (t.points 0) (t.points 1) (1 - r)
  let y :=
    AffineMap.lineMap
      (t.points 2) (t.points 1) (1 + r)
  have hrDistZero :
      r * dist (t.points 0) (t.points 1) <
        δ / 2 := by
    calc
      r * dist (t.points 0) (t.points 1) <
          r * D := by
        apply mul_lt_mul_of_pos_left _ hr
        dsimp [D]
        have h :
            0 ≤ dist (t.points 1) (t.points 2) :=
          dist_nonneg
        linarith
      _ = δ / 2 := by
        dsimp [r]
        field_simp
  have hrDistTwo :
      r * dist (t.points 1) (t.points 2) <
        δ / 2 := by
    calc
      r * dist (t.points 1) (t.points 2) <
          r * D := by
        apply mul_lt_mul_of_pos_left _ hr
        dsimp [D]
        have h :
            0 ≤ dist (t.points 0) (t.points 1) :=
          dist_nonneg
        linarith
      _ = δ / 2 := by
        dsimp [r]
        field_simp
  have hxBall :
      x ∈ Metric.ball (t.points 1) ρ := by
    rw [Metric.mem_ball]
    dsimp [x]
    rw [dist_lineMap_right,
      Real.norm_eq_abs]
    have habs : |1 - (1 - r)| = r := by
      rw [show 1 - (1 - r) = r by ring,
        abs_of_pos hr]
    rw [habs]
    calc
      r * dist (t.points 0) (t.points 1) <
          δ / 2 :=
        hrDistZero
      _ ≤ ρ / 2 := by
        gcongr
        exact min_le_left ρ 1
      _ < ρ := by linarith
  have hyBall :
      y ∈ Metric.ball (t.points 1) ρ := by
    rw [Metric.mem_ball]
    dsimp [y]
    rw [dist_lineMap_right,
      Real.norm_eq_abs]
    have habs : |1 - (1 + r)| = r := by
      rw [show 1 - (1 + r) = -r by ring,
        abs_neg, abs_of_pos hr]
    rw [habs, dist_comm]
    calc
      r * dist (t.points 1) (t.points 2) <
          δ / 2 :=
        hrDistTwo
      _ ≤ ρ / 2 := by
        gcongr
        exact min_le_left ρ 1
      _ < ρ := by linarith
  have hxOpen :
      x ∈ openSegment ℝ (t.points 0) (t.points 1) := by
    dsimp [x]
    exact
      lineMap_mem_openSegment
        ℝ (t.points 0) (t.points 1)
        ⟨by linarith, by linarith⟩
  have hxSide :
      0 < VisibleSide.sideMap t q x := by
    dsimp [x]
    rw [AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring]
    simp
    nlinarith [mul_pos hqTwo hr]
  have hySide :
      0 < VisibleSide.sideMap t q y := by
    dsimp [y]
    rw [AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring]
    simp
    nlinarith [mul_pos hqZero hr]
  have hyAbove :
      f (t.points 1) < f y := by
    dsimp [y]
    simp only [AffineMap.lineMap_apply_module,
      map_add, map_smul, smul_eq_mul]
    nlinarith
  let C : Set (ℝ × ℝ) :=
    Metric.ball (t.points 1) ρ ∩
      {z : ℝ × ℝ |
        0 < VisibleSide.sideMap t q z}
  have hCconvex : Convex ℝ C := by
    exact
      (convex_ball (t.points 1) ρ).inter <|
        (convex_Ioi (0 : ℝ)).affine_preimage
          (VisibleSide.sideMap t q)
  have hxC : x ∈ C :=
    ⟨hxBall, hxSide⟩
  have hyC : y ∈ C :=
    ⟨hyBall, hySide⟩
  have hCsubset : C ⊆ Bᶜ := by
    rintro z ⟨hzBall, hzSide⟩ hzB
    exact
      (not_lt_of_ge
        (hboundary z hzBall hzB)) hzSide
  have hxy :
      JoinedIn Bᶜ x y := by
    apply
      (hCconvex.isPathConnected ⟨x, hxC⟩).joinedIn
        x hxC y hyC |>.mono
    exact hCsubset
  have hyNotFill :
      y ∉ FilledRegion.fill B := by
    intro hyFill
    exact
      (not_lt_of_ge (hfill hyFill)) hyAbove
  exact
    ⟨x, hxOpen,
      DiskGluing.not_mem_fill_of_joined_not_mem_fill
        hxy hyNotFill⟩

end Submission.VisibleLocal
