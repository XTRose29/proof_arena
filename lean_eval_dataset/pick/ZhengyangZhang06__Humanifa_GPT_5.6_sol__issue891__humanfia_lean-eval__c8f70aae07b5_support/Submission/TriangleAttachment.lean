import Submission.TriangleCoords

namespace Submission.TriangleAttachment

open scoped Pointwise

private def tipDirection
    (t : Affine.Triangle ℝ (ℝ × ℝ)) : ℝ × ℝ :=
  (t.points 1 - t.points 0) +
    (t.points 1 - t.points 2)

private def beyondTip
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (r : ℝ) :
    ℝ × ℝ :=
  r • tipDirection t + t.points 1

private theorem coord_beyondTip
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) (r : ℝ) :
    (Submission.Triangle.affineBasis t).coord i
        (beyondTip t r) =
      ![-r, 1 + 2 * r, -r] i := by
  let w : Fin 3 → ℝ :=
    ![-r, 1 + 2 * r, -r]
  have hw : ∑ j, w j = 1 := by
    simp [w, Fin.sum_univ_three]
    ring
  have hbeyond :
      Finset.univ.affineCombination ℝ
          (Submission.Triangle.affineBasis t) w =
        beyondTip t r := by
    rw [Finset.univ.affineCombination_eq_linear_combination
      (Submission.Triangle.affineBasis t) w hw]
    simp [w, Fin.sum_univ_three, beyondTip, tipDirection,
      Submission.Triangle.affineBasis_apply]
    module
  rw [← hbeyond]
  simpa [w] using
    (Submission.Triangle.affineBasis t).coord_apply_combination_of_mem
      (Finset.mem_univ i) hw

private theorem coord_beyondTip_zero
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    ∀ r : ℝ,
      (Submission.Triangle.affineBasis t).coord 0
          (beyondTip t r) = -r := by
  intro r
  simpa using coord_beyondTip t 0 r

private theorem coord_beyondTip_one
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    ∀ r : ℝ,
      (Submission.Triangle.affineBasis t).coord 1
          (beyondTip t r) = 1 + 2 * r := by
  intro r
  simpa using coord_beyondTip t 1 r

private theorem coord_beyondTip_two
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    ∀ r : ℝ,
      (Submission.Triangle.affineBasis t).coord 2
          (beyondTip t r) = -r := by
  intro r
  simpa using coord_beyondTip t 2 r

/-- The part of a closed triangle away from its base face. -/
def openBaseCap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Set (ℝ × ℝ) :=
  t.closedInterior \
    (t.faceOpposite 1).closedInterior

theorem mem_openBaseCap_iff
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) :
    x ∈ openBaseCap t ↔
      x ∈ t.closedInterior ∧
        0 <
          (Submission.Triangle.affineBasis t).coord 1 x := by
  constructor
  · rintro ⟨hxClosed, hxBase⟩
    refine ⟨hxClosed, ?_⟩
    have hxNonneg :=
      (TriangleCoords.mem_closedInterior_iff_coord_nonneg
        t x).mp hxClosed 1
    have hxNe :
        (Submission.Triangle.affineBasis t).coord 1 x ≠ 0 := by
      intro hxZero
      exact hxBase <|
        (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
          t hxClosed 1).mp hxZero
    exact lt_of_le_of_ne hxNonneg hxNe.symm
  · rintro ⟨hxClosed, hxPos⟩
    refine ⟨hxClosed, ?_⟩
    intro hxBase
    have hxZero :=
      (TriangleCoords.coord_eq_zero_iff_mem_faceOpposite
        t hxClosed 1).mpr hxBase
    linarith

private theorem beyondTip_mem_compl_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {r : ℝ} (hr : 0 < r) :
    beyondTip t r ∈ t.closedInteriorᶜ := by
  intro hy
  have hyZero :=
    (TriangleCoords.mem_closedInterior_iff_coord_nonneg
      t (beyondTip t r)).mp hy 0
  rw [coord_beyondTip_zero] at hyZero
  linarith

theorem openBaseCap_subset_compl_of_inter_eq_face
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {R : Set (ℝ × ℝ)}
    (hinter :
      R ∩ t.closedInterior =
        (t.faceOpposite 1).closedInterior) :
    openBaseCap t ⊆ Rᶜ := by
  intro x hxCap hxR
  have hxBase : x ∈ (t.faceOpposite 1).closedInterior := by
    rw [← hinter]
    exact ⟨hxR, hxCap.1⟩
  exact hxCap.2 hxBase

private def translateToTip
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (p q : ℝ × ℝ) : ℝ × ℝ :=
  (t.points 1 - p) + q

private theorem coord_translateToTip
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) (p q : ℝ × ℝ) :
    (Submission.Triangle.affineBasis t).coord i
        (translateToTip t p q) =
      (Submission.Triangle.affineBasis t).coord i q +
        ((Submission.Triangle.affineBasis t).coord i
            (t.points 1) -
          (Submission.Triangle.affineBasis t).coord i p) := by
  change
    (Submission.Triangle.affineBasis t).coord i
        ((t.points 1 -ᵥ p) +ᵥ q) =
      (Submission.Triangle.affineBasis t).coord i q +
        ((Submission.Triangle.affineBasis t).coord i
            (t.points 1) -
          (Submission.Triangle.affineBasis t).coord i p)
  rw [AffineMap.map_vadd,
    AffineMap.linearMap_vsub]
  simp only [vsub_eq_sub, vadd_eq_add]
  ring

private theorem dist_translateToTip_tip
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (p q : ℝ × ℝ) :
    dist (translateToTip t p q) (t.points 1) =
      dist q p := by
  rw [dist_eq_norm, dist_eq_norm]
  congr 1
  dsimp [translateToTip]
  module

private theorem convex_coord_lt
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) :
    Convex ℝ
      {x : ℝ × ℝ |
        (Submission.Triangle.affineBasis t).coord i x < 0} := by
  exact
    (convex_Iio (0 : ℝ)).affine_preimage
      ((Submission.Triangle.affineBasis t).coord i)

private theorem isOpen_coord_pos
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) :
    IsOpen
      {x : ℝ × ℝ |
        0 <
          (Submission.Triangle.affineBasis t).coord i x} := by
  exact
    isOpen_Ioi.preimage <|
      AffineMap.continuous_of_finiteDimensional
        ((Submission.Triangle.affineBasis t).coord i)

private theorem isOpen_coord_neg
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) :
    IsOpen
      {x : ℝ × ℝ |
        (Submission.Triangle.affineBasis t).coord i x < 0} := by
  exact
    isOpen_Iio.preimage <|
      AffineMap.continuous_of_finiteDimensional
        ((Submission.Triangle.affineBasis t).coord i)

private theorem segment_to_tip_subset_openBaseCap
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {p : ℝ × ℝ}
    (hp : p ∈ openBaseCap t) :
    segment ℝ p (t.points 1) ⊆
      openBaseCap t := by
  intro z hz
  rw [mem_openBaseCap_iff] at hp ⊢
  refine ⟨?_, ?_⟩
  · exact
      (Submission.Triangle.convex_closedInterior t).segment_subset
        hp.1 (t.point_mem_closedInterior 1) hz
  · have hconvex :
        Convex ℝ
          {x : ℝ × ℝ |
            0 <
              (Submission.Triangle.affineBasis t).coord 1 x} :=
      (convex_Ioi (0 : ℝ)).affine_preimage
        ((Submission.Triangle.affineBasis t).coord 1)
    exact
      hconvex.segment_subset hp.2
        (by simp [TriangleCoords.coord_point]) hz

private theorem joinedIn_of_near_side_zero
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {R : Set (ℝ × ℝ)}
    (hRclosed : IsClosed R)
    (hinter :
      R ∩ t.closedInterior =
        (t.faceOpposite 1).closedInterior)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hball :
      Metric.ball (t.points 1) ρ ⊆ Rᶜ)
    {y p : ℝ × ℝ}
    (hyball : y ∈ Metric.ball (t.points 1) ρ)
    (hyzero :
      (Submission.Triangle.affineBasis t).coord 0 y < 0)
    (hpClosed : p ∈ t.closedInterior)
    (hpZero :
      (Submission.Triangle.affineBasis t).coord 0 p = 0)
    (hpOne :
      0 <
        (Submission.Triangle.affineBasis t).coord 1 p)
    (_hpTwo :
      0 <
        (Submission.Triangle.affineBasis t).coord 2 p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : ℝ × ℝ,
        dist q p < ε →
        0 <
          (Submission.Triangle.affineBasis t).coord 1 q →
        0 <
          (Submission.Triangle.affineBasis t).coord 2 q →
        q ∈ (R ∪ t.closedInterior)ᶜ →
          JoinedIn (R ∪ t.closedInterior)ᶜ q y := by
  let S : Set (ℝ × ℝ) :=
    segment ℝ p (t.points 1)
  have hpCap : p ∈ openBaseCap t :=
    (mem_openBaseCap_iff t p).2 ⟨hpClosed, hpOne⟩
  have hScompact : IsCompact S := by
    dsimp [S]
    rw [segment_eq_image_lineMap]
    exact
      isCompact_Icc.image
        AffineMap.lineMap_continuous
  have hScompl : S ⊆ Rᶜ :=
    (segment_to_tip_subset_openBaseCap t hpCap).trans
      (openBaseCap_subset_compl_of_inter_eq_face t hinter)
  obtain ⟨δ, hδ, hthick⟩ :=
    hScompact.exists_thickening_subset_open
      hRclosed.isOpen_compl hScompl
  let ε : ℝ := min δ ρ / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro q hqp hqOne hqTwo hqCompl
  let q' := translateToTip t p q
  have hεδ : ε < δ := by
    dsimp [ε]
    have hmin : min δ ρ ≤ δ := min_le_left _ _
    linarith
  have hερ : ε < ρ := by
    dsimp [ε]
    have hmin : min δ ρ ≤ ρ := min_le_right _ _
    linarith
  have hqNotTriangle : q ∉ t.closedInterior := by
    intro hqTriangle
    exact hqCompl (Or.inr hqTriangle)
  have hqZero :
      (Submission.Triangle.affineBasis t).coord 0 q < 0 := by
    by_contra hnot
    have hqZeroNonneg :
        0 ≤
          (Submission.Triangle.affineBasis t).coord 0 q :=
      le_of_not_gt hnot
    apply hqNotTriangle
    rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
    intro i
    fin_cases i
    · exact hqZeroNonneg
    · exact hqOne.le
    · exact hqTwo.le
  have hpS : p ∈ S :=
    left_mem_segment ℝ p (t.points 1)
  have htipS : t.points 1 ∈ S :=
    right_mem_segment ℝ p (t.points 1)
  have hqThick : q ∈ Metric.thickening δ S := by
    rw [Metric.mem_thickening_iff]
    exact ⟨p, hpS, hqp.trans hεδ⟩
  have hq'Dist :
      dist q' (t.points 1) = dist q p := by
    exact dist_translateToTip_tip t p q
  have hq'Thick : q' ∈ Metric.thickening δ S := by
    rw [Metric.mem_thickening_iff]
    exact
      ⟨t.points 1, htipS,
        hq'Dist.trans_lt (hqp.trans hεδ)⟩
  have hq'Zero :
      (Submission.Triangle.affineBasis t).coord 0 q' < 0 := by
    dsimp [q']
    rw [coord_translateToTip, hpZero]
    simp only [TriangleCoords.coord_point]
    simpa using hqZero
  let A : Set (ℝ × ℝ) :=
    Metric.thickening δ S ∩
      {z |
        (Submission.Triangle.affineBasis t).coord 0 z < 0}
  have hAconvex : Convex ℝ A := by
    exact
      (convex_segment p (t.points 1)).thickening δ
        |>.inter (convex_coord_lt t 0)
  have hqA : q ∈ A :=
    ⟨hqThick, hqZero⟩
  have hq'A : q' ∈ A :=
    ⟨hq'Thick, hq'Zero⟩
  have hAsubset :
      A ⊆ (R ∪ t.closedInterior)ᶜ := by
    rintro z ⟨hzThick, hzZero⟩ (hzR | hzTriangle)
    · exact (hthick hzThick) hzR
    · have hzZeroNonneg :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t z).mp hzTriangle 0
      exact (not_lt_of_ge hzZeroNonneg) hzZero
  have hqq' :
      JoinedIn (R ∪ t.closedInterior)ᶜ q q' := by
    apply
      (hAconvex.isPathConnected ⟨q, hqA⟩).joinedIn
        q hqA q' hq'A |>.mono
    exact hAsubset
  have hq'Ball :
      q' ∈ Metric.ball (t.points 1) ρ := by
    rw [Metric.mem_ball, hq'Dist]
    exact hqp.trans hερ
  let B : Set (ℝ × ℝ) :=
    Metric.ball (t.points 1) ρ ∩
      {z |
        (Submission.Triangle.affineBasis t).coord 0 z < 0}
  have hBconvex : Convex ℝ B :=
    (convex_ball (t.points 1) ρ).inter
      (convex_coord_lt t 0)
  have hq'B : q' ∈ B :=
    ⟨hq'Ball, hq'Zero⟩
  have hyB : y ∈ B :=
    ⟨hyball, hyzero⟩
  have hBsubset :
      B ⊆ (R ∪ t.closedInterior)ᶜ := by
    rintro z ⟨hzBall, hzZero⟩ (hzR | hzTriangle)
    · exact (hball hzBall) hzR
    · have hzZeroNonneg :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t z).mp hzTriangle 0
      exact (not_lt_of_ge hzZeroNonneg) hzZero
  have hq'y :
      JoinedIn (R ∪ t.closedInterior)ᶜ q' y := by
    apply
      (hBconvex.isPathConnected ⟨q', hq'B⟩).joinedIn
        q' hq'B y hyB |>.mono
    exact hBsubset
  exact hqq'.trans hq'y

private theorem joinedIn_of_near_side_two
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {R : Set (ℝ × ℝ)}
    (hRclosed : IsClosed R)
    (hinter :
      R ∩ t.closedInterior =
        (t.faceOpposite 1).closedInterior)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hball :
      Metric.ball (t.points 1) ρ ⊆ Rᶜ)
    {y p : ℝ × ℝ}
    (hyball : y ∈ Metric.ball (t.points 1) ρ)
    (hytwo :
      (Submission.Triangle.affineBasis t).coord 2 y < 0)
    (hpClosed : p ∈ t.closedInterior)
    (_hpZero :
      0 <
        (Submission.Triangle.affineBasis t).coord 0 p)
    (hpOne :
      0 <
        (Submission.Triangle.affineBasis t).coord 1 p)
    (hpTwo :
      (Submission.Triangle.affineBasis t).coord 2 p = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : ℝ × ℝ,
        dist q p < ε →
        0 <
          (Submission.Triangle.affineBasis t).coord 0 q →
        0 <
          (Submission.Triangle.affineBasis t).coord 1 q →
        q ∈ (R ∪ t.closedInterior)ᶜ →
          JoinedIn (R ∪ t.closedInterior)ᶜ q y := by
  let S : Set (ℝ × ℝ) :=
    segment ℝ p (t.points 1)
  have hpCap : p ∈ openBaseCap t :=
    (mem_openBaseCap_iff t p).2 ⟨hpClosed, hpOne⟩
  have hScompact : IsCompact S := by
    dsimp [S]
    rw [segment_eq_image_lineMap]
    exact
      isCompact_Icc.image
        AffineMap.lineMap_continuous
  have hScompl : S ⊆ Rᶜ :=
    (segment_to_tip_subset_openBaseCap t hpCap).trans
      (openBaseCap_subset_compl_of_inter_eq_face t hinter)
  obtain ⟨δ, hδ, hthick⟩ :=
    hScompact.exists_thickening_subset_open
      hRclosed.isOpen_compl hScompl
  let ε : ℝ := min δ ρ / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro q hqp hqZero hqOne hqCompl
  let q' := translateToTip t p q
  have hεδ : ε < δ := by
    dsimp [ε]
    have hmin : min δ ρ ≤ δ := min_le_left _ _
    linarith
  have hερ : ε < ρ := by
    dsimp [ε]
    have hmin : min δ ρ ≤ ρ := min_le_right _ _
    linarith
  have hqNotTriangle : q ∉ t.closedInterior := by
    intro hqTriangle
    exact hqCompl (Or.inr hqTriangle)
  have hqTwo :
      (Submission.Triangle.affineBasis t).coord 2 q < 0 := by
    by_contra hnot
    have hqTwoNonneg :
        0 ≤
          (Submission.Triangle.affineBasis t).coord 2 q :=
      le_of_not_gt hnot
    apply hqNotTriangle
    rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
    intro i
    fin_cases i
    · exact hqZero.le
    · exact hqOne.le
    · exact hqTwoNonneg
  have hpS : p ∈ S :=
    left_mem_segment ℝ p (t.points 1)
  have htipS : t.points 1 ∈ S :=
    right_mem_segment ℝ p (t.points 1)
  have hqThick : q ∈ Metric.thickening δ S := by
    rw [Metric.mem_thickening_iff]
    exact ⟨p, hpS, hqp.trans hεδ⟩
  have hq'Dist :
      dist q' (t.points 1) = dist q p := by
    exact dist_translateToTip_tip t p q
  have hq'Thick : q' ∈ Metric.thickening δ S := by
    rw [Metric.mem_thickening_iff]
    exact
      ⟨t.points 1, htipS,
        hq'Dist.trans_lt (hqp.trans hεδ)⟩
  have hq'Two :
      (Submission.Triangle.affineBasis t).coord 2 q' < 0 := by
    dsimp [q']
    rw [coord_translateToTip, hpTwo]
    simp only [TriangleCoords.coord_point]
    simpa using hqTwo
  let A : Set (ℝ × ℝ) :=
    Metric.thickening δ S ∩
      {z |
        (Submission.Triangle.affineBasis t).coord 2 z < 0}
  have hAconvex : Convex ℝ A := by
    exact
      (convex_segment p (t.points 1)).thickening δ
        |>.inter (convex_coord_lt t 2)
  have hqA : q ∈ A :=
    ⟨hqThick, hqTwo⟩
  have hq'A : q' ∈ A :=
    ⟨hq'Thick, hq'Two⟩
  have hAsubset :
      A ⊆ (R ∪ t.closedInterior)ᶜ := by
    rintro z ⟨hzThick, hzTwo⟩ (hzR | hzTriangle)
    · exact (hthick hzThick) hzR
    · have hzTwoNonneg :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t z).mp hzTriangle 2
      exact (not_lt_of_ge hzTwoNonneg) hzTwo
  have hqq' :
      JoinedIn (R ∪ t.closedInterior)ᶜ q q' := by
    apply
      (hAconvex.isPathConnected ⟨q, hqA⟩).joinedIn
        q hqA q' hq'A |>.mono
    exact hAsubset
  have hq'Ball :
      q' ∈ Metric.ball (t.points 1) ρ := by
    rw [Metric.mem_ball, hq'Dist]
    exact hqp.trans hερ
  let B : Set (ℝ × ℝ) :=
    Metric.ball (t.points 1) ρ ∩
      {z |
        (Submission.Triangle.affineBasis t).coord 2 z < 0}
  have hBconvex : Convex ℝ B :=
    (convex_ball (t.points 1) ρ).inter
      (convex_coord_lt t 2)
  have hq'B : q' ∈ B :=
    ⟨hq'Ball, hq'Two⟩
  have hyB : y ∈ B :=
    ⟨hyball, hytwo⟩
  have hBsubset :
      B ⊆ (R ∪ t.closedInterior)ᶜ := by
    rintro z ⟨hzBall, hzTwo⟩ (hzR | hzTriangle)
    · exact (hball hzBall) hzR
    · have hzTwoNonneg :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t z).mp hzTriangle 2
      exact (not_lt_of_ge hzTwoNonneg) hzTwo
  have hq'y :
      JoinedIn (R ∪ t.closedInterior)ᶜ q' y := by
    apply
      (hBconvex.isPathConnected ⟨q', hq'B⟩).joinedIn
        q' hq'B y hyB |>.mono
    exact hBsubset
  exact hqq'.trans hq'y

private theorem dist_beyondTip_tip
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {r : ℝ} (hr : 0 ≤ r) :
    dist (beyondTip t r) (t.points 1) =
      r * ‖tipDirection t‖ := by
  rw [dist_eq_norm]
  simp only [beyondTip, add_sub_cancel_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem exists_tip_ball_and_exterior_point
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {R : Set (ℝ × ℝ)}
    (hRclosed : IsClosed R)
    (hinter :
      R ∩ t.closedInterior =
        (t.faceOpposite 1).closedInterior) :
    ∃ (ρ : ℝ) (y : ℝ × ℝ),
      0 < ρ ∧
        Metric.ball (t.points 1) ρ ⊆ Rᶜ ∧
        (∀ z ∈ Metric.ball (t.points 1) ρ,
          0 <
            (Submission.Triangle.affineBasis t).coord 1 z) ∧
        y ∈ Metric.ball (t.points 1) ρ ∧
        (Submission.Triangle.affineBasis t).coord 0 y < 0 ∧
        (Submission.Triangle.affineBasis t).coord 2 y < 0 := by
  let O : Set (ℝ × ℝ) :=
    Rᶜ ∩
      {z |
        0 <
          (Submission.Triangle.affineBasis t).coord 1 z}
  have htipCap : t.points 1 ∈ openBaseCap t := by
    rw [mem_openBaseCap_iff]
    exact
      ⟨t.point_mem_closedInterior 1,
        by simp [TriangleCoords.coord_point]⟩
  have htipR : t.points 1 ∈ Rᶜ :=
    openBaseCap_subset_compl_of_inter_eq_face
      t hinter htipCap
  have htipO : t.points 1 ∈ O := by
    exact
      ⟨htipR,
        by simp [TriangleCoords.coord_point]⟩
  have hOopen : IsOpen O :=
    hRclosed.isOpen_compl.inter (isOpen_coord_pos t 1)
  obtain ⟨ρ, hρ, hballO⟩ :=
    Metric.isOpen_iff.mp hOopen (t.points 1) htipO
  let r : ℝ :=
    ρ / (2 * (‖tipDirection t‖ + 1))
  have hden :
      0 < 2 * (‖tipDirection t‖ + 1) := by
    positivity
  have hr : 0 < r := by
    exact div_pos hρ hden
  let y := beyondTip t r
  have hyDist :
      dist y (t.points 1) < ρ := by
    rw [show y = beyondTip t r by rfl,
      dist_beyondTip_tip t hr.le]
    calc
      r * ‖tipDirection t‖ <
          r * (‖tipDirection t‖ + 1) := by
        exact
          mul_lt_mul_of_pos_left
            (lt_add_one ‖tipDirection t‖) hr
      _ = ρ / 2 := by
        dsimp [r]
        field_simp
      _ < ρ := by
        linarith
  have hyBall :
      y ∈ Metric.ball (t.points 1) ρ :=
    hyDist
  refine
    ⟨ρ, y, hρ, ?_, ?_, hyBall, ?_, ?_⟩
  · intro z hz
    exact (hballO hz).1
  · intro z hz
    exact (hballO hz).2
  · dsimp [y]
    rw [coord_beyondTip_zero]
    linarith
  · dsimp [y]
    rw [coord_beyondTip_two]
    linarith

private theorem joinedIn_of_mem_tip_ball_compl
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {R : Set (ℝ × ℝ)}
    {ρ : ℝ} {y q : ℝ × ℝ}
    (hball :
      Metric.ball (t.points 1) ρ ⊆ Rᶜ)
    (hyball : y ∈ Metric.ball (t.points 1) ρ)
    (hyzero :
      (Submission.Triangle.affineBasis t).coord 0 y < 0)
    (hytwo :
      (Submission.Triangle.affineBasis t).coord 2 y < 0)
    (hqball : q ∈ Metric.ball (t.points 1) ρ)
    (hqone :
      0 <
        (Submission.Triangle.affineBasis t).coord 1 q)
    (hqnot : q ∉ t.closedInterior) :
    JoinedIn (R ∪ t.closedInterior)ᶜ q y := by
  have hqSide :
      (Submission.Triangle.affineBasis t).coord 0 q < 0 ∨
        (Submission.Triangle.affineBasis t).coord 2 q < 0 := by
    by_cases hqzero :
        (Submission.Triangle.affineBasis t).coord 0 q < 0
    · exact Or.inl hqzero
    · right
      by_contra hqtwo
      apply hqnot
      rw [TriangleCoords.mem_closedInterior_iff_coord_nonneg]
      intro i
      fin_cases i
      · exact le_of_not_gt hqzero
      · exact hqone.le
      · exact le_of_not_gt hqtwo
  rcases hqSide with hqzero | hqtwo
  · let B : Set (ℝ × ℝ) :=
      Metric.ball (t.points 1) ρ ∩
        {z |
          (Submission.Triangle.affineBasis t).coord 0 z < 0}
    have hBconvex : Convex ℝ B :=
      (convex_ball (t.points 1) ρ).inter
        (convex_coord_lt t 0)
    have hqB : q ∈ B :=
      ⟨hqball, hqzero⟩
    have hyB : y ∈ B :=
      ⟨hyball, hyzero⟩
    have hBsubset :
        B ⊆ (R ∪ t.closedInterior)ᶜ := by
      rintro z ⟨hzBall, hzZero⟩ (hzR | hzTriangle)
      · exact (hball hzBall) hzR
      · have hzZeroNonneg :=
          (TriangleCoords.mem_closedInterior_iff_coord_nonneg
            t z).mp hzTriangle 0
        exact (not_lt_of_ge hzZeroNonneg) hzZero
    apply
      (hBconvex.isPathConnected ⟨q, hqB⟩).joinedIn
        q hqB y hyB |>.mono
    exact hBsubset
  · let B : Set (ℝ × ℝ) :=
      Metric.ball (t.points 1) ρ ∩
        {z |
          (Submission.Triangle.affineBasis t).coord 2 z < 0}
    have hBconvex : Convex ℝ B :=
      (convex_ball (t.points 1) ρ).inter
        (convex_coord_lt t 2)
    have hqB : q ∈ B :=
      ⟨hqball, hqtwo⟩
    have hyB : y ∈ B :=
      ⟨hyball, hytwo⟩
    have hBsubset :
        B ⊆ (R ∪ t.closedInterior)ᶜ := by
      rintro z ⟨hzBall, hzTwo⟩ (hzR | hzTriangle)
      · exact (hball hzBall) hzR
      · have hzTwoNonneg :=
          (TriangleCoords.mem_closedInterior_iff_coord_nonneg
            t z).mp hzTriangle 2
        exact (not_lt_of_ge hzTwoNonneg) hzTwo
    apply
      (hBconvex.isPathConnected ⟨q, hqB⟩).joinedIn
        q hqB y hyB |>.mono
    exact hBsubset

/-- Attaching a closed affine triangle to a closed planar region exactly
along one face preserves the connectedness of the region's exterior. -/
theorem isPreconnected_compl_union_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ))
    {R : Set (ℝ × ℝ)}
    (hRclosed : IsClosed R)
    (hRcompl :
      IsPreconnected Rᶜ)
    (hinter :
      R ∩ t.closedInterior =
        (t.faceOpposite 1).closedInterior) :
    IsPreconnected
      (R ∪ t.closedInterior)ᶜ := by
  let V : Set (ℝ × ℝ) :=
    (R ∪ t.closedInterior)ᶜ
  let W : Set (ℝ × ℝ) :=
    openBaseCap t
  obtain
    ⟨ρ, y, hρ, hball, hballOne, hyball,
      hyzero, hytwo⟩ :=
    exists_tip_ball_and_exterior_point
      t hRclosed hinter
  have hyR : y ∈ Rᶜ :=
    hball hyball
  have hyNotTriangle : y ∉ t.closedInterior := by
    intro hyTriangle
    have hyZeroNonneg :=
      (TriangleCoords.mem_closedInterior_iff_coord_nonneg
        t y).mp hyTriangle 0
    linarith
  have hyV : y ∈ V := by
    intro hyUnion
    rcases hyUnion with hyR' | hyTriangle
    · exact hyR hyR'
    · exact hyNotTriangle hyTriangle
  let C : Set (ℝ × ℝ) :=
    pathComponentIn V y
  have hVopen : IsOpen V := by
    exact
      (hRclosed.union t.isClosed_closedInterior).isOpen_compl
  have hCopen : IsOpen C := by
    exact hVopen.pathComponentIn y
  have hVdiffCopen : IsOpen (V \ C) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxComponent :
        x ∈ pathComponentIn V x :=
      mem_pathComponentIn_self hx.1
    have hxOpen :
        IsOpen (pathComponentIn V x) :=
      hVopen.pathComponentIn x
    apply
      Filter.mem_of_superset
        (hxOpen.mem_nhds hxComponent)
    intro z hz
    refine ⟨pathComponentIn_subset hz, ?_⟩
    intro hzC
    apply hx.2
    change JoinedIn V y x
    exact hzC.trans hz.symm
  have hCUnionWOpen : IsOpen (C ∪ W) := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    rcases hp with hpC | hpW
    · exact
        Filter.mem_of_superset
          (hCopen.mem_nhds hpC)
          Set.subset_union_left
    · have hpCap :
          p ∈ openBaseCap t := hpW
      have hpData :=
        (mem_openBaseCap_iff t p).mp hpCap
      have hpClosed : p ∈ t.closedInterior :=
        hpData.1
      have hpOne :
          0 <
            (Submission.Triangle.affineBasis t).coord 1 p :=
        hpData.2
      have hpCoords :=
        (TriangleCoords.mem_closedInterior_iff_coord_nonneg
          t p).mp hpClosed
      by_cases hpZeroEq :
          (Submission.Triangle.affineBasis t).coord 0 p = 0
      · by_cases hpTwoEq :
            (Submission.Triangle.affineBasis t).coord 2 p = 0
        · have hpTip : p = t.points 1 := by
            by_contra hpNe
            have hpDepth :=
              TriangleCoords.depth_pos_of_mem_closedInterior_of_ne
                t hpClosed hpNe
            have hpSum :=
              (Submission.Triangle.affineBasis t).sum_coord_apply_eq_one p
            simp only [Fin.sum_univ_three] at hpSum
            dsimp [TriangleCoords.depth] at hpDepth
            rw [hpZeroEq, hpTwoEq] at hpSum
            linarith
          subst p
          apply
            Filter.mem_of_superset
              (Metric.ball_mem_nhds
                (t.points 1) hρ)
          intro q hqBall
          by_cases hqTriangle : q ∈ t.closedInterior
          · exact
              Or.inr <|
                (mem_openBaseCap_iff t q).2
                  ⟨hqTriangle, hballOne q hqBall⟩
          · left
            change JoinedIn V y q
            exact
              (joinedIn_of_mem_tip_ball_compl
                t hball hyball hyzero hytwo hqBall
                  (hballOne q hqBall) hqTriangle).symm
        · have hpTwo :
              0 <
                (Submission.Triangle.affineBasis t).coord 2 p :=
            lt_of_le_of_ne (hpCoords 2) (Ne.symm hpTwoEq)
          obtain ⟨ε, hε, hnear⟩ :=
            joinedIn_of_near_side_zero
              t hRclosed hinter hρ hball hyball hyzero
                hpClosed hpZeroEq hpOne hpTwo
          let N : Set (ℝ × ℝ) :=
            Rᶜ ∩ Metric.ball p ε ∩
              {z |
                0 <
                  (Submission.Triangle.affineBasis t).coord 1 z} ∩
              {z |
                0 <
                  (Submission.Triangle.affineBasis t).coord 2 z}
          have hpR : p ∈ Rᶜ :=
            openBaseCap_subset_compl_of_inter_eq_face
              t hinter hpCap
          have hpN : p ∈ N := by
            exact
              ⟨⟨⟨hpR, Metric.mem_ball_self hε⟩,
                hpOne⟩, hpTwo⟩
          have hNopen : IsOpen N := by
            exact
              (hRclosed.isOpen_compl.inter Metric.isOpen_ball)
                |>.inter (isOpen_coord_pos t 1)
                |>.inter (isOpen_coord_pos t 2)
          apply
            Filter.mem_of_superset
              (hNopen.mem_nhds hpN)
          intro q hqN
          rcases hqN with
            ⟨⟨⟨hqR, hqBall⟩, hqOne⟩, hqTwo⟩
          by_cases hqTriangle : q ∈ t.closedInterior
          · exact
              Or.inr <|
                (mem_openBaseCap_iff t q).2
                  ⟨hqTriangle, hqOne⟩
          · left
            change JoinedIn V y q
            have hqV :
                q ∈ (R ∪ t.closedInterior)ᶜ := by
              intro hqUnion
              rcases hqUnion with hqR' | hqTriangle'
              · exact hqR hqR'
              · exact hqTriangle hqTriangle'
            exact
              (hnear q
                (by simpa [Metric.mem_ball] using hqBall)
                hqOne hqTwo hqV).symm
      · have hpZero :
            0 <
              (Submission.Triangle.affineBasis t).coord 0 p :=
          lt_of_le_of_ne (hpCoords 0) (Ne.symm hpZeroEq)
        by_cases hpTwoEq :
            (Submission.Triangle.affineBasis t).coord 2 p = 0
        · obtain ⟨ε, hε, hnear⟩ :=
            joinedIn_of_near_side_two
              t hRclosed hinter hρ hball hyball hytwo
                hpClosed hpZero hpOne hpTwoEq
          let N : Set (ℝ × ℝ) :=
            Rᶜ ∩ Metric.ball p ε ∩
              {z |
                0 <
                  (Submission.Triangle.affineBasis t).coord 0 z} ∩
              {z |
                0 <
                  (Submission.Triangle.affineBasis t).coord 1 z}
          have hpR : p ∈ Rᶜ :=
            openBaseCap_subset_compl_of_inter_eq_face
              t hinter hpCap
          have hpN : p ∈ N := by
            exact
              ⟨⟨⟨hpR, Metric.mem_ball_self hε⟩,
                hpZero⟩, hpOne⟩
          have hNopen : IsOpen N := by
            exact
              (hRclosed.isOpen_compl.inter Metric.isOpen_ball)
                |>.inter (isOpen_coord_pos t 0)
                |>.inter (isOpen_coord_pos t 1)
          apply
            Filter.mem_of_superset
              (hNopen.mem_nhds hpN)
          intro q hqN
          rcases hqN with
            ⟨⟨⟨hqR, hqBall⟩, hqZero⟩, hqOne⟩
          by_cases hqTriangle : q ∈ t.closedInterior
          · exact
              Or.inr <|
                (mem_openBaseCap_iff t q).2
                  ⟨hqTriangle, hqOne⟩
          · left
            change JoinedIn V y q
            have hqV :
                q ∈ (R ∪ t.closedInterior)ᶜ := by
              intro hqUnion
              rcases hqUnion with hqR' | hqTriangle'
              · exact hqR hqR'
              · exact hqTriangle hqTriangle'
            exact
              (hnear q
                (by simpa [Metric.mem_ball] using hqBall)
                hqZero hqOne hqV).symm
        · have hpTwo :
              0 <
                (Submission.Triangle.affineBasis t).coord 2 p :=
            lt_of_le_of_ne (hpCoords 2) (Ne.symm hpTwoEq)
          have hpInterior : p ∈ t.interior := by
            rw [Submission.Triangle.mem_interior_iff_coord_pos]
            intro i
            fin_cases i
            · exact hpZero
            · exact hpOne
            · exact hpTwo
          apply
            Filter.mem_of_superset
              ((Submission.Triangle.isOpen_interior t).mem_nhds
                hpInterior)
          intro q hqInterior
          exact
            Or.inr <|
              (mem_openBaseCap_iff t q).2
                ⟨t.interior_subset_closedInterior hqInterior,
                  (Submission.Triangle.mem_interior_iff_coord_pos
                    t q).mp hqInterior 1⟩
  have hUdecomp :
      Rᶜ = V ∪ W := by
    ext x
    constructor
    · intro hxR
      by_cases hxTriangle : x ∈ t.closedInterior
      · right
        change x ∈ openBaseCap t
        refine ⟨hxTriangle, ?_⟩
        intro hxBase
        have hxInter : x ∈ R ∩ t.closedInterior := by
          rw [hinter]
          exact hxBase
        exact hxR hxInter.1
      · left
        intro hxUnion
        rcases hxUnion with hxR' | hxTriangle'
        · exact hxR hxR'
        · exact hxTriangle hxTriangle'
    · rintro (hxV | hxW)
      · intro hxR
        exact hxV (Or.inl hxR)
      · exact
          openBaseCap_subset_compl_of_inter_eq_face
            t hinter hxW
  have hUdiff :
      Rᶜ \ (C ∪ W) = V \ C := by
    ext x
    constructor
    · rintro ⟨hxR, hxNot⟩
      have hxDecomp : x ∈ V ∪ W := by
        rw [← hUdecomp]
        exact hxR
      rcases hxDecomp with hxV | hxW
      · exact
          ⟨hxV, fun hxC =>
            hxNot (Or.inl hxC)⟩
      · exact False.elim <|
          hxNot (Or.inr hxW)
    · rintro ⟨hxV, hxNotC⟩
      refine ⟨?_, ?_⟩
      · intro hxR
        exact hxV (Or.inl hxR)
      · rintro (hxC | hxW)
        · exact hxNotC hxC
        · exact hxV (Or.inr hxW.1)
  let U : Set (ℝ × ℝ) := Rᶜ
  let Q : Set U :=
    Subtype.val ⁻¹' (C ∪ W)
  have hQopen : IsOpen Q := by
    exact hCUnionWOpen.preimage continuous_subtype_val
  have hQclosed : IsClosed Q := by
    rw [← isOpen_compl_iff]
    have hQcompl :
        Qᶜ =
          Subtype.val ⁻¹' (V \ C) := by
      ext x
      change
        x.1 ∉ C ∪ W ↔
          x.1 ∈ V \ C
      have hx :=
        Set.ext_iff.mp hUdiff x.1
      simpa [x.2] using hx
    rw [hQcompl]
    exact hVdiffCopen.preimage continuous_subtype_val
  letI : PreconnectedSpace U := by
    exact
      isPreconnected_iff_preconnectedSpace.mp
        (by simpa [U] using hRcompl)
  have hyC : y ∈ C :=
    mem_pathComponentIn_self hyV
  have hyU : y ∈ U := by
    exact hyR
  have hQnonempty : Q.Nonempty := by
    exact
      ⟨⟨y, hyU⟩, Or.inl hyC⟩
  have hQuniv : Q = Set.univ :=
    IsClopen.eq_univ ⟨hQclosed, hQopen⟩ hQnonempty
  have hVsubsetC : V ⊆ C := by
    intro x hxV
    have hxU : x ∈ U := by
      intro hxR
      exact hxV (Or.inl hxR)
    have hxQ : (⟨x, hxU⟩ : U) ∈ Q := by
      rw [hQuniv]
      trivial
    rcases hxQ with hxC | hxW
    · exact hxC
    · exact False.elim <|
        hxV (Or.inr hxW.1)
  have hVpath : IsPathConnected V := by
    refine ⟨y, hyV, ?_⟩
    intro x hxV
    exact hVsubsetC hxV
  exact hVpath.isConnected.isPreconnected

end Submission.TriangleAttachment
