import Submission.PolygonalArcCollarCompatibleOrientedTubeData
import Submission.PolygonalArcAdjacentOutwardDirectionsNotSameRay
import Submission.PlanarRot90ConeAvoidsRay
import Submission.PlanarRot90SameSideConesDisjoint
import Submission.PositiveSeparation

open Classical
noncomputable section

set_option maxHeartbeats 5000000

-- [TABLET NODE: PolygonalArcCollarCompatibleOrientedTubeDataExists]
lemma PolygonalArcCollarCompatibleOrientedTubeDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins) := by
-- BODY
  have segmentEndpoints_ne :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        γ.vertices[j] ≠ γ.vertices[j + 1] := by
    intro j hj
    have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft :=
        controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    exact dist_pos.mp hdist_pos
  have forwardDirection_ne_zero :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        γ.vertices[j + 1] - γ.vertices[j] ≠ 0 := by
    intro j hj
    exact sub_ne_zero.mpr (segmentEndpoints_ne j hj).symm
  have backwardDirection_ne_zero :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        γ.vertices[j] - γ.vertices[j + 1] ≠ 0 := by
    intro j hj
    exact sub_ne_zero.mpr (segmentEndpoints_ne j hj)
  have initialConeAvoidsPreviousRay :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ κ : ℝ, 0 < κ ∧
          ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
            c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
              t • (γ.vertices[j + 1] - γ.vertices[j]) +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    intro j hj hprev
    exact
      PlanarRot90ConeAvoidsRay
        (d := γ.vertices[j + 1] - γ.vertices[j])
        (v := γ.vertices[j - 1] - γ.vertices[j])
        (forwardDirection_ne_zero j hj)
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ hprev hj).1
  have terminalConeAvoidsNextRay :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ κ : ℝ, 0 < κ ∧
            ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
              c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
                t • (γ.vertices[j] - γ.vertices[j + 1]) +
                  s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    intro j hj hnext
    have hnot :
        ¬ ∃ a : ℝ, 0 < a ∧
          γ.vertices[j + 2] - γ.vertices[j + 1] =
            a • (γ.vertices[j] - γ.vertices[j + 1]) := by
      simpa [Nat.add_assoc] using
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
          (i := j + 1) (Nat.succ_pos j) hnext).2
    exact
      PlanarRot90ConeAvoidsRay
        (d := γ.vertices[j] - γ.vertices[j + 1])
        (v := γ.vertices[j + 2] - γ.vertices[j + 1])
        (backwardDirection_ne_zero j hj) hnot
  have successiveOutwardConesDisjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ κ : ℝ, 0 < κ ∧
            ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
              |b| < κ * a → |r| < κ * c →
                a • (γ.vertices[j] - γ.vertices[j + 1]) +
                    b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
                  c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
                    r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    intro j hj hnext
    have hnot :
        ¬ ∃ A : ℝ, 0 < A ∧
          γ.vertices[j + 2] - γ.vertices[j + 1] =
            A • (γ.vertices[j] - γ.vertices[j + 1]) := by
      simpa [Nat.add_assoc] using
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
          (i := j + 1) (Nat.succ_pos j) hnext).2
    exact
      PlanarRot90SameSideConesDisjoint
        (u := γ.vertices[j] - γ.vertices[j + 1])
        (d := γ.vertices[j + 2] - γ.vertices[j + 1])
        (backwardDirection_ne_zero j hj)
        (forwardDirection_ne_zero (j + 1) hnext) hnot
  let leftParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let rightParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    1 - controlRadii.radius ⟨j + 1, hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let segmentLength : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    dist γ.vertices[j] γ.vertices[j + 1]
  let paramSlack : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (leftParam j hj / 2)
      (min ((1 - rightParam j hj) / 2)
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
  let lowerParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    leftParam j hj - paramSlack j hj
  let upperParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    rightParam j hj + paramSlack j hj
  let normal : (j : ℕ) → j + 1 < γ.vertices.length →
      EuclideanSpace ℝ (Fin 2) := fun j hj =>
    PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])
  let initialRayCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      Classical.choose (initialConeAvoidsPreviousRay j hj hprev)
    else
      1
  let terminalRayCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      Classical.choose (terminalConeAvoidsNextRay j hj hnext)
    else
      1
  let initialPairCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      Classical.choose
        (successiveOutwardConesDisjoint (j - 1)
          (by
            have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
          (by
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))
    else
      1
  let terminalPairCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      Classical.choose (successiveOutwardConesDisjoint j hj hnext)
    else
      1
  let initialConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (initialRayCone j hj) (initialPairCone j hj)
  let terminalConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (terminalRayCone j hj) (terminalPairCone j hj)
  have leftParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj := by
    intro j hj
    simpa [leftParam] using middleSegments.left_parameter_pos j hj
  have leftParam_lt_rightParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj < rightParam j hj := by
    intro j hj
    simpa [leftParam, rightParam] using
      middleSegments.left_parameter_lt_right_parameter j hj
  have rightParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightParam j hj < 1 := by
    intro j hj
    simpa [rightParam] using middleSegments.right_parameter_lt_one j hj
  have one_sub_rightParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - rightParam j hj := by
    intro j hj
    linarith [rightParam_lt_one j hj]
  have segmentLength_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentLength j hj := by
    intro j hj
    let i0 : Fin γ.vertices.length := ⟨j, Nat.lt_of_succ_lt hj⟩
    let i1 : Fin γ.vertices.length := ⟨j + 1, hj⟩
    have hleft : 0 < controlRadii.radius i0 := controlRadii.radius_pos i0
    have hright : 0 < controlRadii.radius i1 := controlRadii.radius_pos i1
    have hsum :
        controlRadii.radius i0 + controlRadii.radius i1 <
          dist γ.vertices[j] γ.vertices[j + 1] := by
      simpa [i0, i1] using controlRadii.adjacent_radii_sum_lt (j := j) hj
    dsimp [segmentLength]
    nlinarith
  have eta_pos : 0 < η := by
    have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
    have hidx : (0 : ℕ) < γ.vertices.length := by omega
    exact (controlRadii.radius_pos ⟨0, hidx⟩).trans
      (controlRadii.radius_lt_eta ⟨0, hidx⟩)
  have paramSlack_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < paramSlack j hj := by
    intro j hj
    have hden : 0 < 8 * (segmentLength j hj + 1) := by
      have hD : 0 < segmentLength j hj := segmentLength_pos j hj
      positivity
    dsimp [paramSlack]
    exact lt_min (half_pos (leftParam_pos j hj))
      (lt_min (half_pos (one_sub_rightParam_pos j hj))
        (div_pos (forbiddenMargins.margin_pos j hj) hden))
  have paramSlack_le_left_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ leftParam j hj / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact min_le_left _ _
  have paramSlack_le_one_sub_right_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ (1 - rightParam j hj) / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have paramSlack_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have paramSlack_mul_segmentLength_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj * segmentLength j hj <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    let D : ℝ := segmentLength j hj
    let μ : ℝ := forbiddenMargins.margin j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hμpos : 0 < μ := by
      dsimp [μ]
      exact forbiddenMargins.margin_pos j hj
    have hdenpos : 0 < 8 * (D + 1) := by positivity
    have hscaled :
        μ / (8 * (D + 1)) * D < μ / 4 := by
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      paramSlack j hj * segmentLength j hj
          ≤ (μ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                simpa [D, μ] using paramSlack_le_margin_scaled j hj)
              hDnonneg
      _ < μ / 4 := hscaled
  have lowerParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj := by
    intro j hj
    have hle := paramSlack_le_left_half j hj
    have hleft := leftParam_pos j hj
    dsimp [lowerParam]
    nlinarith
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj < leftParam j hj := by
    intro j hj
    dsimp [lowerParam]
    linarith [paramSlack_pos j hj]
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < upperParam j hj := by
    intro j hj
    dsimp [upperParam]
    linarith [paramSlack_pos j hj]
  have upperParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1 := by
    intro j hj
    have hle := paramSlack_le_one_sub_right_half j hj
    have hright := rightParam_lt_one j hj
    dsimp [upperParam]
    nlinarith
  have one_sub_upperParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < 1 - upperParam j hj := by
    intro j hj
    linarith [upperParam_lt_one j hj]
  have initialRayCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialRayCone j hj := by
    intro j hj
    dsimp [initialRayCone]
    by_cases hprev : 0 < j
    · simpa [hprev] using
        (Classical.choose_spec (initialConeAvoidsPreviousRay j hj hprev)).1
    · simp [hprev]
  have terminalRayCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalRayCone j hj := by
    intro j hj
    dsimp [terminalRayCone]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · simpa [hnext] using
        (Classical.choose_spec (terminalConeAvoidsNextRay j hj hnext)).1
    · simp [hnext]
  have initialPairCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialPairCone j hj := by
    intro j hj
    dsimp [initialPairCone]
    by_cases hprev : 0 < j
    · simpa [hprev] using
        (Classical.choose_spec
          (successiveOutwardConesDisjoint (j - 1)
            (by
              have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
            (by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))).1
    · simp [hprev]
  have terminalPairCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalPairCone j hj := by
    intro j hj
    dsimp [terminalPairCone]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · simpa [hnext] using
        (Classical.choose_spec (successiveOutwardConesDisjoint j hj hnext)).1
    · simp [hnext]
  have initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialConeBound j hj := by
    intro j hj
    dsimp [initialConeBound]
    exact lt_min (initialRayCone_pos j hj) (initialPairCone_pos j hj)
  have terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalConeBound j hj := by
    intro j hj
    dsimp [terminalConeBound]
    exact lt_min (terminalRayCone_pos j hj) (terminalPairCone_pos j hj)
  let initialCenterline : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
      Set.Icc (leftParam j hj) (1 : ℝ)
  let terminalCenterline : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
      Set.Icc (0 : ℝ) (rightParam j hj)
  have segment_nonempty :
      ∀ (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (segment ℝ γ.vertices[k] γ.vertices[k + 1]).Nonempty := by
    intro k hk
    exact ⟨γ.vertices[k], by simp [left_mem_segment]⟩
  have segment_compact :
      ∀ (k : ℕ) (hk : k + 1 < γ.vertices.length),
        IsCompact (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro k hk
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have initialCenterline_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (initialCenterline j hj).Nonempty := by
    intro j hj
    refine ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] (leftParam j hj), ?_⟩
    exact ⟨leftParam j hj,
      ⟨le_rfl, le_of_lt ((leftParam_lt_rightParam j hj).trans (rightParam_lt_one j hj))⟩,
      rfl⟩
  have terminalCenterline_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (terminalCenterline j hj).Nonempty := by
    intro j hj
    refine ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] (0 : ℝ), ?_⟩
    exact ⟨0, ⟨le_rfl,
      le_of_lt ((leftParam_pos j hj).trans (leftParam_lt_rightParam j hj))⟩, rfl⟩
  have initialCenterline_compact :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        IsCompact (initialCenterline j hj) := by
    intro j hj
    dsimp [initialCenterline]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have terminalCenterline_compact :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        IsCompact (terminalCenterline j hj) := by
    intro j hj
    dsimp [terminalCenterline]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have initialCenterline_disjoint_previous :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        Disjoint (initialCenterline j hj)
          (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
    intro j hj hprev
    rw [Set.disjoint_left]
    intro x hxA hxPrev
    rcases hxA with ⟨t, ht, rfl⟩
    have hCurrent :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨le_trans (le_of_lt (leftParam_pos j hj)) ht.1, ht.2⟩, rfl⟩
    have hprevSeg : (j - 1) + 1 < γ.vertices.length := by
      have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj'
    have hlt : j - 1 < j := Nat.sub_lt hprev Nat.zero_lt_one
    have hinter :
        segment ℝ γ.vertices[j - 1] γ.vertices[j] ∩
            segment ℝ γ.vertices[j] γ.vertices[j + 1] =
          ({γ.vertices[j]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw := γ.segment_intersections (i := j - 1) (j := j) hprevSeg hj hlt
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hraw
    have hxVertex :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j] := by
      have hxInter :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            segment ℝ γ.vertices[j - 1] γ.vertices[j] ∩
              segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
        ⟨hxPrev, hCurrent⟩
      rw [hinter] at hxInter
      simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (segmentEndpoints_ne j hj)
    have ht0 : t = 0 := hf (by simpa [f] using hxVertex)
    linarith [leftParam_pos j hj, ht.1]
  have terminalCenterline_disjoint_next :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint (terminalCenterline j hj)
            (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro x hxA hxNext
    rcases hxA with ⟨t, ht, rfl⟩
    have hCurrent :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht.1, le_trans ht.2 (le_of_lt (rightParam_lt_one j hj))⟩, rfl⟩
    have hinter :
        segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] =
          ({γ.vertices[j + 1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := j) (j := j + 1) hj hnext (Nat.lt_succ_self j)
      simpa using hraw
    have hxVertex :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j + 1] := by
      have hxInter :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
              segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] :=
        ⟨hCurrent, hxNext⟩
      rw [hinter] at hxInter
      simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (segmentEndpoints_ne j hj)
    have ht1 : t = 1 := hf (by simpa [f] using hxVertex)
    linarith [rightParam_lt_one j hj, ht.2]
  have successiveCenterlines_disjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint (terminalCenterline j hj) (initialCenterline (j + 1) hnext) := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro x hxA hxB
    rcases hxA with ⟨t, ht, rfl⟩
    rcases hxB with ⟨u, hu, hxu⟩
    have hCurrent :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht.1, le_trans ht.2 (le_of_lt (rightParam_lt_one j hj))⟩, rfl⟩
    have hNext :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] := by
      rw [← hxu, segment_eq_image_lineMap]
      exact ⟨u, ⟨le_trans (le_of_lt (leftParam_pos (j + 1) hnext)) hu.1, hu.2⟩,
        rfl⟩
    have hinter :
        segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] =
          ({γ.vertices[j + 1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := j) (j := j + 1) hj hnext (Nat.lt_succ_self j)
      simpa using hraw
    have hxVertex :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j + 1] := by
      have hxInter :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
              segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] :=
        ⟨hCurrent, hNext⟩
      rw [hinter] at hxInter
      simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (segmentEndpoints_ne j hj)
    have ht1 : t = 1 := hf (by simpa [f] using hxVertex)
    linarith [rightParam_lt_one j hj, ht.2]
  have initialAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ∈ Set.Icc (leftParam j hj) (1 : ℝ) →
            ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
              δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hprev
    let A : Set (EuclideanSpace ℝ (Fin 2)) := initialCenterline j hj
    let B : Set (EuclideanSpace ℝ (Fin 2)) :=
      segment ℝ γ.vertices[j - 1] γ.vertices[j]
    have hprevSeg : (j - 1) + 1 < γ.vertices.length := by
      have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj'
    have hAne : A.Nonempty := by
      simpa [A] using initialCenterline_nonempty j hj
    have hBne : B.Nonempty := by
      simpa [B, Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using
        segment_nonempty (j - 1) hprevSeg
    have hAc : IsCompact A := by
      simpa [A] using initialCenterline_compact j hj
    have hBc : IsCompact B := by
      simpa [B, Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using
        segment_compact (j - 1) hprevSeg
    have hdisj : Disjoint A B := by
      simpa [A, B] using initialCenterline_disjoint_previous j hj hprev
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
    refine ⟨δ, hδpos, ?_⟩
    intro t ht q hq
    exact hδ (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
      (by exact ⟨t, ht, rfl⟩) q (by simpa [B] using hq)
  have terminalAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (rightParam j hj) →
              ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
                δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hnext
    let A : Set (EuclideanSpace ℝ (Fin 2)) := terminalCenterline j hj
    let B : Set (EuclideanSpace ℝ (Fin 2)) :=
      segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]
    have hAne : A.Nonempty := by
      simpa [A] using terminalCenterline_nonempty j hj
    have hBne : B.Nonempty := by
      simpa [B] using segment_nonempty (j + 1) hnext
    have hAc : IsCompact A := by
      simpa [A] using terminalCenterline_compact j hj
    have hBc : IsCompact B := by
      simpa [B] using segment_compact (j + 1) hnext
    have hdisj : Disjoint A B := by
      simpa [A, B] using terminalCenterline_disjoint_next j hj hnext
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
    refine ⟨δ, hδpos, ?_⟩
    intro t ht q hq
    exact hδ (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
      (by exact ⟨t, ht, rfl⟩) q (by simpa [B] using hq)
  have successiveAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (rightParam j hj) →
              ∀ u : ℝ, u ∈ Set.Icc (leftParam (j + 1) hnext) (1 : ℝ) →
                δ ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u) := by
    intro j hj hnext
    let A : Set (EuclideanSpace ℝ (Fin 2)) := terminalCenterline j hj
    let B : Set (EuclideanSpace ℝ (Fin 2)) := initialCenterline (j + 1) hnext
    have hAne : A.Nonempty := by
      simpa [A] using terminalCenterline_nonempty j hj
    have hBne : B.Nonempty := by
      simpa [B] using initialCenterline_nonempty (j + 1) hnext
    have hAc : IsCompact A := by
      simpa [A] using terminalCenterline_compact j hj
    have hBc : IsCompact B := by
      simpa [B] using initialCenterline_compact (j + 1) hnext
    have hdisj : Disjoint A B := by
      simpa [A, B] using successiveCenterlines_disjoint j hj hnext
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
    refine ⟨δ, hδpos, ?_⟩
    intro t ht u hu
    exact hδ (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
      (by exact ⟨t, ht, rfl⟩)
      (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u)
      (by exact ⟨u, hu, rfl⟩)
  let initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ :=
    fun j hj hprev => Classical.choose (initialAwayExists j hj hprev)
  let terminalAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => Classical.choose (terminalAwayExists j hj hnext)
  let successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => Classical.choose (successiveAwayExists j hj hnext)
  have initialAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        0 < initialAwaySeparation j hj hprev := by
    intro j hj hprev
    simpa [initialAwaySeparation] using
      (Classical.choose_spec (initialAwayExists j hj hprev)).1
  have terminalAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < terminalAwaySeparation j hj hnext := by
    intro j hj hnext
    simpa [terminalAwaySeparation] using
      (Classical.choose_spec (terminalAwayExists j hj hnext)).1
  have successiveAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < successiveAwaySeparation j hj hnext := by
    intro j hj hnext
    simpa [successiveAwaySeparation] using
      (Classical.choose_spec (successiveAwayExists j hj hnext)).1
  let initialAwayWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hprev : 0 < j then
        initialAwaySeparation j hj hprev / (8 * (segmentLength j hj + 1))
      else
        1
  let terminalAwayWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hnext : (j + 1) + 1 < γ.vertices.length then
        terminalAwaySeparation j hj hnext / (8 * (segmentLength j hj + 1))
      else
        1
  let previousSuccessiveAwayWidthTerm :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      successiveAwaySeparation (j - 1)
          (by
            have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
          (by
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj) /
        (16 * (segmentLength j hj + 1))
    else
      1
  let nextSuccessiveAwayWidthTerm :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      successiveAwaySeparation j hj hnext / (16 * (segmentLength j hj + 1))
    else
      1
  let halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min
      (min (η / (4 * (segmentLength j hj + 1)))
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
      (min
        (min (initialConeBound j hj * lowerParam j hj / 2)
          (terminalConeBound j hj * (1 - upperParam j hj) / 2))
        (min
          (min (initialAwayWidthTerm j hj) (terminalAwayWidthTerm j hj))
          (min (previousSuccessiveAwayWidthTerm j hj)
            (nextSuccessiveAwayWidthTerm j hj))))
  let tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let leftHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let rightHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  have initialAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < initialAwayWidthTerm j hj := by
    intro j hj
    dsimp [initialAwayWidthTerm]
    by_cases hprev : 0 < j
    · have hden : 0 < 8 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hprev] using
        div_pos (initialAwaySeparation_pos j hj hprev) hden
    · simp [hprev]
  have terminalAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < terminalAwayWidthTerm j hj := by
    intro j hj
    dsimp [terminalAwayWidthTerm]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · have hden : 0 < 8 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hnext] using
        div_pos (terminalAwaySeparation_pos j hj hnext) hden
    · simp [hnext]
  have previousSuccessiveAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < previousSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [previousSuccessiveAwayWidthTerm]
    by_cases hprev : 0 < j
    · have hden : 0 < 16 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hprev] using
        div_pos
          (successiveAwaySeparation_pos (j - 1)
            (by
              have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
            (by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))
          hden
    · simp [hprev]
  have nextSuccessiveAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < nextSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [nextSuccessiveAwayWidthTerm]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · have hden : 0 < 16 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hnext] using
        div_pos (successiveAwaySeparation_pos j hj hnext) hden
    · simp [hnext]
  have halfWidth_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj := by
    intro j hj
    have hD : 0 < segmentLength j hj := segmentLength_pos j hj
    have hden4 : 0 < 4 * (segmentLength j hj + 1) := by positivity
    have hden8 : 0 < 8 * (segmentLength j hj + 1) := by positivity
    have hconeI :
        0 < initialConeBound j hj * lowerParam j hj / 2 := by
      exact half_pos (mul_pos (initialConeBound_pos j hj) (lowerParam_pos j hj))
    have hconeT :
        0 < terminalConeBound j hj * (1 - upperParam j hj) / 2 := by
      exact half_pos
        (mul_pos (terminalConeBound_pos j hj) (one_sub_upperParam_pos j hj))
    dsimp [halfWidth]
    exact lt_min
      (lt_min (div_pos eta_pos hden4)
        (div_pos (forbiddenMargins.margin_pos j hj) hden8))
      (lt_min (lt_min hconeI hconeT)
        (lt_min
          (lt_min (initialAwayWidthTerm_pos j hj) (terminalAwayWidthTerm_pos j hj))
          (lt_min (previousSuccessiveAwayWidthTerm_pos j hj)
            (nextSuccessiveAwayWidthTerm_pos j hj))))
  have halfWidth_le_eta_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ η / (4 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have halfWidth_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have halfWidth_le_initialConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialConeBound j hj * lowerParam j hj / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have halfWidth_le_terminalConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalConeBound j hj * (1 - upperParam j hj) / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have halfWidth_le_initialAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_left _ _)))
  have halfWidth_le_terminalAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  have halfWidth_le_previousSuccessiveAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ previousSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
  have halfWidth_le_nextSuccessiveAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ nextSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  have halfWidth_lt_initialCone_mul_lowerParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < initialConeBound j hj * lowerParam j hj := by
    intro j hj
    have hprod : 0 < initialConeBound j hj * lowerParam j hj :=
      mul_pos (initialConeBound_pos j hj) (lowerParam_pos j hj)
    have hhalf :
        initialConeBound j hj * lowerParam j hj / 2 <
          initialConeBound j hj * lowerParam j hj := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_initialConeWidth j hj) hhalf
  have halfWidth_lt_terminalCone_mul_one_sub_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < terminalConeBound j hj * (1 - upperParam j hj) := by
    intro j hj
    have hprod : 0 < terminalConeBound j hj * (1 - upperParam j hj) :=
      mul_pos (terminalConeBound_pos j hj) (one_sub_upperParam_pos j hj)
    have hhalf :
        terminalConeBound j hj * (1 - upperParam j hj) / 2 <
          terminalConeBound j hj * (1 - upperParam j hj) := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_terminalConeWidth j hj) hhalf
  have normal_orthogonal :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        inner ℝ (γ.vertices[j + 1] - γ.vertices[j]) (normal j hj) = 0 := by
    intro j hj
    simpa [normal] using PlanarRot90Orthogonal (γ.vertices[j + 1] - γ.vertices[j])
  have normal_norm_eq_tangent_norm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = ‖γ.vertices[j + 1] - γ.vertices[j]‖ := by
    intro j hj
    simpa [normal] using PlanarRot90Norm (γ.vertices[j + 1] - γ.vertices[j])
  have normal_norm_eq_segment_length :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = dist γ.vertices[j] γ.vertices[j + 1] := by
    intro j hj
    calc
      ‖normal j hj‖ = ‖γ.vertices[j + 1] - γ.vertices[j]‖ :=
        normal_norm_eq_tangent_norm j hj
      _ = ‖γ.vertices[j] - γ.vertices[j + 1]‖ := by
        rw [← norm_neg (γ.vertices[j + 1] - γ.vertices[j])]
        congr 1
        abel
      _ = dist γ.vertices[j] γ.vertices[j + 1] := by
        rw [dist_eq_norm]
  have halfWidth_mul_normal_norm_lt_eta :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < η := by
    intro j hj
    let D : ℝ := segmentLength j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hdenpos : 0 < 4 * (D + 1) := by positivity
    have hscaled : η / (4 * (D + 1)) * D < η := by
      have hden_ne : 4 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (η / (4 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [D] using halfWidth_le_eta_scaled j hj) hDnonneg
      _ < η := hscaled
  have halfWidth_mul_normal_norm_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    let D : ℝ := segmentLength j hj
    let μ : ℝ := forbiddenMargins.margin j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hμpos : 0 < μ := by
      dsimp [μ]
      exact forbiddenMargins.margin_pos j hj
    have hdenpos : 0 < 8 * (D + 1) := by positivity
    have hscaled : μ / (8 * (D + 1)) * D < μ / 4 := by
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (μ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [D, μ] using halfWidth_le_margin_scaled j hj) hDnonneg
      _ < μ / 4 := hscaled
  have dist_lineMap_lineMap_local :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (c₁ c₂ : ℝ),
        dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
          dist c₁ c₂ * dist A B := by
    intro A B c₁ c₂
    rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
    have hvec :
        AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
          (c₁ - c₂) • (B - A) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    rw [hvec, norm_smul, Real.norm_eq_abs]
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      have hneg : B - A = -(A - B) := by
        abel
      rw [hneg, norm_neg]
    rw [hnorm]
  have real_dist_to_Icc_of_mem_Ioo_expansion :
      ∀ {L R ε t : ℝ}, 0 < ε → L < R →
        t ∈ Set.Ioo (L - ε) (R + ε) →
          ∃ u : ℝ, u ∈ Set.Icc L R ∧ dist t u < ε := by
    intro L R ε t hε hLR ht
    by_cases htL : t < L
    · refine ⟨L, ⟨le_rfl, le_of_lt hLR⟩, ?_⟩
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htL)]
      linarith [ht.1]
    · by_cases htR : t ≤ R
      · refine ⟨t, ⟨le_of_not_gt htL, htR⟩, ?_⟩
        simpa using hε
      · have hRt : R < t := lt_of_not_ge htR
        refine ⟨R, ⟨le_of_lt hLR, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hRt)]
        linarith [ht.2]
  have middle_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        middleSegments.middle j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [middleSegments.middle_eq j hj] at hz
    rcases hz with ⟨t, ht, rfl⟩
    rw [show tube j hj =
        {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
          ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj} by rfl]
    refine ⟨t, ?_, 0, ?_, by simp⟩
    · exact ⟨(lowerParam_lt_leftParam j hj).trans_le ht.1,
        lt_of_le_of_lt ht.2 (rightParam_lt_upperParam j hj)⟩
    · exact ⟨by simpa using halfWidth_pos j hj, halfWidth_pos j hj⟩
  have leftHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [leftHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨lt_trans (neg_neg_of_pos (halfWidth_pos j hj)) hs.1, hs.2⟩
  have rightHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [rightHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨hs.1, hs.2.trans (halfWidth_pos j hj)⟩
  have tube_subset_eta_neighborhood :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    let p : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
    have hpseg : p ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      refine ⟨t, ?_, rfl⟩
      exact ⟨le_of_lt ((lowerParam_pos j hj).trans ht.1),
        le_of_lt (ht.2.trans (upperParam_lt_one j hj))⟩
    have hpcarrier : p ∈ γ.carrier := by
      rw [γ.carrier_eq]
      exact ⟨j, hj, hpseg⟩
    refine ⟨p, hpcarrier, ?_⟩
    have hs_abs : |s| < halfWidth j hj := abs_lt.mpr hs
    have hdist :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p = |s| * ‖normal j hj‖ := by
      have hsub :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj - p =
            s • normal j hj := by
        simp [p]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc
      dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p = |s| * ‖normal j hj‖ := hdist
      _ ≤ halfWidth j hj * ‖normal j hj‖ := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
      _ < η := halfWidth_mul_normal_norm_lt_eta j hj
  have tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2 := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    obtain ⟨u, huIcc, htu⟩ :=
      real_dist_to_Icc_of_mem_Ioo_expansion
        (L := leftParam j hj) (R := rightParam j hj)
        (ε := paramSlack j hj) (t := t) (paramSlack_pos j hj)
        (leftParam_lt_rightParam j hj) (by
          simpa [lowerParam, upperParam] using ht)
    let p : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] u
    have hpM : p ∈ middleSegments.middle j hj := by
      rw [middleSegments.middle_eq j hj]
      exact ⟨u, by simpa [leftParam, rightParam] using huIcc, rfl⟩
    refine ⟨p, hpM, ?_⟩
    let q : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
    have hs_abs : |s| < halfWidth j hj := abs_lt.mpr hs
    have hperp :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q = |s| * ‖normal j hj‖ := by
      have hsub :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj - q =
            s • normal j hj := by
        simp [q]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    have hperp_lt :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q <
          forbiddenMargins.margin j hj / 4 := by
      calc
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q = |s| * ‖normal j hj‖ := hperp
        _ ≤ halfWidth j hj * ‖normal j hj‖ := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
        _ < forbiddenMargins.margin j hj / 4 :=
          halfWidth_mul_normal_norm_lt_margin_quarter j hj
    have hline_lt : dist q p < forbiddenMargins.margin j hj / 4 := by
      have htuD :
          dist t u * segmentLength j hj <
            forbiddenMargins.margin j hj / 4 := by
        have hmul :
            dist t u * segmentLength j hj <
              paramSlack j hj * segmentLength j hj :=
          mul_lt_mul_of_pos_right htu (segmentLength_pos j hj)
        exact hmul.trans (paramSlack_mul_segmentLength_lt_margin_quarter j hj)
      calc
        dist q p =
            dist t u * dist γ.vertices[j] γ.vertices[j + 1] := by
              simpa [q, p] using
                dist_lineMap_lineMap_local γ.vertices[j] γ.vertices[j + 1] t u
        _ = dist t u * segmentLength j hj := by
              simp [segmentLength]
        _ < forbiddenMargins.margin j hj / 4 := htuD
    have htri :
        dist
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj) p ≤
          dist
              (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj) q +
            dist q p :=
      dist_triangle _ _ _
    calc
      dist
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p
          ≤
        dist
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj) q +
          dist q p := htri
      _ < forbiddenMargins.margin j hj / 4 +
          forbiddenMargins.margin j hj / 4 := add_lt_add hperp_lt hline_lt
      _ = forbiddenMargins.margin j hj / 2 := by ring
  have tube_disjoint_nonadjacent_segments :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzSeg
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
    have hmargin :=
      forbiddenMargins.middle_segment_separation j hj k hk hgap p hpM z hzSeg
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']
  have tube_disjoint_nonincident_control_disks :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (i : Fin γ.vertices.length),
          i.1 ≠ j → i.1 ≠ j + 1 →
            Disjoint (tube j hj)
              (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) := by
    intro j hj i hij hijs
    rw [Set.disjoint_left]
    intro z hzTube hzDisk
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
    have hmargin :=
      forbiddenMargins.middle_control_disk_separation j hj i hij hijs p hpM z hzDisk
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']
  have tube_disjoint_nonadjacent_middle_cores :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (middleSegments.middle k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzMiddle
    exact Set.disjoint_left.mp
      (tube_disjoint_nonadjacent_segments j hj k hk hgap) hzTube
      (middleSegments.middle_subset_segment k hk hzMiddle)
  have tube_disjoint_nonadjacent_tubes :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (tube k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzj hzk
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzj
    obtain ⟨q, hqM, hqClose⟩ := tube_point_close_to_middle k hk z hzk
    have hgap_sym : k + 1 < j ∨ j + 1 < k := by
      cases hgap with
      | inl h => exact Or.inr h
      | inr h => exact Or.inl h
    have hmj :=
      forbiddenMargins.middle_core_separation j hj k hk hgap p hpM q hqM
    have hmk :=
      forbiddenMargins.middle_core_separation k hk j hj hgap_sym q hqM p hpM
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    have hmk' : forbiddenMargins.margin k hk ≤ dist p q := by
      simpa [dist_comm] using hmk
    have htri : dist p q ≤ dist p z + dist z q := dist_triangle p z q
    have hsum :
        dist p q <
          forbiddenMargins.margin j hj / 2 +
            forbiddenMargins.margin k hk / 2 :=
      lt_of_le_of_lt htri (add_lt_add hpClose' hqClose)
    nlinarith [forbiddenMargins.margin_pos j hj,
      forbiddenMargins.margin_pos k hk, hmj, hmk', hsum]
  have lineMap_sub_left :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (t : ℝ),
        AffineMap.lineMap A B t - A = t • (B - A) := by
    intro A B t
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module]
    ring
  have lineMap_sub_right :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (t : ℝ),
        AffineMap.lineMap A B t - B = (1 - t) • (A - B) := by
    intro A B t
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module]
    ring
  have lineMap_add_sub_left :
      ∀ (A B n : EuclideanSpace ℝ (Fin 2)) (t s : ℝ),
        AffineMap.lineMap A B t + s • n - A = t • (B - A) + s • n := by
    intro A B n t s
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module, sub_eq_add_neg]
    ring
  have lineMap_add_sub_right :
      ∀ (A B n : EuclideanSpace ℝ (Fin 2)) (t s : ℝ),
        AffineMap.lineMap A B t + s • n - B = (1 - t) • (A - B) + s • n := by
    intro A B n t s
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module, sub_eq_add_neg]
    ring
  have PlanarRot90_neg :
      ∀ v : EuclideanSpace ℝ (Fin 2), PlanarRot90 (-v) = -PlanarRot90 v := by
    intro v
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [PlanarRot90]
  have initialConeAvoidsPreviousRay_bound :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 →
          |s| < initialConeBound j hj * t →
            c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
              t • (γ.vertices[j + 1] - γ.vertices[j]) +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    intro j hj hprev c t s hc ht hs_ne hs_lt
    have hle :
        initialConeBound j hj ≤
          Classical.choose (initialConeAvoidsPreviousRay j hj hprev) := by
      dsimp [initialConeBound, initialRayCone]
      exact le_trans (min_le_left _ _) (by simp [hprev])
    have hs_lt' :
        |s| < Classical.choose (initialConeAvoidsPreviousRay j hj hprev) * t :=
      lt_of_lt_of_le hs_lt (mul_le_mul_of_nonneg_right hle (le_of_lt ht))
    exact
      (Classical.choose_spec (initialConeAvoidsPreviousRay j hj hprev)).2
        c t s hc ht hs_ne hs_lt'
  have terminalConeAvoidsNextRay_bound :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 →
            |s| < terminalConeBound j hj * t →
              c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
                t • (γ.vertices[j] - γ.vertices[j + 1]) +
                  s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    intro j hj hnext c t s hc ht hs_ne hs_lt
    have hle :
        terminalConeBound j hj ≤
          Classical.choose (terminalConeAvoidsNextRay j hj hnext) := by
      dsimp [terminalConeBound, terminalRayCone]
      exact le_trans (min_le_left _ _) (by simp [hnext])
    have hs_lt' :
        |s| < Classical.choose (terminalConeAvoidsNextRay j hj hnext) * t :=
      lt_of_lt_of_le hs_lt (mul_le_mul_of_nonneg_right hle (le_of_lt ht))
    exact
      (Classical.choose_spec (terminalConeAvoidsNextRay j hj hnext)).2
        c t s hc ht hs_ne hs_lt'
  have successiveOutwardConesDisjoint_bound :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
            |b| < terminalConeBound j hj * a →
              |r| < initialConeBound (j + 1) hnext * c →
                a • (γ.vertices[j] - γ.vertices[j + 1]) +
                    b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
                  c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
                    r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    intro j hj hnext a c b r ha hc hbr hb hr
    have hleT :
        terminalConeBound j hj ≤
          Classical.choose (successiveOutwardConesDisjoint j hj hnext) := by
      dsimp [terminalConeBound, terminalPairCone]
      exact le_trans (min_le_right _ _) (by simp [hnext])
    have hleI :
        initialConeBound (j + 1) hnext ≤
          Classical.choose (successiveOutwardConesDisjoint j hj hnext) := by
      dsimp [initialConeBound, initialPairCone]
      refine le_trans (min_le_right _ _) ?_
      simp
    have hb' :
        |b| < Classical.choose (successiveOutwardConesDisjoint j hj hnext) * a :=
      lt_of_lt_of_le hb (mul_le_mul_of_nonneg_right hleT (le_of_lt ha))
    have hr' :
        |r| < Classical.choose (successiveOutwardConesDisjoint j hj hnext) * c :=
      lt_of_lt_of_le hr (mul_le_mul_of_nonneg_right hleI (le_of_lt hc))
    exact
      (Classical.choose_spec (successiveOutwardConesDisjoint j hj hnext)).2
        a c b r ha hc hbr hb' hr'
  have initial_signed_cone_disjoint_previous_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • normal j hj}
          (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
    intro j hj hprev
    rw [Set.disjoint_left]
    intro z hzCone hzSeg
    rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
    rw [segment_eq_image_lineMap] at hzSeg
    rcases hzSeg with ⟨u, hu, hzPrev⟩
    have hPrevVec :
        z - γ.vertices[j] =
          (1 - u) • (γ.vertices[j - 1] - γ.vertices[j]) := by
      rw [← hzPrev]
      exact lineMap_sub_right γ.vertices[j - 1] γ.vertices[j] u
    have hConeVec :
        z - γ.vertices[j] =
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
      rw [hz]
      exact lineMap_add_sub_left γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have heq :
        (1 - u) • (γ.vertices[j - 1] - γ.vertices[j]) =
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
      exact hPrevVec.symm.trans hConeVec
    exact
      initialConeAvoidsPreviousRay_bound j hj hprev (1 - u) t s
        (by nlinarith [hu.2]) ht.1 hs_ne hs_lt heq
  have terminal_signed_cone_disjoint_next_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • normal j hj}
            (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro z hzCone hzSeg
    rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
    rw [segment_eq_image_lineMap] at hzSeg
    rcases hzSeg with ⟨u, hu, hzNext⟩
    have hNextVec :
        z - γ.vertices[j + 1] =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      rw [← hzNext]
      exact lineMap_sub_left γ.vertices[j + 1] γ.vertices[j + 2] u
    have hConeVec :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            s • normal j hj := by
      rw [hz]
      exact lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have hrot :
        (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          s • normal j hj := by
      have hback : γ.vertices[j] - γ.vertices[j + 1] =
          -(γ.vertices[j + 1] - γ.vertices[j]) := by
        abel
      rw [hback, PlanarRot90_neg]
      simp [normal]
    have heq :
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
      have hConeVec' :
          z - γ.vertices[j + 1] =
            (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
              (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
        hConeVec.trans (by rw [hrot])
      exact hNextVec.symm.trans hConeVec'
    exact
      terminalConeAvoidsNextRay_bound j hj hnext u (1 - t) (-s)
        hu.1 (by nlinarith [ht.2]) (by simpa using neg_ne_zero.mpr hs_ne)
        (by simpa [abs_neg] using hs_lt) heq
  have successive_positive_negative_cones_disjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, 0 < s ∧ s < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • normal j hj}
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s < 0 ∧ |s| < initialConeBound (j + 1) hnext * t ∧
                z =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                    s • normal (j + 1) hnext} := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro z hzL hzR
    rcases hzL with ⟨t, ht, s, hs_pos, hs_lt, hzL⟩
    rcases hzR with ⟨u, hu, r, hr_neg, hr_lt, hzR⟩
    have hLeftVec :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) + s • normal j hj := by
      rw [hzL]
      exact lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have hRightVec :
        z - γ.vertices[j + 1] =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      rw [hzR]
      exact lineMap_add_sub_left γ.vertices[j + 1] γ.vertices[j + 2]
        (normal (j + 1) hnext) u r
    have hrot :
        (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          s • normal j hj := by
      have hback : γ.vertices[j] - γ.vertices[j + 1] =
          -(γ.vertices[j + 1] - γ.vertices[j]) := by
        abel
      rw [hback, PlanarRot90_neg]
      simp [normal]
    have heq :
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      have hLeftVec' :
          z - γ.vertices[j + 1] =
            (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
              (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
        hLeftVec.trans (by rw [hrot])
      exact hLeftVec'.symm.trans hRightVec
    exact
      successiveOutwardConesDisjoint_bound j hj hnext (1 - t) u (-s) r
        (by nlinarith [ht.2]) hu.1 (by nlinarith [hs_pos, hr_neg])
        (by simpa [abs_neg, abs_of_pos hs_pos] using hs_lt)
        hr_lt heq
  have successive_negative_positive_cones_disjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s < 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • normal j hj}
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, 0 < s ∧ s < initialConeBound (j + 1) hnext * t ∧
                z =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                    s • normal (j + 1) hnext} := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro z hzL hzR
    rcases hzL with ⟨t, ht, s, hs_neg, hs_lt, hzL⟩
    rcases hzR with ⟨u, hu, r, hr_pos, hr_lt, hzR⟩
    have hLeftVec :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) + s • normal j hj := by
      rw [hzL]
      exact lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have hRightVec :
        z - γ.vertices[j + 1] =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      rw [hzR]
      exact lineMap_add_sub_left γ.vertices[j + 1] γ.vertices[j + 2]
        (normal (j + 1) hnext) u r
    have hrot :
        (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          s • normal j hj := by
      have hback : γ.vertices[j] - γ.vertices[j + 1] =
          -(γ.vertices[j + 1] - γ.vertices[j]) := by
        abel
      rw [hback, PlanarRot90_neg]
      simp [normal]
    have heq :
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      have hLeftVec' :
          z - γ.vertices[j + 1] =
            (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
              (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
        hLeftVec.trans (by rw [hrot])
      exact hLeftVec'.symm.trans hRightVec
    exact
      successiveOutwardConesDisjoint_bound j hj hnext (1 - t) u (-s) r
        (by nlinarith [ht.2]) hu.1 (by nlinarith [hs_neg, hr_pos])
        (by simpa [abs_neg] using hs_lt)
        (by simpa [abs_of_pos hr_pos] using hr_lt) heq
  have initial_centerline_previous_segment_away :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∀ t : ℝ,
          t ∈ Set.Icc
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) →
          ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
            initialAwaySeparation j hj hprev ≤
              dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hprev t ht q hq
    exact
      (Classical.choose_spec (initialAwayExists j hj hprev)).2 t
        (by simpa [leftParam] using ht) q hq
  have terminal_centerline_next_segment_away :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ t : ℝ,
            t ∈ Set.Icc (0 : ℝ)
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
              terminalAwaySeparation j hj hnext ≤
                dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hnext t ht q hq
    exact
      (Classical.choose_spec (terminalAwayExists j hj hnext)).2 t
        (by simpa [rightParam] using ht) q hq
  have successive_centerlines_away :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ t : ℝ,
            t ∈ Set.Icc (0 : ℝ)
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ u : ℝ,
              u ∈ Set.Icc
                (controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j + 1] γ.vertices[j + 2]) (1 : ℝ) →
                successiveAwaySeparation j hj hnext ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u) := by
    intro j hj hnext t ht u hu
    exact
      (Classical.choose_spec (successiveAwayExists j hj hnext)).2 t
        (by simpa [rightParam] using ht) u
        (by simpa [leftParam] using hu)
  have initial_halfWidth_mul_normal_norm_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        halfWidth j hj * ‖normal j hj‖ <
          initialAwaySeparation j hj hprev / 4 := by
    intro j hj hprev
    let D : ℝ := segmentLength j hj
    let δ : ℝ := initialAwaySeparation j hj hprev
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact initialAwaySeparation_pos j hj hprev
    have hscaled : δ / (8 * (D + 1)) * D < δ / 4 := by
      have hdenpos : 0 < 8 * (D + 1) := by positivity
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (δ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                dsimp [initialAwayWidthTerm] at halfWidth_le_initialAwayWidthTerm
                simpa [D, δ, hprev] using halfWidth_le_initialAwayWidthTerm j hj)
              hDnonneg
      _ < δ / 4 := hscaled
  have terminal_halfWidth_mul_normal_norm_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj * ‖normal j hj‖ <
            terminalAwaySeparation j hj hnext / 4 := by
    intro j hj hnext
    let D : ℝ := segmentLength j hj
    let δ : ℝ := terminalAwaySeparation j hj hnext
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact terminalAwaySeparation_pos j hj hnext
    have hscaled : δ / (8 * (D + 1)) * D < δ / 4 := by
      have hdenpos : 0 < 8 * (D + 1) := by positivity
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (δ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                dsimp [terminalAwayWidthTerm] at halfWidth_le_terminalAwayWidthTerm
                simpa [D, δ, hnext] using halfWidth_le_terminalAwayWidthTerm j hj)
              hDnonneg
      _ < δ / 4 := hscaled
  have successive_halfWidth_normal_sum_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj * ‖normal j hj‖ +
            halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ <
            successiveAwaySeparation j hj hnext / 4 := by
    intro j hj hnext
    let Δ : ℝ := successiveAwaySeparation j hj hnext
    have hΔpos : 0 < Δ := by
      dsimp [Δ]
      exact successiveAwaySeparation_pos j hj hnext
    have left_lt : halfWidth j hj * ‖normal j hj‖ < Δ / 8 := by
      let D : ℝ := segmentLength j hj
      have hDpos : 0 < D := by
        dsimp [D]
        exact segmentLength_pos j hj
      have hDnonneg : 0 ≤ D := le_of_lt hDpos
      have hscaled : Δ / (16 * (D + 1)) * D < Δ / 8 := by
        have hdenpos : 0 < 16 * (D + 1) := by positivity
        have hden_ne : 16 * (D + 1) ≠ 0 := ne_of_gt hdenpos
        field_simp [hden_ne]
        nlinarith
      calc
        halfWidth j hj * ‖normal j hj‖ =
            halfWidth j hj * D := by
              simp [D, segmentLength, normal_norm_eq_segment_length j hj]
        _ ≤ (Δ / (16 * (D + 1))) * D := by
              exact mul_le_mul_of_nonneg_right
                (by
                  dsimp [nextSuccessiveAwayWidthTerm] at halfWidth_le_nextSuccessiveAwayWidthTerm
                  simpa [D, Δ, hnext] using halfWidth_le_nextSuccessiveAwayWidthTerm j hj)
                hDnonneg
        _ < Δ / 8 := hscaled
    have right_lt :
        halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ < Δ / 8 := by
      let D : ℝ := segmentLength (j + 1) hnext
      have hDpos : 0 < D := by
        dsimp [D]
        exact segmentLength_pos (j + 1) hnext
      have hDnonneg : 0 ≤ D := le_of_lt hDpos
      have hscaled : Δ / (16 * (D + 1)) * D < Δ / 8 := by
        have hdenpos : 0 < 16 * (D + 1) := by positivity
        have hden_ne : 16 * (D + 1) ≠ 0 := ne_of_gt hdenpos
        field_simp [hden_ne]
        nlinarith
      calc
        halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ =
            halfWidth (j + 1) hnext * D := by
              simp [D, segmentLength, normal_norm_eq_segment_length (j + 1) hnext]
        _ ≤ (Δ / (16 * (D + 1))) * D := by
              exact mul_le_mul_of_nonneg_right
                (by
                  dsimp [previousSuccessiveAwayWidthTerm] at halfWidth_le_previousSuccessiveAwayWidthTerm
                  simpa [D, Δ, Nat.succ_pos] using
                    halfWidth_le_previousSuccessiveAwayWidthTerm (j + 1) hnext)
                hDnonneg
        _ < Δ / 8 := hscaled
    nlinarith
  let orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins :=
    { lowerParam := lowerParam
      upperParam := upperParam
      halfWidth := halfWidth
      normal := normal
      tube := tube
      leftHalf := leftHalf
      rightHalf := rightHalf
      lowerParam_pos := lowerParam_pos
      lowerParam_lt_left_parameter := by
        intro j hj
        simpa [leftParam] using lowerParam_lt_leftParam j hj
      right_parameter_lt_upperParam := by
        intro j hj
        simpa [rightParam] using rightParam_lt_upperParam j hj
      upperParam_lt_one := upperParam_lt_one
      halfWidth_pos := halfWidth_pos
      normal_orthogonal := normal_orthogonal
      normal_norm_eq_segment_length := normal_norm_eq_segment_length
      halfWidth_mul_normal_norm_lt_eta := halfWidth_mul_normal_norm_lt_eta
      halfWidth_mul_normal_norm_lt_margin_quarter :=
        halfWidth_mul_normal_norm_lt_margin_quarter
      lower_parameter_slack_mul_segment_length_lt_margin_quarter := by
        intro j hj
        dsimp [lowerParam, leftParam, segmentLength]
        simpa [sub_sub_cancel] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj
      upper_parameter_slack_mul_segment_length_lt_margin_quarter := by
        intro j hj
        dsimp [upperParam, rightParam, segmentLength]
        simpa [add_sub_cancel_left] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj
      tube_eq := by
        intro j hj
        rfl
      leftHalf_eq := by
        intro j hj
        rfl
      rightHalf_eq := by
        intro j hj
        rfl
      middle_subset_tube := middle_subset_tube
      leftHalf_subset_tube := leftHalf_subset_tube
      rightHalf_subset_tube := rightHalf_subset_tube
      tube_subset_eta_neighborhood := tube_subset_eta_neighborhood
      tube_point_close_to_middle := tube_point_close_to_middle
      tube_disjoint_nonadjacent_segments := tube_disjoint_nonadjacent_segments
      tube_disjoint_nonincident_control_disks :=
        tube_disjoint_nonincident_control_disks
      tube_disjoint_nonadjacent_middle_cores :=
        tube_disjoint_nonadjacent_middle_cores
      tube_disjoint_nonadjacent_tubes :=
        tube_disjoint_nonadjacent_tubes
      normal_eq_positive_quarter_turn := by
        intro j hj
        rfl }
  refine ⟨
    { orientedTubes := orientedTubes
      initialConeBound := initialConeBound
      terminalConeBound := terminalConeBound
      initialConeBound_pos := initialConeBound_pos
      terminalConeBound_pos := terminalConeBound_pos
      initial_halfWidth_lt_cone_mul_lowerParam := by
        intro j hj
        simpa [orientedTubes] using halfWidth_lt_initialCone_mul_lowerParam j hj
      terminal_halfWidth_lt_cone_mul_one_sub_upperParam := by
        intro j hj
        simpa [orientedTubes] using
          halfWidth_lt_terminalCone_mul_one_sub_upperParam j hj
      initial_signed_cone_disjoint_previous_segment := by
        intro j hj hprev
        simpa [orientedTubes] using
          initial_signed_cone_disjoint_previous_segment j hj hprev
      terminal_signed_cone_disjoint_next_segment := by
        intro j hj hnext
        simpa [orientedTubes] using
          terminal_signed_cone_disjoint_next_segment j hj hnext
      successive_positive_negative_cones_disjoint := by
        intro j hj hnext
        simpa [orientedTubes] using
          successive_positive_negative_cones_disjoint j hj hnext
      successive_negative_positive_cones_disjoint := by
        intro j hj hnext
        simpa [orientedTubes] using
          successive_negative_positive_cones_disjoint j hj hnext
      initialAwaySeparation := initialAwaySeparation
      terminalAwaySeparation := terminalAwaySeparation
      successiveAwaySeparation := successiveAwaySeparation
      initialAwaySeparation_pos := initialAwaySeparation_pos
      terminalAwaySeparation_pos := terminalAwaySeparation_pos
      successiveAwaySeparation_pos := successiveAwaySeparation_pos
      initial_centerline_previous_segment_away :=
        initial_centerline_previous_segment_away
      terminal_centerline_next_segment_away :=
        terminal_centerline_next_segment_away
      successive_centerlines_away := successive_centerlines_away
      initial_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hprev
        simpa [orientedTubes] using
          initial_halfWidth_mul_normal_norm_lt_away_quarter j hj hprev
      terminal_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          terminal_halfWidth_mul_normal_norm_lt_away_quarter j hj hnext
      successive_halfWidth_normal_sum_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          successive_halfWidth_normal_sum_lt_away_quarter j hj hnext }⟩
