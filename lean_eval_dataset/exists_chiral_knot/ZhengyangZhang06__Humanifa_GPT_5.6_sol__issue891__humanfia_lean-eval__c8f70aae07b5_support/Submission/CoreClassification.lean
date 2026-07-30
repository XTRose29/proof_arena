import Submission.CoreMonodromy

open Complex
open scoped unitInterval

namespace Submission.CoreClassification

noncomputable section

theorem exists_zRoot_of_sq_eq_normSq {z : ℂ}
    (hz : z ^ 2 = (normSq z : ℂ)) :
    ∃ i : Fin 2, z = (Real.sqrt (normSq z) : ℂ) * CoreEdges.zRoot i := by
  have hre := congrArg Complex.re hz
  have him : z.im = 0 := by
    simp [pow_two, mul_re, normSq_apply] at hre
    nlinarith [sq_nonneg z.im]
  by_cases hnonneg : 0 ≤ z.re
  · refine ⟨0, ?_⟩
    apply Complex.ext
    · simp [CoreEdges.zRoot, normSq_apply, him]
      rw [show z.re * z.re = z.re ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
    · simp [CoreEdges.zRoot, him]
  · have hneg : z.re < 0 := lt_of_not_ge hnonneg
    refine ⟨1, ?_⟩
    apply Complex.ext
    · simp [CoreEdges.zRoot, normSq_apply, him]
      rw [show z.re * z.re = z.re ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_neg hneg]
      ring
    · simp [CoreEdges.zRoot, him]

theorem exists_wRoot_of_radialCube_eq_normSq {w : ℂ}
    (hwEq : RadialMilnor.radialCube w = (normSq w : ℂ)) :
    ∃ j : Fin 3, w = (Real.sqrt (normSq w) : ℂ) * CoreEdges.wRoot j := by
  by_cases hw : w = 0
  · refine ⟨0, ?_⟩
    simp [hw]
  · have hnormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hnormNe : (‖w‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hnormPos.ne'
    have hcube : w ^ 3 = (‖w‖ : ℂ) ^ 3 := by
      rw [RadialMilnor.radialCube_of_ne hw] at hwEq
      have hmul := (div_eq_iff hnormNe).mp hwEq
      calc
        w ^ 3 = (normSq w : ℂ) * (‖w‖ : ℂ) := hmul
        _ = (‖w‖ : ℂ) ^ 3 := by
          rw [normSq_eq_norm_sq]
          push_cast
          ring
    have hunit : (w / (‖w‖ : ℂ)) ^ 3 = 1 := by
      rw [div_pow, hcube, div_self (pow_ne_zero 3 hnormNe)]
    obtain ⟨j, hj⟩ := CoreEdges.exists_wRoot_of_cube_eq_one hunit
    refine ⟨j, ?_⟩
    rw [hj]
    have hsqrt : Real.sqrt (normSq w) = ‖w‖ := by
      rw [normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
    rw [hsqrt]
    field_simp

theorem core_zTerm_eq_normSq (q : RadialCore.Core) :
    RadialSpine.zTerm q.1.1.1.1.1 =
      ((16 * normSq q.1.1.1.1.1 : ℝ) : ℂ) := by
  apply Complex.ext
  · have h := RadialCore.spine_abs_zTerm_re q.1
    rw [abs_of_nonneg q.2.1] at h
    simpa using h
  · simpa using q.1.2.1

theorem core_wTerm_eq_normSq (q : RadialCore.Core) :
    RadialSpine.wTerm q.1.1.1.1.2 =
      ((9 * normSq q.1.1.1.1.2 : ℝ) : ℂ) := by
  apply Complex.ext
  · have h := RadialCore.spine_abs_wTerm_re q.1
    rw [abs_of_nonneg q.2.2] at h
    simpa using h
  · simpa using q.1.2.2

theorem core_zCoordinate_sq (q : RadialCore.Core) :
    RadialCore.zCoordinate q.1.1.1.1.1 ^ 2 =
      (normSq (RadialCore.zCoordinate q.1.1.1.1.1) : ℂ) := by
  have hmul :
      (16 : ℂ) * RadialCore.zCoordinate q.1.1.1.1.1 ^ 2 =
        (16 : ℂ) * (normSq q.1.1.1.1.1 : ℂ) := by
    calc
      (16 : ℂ) * RadialCore.zCoordinate q.1.1.1.1.1 ^ 2 =
          RadialSpine.zTerm q.1.1.1.1.1 :=
        (RadialCore.zTerm_eq_coordinate _).symm
      _ = ((16 * normSq q.1.1.1.1.1 : ℝ) : ℂ) :=
        core_zTerm_eq_normSq q
      _ = (16 : ℂ) * (normSq q.1.1.1.1.1 : ℂ) := by
        push_cast
        ring
  have heq : RadialCore.zCoordinate q.1.1.1.1.1 ^ 2 =
      (normSq q.1.1.1.1.1 : ℂ) := by
    exact mul_left_cancel₀ (by norm_num : (16 : ℂ) ≠ 0) hmul
  have hnorm : normSq (RadialCore.zCoordinate q.1.1.1.1.1) =
      normSq q.1.1.1.1.1 := by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq, RadialCore.norm_zCoordinate]
  rwa [hnorm]

theorem core_wCoordinate_radialCube (q : RadialCore.Core) :
    RadialMilnor.radialCube (RadialCore.wCoordinate q.1.1.1.1.2) =
      (normSq (RadialCore.wCoordinate q.1.1.1.1.2) : ℂ) := by
  have hmul :
      (9 : ℂ) * RadialMilnor.radialCube
          (RadialCore.wCoordinate q.1.1.1.1.2) =
        (9 : ℂ) * (normSq q.1.1.1.1.2 : ℂ) := by
    calc
      (9 : ℂ) * RadialMilnor.radialCube
            (RadialCore.wCoordinate q.1.1.1.1.2) =
          RadialSpine.wTerm q.1.1.1.1.2 :=
        (RadialCore.wTerm_eq_coordinate _).symm
      _ = ((9 * normSq q.1.1.1.1.2 : ℝ) : ℂ) :=
        core_wTerm_eq_normSq q
      _ = (9 : ℂ) * (normSq q.1.1.1.1.2 : ℂ) := by
        push_cast
        ring
  have heq : RadialMilnor.radialCube
      (RadialCore.wCoordinate q.1.1.1.1.2) =
      (normSq q.1.1.1.1.2 : ℂ) := by
    exact mul_left_cancel₀ (by norm_num : (9 : ℂ) ≠ 0) hmul
  have hnorm : normSq (RadialCore.wCoordinate q.1.1.1.1.2) =
      normSq q.1.1.1.1.2 := by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq, RadialCore.norm_wCoordinate]
  rwa [hnorm]

theorem exists_edge (q : RadialCore.Core) :
    ∃ i : Fin 2, ∃ j : Fin 3, ∃ u : unitInterval,
      q = CoreEdges.edge i j u := by
  let u : unitInterval := ⟨normSq q.1.1.1.1.2,
    normSq_nonneg _, by
      have hsphere := q.1.1.1.2
      nlinarith [normSq_nonneg q.1.1.1.1.1]⟩
  obtain ⟨i, hi⟩ := exists_zRoot_of_sq_eq_normSq (core_zCoordinate_sq q)
  obtain ⟨j, hj⟩ :=
    exists_wRoot_of_radialCube_eq_normSq (core_wCoordinate_radialCube q)
  have hzNorm : normSq (RadialCore.zCoordinate q.1.1.1.1.1) =
      1 - (u : ℝ) := by
    rw [normSq_eq_norm_sq, RadialCore.norm_zCoordinate,
      ← normSq_eq_norm_sq]
    dsimp [u]
    linarith [q.1.1.1.2]
  have hwNorm : normSq (RadialCore.wCoordinate q.1.1.1.1.2) =
      (u : ℝ) := by
    rw [normSq_eq_norm_sq, RadialCore.norm_wCoordinate,
      ← normSq_eq_norm_sq]
  have hzCoordinate : RadialCore.zCoordinate q.1.1.1.1.1 =
      CoreEdges.edgeZCoordinate i u := by
    calc
      RadialCore.zCoordinate q.1.1.1.1.1 =
          (Real.sqrt (normSq (RadialCore.zCoordinate q.1.1.1.1.1)) : ℂ) *
            CoreEdges.zRoot i := hi
      _ = (Real.sqrt (1 - (u : ℝ)) : ℂ) * CoreEdges.zRoot i := by rw [hzNorm]
      _ = CoreEdges.edgeZCoordinate i u := rfl
  have hwCoordinate : RadialCore.wCoordinate q.1.1.1.1.2 =
      CoreEdges.edgeWCoordinate j u := by
    calc
      RadialCore.wCoordinate q.1.1.1.1.2 =
          (Real.sqrt (normSq (RadialCore.wCoordinate q.1.1.1.1.2)) : ℂ) *
            CoreEdges.wRoot j := hj
      _ = (Real.sqrt (u : ℝ) : ℂ) * CoreEdges.wRoot j := by rw [hwNorm]
      _ = CoreEdges.edgeWCoordinate j u := rfl
  refine ⟨i, j, u, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · calc
      q.1.1.1.1.1 =
          CoreEdges.fromZCoordinate (RadialCore.zCoordinate q.1.1.1.1.1) :=
        (CoreEdges.fromZCoordinate_zCoordinate _).symm
      _ = CoreEdges.fromZCoordinate (CoreEdges.edgeZCoordinate i u) := by
        rw [hzCoordinate]
      _ = CoreEdges.edgeZ i u := rfl
  · calc
      q.1.1.1.1.2 =
          CoreEdges.fromWCoordinate (RadialCore.wCoordinate q.1.1.1.1.2) :=
        (CoreEdges.fromWCoordinate_wCoordinate _).symm
      _ = CoreEdges.fromWCoordinate (CoreEdges.edgeWCoordinate j u) := by
        rw [hwCoordinate]
      _ = CoreEdges.edgeW j u := rfl

end

end Submission.CoreClassification
