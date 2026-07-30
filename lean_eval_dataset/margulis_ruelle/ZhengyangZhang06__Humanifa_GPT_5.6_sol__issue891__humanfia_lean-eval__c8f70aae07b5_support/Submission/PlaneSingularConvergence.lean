import Submission.PlaneSingularProjection
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.CompleteCodomain

namespace Submission.Helpers

open LeanEval.Dynamics Filter Topology

lemma norm_planeMinProjection_sub_comp_le
    (A C C_inv : EucPlane →L[ℝ] EucPlane)
    (hA_det : A.toLinearMap.det ≠ 0)
    (hC_left : C_inv ∘L C = ContinuousLinearMap.id ℝ EucPlane) :
    ‖planeMinProjection A - planeMinProjection (C ∘L A)‖ ≤
      2 * Real.sqrt 2 *
        (‖A (planeSingularBasis A 1)‖ * ‖C_inv‖ *
            ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ /
          |A.toLinearMap.det|) := by
  calc
    ‖planeMinProjection A - planeMinProjection (C ∘L A)‖ ≤
        2 * Real.sqrt 2 *
          |planeCross (planeSingularBasis A 1)
            (planeSingularBasis (C ∘L A) 1)| :=
      norm_planeMinProjection_sub_le_cross A (C ∘L A)
    _ ≤ 2 * Real.sqrt 2 *
        (‖A (planeSingularBasis A 1)‖ * ‖C_inv‖ *
            ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ /
          |A.toLinearMap.det|) := by
      gcongr
      exact abs_planeCross_minSingular_le A C C_inv hA_det hC_left

lemma norm_planeMinProjection_sub_comp_le_div_norm
    (A C C_inv : EucPlane →L[ℝ] EucPlane)
    (hA_det : A.toLinearMap.det ≠ 0)
    (hC_left : C_inv ∘L C = ContinuousLinearMap.id ℝ EucPlane) :
    ‖planeMinProjection A - planeMinProjection (C ∘L A)‖ ≤
      2 * Real.sqrt 2 *
        (‖C_inv‖ *
            ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ / ‖A‖) := by
  have hproduct_pos :
      0 < ‖A (planeSingularBasis A 1)‖ * ‖A‖ := by
    rw [norm_minSingular_mul_norm]
    exact abs_pos.mpr hA_det
  have hmin_pos : 0 < ‖A (planeSingularBasis A 1)‖ := by
    nlinarith [norm_nonneg A]
  have hnorm_pos : 0 < ‖A‖ := by
    nlinarith [norm_nonneg (A (planeSingularBasis A 1))]
  calc
    ‖planeMinProjection A - planeMinProjection (C ∘L A)‖ ≤
        2 * Real.sqrt 2 *
          (‖A (planeSingularBasis A 1)‖ * ‖C_inv‖ *
              ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ /
            |A.toLinearMap.det|) :=
      norm_planeMinProjection_sub_comp_le A C C_inv hA_det hC_left
    _ = 2 * Real.sqrt 2 *
        (‖C_inv‖ *
            ‖(C ∘L A) (planeSingularBasis (C ∘L A) 1)‖ / ‖A‖) := by
      rw [← norm_minSingular_mul_norm A]
      field_simp [hmin_pos.ne', hnorm_pos.ne']

lemma norm_minSingular_eq_one_div_norm_inverse
    (A A_inv : EucPlane →L[ℝ] EucPlane)
    (hA_det : A.toLinearMap.det ≠ 0)
    (hleft : A_inv ∘L A = ContinuousLinearMap.id ℝ EucPlane) :
    ‖A (planeSingularBasis A 1)‖ = 1 / ‖A_inv‖ := by
  have hdet_pos : 0 < |A.toLinearMap.det| := abs_pos.mpr hA_det
  have hA_inv_norm_pos : 0 < ‖A_inv‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    have hcoord := congrArg (fun y : EucPlane => y.ofLp 0)
      (congrArg (fun L : EucPlane →L[ℝ] EucPlane =>
        L (EuclideanSpace.single 0 1)) hleft)
    simp [hzero] at hcoord
  apply (eq_div_iff hA_inv_norm_pos.ne').2
  have hmin := norm_minSingular_mul_norm A
  rw [norm_eq_abs_det_mul_norm_inverse A A_inv hleft] at hmin
  apply mul_left_cancel₀ hdet_pos.ne'
  calc
    |A.toLinearMap.det| *
        (‖A (planeSingularBasis A 1)‖ * ‖A_inv‖) =
        ‖A (planeSingularBasis A 1)‖ *
          (|A.toLinearMap.det| * ‖A_inv‖) := by ring
    _ = |A.toLinearMap.det| := hmin
    _ = |A.toLinearMap.det| * 1 := by ring

set_option synthInstance.maxHeartbeats 100000 in
lemma exists_limit_of_projection_geometric_step
    (P : ℕ → EucPlane →L[ℝ] EucPlane)
    {C gamma : ℝ} (hgamma : 0 < gamma)
    (hstep : ∀ n,
      ‖P n - P (n + 1)‖ ≤ C * Real.exp (-gamma * n)) :
    ∃ Q : EucPlane →L[ℝ] EucPlane,
      Tendsto P atTop (nhds Q) ∧
        ∀ n, ‖P n - Q‖ ≤
          C * Real.exp (-gamma) ^ n / (1 - Real.exp (-gamma)) := by
  let r := Real.exp (-gamma)
  have hr_nonneg : 0 ≤ r := Real.exp_nonneg _
  have hr_lt : r < 1 := by
    dsimp [r]
    exact (Real.exp_lt_one_iff).2 (neg_neg_of_pos hgamma)
  have hstep' : ∀ n, dist (P n) (P (n + 1)) ≤ C * r ^ n := by
    intro n
    rw [dist_eq_norm]
    calc
      ‖P n - P (n + 1)‖ ≤ C * Real.exp (-gamma * n) := hstep n
      _ = C * r ^ n := by
        congr 1
        dsimp [r]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hcauchy : CauchySeq P :=
    cauchySeq_of_le_geometric r C hr_lt hstep'
  obtain ⟨Q, hQ⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨Q, hQ, ?_⟩
  intro n
  rw [← dist_eq_norm]
  exact dist_le_of_le_geometric_of_tendsto r C hr_lt hstep' hQ n

set_option synthInstance.maxHeartbeats 100000 in
lemma exists_limit_of_projection_eventually_geometric_step
    (P : ℕ → EucPlane →L[ℝ] EucPlane)
    {C gamma : ℝ} (hgamma : 0 < gamma)
    (hstep : ∀ᶠ n : ℕ in atTop,
      ‖P n - P (n + 1)‖ ≤ C * Real.exp (-gamma * n)) :
    ∃ Q : EucPlane →L[ℝ] EucPlane, ∃ n0 : ℕ,
      Tendsto P atTop (nhds Q) ∧
        ∀ k, ‖P (k + n0) - Q‖ ≤
          (C * Real.exp (-gamma * n0)) * Real.exp (-gamma) ^ k /
            (1 - Real.exp (-gamma)) := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hstep
  let P' : ℕ → EucPlane →L[ℝ] EucPlane := fun k => P (n0 + k)
  have hstep' : ∀ k,
      ‖P' k - P' (k + 1)‖ ≤
        (C * Real.exp (-gamma * n0)) * Real.exp (-gamma * k) := by
    intro k
    dsimp [P']
    have hk := hn0 (n0 + k) (Nat.le_add_right n0 k)
    calc
      ‖P (n0 + k) - P (n0 + (k + 1))‖ ≤
          C * Real.exp (-gamma * (n0 + k)) := by
        simpa [Nat.add_assoc] using hk
      _ = (C * Real.exp (-gamma * n0)) * Real.exp (-gamma * k) := by
        rw [show -gamma * ((n0 : ℝ) + (k : ℝ)) =
            -gamma * (n0 : ℝ) + -gamma * (k : ℝ) by ring]
        rw [Real.exp_add]
        ring
  obtain ⟨Q, hQ, hQbound⟩ :=
    exists_limit_of_projection_geometric_step P' hgamma hstep'
  refine ⟨Q, n0, (tendsto_add_atTop_iff_nat n0).mp ?_, ?_⟩
  · simpa [P', Nat.add_comm] using hQ
  · intro k
    simpa [P', Nat.add_comm] using hQbound k

end Submission.Helpers
