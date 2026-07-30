import Submission.TwoSidedGeneratorEntropy

namespace Submission.Helpers

open LeanEval.Dynamics

lemma exists_fderiv_lipschitz_constant_on_compact_convex
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {S : Set EucPlane} (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ B * dist x y := by
  let F : EucPlane → (EucPlane →L[ℝ] EucPlane) := fderiv ℝ T
  have hF_smooth : ContDiff ℝ 1 F := by
    exact hT_smooth.fderiv_right (by norm_num)
  have hFderiv_cont : Continuous fun x => ‖fderiv ℝ F x‖ :=
    (hF_smooth.continuous_fderiv (by norm_num)).norm
  obtain ⟨C, hC⟩ := hS_compact.bddAbove_image hFderiv_cont.continuousOn
  let B := max C 1
  have hB_one : 1 ≤ B := le_max_right _ _
  have hBderiv : ∀ z ∈ S, ‖fderiv ℝ F z‖ ≤ B := by
    intro z hz
    exact (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hF_diff : Differentiable ℝ F := hF_smooth.differentiable (by norm_num)
  refine ⟨B, hB_one, ?_⟩
  intro x hx y hy
  have hbound := hS_convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz => hF_diff.differentiableAt) hBderiv hx hy
  simpa [F, dist_eq_norm, norm_sub_rev] using hbound

lemma exists_fderiv_lipschitz_constant_on_compact
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {K : Set EucPlane} (hK_compact : IsCompact K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ B * dist x y := by
  obtain ⟨R, hKR⟩ := hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  have hball_compact : IsCompact (Metric.closedBall (0 : EucPlane) R) :=
    isCompact_closedBall (0 : EucPlane) R
  obtain ⟨B, hB_one, hB⟩ := exists_fderiv_lipschitz_constant_on_compact_convex
    T hT_smooth hball_compact (convex_closedBall (0 : EucPlane) R)
  refine ⟨B, hB_one, ?_⟩
  intro x hx y hy
  exact hB x (hKR hx) y (hKR hy)

lemma norm_image_sub_linearization_le
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {S : Set EucPlane} (hS_convex : Convex ℝ S)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ B * dist x y)
    {x y : EucPlane} (hx : x ∈ S) (hy : y ∈ S) :
    ‖T y - T x - fderiv ℝ T x (y - x)‖ ≤ B * ‖y - x‖ ^ 2 := by
  let L := fderiv ℝ T x
  let g : EucPlane → EucPlane := fun z => T z - L z
  have hT_diff : Differentiable ℝ T := hT_smooth.differentiable (by norm_num)
  have hg_diff : Differentiable ℝ g := hT_diff.sub L.differentiable
  have hg_fderiv (z : EucPlane) :
      fderiv ℝ g z = fderiv ℝ T z - L := by
    change fderiv ℝ (T - (L : EucPlane → EucPlane)) z = fderiv ℝ T z - L
    simpa using fderiv_sub hT_diff.differentiableAt L.differentiableAt
  have hsegment : segment ℝ x y ⊆ S := hS_convex.segment_subset hx hy
  have hderiv_bound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ g z‖ ≤ B * ‖y - x‖ := by
    intro z hz
    rw [hg_fderiv]
    calc
      ‖fderiv ℝ T z - L‖ ≤ B * dist z x :=
        hB z (hsegment hz) x hx
      _ ≤ B * ‖y - x‖ := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hB_nonneg
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz => hg_diff.differentiableAt) hderiv_bound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  change ‖g y - g x‖ ≤ (B * ‖y - x‖) * ‖y - x‖ at hmean
  calc
    ‖T y - T x - fderiv ℝ T x (y - x)‖ = ‖g y - g x‖ := by
      simp only [g, L, map_sub]
      congr 1
      abel
    _ ≤ (B * ‖y - x‖) * ‖y - x‖ := hmean
    _ = B * ‖y - x‖ ^ 2 := by ring

end Submission.Helpers
