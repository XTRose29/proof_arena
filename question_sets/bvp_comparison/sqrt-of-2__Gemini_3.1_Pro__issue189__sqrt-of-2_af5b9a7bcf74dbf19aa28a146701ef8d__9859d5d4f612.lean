/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: bvp_comparison
user: sqrt-of-2
model: Gemini 3.1 Pro
submission_repo: sqrt-of-2/af5b9a7bcf74dbf19aa28a146701ef8d
submission_ref: 9859d5d4f612b1d4ca3437effb805d92c25b47a8
issue_number: 189
-/
import Mathlib

open Set Filter
open scoped Topology

namespace Submission

theorem bvp_comparison (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  let w := u - v
  have hw : ∀ x ∈ J, HasDerivAt w (deriv u x - deriv v x) x := fun x hx =>
    (hu x hx).sub (hv x hx)
  have hw_diff : ∀ x ∈ J, DifferentiableAt ℝ w x := fun x hx =>
    (hw x hx).differentiableAt
  
  have hwc : ContinuousOn w (Set.Icc 0 1) :=
    continuousOn_of_forall_continuousAt fun x hx => (hw_diff x (hJ_sub hx)).continuousAt

  have hwd : DifferentiableOn ℝ w (interior (Set.Icc 0 1)) := by
    rw [interior_Icc]
    exact fun x hx => (hw_diff x (hJ_sub (Set.Ioo_subset_Icc_self hx))).differentiableWithinAt
    
  have hw' : ∀ x ∈ J, deriv w x = deriv u x - deriv v x := fun x hx =>
    (hw x hx).deriv
    
  have hw'' : ∀ x ∈ J, HasDerivAt (deriv w) (deriv (deriv u) x - deriv (deriv v) x) x := by
    intro x hx
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y => deriv u y - deriv v y)
    · exact (hu' x hx).sub (hv' x hx)
    · filter_upwards [hJ_open.mem_nhds hx] using hw'
    
  have hwd' : DifferentiableOn ℝ (deriv w) (interior (Set.Icc 0 1)) := by
    rw [interior_Icc]
    intro x hx
    exact (hw'' x (hJ_sub (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
    
  have hw''_nonneg : ∀ x ∈ interior (Set.Icc 0 1), 0 ≤ deriv (deriv w) x := by
    intro x hx
    rw [interior_Icc] at hx
    rw [(hw'' x (hJ_sub (Set.Ioo_subset_Icc_self hx))).deriv]
    specialize hineq x hx
    linarith

  have h_conv : ConvexOn ℝ (Set.Icc 0 1) w :=
    convexOn_of_deriv2_nonneg (convex_Icc 0 1) hwc hwd hwd' hw''_nonneg

  intro x hx
  have h_le := h_conv.le_on_segment (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) (by rwa [segment_eq_uIcc, uIcc_of_le zero_le_one])
  have wu0 : w 0 ≤ 0 := by simp [w]; linarith
  have wu1 : w 1 ≤ 0 := by simp [w]; linarith
  have : max (w 0) (w 1) ≤ 0 := max_le wu0 wu1
  exact le_of_sub_nonpos (h_le.trans this)

end Submission
