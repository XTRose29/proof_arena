import Mathlib

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
  let w := fun x => u x - v x
  have hw_deriv : ∀ x ∈ J, HasDerivAt w (deriv u x - deriv v x) x := fun x hx =>
    (hu x hx).sub (hv x hx)
  have hw_deriv' : ∀ x ∈ J, HasDerivAt (deriv w) (deriv (deriv u) x - deriv (deriv v) x) x := by
    intro x hx
    have : ∀ y ∈ J, deriv w y = deriv u y - deriv v y := fun y hy => (hw_deriv y hy).deriv
    apply HasDerivAt.congr_of_eventuallyEq ((hu' x hx).sub (hv' x hx))
    filter_upwards [hJ_open.mem_nhds hx]
    intro y hy
    exact (hw_deriv y hy).deriv
  
  have h_convex : ConvexOn ℝ (Set.Icc 0 1) w :=
    convexOn_of_deriv2_nonneg (convex_Icc 0 1)
      (DifferentiableOn.continuousOn fun x hx => (hw_deriv x (hJ_sub hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (hw_deriv x (hJ_sub (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (hw_deriv' x (hJ_sub (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        have hxJ := hJ_sub (Set.Ioo_subset_Icc_self hx)
        have : deriv (deriv w) x = deriv (deriv u) x - deriv (deriv v) x := (hw_deriv' x hxJ).deriv
        change 0 ≤ deriv (deriv w) x
        rw [this]
        exact sub_nonneg.2 (neg_le_neg_iff.1 (hineq x hx)))

  intro x hx
  have h_le := h_convex.2 (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    (sub_nonneg.2 hx.2) hx.1 (by ring)
  have h_smul0 : (1 - x) • (0 : ℝ) + x • (1 : ℝ) = x := by simp [smul_eq_mul]
  rw [h_smul0] at h_le
  have hw0 : w 0 ≤ 0 := sub_nonpos.2 hu0
  have hw1 : w 1 ≤ 0 := sub_nonpos.2 hu1
  have : (1 - x) • w 0 + x • w 1 ≤ 0 := by
    simp [smul_eq_mul]
    nlinarith [hx.1, hx.2, hw0, hw1]
  exact sub_nonpos.1 (h_le.trans this)

end Submission
