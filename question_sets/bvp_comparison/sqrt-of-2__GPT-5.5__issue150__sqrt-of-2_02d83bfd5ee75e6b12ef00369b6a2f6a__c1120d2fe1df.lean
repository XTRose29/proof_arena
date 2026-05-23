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
  intro x hx
  let w : ℝ → ℝ := fun x => u x - v x
  have hIoo_sub_J : Set.Ioo (0 : ℝ) 1 ⊆ J := fun y hy =>
    hJ_sub ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hw_cont : ContinuousOn w (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    exact ((hu y (hJ_sub hy)).sub (hv y (hJ_sub hy))).continuousAt.continuousWithinAt
  have hw' :
      ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
        HasDerivWithinAt w (deriv u y - deriv v y) (interior (Set.Icc (0 : ℝ) 1)) y := by
    intro y hy
    rw [interior_Icc] at hy
    exact ((hu y (hIoo_sub_J hy)).sub (hv y (hIoo_sub_J hy))).hasDerivWithinAt
  have hw'' :
      ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
        HasDerivWithinAt (fun y => deriv u y - deriv v y)
          (deriv (deriv u) y - deriv (deriv v) y) (interior (Set.Icc (0 : ℝ) 1)) y := by
    intro y hy
    rw [interior_Icc] at hy
    exact ((hu' y (hIoo_sub_J hy)).sub (hv' y (hIoo_sub_J hy))).hasDerivWithinAt
  have hw_nonneg :
      ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
        0 ≤ deriv (deriv u) y - deriv (deriv v) y := by
    intro y hy
    rw [interior_Icc] at hy
    linarith [hineq y hy]
  have hw_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1) hw_cont hw' hw'' hw_nonneg
  have hx_bound : w x ≤ max (w 0) (w 1) :=
    hw_convex.le_max_of_mem_Icc (by norm_num) (by norm_num) hx
  have hend : max (w 0) (w 1) ≤ 0 := by
    rw [max_le_iff]
    exact ⟨sub_nonpos.mpr hu0, sub_nonpos.mpr hu1⟩
  have : u x - v x ≤ 0 := le_trans hx_bound hend
  exact sub_nonpos.mp this

end Submission
