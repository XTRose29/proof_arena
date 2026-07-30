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
  have hcont : ContinuousOn (fun x => u x - v x) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have hxJ : x ∈ interior J := by
      rw [hJ_open.interior_eq]
      exact hJ_sub hx
    exact ((hu x (interior_subset hxJ)).continuousAt.sub
      (hv x (interior_subset hxJ)).continuousAt).continuousWithinAt
  have hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => u x - v x) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => deriv u x - deriv v x)
      (f'' := fun x => deriv (deriv u) x - deriv (deriv v) x)
      (convex_Icc 0 1) hcont ?_ ?_ ?_
    · intro x hx
      exact ((hu x (hJ_sub (interior_subset hx))).sub
        (hv x (hJ_sub (interior_subset hx)))).hasDerivWithinAt
    · intro x hx
      exact ((hu' x (hJ_sub (interior_subset hx))).sub
        (hv' x (hJ_sub (interior_subset hx)))).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      linarith [hineq x hx]
  intro x hx
  have hle := hconvex.le_max_of_mem_Icc
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) hx
  have hend : max (u 0 - v 0) (u 1 - v 1) ≤ 0 :=
    max_le (sub_nonpos.mpr hu0) (sub_nonpos.mpr hu1)
  linarith

end Submission
