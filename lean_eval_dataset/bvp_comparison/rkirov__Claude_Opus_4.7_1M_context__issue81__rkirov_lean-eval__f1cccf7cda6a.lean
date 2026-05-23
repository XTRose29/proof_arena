import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Add
import Submission.Helpers

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
  let _ := hJ_open
  set w : ℝ → ℝ := fun x => u x - v x with hw_def
  set D : Set ℝ := Set.Icc (0 : ℝ) 1 with hD_def
  have hD_conv : Convex ℝ D := convex_Icc _ _
  have hint_eq : interior D = Set.Ioo (0 : ℝ) 1 := interior_Icc
  -- Continuity of w on D.
  have hw_cont : ContinuousOn w D := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub hx
    exact ((hu x hxJ).continuousAt.sub (hv x hxJ).continuousAt).continuousWithinAt
  -- w is convex on D, via convexOn_of_hasDerivWithinAt2_nonneg.
  have hw_conv : ConvexOn ℝ D w := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun x => deriv u x - deriv v x)
      (f'' := fun x => deriv (deriv u) x - deriv (deriv v) x)
      hD_conv hw_cont ?_ ?_ ?_
    · intro x hx
      rw [hint_eq] at hx
      have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
      exact ((hu x hxJ).sub (hv x hxJ)).hasDerivWithinAt
    · intro x hx
      rw [hint_eq] at hx
      have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
      exact ((hu' x hxJ).sub (hv' x hxJ)).hasDerivWithinAt
    · intro x hx
      rw [hint_eq] at hx
      linarith [hineq x hx]
  -- Use convex_le: {x ∈ D | w x ≤ 0} is convex; 0 and 1 are in it; hence all of D is.
  have hS_conv : Convex ℝ {x ∈ D | w x ≤ 0} := hw_conv.convex_le 0
  have h0 : (0 : ℝ) ∈ {x ∈ D | w x ≤ 0} :=
    ⟨by simp [hD_def, Set.mem_Icc], by simp [hw_def]; linarith⟩
  have h1 : (1 : ℝ) ∈ {x ∈ D | w x ≤ 0} :=
    ⟨by simp [hD_def, Set.mem_Icc], by simp [hw_def]; linarith⟩
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hcombo := hS_conv h0 h1 (by linarith : (0:ℝ) ≤ 1 - x) hx0 (by linarith : (1 - x) + x = 1)
  have heq : (1 - x) • (0 : ℝ) + x • (1 : ℝ) = x := by simp
  rw [heq] at hcombo
  have : w x ≤ 0 := hcombo.2
  simp only [hw_def] at this
  linarith

end Submission
