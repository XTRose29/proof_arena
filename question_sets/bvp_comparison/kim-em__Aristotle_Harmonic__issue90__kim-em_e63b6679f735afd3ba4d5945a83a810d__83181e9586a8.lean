/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: bvp_comparison
user: kim-em
model: Aristotle (Harmonic)
submission_repo: kim-em/e63b6679f735afd3ba4d5945a83a810d
submission_ref: 83181e9586a8fe41e7fa7168047271add60789bb
issue_number: 90
-/
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
  -- Define $w(x) = u(x) - v(x)$.
  set w : ℝ → ℝ := fun x => u x - v x;
  -- By definition of $w$, we know that $w''(x) \geq 0$ for all $x \in (0,1)$.
  have hw''_nonneg : ∀ x ∈ Set.Ioo 0 1, deriv^[2] w x ≥ 0 := by
    simp +zetaDelta at *;
    intro x hx₁ hx₂; rw [ show deriv ( deriv fun x => u x - v x ) x = deriv ( fun x => deriv u x - deriv v x ) x from Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx₁ hx₂ ) fun y hy => deriv_sub ( hu y <| hJ_sub <| Set.Ioo_subset_Icc_self hy ) ( hv y <| hJ_sub <| Set.Ioo_subset_Icc_self hy ) ] ;
    norm_num [ hu' x ( hJ_sub <| Set.mem_Icc.mpr ⟨ hx₁.le, hx₂.le ⟩ ), hv' x ( hJ_sub <| Set.mem_Icc.mpr ⟨ hx₁.le, hx₂.le ⟩ ) ] ; linarith [ hineq x hx₁ hx₂ ];
  -- Since $w''(x) \geq 0$ for all $x \in (0,1)$, $w$ is convex on $[0,1]$.
  have hw_convex : ConvexOn ℝ (Set.Icc 0 1) w := by
    apply_rules [ convexOn_of_deriv2_nonneg, convex_Icc ];
    · exact ContinuousOn.sub ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hu x ( hJ_sub hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hv x ( hJ_sub hx ) ) );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( hu x ( hJ_sub <| interior_subset hx ) |> HasDerivAt.differentiableAt ) ( hv x ( hJ_sub <| interior_subset hx ) |> HasDerivAt.differentiableAt ) );
    · norm_num +zetaDelta at *;
      refine' DifferentiableOn.congr _ _;
      exacts [ fun x => deriv u x - deriv v x, fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( hu' x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) ) ( hv' x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) ) ), fun x hx => deriv_sub ( hu x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) ) ( hv x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) ) ];
    · aesop;
  intro x hx;
  have := hw_convex.2 ( show 0 ∈ Set.Icc 0 1 by norm_num ) ( show 1 ∈ Set.Icc 0 1 by norm_num );
  simp +zetaDelta at *;
  nlinarith [ this ( show 0 ≤ 1 - x by linarith ) ( show 0 ≤ x by linarith ) ( by linarith ) ]

end Submission