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
  -- Apply the concavity result to conclude the proof.
  have h_concave : ConcaveOn ℝ (Set.Icc 0 1) (fun x => v x - u x) := by
    apply_rules [ concaveOn_of_deriv2_nonpos ];
    · exact convex_Icc _ _;
    · exact ContinuousOn.sub ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hv x ( hJ_sub hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hu x ( hJ_sub hx ) ) );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( hv x ( hJ_sub <| interior_subset hx ) |> HasDerivAt.differentiableAt ) ( hu x ( hJ_sub <| interior_subset hx ) |> HasDerivAt.differentiableAt ) );
    · norm_num +zetaDelta at *;
      exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.congr_of_eventuallyEq ( show DifferentiableAt ℝ ( fun x => deriv v x - deriv u x ) x from DifferentiableAt.sub ( hv' x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) ) ( hu' x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) ) ) <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx.1 hx.2 ) fun y hy => by rw [ show deriv ( fun x => v x - u x ) y = deriv v y - deriv u y from deriv_sub ( hv y ( hJ_sub <| Set.Ioo_subset_Icc_self hy ) ) ( hu y ( hJ_sub <| Set.Ioo_subset_Icc_self hy ) ) ] );
    · simp +zetaDelta at *;
      intro x hx₁ hx₂; rw [ show deriv ( deriv fun x => v x - u x ) x = deriv ( fun x => deriv v x - deriv u x ) x from Filter.EventuallyEq.deriv_eq <| by filter_upwards [ Ioo_mem_nhds hx₁ hx₂ ] with y hy using deriv_sub ( hv y <| hJ_sub <| Set.Ioo_subset_Icc_self hy ) ( hu y <| hJ_sub <| Set.Ioo_subset_Icc_self hy ) ] ;
      norm_num [ hv' x ( hJ_sub ⟨ hx₁.le, hx₂.le ⟩ ), hu' x ( hJ_sub ⟨ hx₁.le, hx₂.le ⟩ ) ] ; linarith [ hineq x hx₁ hx₂ ];
  intro x hx; have := h_concave.2 ( show 0 ∈ Set.Icc 0 1 by norm_num ) ( show 1 ∈ Set.Icc 0 1 by norm_num ) ; simp_all +decide [ ConcaveOn ] ;
  have := @this ( 1 - x ) x ( by linarith ) ( by linarith ) ( by linarith ) ; norm_num at this ; nlinarith;

end Submission
