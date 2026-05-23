import Mathlib

open Filter Topology Set

namespace Submission

/-
y is continuous on [0, ∞) from the hypotheses
-/
private lemma y_continuousOn (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) :
    ContinuousOn y (Ici 0) := by
      intro t ht;
      cases eq_or_lt_of_le ht.out <;> [ aesop; exact ContinuousAt.continuousWithinAt ( hy_diff t ‹_› |> HasDerivAt.continuousAt ) ]

/-
The derivative of g(t) = y(t)^2 * (1 + 2*t) - 1
-/
private lemma hasDerivAt_g (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => y s ^ 2 * (1 + 2 * s) - 1)
      (-2 * y t ^ 2 * (y t ^ 2 * (1 + 2 * t) - 1)) t := by
        -- Apply the product rule to find the derivative of $g(t)$.
        have hg_deriv : HasDerivAt (fun s => (y s) ^ 2 * (1 + 2 * s)) (-2 * (y t) ^ 4 * (1 + 2 * t) + 2 * (y t) ^ 2) t := by
          convert HasDerivAt.mul ( HasDerivAt.comp t ( hasDerivAt_pow 2 _ ) ( hy_diff t ht ) ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id t ) ) ) using 1 ; ring!;
          norm_num ; ring!;
        convert hg_deriv.sub_const 1 using 1 ; ring

/-
The derivative of g(t)^2
-/
private lemma hasDerivAt_g_sq (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => (y s ^ 2 * (1 + 2 * s) - 1) ^ 2)
      (2 * (y t ^ 2 * (1 + 2 * t) - 1) * (-2 * y t ^ 2 * (y t ^ 2 * (1 + 2 * t) - 1))) t := by
        -- Apply the HasDerivAt.pow 2 rule to the function (y s)^2 * (1 + 2 * s) - 1.
        have h_pow : HasDerivAt (fun s => (y s)^2 * (1 + 2 * s) - 1) (-2 * y t^2 * ((y t)^2 * (1 + 2 * t) - 1)) t := by
          exact?;
        convert h_pow.pow 2 using 1 ; ring

/-
The derivative of g(t)^2 is ≤ 0
-/
private lemma deriv_g_sq_nonpos (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (t : ℝ) (ht : 0 < t) :
    2 * (y t ^ 2 * (1 + 2 * t) - 1) * (-2 * y t ^ 2 * (y t ^ 2 * (1 + 2 * t) - 1)) ≤ 0 := by
      nlinarith [ sq_nonneg ( y t ^ 2 * ( 1 + 2 * t ) - 1 ), sq_nonneg ( y t ^ 2 ) ]

/-
g(t)^2 is non-increasing on [0, ∞), hence g(t) = 0
-/
private lemma y_sq_identity (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) :
    ∀ t : ℝ, 0 ≤ t → y t ^ 2 * (1 + 2 * t) = 1 := by
      -- Define G(t) = (y(t)^2 * (1+2t) - 1)^2. G is continuous on [0,∞) (from y_continuousOn) and differentiable on (0,∞) (from hasDerivAt_g_sq).
      set G : ℝ → ℝ := fun t => (y t ^ 2 * (1 + 2 * t) - 1) ^ 2;
      -- G is non-increasing on [0, ∞) by antitoneOn_of_deriv_nonpos.
      have G_noninc : AntitoneOn G (Set.Ici 0) := by
        -- Apply the fact that if the derivative of a function is non-positive, then the function is non-increasing.
        have hG_deriv_nonpos : ∀ t : ℝ, 0 < t → deriv G t ≤ 0 := by
          intro t ht; rw [ show deriv G t = _ from HasDerivAt.deriv ( hasDerivAt_g_sq y hy_diff t ht ) ] ; nlinarith [ deriv_g_sq_nonpos y hy_diff t ht ] ;
        apply_rules [ antitoneOn_of_deriv_nonpos ];
        · exact convex_Ici _;
        · exact ContinuousOn.pow ( ContinuousOn.sub ( ContinuousOn.mul ( ContinuousOn.pow ( y_continuousOn y hy_diff hy_cont ) 2 ) ( continuousOn_const.add ( continuousOn_const.mul continuousOn_id ) ) ) continuousOn_const ) 2;
        · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.pow ( by exact DifferentiableAt.sub ( DifferentiableAt.mul ( DifferentiableAt.pow ( hy_diff t ( by aesop ) |> HasDerivAt.differentiableAt ) _ ) ( by norm_num [ mul_comm ] ) ) ( by norm_num ) ) _ );
        · aesop;
      have h_g_zero : ∀ t, 0 ≤ t → G t ≤ 0 := by
        exact fun t ht => le_trans ( G_noninc ( by norm_num ) ht ht ) ( by aesop );
      exact fun t ht => eq_of_sub_eq_zero ( sq_eq_zero_iff.mp ( le_antisymm ( h_g_zero t ht ) ( sq_nonneg _ ) ) )

/-
y(t) > 0 for all t ≥ 0 (follows from the identity and continuity)
-/
private lemma y_pos (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) (t : ℝ) (ht : 0 ≤ t) :
    0 < y t := by
      -- Since y is continuous on [0,∞) and y(0) = 1 > 0, by the intermediate value theorem, y(t) must be positive for all t ≥ 0.
      have h_ivt : ∀ t : ℝ, 0 ≤ t → y t ≠ 0 := by
        -- Apply the lemma y_sq_identity to conclude that y(t)^2 * (1 + 2 * t) = 1 for all t ≥ 0.
        have := y_sq_identity y hy_diff hy_cont hy0
        simp_all +decide;
        exact fun t ht h => by simpa [ h ] using this t ht;
      contrapose! h_ivt;
      have h_ivt : IsConnected (y '' Set.Ici 0) := by
        apply_rules [ IsConnected.image, isConnected_Ici ];
        exact?;
      exact h_ivt.Icc_subset ( Set.mem_image_of_mem _ ht ) ( Set.mem_image_of_mem _ ( show 0 ∈ Set.Ici 0 by norm_num ) ) ⟨ by linarith, by linarith ⟩

/-
The limit computation
-/
private lemma limit_from_identity (y : ℝ → ℝ)
    (h_id : ∀ t : ℝ, 0 ≤ t → y t ^ 2 * (1 + 2 * t) = 1)
    (h_pos : ∀ t : ℝ, 0 ≤ t → 0 < y t) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
      -- Rewrite y(t) * sqrt(t) as sqrt(t/(1+2t)).
      have h_sqrt : ∀ t ≥ 0, y t * Real.sqrt t = Real.sqrt (t / (1 + 2 * t)) := by
        intro t ht; rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ] <;> try positivity;
        · grind;
        · exact mul_nonneg ( le_of_lt ( h_pos t ht ) ) ( Real.sqrt_nonneg _ );
      rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with t ht using h_sqrt t ht ) ];
      -- Divide numerator and denominator by $t$:
      suffices h_suff : Filter.Tendsto (fun t => Real.sqrt (1 / (1 / t + 2))) Filter.atTop (nhds (1 / Real.sqrt 2)) by
        refine h_suff.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ show t / ( 1 + 2 * t ) = 1 / ( 1 / t + 2 ) by rw [ div_eq_div_iff ] <;> ring <;> nlinarith [ mul_inv_cancel₀ ht.ne' ] ] );
      exact le_trans ( Filter.Tendsto.sqrt <| tendsto_const_nhds.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) <| by norm_num ) <| by norm_num;

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  exact limit_from_identity y
    (y_sq_identity y hy_diff hy_cont hy0)
    (y_pos y hy_diff hy_cont hy0)

end Submission