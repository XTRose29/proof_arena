import Mathlib

open Filter Topology Real

namespace Submission

/-
Proof strategy:
Define g(t) = (y(t)² * (2t + 1) - 1)². We show:
1. g has derivative -4 * y(t)² * g(t) ≤ 0 for t > 0
2. g is continuous on [0, ∞) and g(0) = 0
3. Therefore g is non-increasing, so g(t) ≤ g(0) = 0, but g ≥ 0, so g = 0
4. This gives y(t)² = 1/(2t+1) for t ≥ 0
5. Combined with y(0) = 1 > 0 and continuity, y(t) > 0
6. Then y(t) * √t = √(t/(2t+1)) → 1/√2
-/
private lemma y_continuousOn (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) :
    ContinuousOn y (Set.Ici 0) := by
  intro t ht;
  by_cases h : 0 < t;
  · exact HasDerivAt.continuousAt ( hy_diff t h ) |> ContinuousAt.continuousWithinAt;
  · cases eq_or_lt_of_le ht.out <;> aesop

private lemma hasDerivAt_ysq_lin (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => y s ^ 2 * (2 * s + 1))
      (2 * y t ^ 2 * (1 - y t ^ 2 * (2 * t + 1))) t := by
  convert HasDerivAt.mul ( HasDerivAt.comp t ( hasDerivAt_pow 2 _ ) ( hy_diff t ht ) ) ( HasDerivAt.add ( HasDerivAt.const_mul 2 ( hasDerivAt_id' t ) ) ( hasDerivAt_const _ _ ) ) using 1 ; ring!;
  norm_num ; ring

private lemma hasDerivAt_g (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => (y s ^ 2 * (2 * s + 1) - 1) ^ 2)
      (-4 * y t ^ 2 * (y t ^ 2 * (2 * t + 1) - 1) ^ 2) t := by
  have h_deriv : HasDerivAt (fun s => y s ^ 2 * (2 * s + 1) - 1) (2 * y t ^ 2 * (1 - y t ^ 2 * (2 * t + 1))) t := by
    have := hasDerivAt_ysq_lin y hy_diff t ht;
    exact this.sub_const 1;
  convert h_deriv.pow 2 using 1 ; ring

private lemma ysq_lin_eq_one (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) (t : ℝ) (ht : 0 ≤ t) :
    y t ^ 2 * (2 * t + 1) = 1 := by
  -- Let's define the function $g(t) = (y(t)^2 * (2t + 1) - 1)^2$ and show that it satisfies the conditions for $g$.
  set g : ℝ → ℝ := fun t => (y t ^ 2 * (2 * t + 1) - 1) ^ 2
  have hg_cont : ContinuousOn g (Set.Ici 0) := by
    exact ContinuousOn.pow ( ContinuousOn.sub ( ContinuousOn.mul ( ContinuousOn.pow ( y_continuousOn y hy_diff hy_cont ) 2 ) ( ContinuousOn.add ( continuousOn_const.mul continuousOn_id ) continuousOn_const ) ) continuousOn_const ) 2
  have hg_diff : DifferentiableOn ℝ g (Set.Ioi 0) := by
    exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.pow ( by exact DifferentiableAt.sub ( DifferentiableAt.mul ( DifferentiableAt.pow ( hy_diff t ht |> HasDerivAt.differentiableAt ) 2 ) ( by norm_num [ mul_comm ] ) ) ( differentiableAt_const _ ) ) _ )
  have hg_deriv : ∀ t, 0 < t → deriv g t ≤ 0 := by
    intro t ht; rw [ show deriv g t = -4 * y t ^ 2 * ( y t ^ 2 * ( 2 * t + 1 ) - 1 ) ^ 2 by simpa using HasDerivAt.deriv ( hasDerivAt_g y hy_diff t ht ) ] ; nlinarith [ sq_nonneg ( y t ^ 2 * ( 2 * t + 1 ) - 1 ) ] ;
  have hg_zero : g 0 = 0 := by
    grind +qlia
  have hg_noninc : AntitoneOn g (Set.Ici 0) := by
    apply_rules [ antitoneOn_of_deriv_nonpos ];
    · exact convex_Ici _;
    · aesop;
    · aesop
  have hg_zero_all : ∀ t, 0 ≤ t → g t ≤ 0 := by
    exact fun t ht => hg_zero ▸ hg_noninc ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht
  have hg_zero_all_sq : ∀ t, 0 ≤ t → y t ^ 2 * (2 * t + 1) = 1 := by
    exact fun t ht => eq_of_sub_eq_zero ( sq_eq_zero_iff.mp ( le_antisymm ( hg_zero_all t ht ) ( sq_nonneg _ ) ) )
  exact hg_zero_all_sq t ht

private lemma y_pos (y : ℝ → ℝ)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) (t : ℝ) (ht : 0 ≤ t) :
    0 < y t := by
  by_contra h_neg;
  -- Since $y(t)$ is continuous on $[0, \infty)$ and $y(0) = 1 > 0$, by the intermediate value theorem, there exists some $t_0 \geq 0$ such that $y(t_0) = 0$.
  obtain ⟨t0, ht0⟩ : ∃ t0 ≥ 0, y t0 = 0 := by
    have h_cont : ContinuousOn y (Set.Icc 0 t) := by
      exact ContinuousOn.mono ( y_continuousOn y hy_diff hy_cont ) ( Set.Icc_subset_Ici_self );
    have := intermediate_value_Icc' ht h_cont;
    exact Exists.elim ( this ⟨ by linarith, by linarith ⟩ ) fun x hx => ⟨ x, hx.1.1, hx.2 ⟩;
  have := ysq_lin_eq_one y hy_diff hy_cont hy0 t0 ht0.1; aesop;

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  -- Squaring and using that $\sqrt{t}$ tends to infinity as $t$ tends to infinity, we get that $y(t)^2 t$ tends to $1/2$.
  have h_sq : Filter.Tendsto (fun t ↦ y t ^ 2 * t) Filter.atTop (nhds (1 / 2)) := by
    have := @ysq_lin_eq_one;
    rw [ Metric.tendsto_nhds ];
    intro ε hε; filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( ε⁻¹ * 2 ) ] with t ht₁ ht₂ using abs_lt.mpr ⟨ by nlinarith [ inv_mul_cancel₀ hε.ne', this y hy_diff hy_cont hy0 t ht₁.le, mul_inv_cancel₀ ht₁.ne' ], by nlinarith [ inv_mul_cancel₀ hε.ne', this y hy_diff hy_cont hy0 t ht₁.le, mul_inv_cancel₀ ht₁.ne' ] ⟩ ;
  convert h_sq.sqrt.congr' _ using 1;
  · norm_num;
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq ( le_of_lt ( y_pos y hy_diff hy_cont hy0 t ht.le ) ) ] ;

end Submission
