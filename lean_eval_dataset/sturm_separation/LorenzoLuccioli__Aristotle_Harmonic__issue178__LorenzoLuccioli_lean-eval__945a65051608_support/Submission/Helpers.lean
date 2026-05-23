import Mathlib

namespace Submission.Helpers

open Set Real

/-! ## Grönwall-based uniqueness for linear scalar ODEs -/

/-
If a continuous function on [a,b] has right derivative bounded by K * |f| and starts at 0,
then it vanishes on [a,b]. This is a corollary of `norm_le_gronwallBound_of_norm_deriv_right_le`.
-/
lemma eq_zero_on_Icc_of_deriv_le_mul_norm_forward
    {f f' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖)
    (hfa : f a = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  have := @norm_le_gronwallBound_of_norm_deriv_right_le;
  specialize @this ℝ _ _ f f' 0 K 0 a b ; simp_all +decide [ gronwallBound_ε0_δ0 ]

/-
Backward version: if f(b) = 0 and |f'| ≤ K |f|, then f = 0 on [a,b].
-/
lemma eq_zero_on_Icc_of_deriv_le_mul_norm_backward
    {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hf : ContinuousOn f (Icc a b))
    (hf_deriv : ∀ x ∈ Ioo a b, HasDerivAt f (deriv f x) x)
    (hbound : ∀ x ∈ Ioo a b, ‖deriv f x‖ ≤ K * ‖f x‖)
    (hfb : f b = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  -- Define a new function g(t) = f(a + b - t) for t ∈ [a, b]. Then g(a) = f(b) = 0, and g is continuous on [a,b].
  set g : ℝ → ℝ := fun t => f (a + b - t)
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    exact hf.comp ( continuousOn_const.sub continuousOn_id ) fun x hx => ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩;
  -- The derivative of g at t is -f'(a+b-t). So |g'(t)| = |f'(a+b-t)| ≤ K |f(a+b-t)| = K |g(t)|.
  have hg_deriv : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt g (-deriv f (a + b - t)) (Set.Ici t) t := by
    intro t ht;
    convert HasDerivAt.hasDerivWithinAt ( HasDerivAt.comp t ( hf_deriv ( a + b - t ) ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ) ( HasDerivAt.const_sub _ ( hasDerivAt_id t ) ) ) using 1 ; ring;
  -- Apply eq_zero_on_Icc_of_deriv_le_mul_norm_forward to g to get g = 0 on [a,b], hence f = 0 on [a,b].
  have hg_zero : ∀ x ∈ Set.Icc a b, g x = 0 := by
    have hg_deriv_bound : ∀ t ∈ Set.Ioo a b, ‖-deriv f (a + b - t)‖ ≤ K * ‖g t‖ := by
      exact fun t ht => by simpa using hbound ( a + b - t ) ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ;
    apply eq_zero_on_Icc_of_deriv_le_mul_norm_forward hab hg_cont;
    any_goals exact K;
    rotate_right;
    use fun t => if t = a then 0 else -deriv f ( a + b - t );
    · intro x hx; cases eq_or_lt_of_le hx.1 <;> cases eq_or_lt_of_le hx.2.le <;> simp_all +decide ;
      · have h_lim : Filter.Tendsto (fun t => (g t - g x) / (t - x)) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
          have h_lim : Filter.Tendsto (fun t => deriv f (a + b - t)) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
            have h_lim : Filter.Tendsto (fun t => K * |g t|) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
              have h_lim : Filter.Tendsto (fun t => g t) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
                have h_lim : Filter.Tendsto (fun t => g t) (nhdsWithin x (Set.Ioi x)) (nhds (g x)) := by
                  have := hg_cont x ⟨ by linarith, by linarith ⟩;
                  convert this.mono_left _ using 2;
                  rw [ nhdsWithin_le_iff ];
                  exact mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨ b, by norm_num; linarith, fun y hy => ⟨ by linarith [ hy.out ], by linarith [ hy.out ] ⟩ ⟩;
                aesop;
              simpa using h_lim.abs.const_mul K;
            refine' squeeze_zero_norm' _ h_lim;
            filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, ‹x < b› ⟩ ] with t ht using by simpa [ * ] using hg_deriv_bound t ht.1 ht.2;
          have h_lim : ∀ᶠ t in nhdsWithin x (Set.Ioi x), ∃ c ∈ Set.Ioo x t, deriv f (a + b - c) = (g t - g x) / (t - x) * (-1) := by
            filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, ‹x < b› ⟩ ] with t ht;
            have := exists_deriv_eq_slope ( f := fun t => f ( a + b - t ) ) ht.1;
            simp +zetaDelta at *;
            have h_diff : DifferentiableOn ℝ (fun t => f (a + b - t)) (Set.Ioo x t) := by
              exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.comp u ( hf_deriv _ ( by linarith [ hu.1, hu.2 ] ) ( by linarith [ hu.1, hu.2 ] ) ) ( differentiableAt_id.const_sub _ ) );
            have h_diff : ∀ c ∈ Set.Ioo x t, deriv (fun t => f (a + b - t)) c = -deriv f (a + b - c) := by
              intro c hc
              have hd := (hf_deriv (a + b - c) (by linarith [hc.1, hc.2]) (by linarith [hc.1, hc.2])).hasDerivAt
              have hcomp := hd.comp c ((hasDerivAt_id c).const_sub (a + b))
              simp [Function.comp] at hcomp
              exact hcomp.deriv
            exact this ( hg_cont.mono ( Set.Icc_subset_Icc le_rfl ht.2.le ) ) ‹_› |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by linarith [ h_diff c hc₁ ] ⟩;
          rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
          intro ε hε; rcases ‹∀ ε > 0, ∃ δ > 0, ∀ ⦃x_1 : ℝ⦄, x_1 ∈ Ioi x → dist x_1 x < δ → dist ( deriv f ( a + b - x_1 ) ) 0 < ε› ε hε with ⟨ δ, hδ, H ⟩ ; rcases Metric.mem_nhdsWithin_iff.mp ( h_lim ) with ⟨ δ', hδ', H' ⟩ ; use Min.min δ δ'; simp_all +decide [ abs_mul, abs_div ] ;
          intro t ht₁ ht₂ ht₃; specialize H' ⟨ ht₃, ht₁ ⟩ ; rcases H' with ⟨ c, ⟨ hc₁, hc₂ ⟩, hc₃ ⟩ ; specialize H hc₁ ( abs_lt.mpr ⟨ by linarith [ abs_lt.mp ht₂ ], by linarith [ abs_lt.mp ht₂ ] ⟩ ) ; simp_all +decide [ abs_div, abs_neg ] ;
        rw [ hasDerivWithinAt_iff_tendsto_slope ];
        rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
        intro ε hε; rcases h_lim ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun { y } hy₁ hy₂ => by simpa [ div_eq_inv_mul, slope_def_field, hy₁.2 ] using H ( show x < y from lt_of_le_of_ne hy₁.1 ( Ne.symm hy₁.2 ) ) hy₂ ⟩ ;
      · rw [ if_neg ( by linarith ) ] ; exact hg_deriv x ‹_› ‹_›;
    · intro x hx; cases eq_or_lt_of_le hx.1 <;> aesop;
    · simp [g, hfb];
  intro x hx; have := hg_zero (a + b - x) ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩; simp [g] at this; exact this

/-
If f is differentiable on an open connected set J, satisfies |f'(x)| ≤ K|f(x)| for all x ∈ J,
and vanishes at some point, then f vanishes on all of J.
-/
lemma eq_zero_on_open_connected_of_deriv_bound
    {f : ℝ → ℝ} {J : Set ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hf_deriv : ∀ x ∈ J, HasDerivAt f (deriv f x) x)
    (hbound : ∀ x ∈ J, ‖deriv f x‖ ≤ K * ‖f x‖)
    (hc : ∃ c ∈ J, f c = 0) :
    ∀ x ∈ J, f x = 0 := by
  -- By the properties of the derivative, if $f'(x) = 0$ for all $x \in J$, then $f$ is constant on $J$.
  have h_const : ∀ x ∈ J, f x = 0 := by
    have h_open : IsOpen (J ∩ {x | f x = 0}) := by
      refine' isOpen_iff_mem_nhds.mpr _;
      intro x hx
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball x ε ⊆ J := by
        exact Metric.isOpen_iff.mp hJ_open x hx.1
      have h_ball_zero : ∀ y ∈ Metric.ball x ε, f y = 0 := by
        intro y hy
        have h_ball_zero : ∀ z ∈ Set.Icc (min x y) (max x y), f z = 0 := by
          cases le_total x y <;> simp_all +decide [ Metric.mem_ball ];
          · have := eq_zero_on_Icc_of_deriv_le_mul_norm_forward ( show x ≤ y by linarith ) ( show ContinuousOn f ( Set.Icc x y ) from continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt ( hf_deriv z <| hε <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ hz.1, abs_lt.mp hy ], by linarith [ hz.2, abs_lt.mp hy ] ⟩ ) ) ( fun z hz => HasDerivAt.hasDerivWithinAt <| hf_deriv z ( hε <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ hz.1, abs_lt.mp hy ], by linarith [ hz.2, abs_lt.mp hy ] ⟩ ) |> DifferentiableAt.hasDerivAt ) ( fun z hz => hbound z <| hε <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ hz.1, abs_lt.mp hy ], by linarith [ hz.2, abs_lt.mp hy ] ⟩ ) hx.2; aesop;
          · intro z hz₁ hz₂; exact eq_zero_on_Icc_of_deriv_le_mul_norm_backward ( by linarith ) hK ( show ContinuousOn f ( Set.Icc y x ) from continuousOn_of_forall_continuousAt fun t ht => DifferentiableAt.continuousAt ( hf_deriv t <| hε <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1, ht.2, abs_lt.mp hy ], by linarith [ ht.1, ht.2, abs_lt.mp hy ] ⟩ ) ) ( fun t ht => DifferentiableAt.hasDerivAt ( hf_deriv t <| hε <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1, ht.2, abs_lt.mp hy ], by linarith [ ht.1, ht.2, abs_lt.mp hy ] ⟩ ) ) ( fun t ht => hbound t <| hε <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1, ht.2, abs_lt.mp hy ], by linarith [ ht.1, ht.2, abs_lt.mp hy ] ⟩ ) hx.2 |> fun h => h z ⟨ by linarith, by linarith ⟩ ;
        grind +splitIndPred
      exact Filter.mem_of_superset (Metric.ball_mem_nhds x hε_pos) (by
      exact fun y hy => ⟨ hε hy, h_ball_zero y hy ⟩)
    -- Since $f$ is continuous on $J$, the set $\{x \in J \mid f(x) \neq 0\}$ is open in $J$.
    have h_compl_open : IsOpen (J ∩ {x | f x ≠ 0}) := by
      exact isOpen_iff_mem_nhds.mpr fun x hx => Filter.inter_mem ( hJ_open.mem_nhds hx.1 ) ( Filter.mem_of_superset ( hf_deriv x hx.1 |> HasDerivAt.continuousAt |> ContinuousAt.eventually_ne <| hx.2 ) fun y hy => hy );
    specialize hJ_conn ( J ∩ { x | f x = 0 } ) ( J ∩ { x | ¬f x = 0 } ) ; simp_all +decide [ Set.disjoint_left ] ;
    contrapose! hJ_conn; simp_all +decide [ Set.Nonempty ] ;
    exact ⟨ fun x hx => by by_cases h : f x = 0 <;> aesop, by ext; aesop ⟩;
  assumption

/-! ## Wronskian properties -/

/-
Abel's identity: the Wronskian W = y₁·y₂' - y₂·y₁' has derivative -p·W.
-/
lemma wronskian_hasDerivAt
    (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x) :
    ∀ x ∈ J, HasDerivAt (fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x)
      (-(p x * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x))) x := by
  intro x hx; convert HasDerivAt.sub ( HasDerivAt.mul ( hy₁ x hx ) ( hy₂' x hx ) ) ( HasDerivAt.mul ( hy₂ x hx ) ( hy₁' x hx ) ) using 1; ring;

/-
If the Wronskian is nonzero somewhere on J (open, connected), it's nonzero everywhere on J.
-/
lemma wronskian_ne_zero_on_J
    (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ)
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp : ContinuousOn p J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0) :
    ∀ x ∈ J, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x ≠ 0 := by
  -- By definition of $W$, we know that its derivative is $-p(x)W(x)$.
  have hW_deriv : ∀ x ∈ J, HasDerivAt (fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) (-(p x * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x))) x := by
    exact fun x a => wronskian_hasDerivAt p q y₁ y₂ J hy₁ hy₁' hy₂ hy₂' x a;
  obtain ⟨ x₀, hx₀₁, hx₀₂ ⟩ := hW;
  -- Consider the function $f(x) = e^{\int p(x) \, dx} W(x)$. We will show that $f(x)$ is constant.
  set f : ℝ → ℝ := fun x => (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) * Real.exp (∫ t in x₀..x, p t);
  -- We will show that $f(x)$ is constant on $J$.
  have hf_const : ∀ x ∈ J, HasDerivAt f 0 x := by
    intro x hx
    have h_int_deriv : HasDerivAt (fun x => ∫ t in x₀..x, p t) (p x) x := by
      apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
      · apply_rules [ ContinuousOn.intervalIntegrable, hp ];
        exact hp.mono ( by intro y hy; cases Set.mem_uIcc.mp hy <;> [ exact hJ_conn.Icc_subset hx₀₁ hx ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hx hx₀₁ ⟨ by linarith, by linarith ⟩ ] );
      · exact ContinuousOn.stronglyMeasurableAtFilter hJ_open hp x hx;
      · exact hp.continuousAt ( hJ_open.mem_nhds hx );
    convert HasDerivAt.mul ( hW_deriv x hx ) ( HasDerivAt.exp h_int_deriv ) using 1 ; ring;
  -- Since $f(x)$ is constant on $J$, we have $f(x) = f(x₀)$ for all $x \in J$.
  have hf_eq : ∀ x ∈ J, f x = f x₀ := by
    have hf_eq : ∀ a b, a ∈ J → b ∈ J → ∫ x in a..b, deriv f x = f b - f a := by
      intros a b ha hb;
      rw [ intervalIntegral.integral_deriv_eq_sub' ];
      · rfl;
      · exact fun x hx => HasDerivAt.differentiableAt ( hf_const x <| by cases Set.mem_uIcc.mp hx <;> [ exact hJ_conn.Icc_subset ha hb ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hb ha ⟨ by linarith, by linarith ⟩ ] );
      · exact ContinuousOn.congr ( show ContinuousOn ( fun _ => 0 ) _ from continuousOn_const ) fun x hx => HasDerivAt.deriv ( hf_const x <| by cases Set.mem_uIcc.mp hx <;> [ exact hJ_conn.Icc_subset ha hb ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hb ha ⟨ by linarith, by linarith ⟩ ] );
    intro x hx; specialize hf_eq x₀ x hx₀₁ hx; rw [ intervalIntegral.integral_congr fun t ht => HasDerivAt.deriv ( hf_const t <| by cases ( Set.mem_uIcc.mp ht ) <;> [ exact hJ_conn.Icc_subset hx₀₁ hx ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hx hx₀₁ ⟨ by linarith, by linarith ⟩ ] ) ] at hf_eq; norm_num at * ; linarith;
  intro x hx; specialize hf_eq x hx; contrapose! hf_eq; aesop;

/-! ## Sign analysis -/

/-
y₁ has constant sign on (a,b) when it's nonzero there and continuous.
-/
lemma y1_pos_or_neg_on_Ioo
    {y₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hy₁_cont : ContinuousOn y₁ (Icc a b))
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < y₁ x) ∨ (∀ x ∈ Ioo a b, y₁ x < 0) := by
  contrapose! hne;
  have h_ivt : IsConnected (y₁ '' Set.Ioo a b) := by
    exact ⟨ Set.Nonempty.image _ ⟨ hne.1.choose, hne.1.choose_spec.1 ⟩, isPreconnected_Ioo.image _ <| hy₁_cont.mono <| Set.Ioo_subset_Icc_self ⟩;
  exact h_ivt.Icc_subset ( Set.mem_image_of_mem _ hne.1.choose_spec.1 ) ( Set.mem_image_of_mem _ hne.2.choose_spec.1 ) ⟨ hne.1.choose_spec.2, hne.2.choose_spec.2 ⟩

/-
If y₁ > 0 on (a,b), y₁(a) = 0, and y₁ differentiable at a, then y₁'(a) ≥ 0.
-/
lemma y1_deriv_a_nonneg_of_pos
    {y₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hy₁_diff : HasDerivAt y₁ (deriv y₁ a) a)
    (hza : y₁ a = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < y₁ x) :
    0 ≤ deriv y₁ a := by
  have := hy₁_diff.tendsto_slope_zero;
  -- Since $y_1(x) > 0$ for $x \in (a, b)$, we have $\lim_{t \to 0^+} \frac{y_1(a + t)}{t} \geq 0$.
  have h_lim_pos : Filter.Tendsto (fun t => y₁ (a + t) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv y₁ a)) := by
    simpa [ div_eq_inv_mul, hza ] using this.mono_left ( nhdsWithin_mono _ <| by simp +decide );
  exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim_pos ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show 0 < b - a by linarith ⟩ ) fun t ht => div_nonneg ( le_of_lt ( hpos ( a + t ) ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) ) ht.1.le )

/-
If y₁ > 0 on (a,b), y₁(b) = 0, and y₁ differentiable at b, then y₁'(b) ≤ 0.
-/
lemma y1_deriv_b_nonpos_of_pos
    {y₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hy₁_diff : HasDerivAt y₁ (deriv y₁ b) b)
    (hzb : y₁ b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < y₁ x) :
    deriv y₁ b ≤ 0 := by
  have := hy₁_diff.tendsto_slope_zero;
  -- For $h < 0$ small, $b + h \in (a, b)$ so $y₁(b + h) > 0$ and $h < 0$, giving ratio ≤ 0.
  have h_neg : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), (y₁ (b + h) - y₁ b) / h ≤ 0 := by
    filter_upwards [ Ioo_mem_nhdsLT ( show - ( b - a ) < 0 by linarith ) ] with x hx using div_nonpos_of_nonneg_of_nonpos ( by linarith [ hpos ( b + x ) ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ] ) hx.2.le;
  exact le_of_tendsto ( this.mono_left <| nhdsWithin_mono _ <| by simp +decide ) <| h_neg.mono fun x hx => by simpa [ div_eq_inv_mul, hzb ] using hx;

/-
y₂(a) and y₂(b) have opposite signs.
-/
lemma y2_opposite_signs
    (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Icc a b ⊆ J)
    (hp : ContinuousOn p J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    y₂ a * y₂ b < 0 := by
  -- The Wronskian W(x) = y₁(x)·y₂'(x) - y₂(x)·y₁'(x) is nonzero on J (by wronskian_ne_zero_on_J), hence nonzero on [a,b] ⊆ J.
  have hW_nonzero : ∀ x ∈ Set.Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x ≠ 0 := by
    exact fun x hx => wronskian_ne_zero_on_J p q y₁ y₂ J hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW x ( hJ_sub hx );
  -- By y1_pos_or_neg_on_Ioo, y₁ has constant sign on (a,b). WLOG y₁ > 0 on (a,b) (the negative case is symmetric - just flip the overall sign).
  by_cases h_pos : ∀ x ∈ Set.Ioo a b, 0 < y₁ x;
  · -- By y1_deriv_a_nonneg_of_pos: deriv y₁ a ≥ 0.
    have h_deriv_a_nonneg : 0 < deriv y₁ a := by
      have h_deriv_a_nonneg : 0 ≤ deriv y₁ a := by
        apply y1_deriv_a_nonneg_of_pos hab (hy₁ a (hJ_sub (Set.left_mem_Icc.mpr hab.le))) hza h_pos;
      exact h_deriv_a_nonneg.lt_of_ne' fun h => hW_nonzero a ⟨ by linarith, by linarith ⟩ <| by aesop;
    -- By y1_deriv_b_nonpos_of_pos: deriv y₁ b ≤ 0.
    have h_deriv_b_nonpos : deriv y₁ b < 0 := by
      apply lt_of_le_of_ne;
      · apply y1_deriv_b_nonpos_of_pos hab (hy₁ b (hJ_sub (Set.right_mem_Icc.mpr hab.le))) hzb h_pos;
      · grind;
    -- Since W is continuous on the connected set [a,b] and never zero, W has constant sign on [a,b].
    have hW_const_sign : (∀ x ∈ Set.Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x > 0) ∨ (∀ x ∈ Set.Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x < 0) := by
      have hW_const_sign : IsConnected (Set.image (fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) (Set.Icc a b)) := by
        apply_rules [ IsConnected.image, isConnected_Icc ];
        · linarith;
        · exact ContinuousOn.sub ( ContinuousOn.mul ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₁ x ( hJ_sub hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₂' x ( hJ_sub hx ) ) ) ) ( ContinuousOn.mul ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₂ x ( hJ_sub hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₁' x ( hJ_sub hx ) ) ) );
      contrapose! hW_nonzero;
      exact hW_const_sign.Icc_subset ( Set.mem_image_of_mem _ hW_nonzero.1.choose_spec.1 ) ( Set.mem_image_of_mem _ hW_nonzero.2.choose_spec.1 ) ⟨ hW_nonzero.1.choose_spec.2, hW_nonzero.2.choose_spec.2 ⟩;
    cases' hW_const_sign with h h <;> have := h a ⟨ by linarith, by linarith ⟩ <;> have := h b ⟨ by linarith, by linarith ⟩ <;> simp_all +decide [ mul_comm ];
    · nlinarith [ mul_pos h_deriv_a_nonneg ( neg_pos.mpr h_deriv_b_nonpos ) ];
    · nlinarith;
  · -- Since y₁ is not positive on (a,b), it must be negative on (a,b).
    have h_neg : ∀ x ∈ Set.Ioo a b, y₁ x < 0 := by
      have h_neg : ContinuousOn y₁ (Set.Icc a b) := by
        exact continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₁ x ( hJ_sub hx ) );
      exact Or.resolve_left ( y1_pos_or_neg_on_Ioo hab h_neg hne ) h_pos;
    -- By y1_deriv_a_nonneg_of_pos, we have deriv y₁ a ≤ 0.
    have h_deriv_a_nonpos : deriv y₁ a ≤ 0 := by
      have h_deriv_a_nonpos : Filter.Tendsto (fun h => (y₁ (a + h) - y₁ a) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv y₁ a)) := by
        simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( hy₁ a ( hJ_sub <| Set.left_mem_Icc.mpr hab.le ) );
      exact le_of_tendsto h_deriv_a_nonpos ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show 0 < b - a by linarith ⟩ ) fun x hx => div_nonpos_of_nonpos_of_nonneg ( by linarith [ h_neg ( a + x ) ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ] ) hx.1.le );
    -- By y1_deriv_b_nonpos_of_pos, we have deriv y₁ b ≥ 0.
    have h_deriv_b_nonneg : deriv y₁ b ≥ 0 := by
      have h_deriv_b_nonneg : Filter.Tendsto (fun x => (y₁ x - y₁ b) / (x - b)) (nhdsWithin b (Set.Iio b)) (nhds (deriv y₁ b)) := by
        have h_deriv_b_nonneg : HasDerivAt y₁ (deriv y₁ b) b := by
          exact hy₁ b ( hJ_sub <| Set.right_mem_Icc.mpr hab.le );
        rw [ hasDerivAt_iff_tendsto_slope ] at h_deriv_b_nonneg;
        simpa [ div_eq_inv_mul ] using h_deriv_b_nonneg.mono_left ( nhdsWithin_mono _ <| by simp +decide );
      exact le_of_tendsto_of_tendsto tendsto_const_nhds h_deriv_b_nonneg ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT hab ) fun x hx => div_nonneg_of_nonpos ( by linarith [ h_neg x hx ] ) ( by linarith [ hx.1, hx.2 ] ) );
    -- Since W(a) and W(b) have the same sign, we have -y₂(a)·y₁'(a) and -y₂(b)·y₁'(b) have the same sign.
    have h_sign : (-y₂ a * deriv y₁ a) * (-y₂ b * deriv y₁ b) > 0 := by
      have h_sign : ContinuousOn (fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) (Set.Icc a b) := by
        exact ContinuousOn.sub ( ContinuousOn.mul ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₁ x ( hJ_sub hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₂' x ( hJ_sub hx ) ) ) ) ( ContinuousOn.mul ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₂ x ( hJ_sub hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₁' x ( hJ_sub hx ) ) ) );
      have h_sign : (∀ x ∈ Set.Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x > 0) ∨ (∀ x ∈ Set.Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x < 0) := by
        contrapose! hW_nonzero;
        have := h_sign.image_Icc hab.le;
        exact this.symm.subset ( Set.mem_Icc.mpr ⟨ by obtain ⟨ x, hx₁, hx₂ ⟩ := hW_nonzero.1; linarith [ Set.mem_Icc.mp ( this ▸ Set.mem_image_of_mem _ hx₁ ) ], by obtain ⟨ x, hx₁, hx₂ ⟩ := hW_nonzero.2; linarith [ Set.mem_Icc.mp ( this ▸ Set.mem_image_of_mem _ hx₁ ) ] ⟩ );
      cases' h_sign with h_sign h_sign <;> have := h_sign a ⟨ le_rfl, hab.le ⟩ <;> have := h_sign b ⟨ hab.le, le_rfl ⟩ <;> simp_all +decide;
      nlinarith;
    by_cases h_deriv_a_zero : deriv y₁ a = 0 <;> by_cases h_deriv_b_zero : deriv y₁ b = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    nlinarith [ mul_pos ( neg_pos_of_neg ( lt_of_le_of_ne h_deriv_a_nonpos h_deriv_a_zero ) ) ( lt_of_le_of_ne h_deriv_b_nonneg ( Ne.symm h_deriv_b_zero ) ) ]

/-! ## Existence and uniqueness of zeros -/

/-
If f is continuous on [a,b] and f(a) * f(b) < 0, then f has a zero in (a,b).
-/
lemma exists_zero_of_opposite_signs
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hsigns : f a * f b < 0) :
    ∃ c ∈ Ioo a b, f c = 0 := by
  rw [ mul_neg_iff ] at hsigns;
  rcases hsigns with h | h <;> [ exact intermediate_value_Ioo' hab.le hf ( by aesop ) ; exact intermediate_value_Ioo hab.le hf ( by aesop ) ]

/-
If f = g/h where h ≠ 0, and the Wronskian h·g' - g·h' has constant sign on (a,b),
then f is strictly monotone on (a,b), hence has at most one zero.
-/
lemma at_most_one_zero_of_wronskian_ne_zero
    (y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hne_y1 : ∀ x ∈ Ioo a b, y₁ x ≠ 0)
    (hW_ne : ∀ x ∈ Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x ≠ 0) :
    ∀ c₁ ∈ Ioo a b, ∀ c₂ ∈ Ioo a b, y₂ c₁ = 0 → y₂ c₂ = 0 → c₁ = c₂ := by
  -- Let $f(x) = \frac{y_2(x)}{y_1(x)}$ for $x \in (a, b)$.
  set f : ℝ → ℝ := fun x => y₂ x / y₁ x;
  -- Since $f$ is differentiable and its derivative $f'(x) = \frac{W(x)}{y₁(x)^2}$ is nonzero on $(a, b)$, $f$ is strictly monotonic on $(a, b)$.
  have h_deriv_f_nonzero : ∀ x ∈ Set.Ioo a b, deriv f x ≠ 0 := by
    intro x hx;
    have h_deriv_f : deriv f x = (deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / y₁ x ^ 2 := by
      exact deriv_div ( hy₂ x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) |> HasDerivAt.differentiableAt ) ( hy₁ x ( hJ_sub <| Set.Ioo_subset_Icc_self hx ) |> HasDerivAt.differentiableAt ) ( hne_y1 x hx );
    exact h_deriv_f.symm ▸ div_ne_zero ( by simpa only [ mul_comm ] using hW_ne x <| Set.Ioo_subset_Icc_self hx ) ( pow_ne_zero 2 <| hne_y1 x hx );
  -- Since $f$ is differentiable and its derivative $f'(x) = \frac{W(x)}{y₁(x)^2}$ is nonzero on $(a, b)$, $f$ is strictly monotonic on $(a, b)$ by the Mean Value Theorem.
  have h_mvt : ∀ x₁ x₂, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₁ < x₂ → ∃ c ∈ Set.Ioo x₁ x₂, deriv f c = (f x₂ - f x₁) / (x₂ - x₁) := by
    intros x₁ x₂ hx₁ hx₂ hlt; apply_rules [ exists_deriv_eq_slope _, hx₁.1, hx₁.2, hx₂.1, hx₂.2 ];
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( hy₂ x ( hJ_sub <| Set.Icc_subset_Icc hx₁.1.le hx₂.2.le hx ) |> HasDerivAt.continuousAt ) ( hy₁ x ( hJ_sub <| Set.Icc_subset_Icc hx₁.1.le hx₂.2.le hx ) |> HasDerivAt.continuousAt ) ( hne_y1 x ⟨ by linarith [ hx.1, hx₁.1 ], by linarith [ hx.2, hx₂.2 ] ⟩ );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( h_deriv_f_nonzero x ⟨ by linarith [ hx.1, hx₁.1 ], by linarith [ hx.2, hx₂.2 ] ⟩ ) );
  grind +revert

end Submission.Helpers