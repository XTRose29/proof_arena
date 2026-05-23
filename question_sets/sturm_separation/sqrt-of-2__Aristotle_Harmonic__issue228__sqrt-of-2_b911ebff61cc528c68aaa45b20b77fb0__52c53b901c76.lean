import Mathlib

namespace Submission

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  -- By the Wronskian condition, there exists a constant $C \neq 0$ such that $y_1(x)y_2'(x) - y_2(x)y_1'(x) = Ce^{-G(x)}$ for all $x \in J$.
  obtain ⟨C, hC⟩ : ∃ C ≠ 0, ∀ x ∈ J, (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) * Real.exp (∫ t in a..x, p t) = C := by
    have h_wronskian : ∀ x ∈ J, HasDerivAt (fun x => (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) * Real.exp (∫ t in a..x, p t)) 0 x := by
      intro x hx
      have h_deriv : HasDerivAt (fun x => ∫ t in a..x, p t) (p x) x := by
        apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
        · apply_rules [ ContinuousOn.intervalIntegrable, hp ];
          cases le_total x a <;> simp_all +decide [ Set.uIcc_of_le ];
          · exact hp.mono ( show Set.Icc x a ⊆ J from fun y hy => hJ_conn.Icc_subset hx ( hJ_sub <| Set.left_mem_Icc.mpr hab.le ) hy );
          · exact hp.mono ( show Set.Icc a x ⊆ J from fun y hy => hJ_conn.Icc_subset ( hJ_sub <| Set.left_mem_Icc.mpr hab.le ) hx hy );
        · grind +suggestions;
        · exact hp.continuousAt ( hJ_open.mem_nhds hx );
      convert HasDerivAt.mul ( HasDerivAt.sub ( HasDerivAt.mul ( hy₁ x hx ) ( hy₂' x hx ) ) ( HasDerivAt.mul ( hy₂ x hx ) ( hy₁' x hx ) ) ) ( HasDerivAt.exp h_deriv ) using 1 ; ring;
      norm_num ; ring;
    -- Since the derivative of the Wronskian is zero, the Wronskian is constant on $J$.
    have h_wronskian_const : ∀ x y : ℝ, x ∈ J → y ∈ J → (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) * Real.exp (∫ t in a..x, p t) = (y₁ y * deriv y₂ y - y₂ y * deriv y₁ y) * Real.exp (∫ t in a..y, p t) := by
      have h_wronskian_const : ∀ x y : ℝ, x ∈ J → y ∈ J → ∫ t in x..y, deriv (fun x => (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) * Real.exp (∫ t in a..x, p t)) t = (y₁ y * deriv y₂ y - y₂ y * deriv y₁ y) * Real.exp (∫ t in a..y, p t) - (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) * Real.exp (∫ t in a..x, p t) := by
        intros x y hx hy;
        rw [ intervalIntegral.integral_deriv_eq_sub' ];
        · rfl;
        · exact fun z hz => HasDerivAt.differentiableAt ( h_wronskian z <| by cases Set.mem_uIcc.mp hz <;> [ exact hJ_conn.Icc_subset hx hy ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hy hx ⟨ by linarith, by linarith ⟩ ] );
        · exact ContinuousOn.congr ( show ContinuousOn ( fun _ => 0 ) _ from continuousOn_const ) fun z hz => HasDerivAt.deriv ( h_wronskian z <| by cases Set.mem_uIcc.mp hz <;> [ exact hJ_conn.Icc_subset hx hy ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hy hx ⟨ by linarith, by linarith ⟩ ] );
      intro x y hx hy; specialize h_wronskian_const x y hx hy; rw [ intervalIntegral.integral_congr fun t ht => HasDerivAt.deriv ( h_wronskian t <| by cases ( Set.mem_uIcc.mp ht ) <;> [ exact hJ_conn.Icc_subset hx hy ⟨ by linarith, by linarith ⟩ ; exact hJ_conn.Icc_subset hy hx ⟨ by linarith, by linarith ⟩ ] ) ] at h_wronskian_const; norm_num at h_wronskian_const; linarith;
    obtain ⟨ x₀, hx₀₁, hx₀₂ ⟩ := hW; use ( y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ) * Real.exp ( ∫ t in a..x₀, p t ) ; aesop;
  -- Since $y₂(a) \neq 0$ and $y₂(b) \neq 0$, and $y₁(a) = 0$ and $y₁(b) = 0$, the Wronskian condition implies that $y₂(a)$ and $y₂(b)$ have opposite signs.
  have h_signs : y₂ a * y₂ b < 0 := by
    have h_signs : deriv y₁ a * deriv y₁ b < 0 := by
      -- By the properties of the derivative, since $y₁(a) = 0$ and $y₁(b) = 0$, we have $deriv y₁(a) \neq 0$ and $deriv y₁(b) \neq 0$.
      have h_deriv_ne_zero : deriv y₁ a ≠ 0 ∧ deriv y₁ b ≠ 0 := by
        grind;
      -- Since $y₁$ is continuous on $[a, b]$ and $y₁(a) = y₁(b) = 0$, by the Intermediate Value Theorem, $y₁$ must change sign between $a$ and $b$.
      have h_ivt : (∀ x ∈ Set.Ioo a b, y₁ x > 0) ∨ (∀ x ∈ Set.Ioo a b, y₁ x < 0) := by
        contrapose! hne;
        have h_ivt : IsConnected (y₁ '' Set.Ioo a b) := by
          exact ⟨ Set.Nonempty.image _ ⟨ _, hne.1.choose_spec.1 ⟩, isPreconnected_Ioo.image _ <| continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt <| hy₁ x <| hJ_sub <| Set.Ioo_subset_Icc_self hx ⟩;
        exact h_ivt.Icc_subset ( Set.mem_image_of_mem _ hne.1.choose_spec.1 ) ( Set.mem_image_of_mem _ hne.2.choose_spec.1 ) ⟨ hne.1.choose_spec.2, hne.2.choose_spec.2 ⟩;
      cases' h_ivt with h_ivt h_ivt;
      · have h_deriv_pos : deriv y₁ a > 0 := by
          have h_deriv_pos : Filter.Tendsto (fun x => (y₁ x - y₁ a) / (x - a)) (nhdsWithin a (Set.Ioi a)) (nhds (deriv y₁ a)) := by
            have := hy₁ a ( hJ_sub <| Set.left_mem_Icc.mpr hab.le );
            rw [ hasDerivAt_iff_tendsto_slope ] at this;
            simpa [ div_eq_inv_mul ] using this.mono_left ( nhdsWithin_mono _ <| by simp +decide );
          exact lt_of_le_of_ne ( le_of_tendsto_of_tendsto tendsto_const_nhds h_deriv_pos <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hab ⟩ ) fun x hx => div_nonneg ( sub_nonneg.2 <| le_of_lt <| by linarith [ h_ivt x hx ] ) <| sub_nonneg.2 hx.1.le ) h_deriv_ne_zero.1.symm
        have h_deriv_neg : deriv y₁ b < 0 := by
          have h_deriv_neg : Filter.Tendsto (fun x => (y₁ x - y₁ b) / (x - b)) (nhdsWithin b (Set.Iio b)) (nhds (deriv y₁ b)) := by
            have h_deriv_neg : HasDerivAt y₁ (deriv y₁ b) b := by
              exact hy₁ b ( hJ_sub <| Set.right_mem_Icc.mpr hab.le );
            rw [ hasDerivAt_iff_tendsto_slope ] at h_deriv_neg;
            simpa [ div_eq_inv_mul ] using h_deriv_neg.mono_left ( nhdsWithin_mono _ <| by simp +decide );
          exact lt_of_le_of_ne ( le_of_tendsto h_deriv_neg <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT hab ) fun x hx => div_nonpos_of_nonneg_of_nonpos ( by linarith [ h_ivt x hx ] ) ( by linarith [ hx.2 ] ) ) h_deriv_ne_zero.2
        exact mul_neg_of_pos_of_neg h_deriv_pos h_deriv_neg;
      · have h_deriv_neg : deriv y₁ a < 0 := by
          have h_deriv_neg : Filter.Tendsto (fun x => (y₁ x - y₁ a) / (x - a)) (nhdsWithin a (Set.Ioi a)) (nhds (deriv y₁ a)) := by
            have := hy₁ a ( hJ_sub <| Set.left_mem_Icc.mpr hab.le );
            rw [ hasDerivAt_iff_tendsto_slope ] at this;
            simpa [ div_eq_inv_mul ] using this.mono_left ( nhdsWithin_mono _ <| by simp +decide );
          exact lt_of_le_of_ne ( le_of_tendsto_of_tendsto h_deriv_neg tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hab ⟩ ) fun x hx => div_nonpos_of_nonpos_of_nonneg ( by linarith [ h_ivt x hx ] ) ( by linarith [ hx.1 ] ) ) h_deriv_ne_zero.1
        have h_deriv_pos : deriv y₁ b > 0 := by
          have h_deriv_pos : Filter.Tendsto (fun x => (y₁ x - y₁ b) / (x - b)) (nhdsWithin b (Set.Iio b)) (nhds (deriv y₁ b)) := by
            have h_deriv_pos : HasDerivAt y₁ (deriv y₁ b) b := by
              exact hy₁ b ( hJ_sub <| Set.right_mem_Icc.mpr hab.le );
            rw [ hasDerivAt_iff_tendsto_slope ] at h_deriv_pos;
            simpa [ div_eq_inv_mul ] using h_deriv_pos.mono_left ( nhdsWithin_mono _ <| by simp +decide );
          exact lt_of_le_of_ne ( le_of_tendsto_of_tendsto tendsto_const_nhds h_deriv_pos <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT hab ) fun x hx => div_nonneg_of_nonpos ( by linarith [ h_ivt x hx ] ) ( by linarith [ hx.1, hx.2 ] ) ) ( Ne.symm h_deriv_ne_zero.2 )
        exact mul_neg_of_neg_of_pos h_deriv_neg h_deriv_pos;
    have h_signs : (-y₂ a * deriv y₁ a) * Real.exp (∫ t in a..a, p t) = C ∧ (-y₂ b * deriv y₁ b) * Real.exp (∫ t in a..b, p t) = C := by
      exact ⟨ by simpa [ hza ] using hC.2 a ( hJ_sub <| Set.left_mem_Icc.mpr hab.le ), by simpa [ hzb ] using hC.2 b ( hJ_sub <| Set.right_mem_Icc.mpr hab.le ) ⟩;
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    cases lt_or_gt_of_ne hC.1 <;> cases lt_or_gt_of_ne ( show deriv y₁ a ≠ 0 from fun h => by norm_num [ h ] at * ) <;> cases lt_or_gt_of_ne ( show deriv y₁ b ≠ 0 from fun h => by norm_num [ h ] at * ) <;> nlinarith [ Real.exp_pos ( ∫ t in a..b, p t ), mul_pos ( Real.exp_pos ( ∫ t in a..b, p t ) ) ( sub_pos.mpr ‹deriv y₁ a * deriv y₁ b < 0› ) ];
  -- By the Intermediate Value Theorem, since $y₂(a)$ and $y₂(b)$ have opposite signs, there exists at least one $c \in (a, b)$ such that $y₂(c) = 0$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
    have h_ivt : ContinuousOn y₂ (Set.Icc a b) := by
      exact continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₂ x ( hJ_sub hx ) );
    rw [ mul_neg_iff ] at h_signs;
    rcases h_signs with h | h <;> [ exact intermediate_value_Ioo' hab.le h_ivt ( by aesop ) ; exact intermediate_value_Ioo hab.le h_ivt ( by aesop ) ];
  -- To prove uniqueness, assume there exists another $d \in (a, b)$ such that $y₂(d) = 0$.
  by_contra h_unique_contra
  obtain ⟨d, hd⟩ : ∃ d ∈ Set.Ioo a b, y₂ d = 0 ∧ d ≠ c := by
    exact not_forall_not.mp fun h => h_unique_contra ⟨ c, hc, fun x hx => Classical.not_not.mp fun hx' => h x <| by aesop ⟩;
  -- Since $y₁(x) \neq 0$ for all $x \in (a, b)$, we can apply the Mean Value Theorem to the interval $(c, d)$.
  have h_mvt : ∃ ξ ∈ Set.Ioo (min c d) (max c d), deriv (fun x => y₂ x / y₁ x) ξ = 0 := by
    apply_mod_cast exists_deriv_eq_zero <;> norm_num;
    · tauto;
    · exact ContinuousOn.div ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₂ x <| hJ_sub <| by constructor <;> cases max_cases c d <;> cases min_cases c d <;> linarith [ hx.1, hx.2, hc.1.1, hc.1.2, hd.1.1, hd.1.2 ] ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy₁ x <| hJ_sub <| by constructor <;> cases max_cases c d <;> cases min_cases c d <;> linarith [ hx.1, hx.2, hc.1.1, hc.1.2, hd.1.1, hd.1.2 ] ) ) fun x hx => hne x ⟨ by cases max_cases c d <;> cases min_cases c d <;> linarith [ hx.1, hx.2, hc.1.1, hc.1.2, hd.1.1, hd.1.2 ], by cases max_cases c d <;> cases min_cases c d <;> linarith [ hx.1, hx.2, hc.1.1, hc.1.2, hd.1.1, hd.1.2 ] ⟩;
    · cases le_total c d <;> simp +decide [ * ];
  obtain ⟨ ξ, hξ₁, hξ₂ ⟩ := h_mvt; have := hC.2 ξ ( hJ_sub <| by constructor <;> cases max_cases c d <;> cases min_cases c d <;> linarith [ hξ₁.1, hξ₁.2, hc.1.1, hc.1.2, hd.1.1, hd.1.2 ] ) ; simp_all +decide [ Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
  have h_deriv_zero : deriv (fun x => y₂ x / y₁ x) ξ = (deriv y₂ ξ * y₁ ξ - y₂ ξ * deriv y₁ ξ) / y₁ ξ ^ 2 := by
    exact deriv_div ( hy₂ ξ ( hJ_sub <| by constructor <;> cases hξ₁.1 <;> cases hξ₁.2 <;> linarith ) ) ( hy₁ ξ ( hJ_sub <| by constructor <;> cases hξ₁.1 <;> cases hξ₁.2 <;> linarith ) ) ( hne ξ ( by cases hξ₁.1 <;> cases hξ₁.2 <;> linarith ) ( by cases hξ₁.1 <;> cases hξ₁.2 <;> linarith ) );
  grind

end Submission
