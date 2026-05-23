import Mathlib
import Submission.Helpers

namespace Submission.Helpers

open MeromorphicOn Complex Topology Filter MeasureTheory Set Metric Function
open scoped Classical

noncomputable section

/-! ## Identity theorem: analytic functions agreeing on accumulating set agree on nhds -/

lemma analyticAt_eventuallyEq_of_nhdsWithin {f g : ℂ → ℂ} {z : ℂ} {S : Set ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hne : (nhdsWithin z S).NeBot)
    (hS : S ⊆ {z}ᶜ)
    (heq : f =ᶠ[nhdsWithin z S] g) :
    f =ᶠ[nhds z] g := by
  -- Step 1: (f - g) is analytic at z (hf.sub hg), hence meromorphicAt.
  have h_diff_analytic : AnalyticAt ℂ (f - g) z := by
    exact hf.sub hg;
  -- Step 2: Show meromorphicOrderAt (f - g) z = ⊤ by contradiction.
  have h_meromorphicOrderAt_top : meromorphicOrderAt (f - g) z = ⊤ := by
    contrapose! hne;
    have := meromorphicOrderAt_ne_top_iff_eventually_ne_zero ( h_diff_analytic.meromorphicAt ) |>.1 hne;
    simp_all +decide [ Filter.EventuallyEq, sub_eq_zero ];
    rw [ nhdsWithin, Filter.eventually_iff ] at *;
    simp_all +decide [ Filter.inf_principal_eq_bot ];
    rw [ Filter.mem_inf_principal ] at *;
    filter_upwards [ this, heq ] with x hx₁ hx₂ using by by_cases hx₃ : x = z <;> aesop;
  -- Step 3: meromorphicOrderAt (f - g) z = ⊤ gives, by meromorphicOrderAt_eq_top_iff:
  have h_eventually_zero : ∀ᶠ w in nhdsWithin z {z}ᶜ, (f - g) w = 0 := by
    exact meromorphicOrderAt_eq_top_iff.mp h_meromorphicOrderAt_top
  -- Step 4: Since (f - g) is continuous at z (analytic implies continuous), (f - g) z = 0 by limit argument (tendsto_nhds_unique or ContinuousAt combined with the eventual zero in punctured nhd).
  have h_cont : (f - g) z = 0 := by
    exact tendsto_nhds_unique ( h_diff_analytic.continuousAt.continuousWithinAt ) ( tendsto_nhds_of_eventually_eq h_eventually_zero );
  rw [ eventually_nhdsWithin_iff ] at h_eventually_zero;
  filter_upwards [ h_eventually_zero ] with x hx using if hx' : x = z then hx'.symm ▸ sub_eq_zero.mp h_cont else sub_eq_zero.mp ( hx hx' )

/-! ## Circle integral of logDeriv of analytic nonvanishing function is zero -/

lemma circleIntegral_logDeriv_analytic_nonvanishing {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (h_an : AnalyticOnNhd ℂ h (closedBall 0 R))
    (h_nz : ∀ z ∈ closedBall 0 R, h z ≠ 0) :
    ∮ w in C(0, R), deriv h w / h w = 0 := by
  have h_analytic : AnalyticOnNhd ℂ (fun w => deriv h w / h w) (closedBall 0 R) := by
    apply_rules [ AnalyticOnNhd.div, h_an.deriv ];
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable;
  exacts [ le_of_lt hR, Set.countable_singleton 0, h_analytic.continuousOn, fun z hz => h_analytic.differentiableOn.differentiableAt ( Metric.closedBall_mem_nhds_of_mem hz.1 ) ]

/-! ## logDeriv of finprod of zpow -/

lemma logDeriv_finprod_zpow {S : Finset ℂ} {d : ℂ → ℤ} {z : ℂ}
    (hz : z ∉ S) :
    (fun w => deriv (∏ u ∈ S, (· - u) ^ d u) w / (∏ u ∈ S, (w - u) ^ d u))
      z = ∑ u ∈ S, ↑(d u) * (z - u)⁻¹ := by
  induction' S using Finset.induction with u S huS ih generalizing z <;> simp_all +decide [ Finset.prod_insert ];
  convert congr_arg₂ ( · + · ) _ ( ih hz.2 ) using 1;
  rotate_left;
  exact deriv ( fun x => ( x - u ) ^ d u ) z / ( z - u ) ^ d u;
  · rcases k : d u with ( _ | k ) <;> simp_all +decide [div_eq_mul_inv];
    · cases ‹ℕ› <;> simp_all +decide [pow_succ, mul_assoc, mul_comm, mul_left_comm];
      simp +decide [mul_left_comm ((z - u) ^ _), sub_ne_zero.mpr hz.1];
    · erw [ deriv_comp ] <;> norm_num [ sub_ne_zero.mpr hz.1 ];
      · field_simp;
        rw [ neg_div', div_eq_div_iff ] <;> simp +decide [ sub_ne_zero.mpr hz.1, pow_succ' ] ; ring;
      · exact differentiableAt_inv ( pow_ne_zero _ ( sub_ne_zero_of_ne hz.1 ) );
  · erw [ deriv_mul ];
    · rw [ div_add_div ] <;> norm_num [ sub_ne_zero.mpr hz.1 ];
      · rfl;
      · exact zpow_ne_zero _ ( sub_ne_zero_of_ne hz.1 );
      · exact Finset.prod_ne_zero_iff.mpr fun x hx => zpow_ne_zero _ <| sub_ne_zero_of_ne <| by aesop;
    · rcases k : d u with ( _ | k ) <;> simp_all +decide;
      exact DifferentiableAt.inv ( DifferentiableAt.pow ( differentiableAt_id.sub_const _ ) _ ) ( pow_ne_zero _ ( sub_ne_zero_of_ne hz.1 ) );
    · have h_diff : ∀ u ∈ S, DifferentiableAt ℂ (fun x => (x - u) ^ d u) z := by
        intro u hu; rcases d_u : d u with ( _ | _ ) <;> simp_all +decide;
        exact DifferentiableAt.inv ( DifferentiableAt.pow ( differentiableAt_id.sub_const _ ) _ ) ( pow_ne_zero _ ( sub_ne_zero_of_ne <| by aesop ) );
      have h_prod_diff : ∀ {T : Finset ℂ}, (∀ u ∈ T, DifferentiableAt ℂ (fun x => (x - u) ^ d u) z) → DifferentiableAt ℂ (∏ u ∈ T, (fun x => (x - u) ^ d u)) z := by
        intros T hT; induction T using Finset.induction <;> simp_all +decide [Finset.prod_insert];
      exact h_prod_diff h_diff

/-! ## Circle integral of n/(w-a) -/

lemma circleIntegral_intMul_inv_sub {R : ℝ} {a : ℂ} {n : ℤ}
    (hR : 0 < R) (ha_not_sphere : ‖a‖ ≠ R) :
    ∮ w in C(0, R), (↑n * (w - a)⁻¹) =
      if a ∈ ball (0 : ℂ) R then ↑n * (2 * ↑Real.pi * I) else 0 := by
  split_ifs with h₁;
  · rw [ circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball ] ; aesop;
  · apply_rules [ @Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable ];
    any_goals exact Set.countable_singleton a;
    · positivity;
    · exact continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.mul continuousAt_const ( ContinuousAt.inv₀ ( continuousAt_id.sub continuousAt_const ) ( sub_ne_zero_of_ne <| by rintro rfl; exact h₁ <| by simpa using hz.out.lt_of_ne <| by aesop ) );
    · exact fun z hz => DifferentiableAt.const_mul ( DifferentiableAt.inv ( differentiableAt_id.sub_const a ) ( sub_ne_zero_of_ne hz.2 ) ) _

/-! ## Divisor support is inside ball for NF functions nonvanishing on sphere -/

lemma divisor_support_subset_ball {f : ℂ → ℂ} {R : ℝ}
    (_hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hfS : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    (divisor f (closedBall 0 R)).support ⊆ ball 0 R := by
  intro z hz; by_cases h : z ∈ ball 0 R <;> simp_all +decide;
  contrapose! hz; simp_all +decide;
  by_cases h : z ∈ closedBall 0 R <;> simp_all +decide;
  rw [ divisor_apply ];
  · nontriviality;
    rw [ show meromorphicOrderAt f z = 0 from _ ] ; aesop;
    have h_order_zero : f z ≠ 0 := by
      exact hfS z ( le_antisymm h hz );
    nontriviality;
    exact (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf trivial)).mpr h_order_zero
  · have h_meromorphic : MeromorphicOn f univ := by
      exact hf.meromorphicOn;
    exact fun z _ => h_meromorphic z trivial;
  · simpa using h

/-! ## f equals factored form on sphere -/

/-
On the sphere, f equals φ·g where φ is the factored rational and g is analytic nonvanishing.
-/
lemma sphere_eq_factored {f g : ℂ → ℂ} {R : ℝ} {D : Function.locallyFinsuppWithin (closedBall 0 R) ℤ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hfS : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0)
    (hg_an : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hg_nz : ∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0)
    (hD : D = divisor f (closedBall 0 R))
    (hS_ball : D.support ⊆ ball 0 R)
    (hS_fin : D.support.Finite)
    (h_eq : f =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)] (∏ᶠ u, (· - u) ^ D u) • g)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
    f z = (∏ u ∈ hS_fin.toFinset, (z - u) ^ D u) * g z := by
  -- Since $f =ᶠ[CODISCRETE] (\prodᶠ u, (fun x => x - u) ^ D u) • g$ and $f$ is continuous at $z$, we can apply the fact that the limit of a continuous function is unique.
  have h_lim_eq : Filter.Tendsto f (nhdsWithin z (closedBall 0 R \ {z})) (nhds ((∏ᶠ u, (fun x => x - u) ^ D u) z * g z)) := by
    have h_lim : ∀ᶠ w in nhdsWithin z (closedBall 0 R \ {z}), f w = (∏ᶠ u, (fun x => x - u) ^ D u) w * g w := by
      rw [ Filter.EventuallyEq, codiscreteWithin ] at h_eq;
      simp_all +decide [ eventually_nhdsWithin_iff ];
    rw [ Filter.tendsto_congr' h_lim ];
    refine' Filter.Tendsto.mul _ _;
    · have h_lim : ∀ᶠ w in nhdsWithin z (closedBall 0 R \ {z}), (∏ᶠ u, (fun x => x - u) ^ D u) w = ∏ u ∈ hS_fin.toFinset, (w - u) ^ D u := by
        refine' Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => _;
        rw [ finprod_eq_prod_of_mulSupport_subset ];
        rotate_left;
        exact hS_fin.toFinset;
        · intro u hu; contrapose! hu; aesop;
        · simp +decide [ Finset.prod_apply ];
      rw [ Filter.tendsto_congr' h_lim ];
      refine' tendsto_nhdsWithin_of_tendsto_nhds _;
      refine' ContinuousAt.tendsto _ |> fun h => h.trans _;
      · refine' tendsto_finset_prod _ fun u hu => _;
        rcases Int.eq_nat_or_neg ( D u ) with ⟨ k, hk | hk ⟩ <;> norm_num [ hk ];
        · exact ContinuousAt.pow ( continuousAt_id.sub continuousAt_const ) _;
        · refine' Filter.Tendsto.inv₀ _ _;
          · exact Continuous.tendsto ( by continuity ) _;
          · simp +zetaDelta at *;
            grind +qlia;
      · rw [ finprod_eq_prod_of_mulSupport_subset ];
        rotate_left;
        exact hS_fin.toFinset;
        · intro x hx; contrapose! hx; simp_all +decide;
        · simp +decide [ Finset.prod_apply ];
    · exact hg_an.continuousOn.continuousWithinAt ( by aesop ) |> fun h => h.mono_left <| nhdsWithin_mono _ <| by aesop_cat;
  have h_cont : ContinuousAt f z := by
    have h_cont : AnalyticAt ℂ f z := by
      have h_cont : meromorphicOrderAt f z = 0 := by
        have h_lim_eq : f z ≠ 0 := by
          exact hfS z ( by simpa using hz );
        exact (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf trivial)).mpr h_lim_eq
      have h_cont : meromorphicOrderAt f z ≥ 0 := by
        exact h_cont.ge;
      exact (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf trivial)).mp h_cont;
    exact h_cont.continuousAt;
  convert tendsto_nhds_unique ( h_cont.mono_left <| nhdsWithin_le_nhds ) h_lim_eq using 1;
  · rw [ finprod_eq_prod_of_mulSupport_subset ];
    rotate_left;
    exact hS_fin.toFinset;
    · intro x hx; contrapose! hx; simp_all +decide;
    · simp +decide [ Finset.prod_apply ];
  · refine' mem_closure_iff_clusterPt.mp _;
    rw [ Metric.mem_closure_iff ] ; norm_num [ hz ];
    intro ε hε;
    -- Choose $b$ such that $b = z \cdot (1 - \delta)$ for some small $\delta > 0$.
    obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ > 0, δ < ε / (2 * R) ∧ δ < 1 := by
      exact ⟨ Min.min ( ε / ( 2 * R ) / 2 ) ( 1 / 2 ), lt_min ( div_pos ( div_pos hε ( mul_pos zero_lt_two hR ) ) zero_lt_two ) ( by norm_num ), min_lt_of_left_lt ( by linarith [ div_pos hε ( mul_pos zero_lt_two hR ) ] ), min_lt_of_right_lt ( by norm_num ) ⟩;
    refine' ⟨ z * ( 1 - δ ), _, _ ⟩ <;> norm_num [ abs_of_pos hR, hδ_pos, hδ_lt ];
    · norm_cast ; norm_num [ show ‖z‖ = R by simpa using hz ];
      exact ⟨ mul_le_of_le_one_right hR.le ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ), by rw [ mul_comm ] ; exact fun h => by norm_num [ show z ≠ 0 from by rintro rfl; norm_num at hz; linarith ] at h; norm_cast at h; linarith ⟩;
    · norm_num [ mul_sub, dist_eq_norm ];
      rw [ abs_of_pos hδ_pos ] ; nlinarith [ mul_div_cancel₀ ε ( by positivity : ( 2 * R ) ≠ 0 ), show ‖z‖ = R from by simpa using hz ]

/-! ## Main argument principle -/

lemma argument_principle {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hfS : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0)
    (hsupp : (divisor f (closedBall 0 R)).support.Finite) :
    (2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, R), deriv f w / f w =
      ↑(∑ᶠ z, divisor f (closedBall 0 R) z) := by
  set D := divisor f (closedBall 0 R) with hD_def
  have hD_ball : D.support ⊆ ball 0 R := divisor_support_subset_ball hR hf hfS
  -- Step 1: Factor f
  obtain ⟨g, hg_an, hg_nz, h_cdw⟩ := (show MeromorphicOn f (closedBall 0 R) from
      fun z hz => hf.meromorphicOn z (Set.mem_univ z)).extract_zeros_poles
    (fun u => hord u) hsupp
  -- Step 2: On sphere, f = φ*g
  have h_sphere_val : ∀ z ∈ sphere (0 : ℂ) R,
      f z = (∏ u ∈ hsupp.toFinset, (z - u) ^ D u) * g z :=
    sphere_eq_factored hR hf hfS hg_an (λ z hz => hg_nz ⟨z, hz⟩) rfl hD_ball hsupp h_cdw
  -- Step 3: On sphere, f'/f = φ'/φ + g'/g
  have h_logderiv : ∀ z ∈ sphere (0 : ℂ) R,
      deriv f z / f z =
        (∑ u ∈ hsupp.toFinset, (↑(D u) * (z - u)⁻¹)) + deriv g z / g z := by
    intro z hz
    have hz_norm : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
    -- z is on sphere, so z ∉ support (support ⊆ ball)
    have hz_not_supp : z ∉ hsupp.toFinset := by
      intro h
      have := hD_ball (hsupp.mem_toFinset.mp h)
      rw [mem_ball, dist_zero_right] at this
      linarith
    -- f is analytic at z
    have hf_an : AnalyticAt ℂ f z :=
      analyticAt_of_NF_nonvanishing (hf (Set.mem_univ z)) (hfS z hz_norm)
    -- Each factor (· - u) ^ D u is differentiable/analytic at z
    set φ := fun w => ∏ u ∈ hsupp.toFinset, (w - u) ^ D u with hφ_def
    have hz_ne_u : ∀ u ∈ hsupp.toFinset, z ≠ u := by
      intro u hu heq; subst heq; exact absurd (hD_ball (hsupp.mem_toFinset.mp hu))
        (by rw [mem_ball, dist_zero_right]; linarith)
    have hφ_an : AnalyticAt ℂ φ z := by
      -- Since each factor (w - u)^(D u) is analytic at z (because z ≠ u and D u is an integer), their product is also analytic at z.
      have h_factor_analytic : ∀ u ∈ hsupp.toFinset, AnalyticAt ℂ (fun w => (w - u) ^ D u) z := by
        intro u hu;
        rcases Int.eq_nat_or_neg ( D u ) with ⟨ k, hk | hk ⟩ <;> norm_num [ hk ];
        · fun_prop;
        · exact AnalyticAt.inv ( by fun_prop ) ( pow_ne_zero _ ( sub_ne_zero_of_ne ( hz_ne_u u hu ) ) );
      exact Finset.analyticAt_fun_prod hsupp.toFinset h_factor_analytic
    have hφ_diff : DifferentiableAt ℂ φ z := hφ_an.differentiableAt
    have hg_an_z : AnalyticAt ℂ g z := hg_an z (by rw [mem_closedBall, dist_zero_right]; linarith)
    -- φ*g is analytic at z
    have hφg_an : AnalyticAt ℂ (fun w => φ w * g w) z := hφ_an.mul hg_an_z
    -- Codiscrete agreement: f = φ*g on nhdsWithin z (closedBall \ {z})
    have h_agree_nhdsWithin : f =ᶠ[nhdsWithin z (closedBall 0 R \ {z})] (fun w => φ w * g w) := by
      have h_codiscrete : nhdsWithin z (closedBall 0 R \ {z}) ≤ codiscreteWithin (closedBall 0 R) := by
        refine' le_iSup₂_of_le z _ _;
        · exact mem_closedBall_zero_iff.mpr hz_norm.le;
        · exact le_rfl;
      convert h_cdw.filter_mono h_codiscrete using 1;
      ext w; simp [hφ_def];
      rw [ finprod_eq_prod_of_mulSupport_subset ];
      any_goals exact hsupp.toFinset;
      · simp +decide [ Finset.prod_apply ];
        exact Or.inl rfl;
      · intro x hx; contrapose! hx; simp_all +decide;
    -- NeBot: z is a limit point of closedBall \ {z}
    have h_nebot : (nhdsWithin z (closedBall (0:ℂ) R \ {z})).NeBot := by
      refine' mem_closure_iff_clusterPt.mp _;
      rw [ Metric.mem_closure_iff ];
      intro ε ε_pos;
      -- Choose $b$ such that $b = z \cdot (1 - \delta)$ for some small $\delta > 0$.
      obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ > 0, δ < ε / R ∧ δ < 1 := by
        exact ⟨ Min.min ( ε / R / 2 ) ( 1 / 2 ), lt_min ( div_pos ( div_pos ε_pos hR ) zero_lt_two ) ( by norm_num ), min_lt_of_left_lt ( by linarith [ div_pos ε_pos hR ] ), min_lt_of_right_lt ( by norm_num ) ⟩;
      refine' ⟨ z * ( 1 - δ ), _, _ ⟩ <;> norm_num [ hz_norm, hδ_pos, hδ_lt ];
      · norm_cast;
        exact ⟨ mul_le_of_le_one_right hR.le ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ), by rw [ mul_comm ] ; exact fun h => by norm_num [ show z ≠ 0 from by rintro rfl; norm_num at hz_norm; linarith ] at h; linarith ⟩;
      · norm_num [ mul_sub, hz_norm ];
        rw [ abs_of_pos hδ_pos ] ; nlinarith [ mul_div_cancel₀ ε hR.ne' ]
    -- Identity theorem: f = φ*g on nhds z
    have h_eq_nhds : f =ᶠ[nhds z] (fun w => φ w * g w) :=
      analyticAt_eventuallyEq_of_nhdsWithin hf_an hφg_an h_nebot (fun x hx => hx.2) h_agree_nhdsWithin
    -- Derivatives are equal
    have h_deriv_eq : deriv f z = deriv (fun w => φ w * g w) z :=
      h_eq_nhds.deriv_eq
    -- Product rule
    have h_prod_rule : deriv (fun w => φ w * g w) z = deriv φ z * g z + φ z * deriv g z :=
      (hφ_diff.hasDerivAt.mul hg_an_z.differentiableAt.hasDerivAt).deriv
    -- Values
    have hfz : f z ≠ 0 := hfS z hz_norm
    have hgz : g z ≠ 0 := hg_nz ⟨z, by rw [mem_closedBall, dist_zero_right]; linarith⟩
    have hφz : φ z ≠ 0 := by
      simp only [hφ_def, Finset.prod_ne_zero_iff]
      intro u hu
      exact zpow_ne_zero _ (sub_ne_zero_of_ne (hz_ne_u u hu))
    have hfz_eq : f z = φ z * g z := h_sphere_val z hz
    -- logDeriv of φ
    have h_logderiv_φ : deriv φ z / φ z = ∑ u ∈ hsupp.toFinset, ↑(D u) * (z - u)⁻¹ := by
      convert logDeriv_finprod_zpow hz_not_supp using 1;
      -- The derivative of a function is equal to itself.
      simp [hφ_def];
      congr! 2;
      ext w; simp +decide [ Finset.prod_apply ] ;
    -- Algebra: deriv f z / f z = deriv φ z / φ z + deriv g z / g z
    have h_algebra : (deriv φ z * g z + φ z * deriv g z) / (φ z * g z) =
        deriv φ z / φ z + deriv g z / g z := by
      field_simp
    rw [h_deriv_eq, h_prod_rule, hfz_eq, h_algebra, h_logderiv_φ]
  -- Step 4: ∮ f'/f = ∮ ∑ D(u)/(z-u) + ∮ g'/g
  have h_int_split : ∮ w in C(0, R), deriv f w / f w =
      (∑ u ∈ hsupp.toFinset, ∮ w in C(0, R), (↑(D u) * (w - u)⁻¹)) +
        ∮ w in C(0, R), deriv g w / g w := by
    have h_integrable : ContinuousOn (fun w => deriv g w / g w) (Metric.sphere 0 R) ∧ ∀ u ∈ hsupp.toFinset, ContinuousOn (fun w => ↑(D u) * (w - u)⁻¹) (Metric.sphere 0 R) := by
      refine' ⟨ _, _ ⟩;
      · refine' ContinuousOn.div _ _ _;
        · have h_cont_deriv : AnalyticOnNhd ℂ (deriv g) (closedBall 0 R) := by
            exact hg_an.deriv;
          exact h_cont_deriv.continuousOn.mono ( sphere_subset_closedBall );
        · exact hg_an.continuousOn.mono ( sphere_subset_closedBall );
        · exact fun z hz => hg_nz ⟨ z, by simpa using hz.le ⟩;
      · intro u hu;
        refine' continuousOn_of_forall_continuousAt fun w hw => ContinuousAt.mul continuousAt_const ( ContinuousAt.inv₀ ( continuousAt_id.sub continuousAt_const ) _ );
        simp +zetaDelta at *;
        exact sub_ne_zero_of_ne <| by rintro rfl; exact absurd hw <| ne_of_lt <| hD_ball _ hu;
    -- Apply the linearity of the integral.
    have h_integral_split : (∮ w in C(0, R), ∑ u ∈ hsupp.toFinset, ↑(D u) * (w - u)⁻¹) = ∑ u ∈ hsupp.toFinset, (∮ w in C(0, R), ↑(D u) * (w - u)⁻¹) := by
      simp +decide [circleIntegral];
      rw [ intervalIntegral.integral_congr fun x hx => by rw [ Finset.mul_sum _ _ _ ] ];
      rw [ intervalIntegral.integral_finset_sum ];
      intro u hu;
      apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' ContinuousOn.mul _ _;
      · fun_prop;
      · refine' ContinuousOn.mul continuousOn_const ( ContinuousOn.inv₀ _ _ );
        · fun_prop;
        · intro x hx; specialize hD_ball ( show u ∈ D.support from by simpa using hu ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact ne_of_apply_ne Norm.norm ( by norm_num [ abs_of_pos hR ] ; linarith );
    rw [ ← h_integral_split, ← circleIntegral.integral_add ];
    · refine' intervalIntegral.integral_congr_ae _;
      filter_upwards [ ] with x hx using by rw [ h_logderiv _ <| by simp +decide [ abs_of_pos hR ] ] ;
    · apply_rules [ ContinuousOn.circleIntegrable ];
      · linarith;
      · exact continuousOn_finset_sum _ fun u hu => h_integrable.2 u hu;
    · apply_rules [ ContinuousOn.circleIntegrable, h_integrable.1 ];
      linarith
  -- Step 5: ∮ g'/g = 0
  have h_int_g : ∮ w in C(0, R), deriv g w / g w = 0 :=
    circleIntegral_logDeriv_analytic_nonvanishing hR hg_an (λ z hz => hg_nz ⟨z, hz⟩)
  -- Step 6: Each ∮ D(u)/(w-u) = D(u) * 2πi
  have h_int_res : ∀ u ∈ hsupp.toFinset, ∮ w in C(0, R), (↑(D u) * (w - u)⁻¹) =
      ↑(D u) * (2 * ↑Real.pi * I) := by
    intro u hu
    rw [circleIntegral.integral_const_mul]
    congr 1
    exact circleIntegral.integral_sub_inv_of_mem_ball (hD_ball (hsupp.mem_toFinset.mp hu))
  -- Combine
  rw [h_int_split, h_int_g, add_zero, Finset.sum_congr rfl h_int_res]
  rw [finsum_eq_sum_of_support_subset _ (fun x hx => hsupp.mem_toFinset.mpr hx)]
  -- Final algebra: (2πi)⁻¹ • ∑ D(x) * (2πi) = ↑(∑ D(x))
  have h2pi : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [smul_eq_mul, ← Finset.sum_mul]
  field_simp
  push_cast; ring

end

end Submission.Helpers
