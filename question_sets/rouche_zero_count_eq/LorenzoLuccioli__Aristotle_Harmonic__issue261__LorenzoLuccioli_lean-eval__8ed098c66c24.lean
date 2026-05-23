/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: rouche_zero_count_eq
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 8ed098c66c24d6da96ea1e7de6489aa4aaf30a60
issue_number: 261
-/
import Mathlib
import Submission.Helpers
import Submission.ArgPrinciple

open MeromorphicOn Complex Topology Filter

namespace Submission

theorem rouche_zero_count_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
  have hf_mero : MeromorphicOn f Set.univ := hf.meromorphicOn
  have hgN := analyticOn_univ.mp hg
  have hfS : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0 := Helpers.sphere_nonvanishing_of_bound hbound
  have hfgS : ∀ z : ℂ, ‖z‖ = R → (f + g) z ≠ 0 := Helpers.fg_sphere_nonvanishing hbound
  have hfnz : f (⟨R, 0⟩ : ℂ) ≠ 0 := hfS _ (Helpers.norm_mk_eq hR)
  have hf_ord : ∀ z, meromorphicOrderAt f z ≠ ⊤ :=
    Helpers.order_ne_top_of_NF_nonvanishing hf _ hfnz
  have hfg_ord : ∀ z, meromorphicOrderAt (f + g) z ≠ ⊤ :=
    Helpers.order_fg_ne_top_of_NF hR hf hg hbound
  have hsupp_f : (divisor f (Metric.closedBall 0 R)).support.Finite :=
    Helpers.divisor_closedBall_support_finite hR hf_mero
  have hfg_mero : MeromorphicOn (f + g) Set.univ :=
    Helpers.meromorphicOn_add_analytic hf_mero hg
  have hsupp_fg : (divisor (f + g) (Metric.closedBall 0 R)).support.Finite :=
    Helpers.divisor_closedBall_support_finite hR hfg_mero
  -- Pole divisors are equal
  have hneg : ∀ z, ((divisor (f + g) (Metric.closedBall 0 R))⁻) z =
      ((divisor f (Metric.closedBall 0 R))⁻) z := by
    intro z
    have h := @negPart_divisor_add_of_analyticNhdOn_right ℂ _ (Metric.closedBall 0 R) ℂ _ _ f g
      (fun z hz => hf_mero z (Set.mem_univ z)) (fun z hz => hgN z (Set.mem_univ z))
    exact congrFun (congrArg _ h) z
  -- Equal circle integrals
  have hint : ∮ w in C(0, R), deriv (f + g) w / (f + g) w =
      ∮ w in C(0, R), deriv f w / f w :=
    Helpers.rouche_integral_eq hR hf hf_ord hg hbound
  -- Argument principle for f
  have hap_f := Helpers.argument_principle hR hf hf_ord hfS hsupp_f
  -- Argument principle for f+g (via toMeromorphicNFOn)
  have hap_fg : (2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, R), deriv (f + g) w / (f + g) w =
      ↑(∑ᶠ z, divisor (f + g) (Metric.closedBall 0 R) z) := by
    -- Use toMeromorphicNFOn to normalize f+g
    set h := toMeromorphicNFOn (f + g) Set.univ with hh_def
    -- h is MeromorphicNFOn
    have hh_nf : MeromorphicNFOn h Set.univ := meromorphicNFOn_toMeromorphicNFOn (f + g) Set.univ
    -- h agrees with f+g codiscreetly
    have hh_codiscrete : (f + g) =ᶠ[Filter.codiscreteWithin Set.univ] h :=
      toMeromorphicNFOn_eqOn_codiscrete hfg_mero
    -- meromorphicOrderAt h = meromorphicOrderAt (f+g) at every point
    have hh_ord : ∀ z, meromorphicOrderAt h z = meromorphicOrderAt (f + g) z := by
      exact fun z => meromorphicOrderAt_toMeromorphicNFOn hfg_mero trivial
    -- h orders are not ⊤
    have hh_ord_ne_top : ∀ z, meromorphicOrderAt h z ≠ ⊤ := by
      intro z; rw [hh_ord]; exact hfg_ord z
    -- On sphere, f+g is analytic, so h = f+g
    have hh_sphere_eq : ∀ z : ℂ, ‖z‖ = R → h z = (f + g) z := by
      -- Since $h$ is equal to $f + g$ almost everywhere and $f + g$ is analytic on the sphere, $h$ must also be analytic on the sphere.
      have h_analytic : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ (f + g) z := by
        have h_analytic : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ f z := by
          exact fun z a => Helpers.analyticAt_of_NF_nonvanishing (hf trivial) (hfS z a);
        exact fun z hz => AnalyticAt.add ( h_analytic z hz ) ( hgN z ( Set.mem_univ z ) );
      intro z hz
      have h_eq : h z = (f + g) z := by
        have h_nf : MeromorphicNFAt (f + g) z := by
          exact AnalyticAt.meromorphicNFAt (h_analytic z hz)
        have h_eq : toMeromorphicNFAt (f + g) z = f + g := by
          exact toMeromorphicNFAt_eq_self.mpr h_nf;
        convert congr_arg ( fun f => f z ) h_eq using 1;
        apply toMeromorphicNFOn_eq_toMeromorphicNFAt;
        · exact hfg_mero;
        · trivial;
      exact h_eq
    -- h doesn't vanish on sphere
    have hh_sphere_nz : ∀ z : ℂ, ‖z‖ = R → h z ≠ 0 := by
      intro z hz; rw [hh_sphere_eq z hz]; exact hfgS z hz
    -- Divisor of h on closedBall = divisor of (f+g) on closedBall
    have hh_div : divisor h (Metric.closedBall 0 R) = divisor (f + g) (Metric.closedBall 0 R) := by
      -- By definition of divisor, we have that the divisor of h is equal to the divisor of f + g.
      ext z
      simp [divisor, hh_ord];
      -- Since h is MeromorphicOn h (Metric.closedBall 0 R) and z is in the closed ball, the if condition holds, and the value is (meromorphicOrderAt (f + g) z).untop₀.
      have hh_mero : MeromorphicOn h (Metric.closedBall 0 R) := by
        exact MeromorphicNFOn.meromorphicOn fun ⦃z⦄ a => hh_nf trivial
      generalize_proofs at *; (
      have hh_eq : MeromorphicOn h (Metric.closedBall 0 R) ↔ MeromorphicOn (f + g) (Metric.closedBall 0 R) := by
        exact (iff_true_right fun x a => hfg_mero x trivial).mpr hh_mero
      generalize_proofs at *; (
      grind +qlia))
    -- Support is finite
    have hh_supp : (divisor h (Metric.closedBall 0 R)).support.Finite := by
      rw [hh_div]; exact hsupp_fg
    -- Apply argument_principle to h
    have hh_ap := Helpers.argument_principle hR hh_nf hh_ord_ne_top hh_sphere_nz hh_supp
    -- Show integral of h'/h = integral of (f+g)'/(f+g)
    have hh_int : ∮ w in C(0, R), deriv h w / h w = ∮ w in C(0, R), deriv (f + g) w / (f + g) w := by
      apply_rules [ circleIntegral.integral_congr ];
      · linarith;
      · intro z hz; simp_all +decide;
        refine' Filter.EventuallyEq.deriv_eq _;
        have h_codiscrete : f + g =ᶠ[codiscreteWithin Set.univ] toMeromorphicNFOn (f + g) Set.univ := by
          exact hh_codiscrete;
        rw [ Filter.EventuallyEq, Filter.Eventually, codiscreteWithin ] at *;
        simp_all +decide [mem_nhdsWithin];
        obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := hh_codiscrete z; filter_upwards [ IsOpen.mem_nhds hu₁ hu₂ ] with x hx; by_cases hx' : x = z <;> simp_all +decide [ Set.subset_def ] ;
    rw [← hh_int, hh_ap, hh_div]
  -- Total divisor sums are equal
  have htot : ∑ᶠ z, divisor (f + g) (Metric.closedBall 0 R) z =
      ∑ᶠ z, divisor f (Metric.closedBall 0 R) z := by
    have h : (2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, R), deriv (f + g) w / (f + g) w =
        (2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, R), deriv f w / f w := by rw [hint]
    rw [hap_fg, hap_f] at h
    exact_mod_cast h
  exact Helpers.posPart_sum_eq_of_negPart_eq_and_total_eq _ _ hsupp_fg hsupp_f hneg htot

end Submission
