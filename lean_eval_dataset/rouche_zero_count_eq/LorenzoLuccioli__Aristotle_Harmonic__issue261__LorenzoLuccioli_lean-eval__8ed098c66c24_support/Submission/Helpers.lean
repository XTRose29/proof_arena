import Mathlib

namespace Submission.Helpers

open MeromorphicOn Complex Topology Filter MeasureTheory Set Metric

noncomputable section

/-! ## Support finiteness -/

lemma divisor_closedBall_support_finite {f : ℂ → ℂ} {R : ℝ}
    (_hR : 0 < R) (_hf : MeromorphicOn f Set.univ) :
    (divisor f (closedBall 0 R)).support.Finite :=
  (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)

/-! ## Simple helper lemmas -/

lemma sphere_nonvanishing_of_bound {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    ∀ z : ℂ, ‖z‖ = R → f z ≠ 0 := by
  exact fun z hz h => absurd (hbound z hz) (by norm_num [h])

lemma meromorphicOn_add_analytic {f g : ℂ → ℂ}
    (hf : MeromorphicOn f Set.univ) (hg : AnalyticOn ℂ g Set.univ) :
    MeromorphicOn (f + g) Set.univ := by
  intro z hz
  exact (hf z hz).add ((analyticOn_univ.mp hg) z hz).meromorphicAt

lemma fg_sphere_nonvanishing {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    ∀ z : ℂ, ‖z‖ = R → (f + g) z ≠ 0 := by
  intro z hz H
  have hb := hbound z hz
  have : ‖f z‖ ≤ ‖g z‖ := by
    have h1 : f z = (f + g) z - g z := by simp [Pi.add_apply]
    calc ‖f z‖ = ‖(f + g) z - g z‖ := by rw [h1]
    _ ≤ ‖(f + g) z‖ + ‖g z‖ := norm_sub_le _ _
    _ = ‖g z‖ := by simp [H]
  linarith

lemma norm_mk_eq {R : ℝ} (hR : 0 < R) : ‖(⟨R, 0⟩ : ℂ)‖ = R := by
  have : (⟨R, 0⟩ : ℂ) = (R : ℂ) := Complex.ext (by simp) (by simp)
  rw [this, Complex.norm_real]; exact abs_of_pos hR

lemma order_ne_top_of_NF_nonvanishing {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (z₀ : ℂ) (hz₀ : f z₀ ≠ 0) :
    ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
  have hord₀ : meromorphicOrderAt f z₀ ≠ ⊤ := by
    rw [(hf (Set.mem_univ z₀)).meromorphicOrderAt_eq_zero_iff.mpr hz₀]
    exact WithTop.zero_ne_top
  intro z
  exact meromorphicOrderAt_ne_top_of_isPreconnected
    hf.meromorphicOn isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ z) hord₀

lemma order_fg_ne_top_of_NF {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    ∀ z, meromorphicOrderAt (f + g) z ≠ ⊤ := by
  have hgN := analyticOn_univ.mp hg
  set z₀ : ℂ := ⟨R, 0⟩
  have hz₀ : ‖z₀‖ = R := norm_mk_eq hR
  have hfnz : f z₀ ≠ 0 := sphere_nonvanishing_of_bound hbound z₀ hz₀
  have hfgz : (f + g) z₀ ≠ 0 := fg_sphere_nonvanishing hbound z₀ hz₀
  have hf_an : AnalyticAt ℂ f z₀ := by
    have hNF := hf (Set.mem_univ z₀)
    rw [← hNF.meromorphicOrderAt_nonneg_iff_analyticAt]
    rw [hNF.meromorphicOrderAt_eq_zero_iff.mpr hfnz]
  have hfg_an : AnalyticAt ℂ (f + g) z₀ := hf_an.add (hgN z₀ (Set.mem_univ z₀))
  have hord₀ : meromorphicOrderAt (f + g) z₀ ≠ ⊤ := by
    rw [hfg_an.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfgz]
    exact WithTop.zero_ne_top
  intro z
  exact meromorphicOrderAt_ne_top_of_isPreconnected
    (meromorphicOn_add_analytic hf.meromorphicOn hg) isPreconnected_univ
    (Set.mem_univ z₀) (Set.mem_univ z) hord₀

/-! ## Positive/negative part sum decomposition -/

lemma posPart_sum_eq_of_negPart_eq_and_total_eq
    {U : Set ℂ} (D₁ D₂ : Function.locallyFinsuppWithin U ℤ)
    (hfin₁ : D₁.support.Finite) (hfin₂ : D₂.support.Finite)
    (hneg : ∀ z, (D₁⁻) z = (D₂⁻) z)
    (htot : ∑ᶠ z, D₁ z = ∑ᶠ z, D₂ z) :
    ∑ᶠ z, (D₁⁺) z = ∑ᶠ z, (D₂⁺) z := by
  have hdecomp : ∀ D : Function.locallyFinsuppWithin U ℤ, D.support.Finite → ∑ᶠ z, D⁺ z - ∑ᶠ z, D⁻ z = ∑ᶠ z, D z := by
    have hdecomp : ∀ D : Function.locallyFinsuppWithin U ℤ, D.support.Finite → ∀ z, D⁺ z - D⁻ z = D z := by
      simp +decide [ Function.locallyFinsuppWithin.posPart_apply, Function.locallyFinsuppWithin.negPart_apply ];
    intros D hfin
    have hdecomp : ∑ᶠ z, (D⁺ z - D⁻ z) = ∑ᶠ z, D z := by
      exact finsum_congr fun z => hdecomp D hfin z;
    rw [ ← hdecomp, finsum_sub_distrib ];
    · exact hfin.subset fun x hx => by contrapose! hx; aesop;
    · exact hfin.subset fun x hx => by contrapose! hx; aesop;
  simp_all +decide [ sub_eq_iff_eq_add ]

/-! ## Rouché integral invariance helpers -/

lemma analyticAt_of_NF_nonvanishing {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicNFAt f z) (hz : f z ≠ 0) : AnalyticAt ℂ f z := by
  rw [← hf.meromorphicOrderAt_nonneg_iff_analyticAt]
  rw [hf.meromorphicOrderAt_eq_zero_iff.mpr hz]

lemma ratio_in_slitPlane {fz gz : ℂ} (hfz : fz ≠ 0) (hbound : ‖gz‖ < ‖fz‖) :
    (1 + gz / fz) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have h : ‖gz / fz‖ < 1 := by
    rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hfz)).mpr hbound
  have hre : -1 < (gz / fz).re := by
    calc -1 < -‖gz / fz‖ := by linarith
    _ ≤ (gz / fz).re := by linarith [abs_le.mp (Complex.abs_re_le_norm (gz / fz))]
  simp only [Complex.add_re, Complex.one_re]; linarith

/-! ## Analyticity of f on sphere given MeromorphicNFOn + nonvanishing -/

lemma analyticOnNhd_on_sphere_of_NF_nonvanishing {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ) (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    (_hR : 0 < R) :
    AnalyticOnNhd ℂ f (sphere 0 R) ∧ AnalyticOnNhd ℂ (f + g) (sphere 0 R) := by
  have hgN := analyticOn_univ.mp hg
  have hfS := sphere_nonvanishing_of_bound hbound
  constructor
  · intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    exact analyticAt_of_NF_nonvanishing (hf (Set.mem_univ z)) (hfS z hz)
  · intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hfan := analyticAt_of_NF_nonvanishing (hf (Set.mem_univ z)) (hfS z hz)
    exact hfan.add (hgN z (Set.mem_univ z))

/-! ## Circle integral of derivative is zero (FTC) -/

lemma circleIntegral_deriv_eq_zero {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hF : ∀ z ∈ sphere c R, DifferentiableAt ℂ F z) :
    ∮ w in C(c, R), deriv F w = 0 := by
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
  intro z hz
  exact (hF z hz).hasDerivAt.hasDerivWithinAt

/-! ## Differentiability of log ratio -/

lemma differentiableAt_log_ratio {f g : ℂ → ℂ} {z : ℂ}
    (hf_an : AnalyticAt ℂ f z) (hg_an : AnalyticAt ℂ g z)
    (hfz : f z ≠ 0) (hbound_z : ‖g z‖ < ‖f z‖) :
    DifferentiableAt ℂ (fun w => Complex.log ((f + g) w / f w)) z := by
  -- Since $f(z) \neq 0$ and $|g(z)| < |f(z)|$, we have $(f(z) + g(z)) / f(z) \in \text{slitPlane}$.
  have h_log_arg : (f z + g z) / f z ∈ Complex.slitPlane := by
    convert ratio_in_slitPlane hfz hbound_z using 1
    rw [add_div, div_self hfz]
  refine' DifferentiableAt.clog _ _;
  · exact DifferentiableAt.div ( hf_an.differentiableAt.add hg_an.differentiableAt ) hf_an.differentiableAt hfz;
  · exact h_log_arg

/-! ## Derivative of log ratio -/

lemma deriv_log_ratio_eq {f g : ℂ → ℂ} {z : ℂ}
    (hf_an : AnalyticAt ℂ f z) (hg_an : AnalyticAt ℂ g z)
    (hfz : f z ≠ 0) (hfgz : (f + g) z ≠ 0) (hbound_z : ‖g z‖ < ‖f z‖) :
    deriv (fun w => Complex.log ((f + g) w / f w)) z =
      deriv (f + g) z / (f + g) z - deriv f z / f z := by
  convert HasDerivAt.deriv ( HasDerivAt.comp z ( Complex.hasDerivAt_log ?_ ) ( HasDerivAt.div ( DifferentiableAt.hasDerivAt ( show DifferentiableAt ℂ ( f + g ) z from DifferentiableAt.add hf_an.differentiableAt hg_an.differentiableAt ) ) ( DifferentiableAt.hasDerivAt ( show DifferentiableAt ℂ f z from hf_an.differentiableAt ) ) hfz ) ) using 1;
  · simp +decide [hfz, sq, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
    field_simp;
    exact div_sub' hfgz;
  · simp_all +decide [ Complex.slitPlane ];
    norm_num [ Complex.div_re, Complex.div_im ];
    norm_num [ Complex.normSq, Complex.norm_def ] at *;
    rw [ Real.sqrt_lt_sqrt_iff <| by nlinarith ] at hbound_z;
    exact Or.inl ( by rw [ ← add_div, lt_div_iff₀ ] <;> nlinarith [ sq_nonneg ( ( f z |> Complex.re ) + ( g z |> Complex.re ) ), sq_nonneg ( ( f z |> Complex.im ) + ( g z |> Complex.im ) ) ] )

/-! ## Rouché integral invariance -/

lemma rouche_integral_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (_hf_ord : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    ∮ w in C(0, R), deriv (f + g) w / (f + g) w =
      ∮ w in C(0, R), deriv f w / f w := by
  -- Since $f$ and $g$ are analytic on the sphere, their derivatives are also analytic on the sphere.
  have h_deriv_analytic : AnalyticOnNhd ℂ f (sphere 0 R) ∧ AnalyticOnNhd ℂ (f + g) (sphere 0 R) := by
    apply_rules [ analyticOnNhd_on_sphere_of_NF_nonvanishing ];
  -- By the properties of the derivative and the chain rule, we can express the derivative of the logarithm as follows:
  have h_log_deriv : ∀ z ∈ sphere 0 R, deriv (fun w => Complex.log ((f + g) w / f w)) z = deriv (f + g) z / (f + g) z - deriv f z / f z := by
    intro z hz;
    convert deriv_log_ratio_eq _ _ _ _ _ using 1;
    · exact h_deriv_analytic.1 z hz;
    · exact hg.differentiableOn.analyticAt (by simp)
    · exact fun h => absurd ( hbound z ( by simpa using hz ) ) ( by norm_num [ h ] );
    · exact fg_sphere_nonvanishing hbound z ( by simpa using hz );
    · aesop;
  have h_integral_zero : (∮ w in C(0, R), deriv (fun w => Complex.log ((f + g) w / f w)) w) = 0 := by
    apply_rules [ circleIntegral_deriv_eq_zero ];
    intro z hz
    have h_log_diff : DifferentiableAt ℂ (fun w => Complex.log ((f + g) w / f w)) z := by
      have h_nonzero : (f + g) z ≠ 0 ∧ f z ≠ 0 := by
        exact ⟨ fg_sphere_nonvanishing hbound z ( by simpa using hz ), sphere_nonvanishing_of_bound hbound z ( by simpa using hz ) ⟩
      apply differentiableAt_log_ratio;
      · exact h_deriv_analytic.1 z hz;
      · exact hg.differentiableOn.analyticAt (by simp)
      · exact h_nonzero.2;
      · aesop
    exact h_log_diff;
  have h_integral_split : (∮ w in C(0, R), deriv (f + g) w / (f + g) w - deriv f w / f w) = (∮ w in C(0, R), deriv (f + g) w / (f + g) w) - (∮ w in C(0, R), deriv f w / f w) := by
    rw [ circleIntegral.integral_sub ];
    · apply_rules [ ContinuousOn.circleIntegrable ];
      · positivity;
      · refine' ContinuousOn.div _ _ _;
        · exact h_deriv_analytic.2.deriv.continuousOn;
        · exact h_deriv_analytic.2.continuousOn;
        · exact fun z hz => fg_sphere_nonvanishing hbound z ( by simpa using hz );
    · apply_rules [ ContinuousOn.circleIntegrable ];
      · positivity;
      · refine' ContinuousOn.div _ _ _;
        · exact h_deriv_analytic.1.deriv.continuousOn;
        · exact h_deriv_analytic.1.continuousOn;
        · exact fun z hz => by specialize hbound z ( by simpa using hz ) ; contrapose! hbound; aesop;
  rw [ circleIntegral.integral_congr ] at h_integral_zero;
  any_goals tauto;
  · linear_combination' h_integral_split.symm.trans h_integral_zero;
  · linarith

end

end Submission.Helpers
