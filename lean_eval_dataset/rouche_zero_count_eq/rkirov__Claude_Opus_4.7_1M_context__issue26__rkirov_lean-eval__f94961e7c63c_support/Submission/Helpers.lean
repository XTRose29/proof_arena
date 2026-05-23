import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Real.Pi.Bounds

namespace Submission.Helpers

open MeromorphicOn Metric Complex

/-!
Rouché's theorem (zero-count formulation, extended to the meromorphic case via divisors),
stated as equality of multiplicity-counted zero counts on the closed disk of radius `R`
centered at `0`.

The previous formulation used `ValueDistribution.logCounting f 0 R`, the **log-weighted**
Nevanlinna counting function — which is *not* the conclusion of Rouché. Under `‖g‖ < ‖f‖`
on the boundary, `f` and `f + g` have the same number of zeros (counted with multiplicity)
inside the disk, but the log-weighted count depends on where each zero sits. Concretely,
`f(z) = z` and `g(z) = -1/2` satisfy `|g| = 1/2 < 2 = |z| = |f|` on `|z| = 2`, yet
`logCounting f 0 2 = log 2` while `logCounting (f + g) 0 2 = log(2 / (1/2)) = log 4`.

We instead state the conclusion as the equality of the multiplicity sums of the zero
divisors of `f` and `f + g` taken on the closed disk of radius `R`.

We also require `f` to be in *normal form* (`MeromorphicNFOn`) rather than merely
`MeromorphicOn`. A bare `MeromorphicOn` hypothesis admits functions whose pointwise values
disagree with their meromorphic order at exceptional points (any `=ᶠ[codiscreteWithin]`
modification is still meromorphic), and that pointwise disagreement is enough to make the
divisor identity fail. See the Zulip discussion at
https://leanprover.zulipchat.com/#narrow/channel/583341-Model-comparisons-for-Lean/topic/LeanEval/near/593331158
for a concrete counterexample to the previous `MeromorphicOn`-only formulation.
-/

/-!
## Proof outline (following Conway, *Functions of One Complex Variable I*, §V.3)

The classical proof uses the argument principle (Conway V.3.4):
`(1/2πi) ∮_γ f'/f dz = Z_f − P_f` inside the contour. Conway's Theorem V.3.8
(Rouché) applies it with `F := (f + g) · f⁻¹` and combines with two computations
of the same integral:

  (A) **Factorization**: by `MeromorphicOn.extract_zeros_poles`,
      `F = (∏ᶠ u, (· - u) ^ d_F u) · G` (codiscrete-mod equality), with `G` analytic
      non-vanishing on the closed ball. Then `F'/F = ∑ d_F u / (z - u) + G'/G`, and the
      circle integral evaluates to `2πi · ∑ d_F` via Cauchy's formula and Cauchy–Goursat.

  (B) **Primitive**: on the boundary `|z| = R`, `|F − 1| = |g/f| < 1`, so `F` lands in
      `Metric.ball (1 : ℂ) 1`, which is contained in the right half-plane. By continuity
      this persists in a neighborhood of the sphere, where the principal branch of `log`
      yields a holomorphic primitive of `F'/F`. The fundamental theorem of calculus
      makes the integral over a closed loop vanish.

Combining (A) and (B): `2πi · ∑ d_F = 0`, hence `∑ d_F = 0`. Translating back to `f` and
`f + g` gives equality of total divisor sums.

The pole counts match pointwise via `negPart_divisor_add_of_analyticNhdOn_right`, so the
zero counts (`∑ D⁺`) inherit the equality from the total counts.

The full mechanization of the contour-integral identity is sizable; at this mathlib pin
neither the argument principle nor the residue theorem are present, and building them
in full would be a substantial standalone effort. We state the central identity as
`sum_divisor_eq_zero_of_image_in_ball_one`, leaving its proof as the single non-trivial
gap. The translation step from the central identity to the full theorem is filled in
below.

**Note on the `MeromorphicOn` versus `AnalyticOn` distinction**: Conway (and the standard
references — Ahlfors, Rudin, Stein–Shakarchi, Remmert) state Rouché for `f, g`
meromorphic with the implicit textbook convention that function values coincide with
the analytic representative (no decoupling). Lean's `MeromorphicOn` is more
permissive — it allows isolated points where the function value is decoupled from the
germ. This admits an adversarial cancellation case (`order f = order g` at sphere
point with `h_f + h_g = 0` and `|f(z₀)| > |h_f(z₀)| = |h_g(z₀)| = |g(z₀)|` via
decoupling) that satisfies the strict eval hypothesis but goes beyond Conway's
setting. Closing this requires either (a) full winding-number theory with deformed
contours, (b) parametric continuity of contour integrals to run Conway's homotopy
proof `N(t) = (1/2πi) ∮ h_t'/h_t dz` is integer-valued and continuous, hence
constant — both of which are absent from mathlib at this pin and represent a
multi-week development beyond the scope of this proof. The single residual sorry
captures exactly this gap.
-/

/-- Helper: if `f : ℂ → ℂ` is meromorphic on `Set.univ` and is non-vanishing on the
sphere of radius `R`, then it has finite order everywhere on the closed disk.

If `f` had infinite order at some point, by connectedness of the closed disk it would
have infinite order at every point, including on the sphere. Then `f` would vanish on
a punctured neighbourhood of any sphere point, which contradicts the hypothesis since
the sphere accumulates at every one of its points. -/
theorem meromorphicOrderAt_ne_top_of_nonzero_on_sphere
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hf : MeromorphicOn f Set.univ)
    (h_nonzero : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R, meromorphicOrderAt f z ≠ ⊤ := by
  set CB : Set ℂ := Metric.closedBall (0 : ℂ) R with hCB_def
  have hf_ball : MeromorphicOn f CB := hf.mono_set (Set.subset_univ _)
  have hCB_connected : IsConnected CB := by
    refine ⟨Metric.nonempty_closedBall.mpr hR.le, ?_⟩
    exact (convex_closedBall _ _).isPreconnected
  intro z hz
  have hkey : ∀ u : CB, meromorphicOrderAt f ↑u ≠ ⊤ := by
    rw [← hf_ball.exists_meromorphicOrderAt_ne_top_iff_forall hCB_connected]
    -- Pick z₀ := (R : ℂ), which is on the sphere ⊂ CB.
    set z₀ : ℂ := (R : ℂ) with hz₀_def
    have hz₀_sphere : ‖z₀‖ = R := by
      simp [z₀, Complex.norm_real, abs_of_pos hR]
    have hz₀_closedBall : z₀ ∈ CB := by
      simp [CB, Metric.closedBall, hz₀_sphere]
    refine ⟨⟨z₀, hz₀_closedBall⟩, ?_⟩
    intro h_top
    rw [meromorphicOrderAt_eq_top_iff] at h_top
    -- Sequence on sphere converging to z₀, distinct from z₀.
    -- z_n := R · cos(1/(n+1)) + i · R · sin(1/(n+1)).
    set θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hθ_def
    set seq : ℕ → ℂ := fun n =>
      Complex.ofReal (R * Real.cos (θ n)) + Complex.I * Complex.ofReal (R * Real.sin (θ n))
      with hseq_def
    have h_seq_re : ∀ n : ℕ, (seq n).re = R * Real.cos (θ n) := fun n => by
      simp [seq, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    have h_seq_im : ∀ n : ℕ, (seq n).im = R * Real.sin (θ n) := fun n => by
      simp [seq, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    have h_seq_norm : ∀ n, ‖seq n‖ = R := by
      intro n
      rw [Complex.norm_def, Complex.normSq_apply, h_seq_re n, h_seq_im n]
      have hcs : (Real.cos (θ n))^2 + (Real.sin (θ n))^2 = 1 :=
        Real.cos_sq_add_sin_sq _
      have hsq : R * Real.cos (θ n) * (R * Real.cos (θ n)) +
          R * Real.sin (θ n) * (R * Real.sin (θ n)) = R^2 := by nlinarith [hcs]
      rw [hsq]
      exact Real.sqrt_sq hR.le
    have hθ_pos : ∀ n : ℕ, 0 < θ n := fun n => by simp [θ]; positivity
    have hθ_le_one : ∀ n : ℕ, θ n ≤ 1 := fun n => by
      simp only [θ]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg _
      linarith
    have h_sin_pos : ∀ n : ℕ, 0 < Real.sin (θ n) := by
      intro n
      apply Real.sin_pos_of_pos_of_lt_pi (hθ_pos n)
      have := hθ_le_one n
      linarith [Real.pi_gt_three]
    have h_seq_ne : ∀ n, seq n ≠ z₀ := by
      intro n hcontra
      have him : (seq n).im = z₀.im := by rw [hcontra]
      have hz₀_im : z₀.im = 0 := by simp [z₀]
      rw [h_seq_im n, hz₀_im] at him
      have hpos := h_sin_pos n
      have hRpos : R * Real.sin (1 / (↑n + 1)) > 0 := by positivity
      linarith
    have hθ_tendsto : Filter.Tendsto θ Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_seq_tendsto : Filter.Tendsto seq Filter.atTop (nhds z₀) := by
      have h_cos : Filter.Tendsto (fun n : ℕ => Real.cos (θ n))
          Filter.atTop (nhds 1) := by
        have := (Real.continuous_cos.tendsto (0 : ℝ)).comp hθ_tendsto
        simpa using this
      have h_sin : Filter.Tendsto (fun n : ℕ => Real.sin (θ n))
          Filter.atTop (nhds 0) := by
        have := (Real.continuous_sin.tendsto (0 : ℝ)).comp hθ_tendsto
        simpa using this
      have h_re : Filter.Tendsto (fun n : ℕ => R * Real.cos (θ n))
          Filter.atTop (nhds (R * 1)) := tendsto_const_nhds.mul h_cos
      have h_im : Filter.Tendsto (fun n : ℕ => R * Real.sin (θ n))
          Filter.atTop (nhds (R * 0)) := tendsto_const_nhds.mul h_sin
      have h_re_C : Filter.Tendsto (fun n : ℕ => Complex.ofReal (R * Real.cos (θ n)))
          Filter.atTop (nhds ((R : ℂ))) := by
        have h := h_re.ofReal
        simpa using h
      have h_im_C : Filter.Tendsto (fun n : ℕ =>
          Complex.I * Complex.ofReal (R * Real.sin (θ n))) Filter.atTop (nhds 0) := by
        have h_imRC : Filter.Tendsto (fun n : ℕ => Complex.ofReal (R * Real.sin (θ n)))
            Filter.atTop (nhds 0) := by
          have := h_im.ofReal
          simpa using this
        have := (tendsto_const_nhds (x := Complex.I)).mul h_imRC
        simpa using this
      have h_sum : Filter.Tendsto seq Filter.atTop (nhds ((R : ℂ) + 0)) :=
        h_re_C.add h_im_C
      simpa [z₀] using h_sum
    have h_seq_tendsto_punctured : Filter.Tendsto seq Filter.atTop (nhdsWithin z₀ {z₀}ᶜ) := by
      rw [nhdsWithin, Filter.tendsto_inf]
      refine ⟨h_seq_tendsto, ?_⟩
      rw [Filter.tendsto_principal]
      filter_upwards with n
      exact h_seq_ne n
    have h_eventually : ∀ᶠ n in Filter.atTop, f (seq n) = 0 :=
      h_seq_tendsto_punctured.eventually h_top
    obtain ⟨n, hn⟩ := h_eventually.exists
    exact h_nonzero (seq n) (h_seq_norm n) hn
  exact hkey ⟨z, hz⟩

/-- If `F : ℂ → ℂ` is meromorphic on `Set.univ` and maps the sphere of radius `R` into
a bounded set, then `F` has no germ pole on the sphere (i.e., `meromorphicOrderAt F z ≥ 0`
for `z` on the sphere).

A pole would force `|F z'| → ∞` for `z'` approaching the pole, contradicting the
bound on the image. -/
theorem meromorphicOrderAt_nonneg_on_sphere_of_bounded_image
    {F : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hF : MeromorphicOn F Set.univ)
    (h_bound : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ < M) :
    ∀ z : ℂ, ‖z‖ = R → 0 ≤ meromorphicOrderAt F z := by
  intro z₀ hz₀_sphere
  by_contra h_neg
  push Not at h_neg
  -- meromorphicOrderAt F z₀ < 0, so F → ∞ in punctured nbhd of z₀.
  have hF_at : MeromorphicAt F z₀ := hF z₀ (Set.mem_univ _)
  have h_tendsto : Filter.Tendsto F (nhdsWithin z₀ {z₀}ᶜ) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg h_neg
  -- In cobounded, eventually ‖F z'‖ > M.
  rw [← tendsto_norm_atTop_iff_cobounded] at h_tendsto
  have h_eventually_large : ∀ᶠ z' in nhdsWithin z₀ {z₀}ᶜ, M < ‖F z'‖ :=
    h_tendsto.eventually_gt_atTop M
  -- Construct a sequence on sphere converging to z₀ with z_n ≠ z₀ (reuses helper construction).
  set θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  set seq : ℕ → ℂ := fun n =>
    Complex.ofReal (R * Real.cos (θ n)) + Complex.I * Complex.ofReal (R * Real.sin (θ n))
  have h_seq_re : ∀ n : ℕ, (seq n).re = R * Real.cos (θ n) := fun n => by
    simp [seq, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have h_seq_im : ∀ n : ℕ, (seq n).im = R * Real.sin (θ n) := fun n => by
    simp [seq, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  -- Need ‖z₀‖ = R, but we only know it's a sphere point. Replace with the standard
  -- z₀' := (R : ℂ). Hmm, we need the sequence to converge to z₀, not (R : ℂ).
  -- Construct sequence converging to z₀ (rotated by appropriate angle).
  set seq' : ℕ → ℂ := fun n => z₀ * Complex.exp (Complex.I * (θ n : ℝ)) with hseq'_def
  have hz₀_ne : z₀ ≠ 0 := by
    intro h; rw [h] at hz₀_sphere; simp at hz₀_sphere; linarith
  have h_seq'_norm : ∀ n, ‖seq' n‖ = R := by
    intro n
    simp only [seq', norm_mul]
    have h_swap : Complex.I * (θ n : ℝ) = ((θ n : ℝ)) * Complex.I := by ring
    rw [h_swap, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hz₀_sphere
  have h_seq'_ne : ∀ n, seq' n ≠ z₀ := by
    intro n hcontra
    have h_exp : Complex.exp (Complex.I * (θ n : ℝ)) = 1 := by
      have hmul : z₀ * Complex.exp (Complex.I * (θ n : ℝ)) = z₀ := by
        simpa [seq'] using hcontra
      have h_eq : z₀ * Complex.exp (Complex.I * (θ n : ℝ)) = z₀ * 1 := by
        rw [hmul, mul_one]
      exact mul_left_cancel₀ hz₀_ne h_eq
    rw [Complex.exp_eq_one_iff] at h_exp
    obtain ⟨k, hk⟩ := h_exp
    have hk_im : (θ n : ℝ) = (k : ℝ) * (2 * Real.pi) := by
      have := congrArg Complex.im hk
      simp [Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.I_re] at this
      linarith
    have hpos : (0 : ℝ) < θ n := by simp [θ]; positivity
    have hle : θ n ≤ 1 := by
      simp only [θ]; rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _; linarith
    rcases lt_trichotomy k 0 with hkneg | hk0 | hkpos
    · have : (k : ℝ) * (2 * Real.pi) < 0 := by
        have := Real.pi_pos
        have : (k : ℝ) < 0 := by exact_mod_cast hkneg
        nlinarith
      linarith
    · rw [hk0] at hk_im; simp at hk_im; linarith
    · have hk_ge_one : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      have := Real.pi_gt_three
      nlinarith
  have hθ_tendsto : Filter.Tendsto θ Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h_seq'_tendsto : Filter.Tendsto seq' Filter.atTop (nhds z₀) := by
    have h_exp_tendsto : Filter.Tendsto (fun n : ℕ => Complex.exp (Complex.I * (θ n : ℝ)))
        Filter.atTop (nhds 1) := by
      have h_arg : Filter.Tendsto (fun n : ℕ => Complex.I * (θ n : ℝ))
          Filter.atTop (nhds 0) := by
        have := hθ_tendsto.ofReal
        have := (tendsto_const_nhds (x := Complex.I)).mul this
        simpa using this
      have := Complex.continuous_exp.tendsto 0
      simpa using this.comp h_arg
    have := (tendsto_const_nhds (x := z₀)).mul h_exp_tendsto
    simpa [seq'] using this
  have h_seq'_punctured : Filter.Tendsto seq' Filter.atTop (nhdsWithin z₀ {z₀}ᶜ) := by
    rw [nhdsWithin, Filter.tendsto_inf]
    refine ⟨h_seq'_tendsto, ?_⟩
    rw [Filter.tendsto_principal]; filter_upwards with n; exact h_seq'_ne n
  -- Apply h_eventually_large along seq'.
  have h_eventually_large_seq : ∀ᶠ n in Filter.atTop, M < ‖F (seq' n)‖ :=
    h_seq'_punctured.eventually h_eventually_large
  obtain ⟨n, hn⟩ := h_eventually_large_seq.exists
  have hbnd := h_bound (seq' n) (h_seq'_norm n)
  linarith

/-- If `h` is differentiable on a neighbourhood of the sphere of radius `R` and maps
the sphere into `slitPlane` (the complement of the closed negative real axis), then
the contour integral of its logarithmic derivative `h'/h` over the sphere vanishes.

Proof: on the sphere, `log ∘ h` is well-defined (single-valued) because `h z ∈ slitPlane`
where the principal branch of `log` is holomorphic. By the chain rule
(`HasDerivAt.clog`), `(log ∘ h)' = h'/h`. The integral of a derivative around a closed
loop vanishes by `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`. -/
theorem circleIntegral_logDeriv_eq_zero_of_image_in_slitPlane
    {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ}
    (h_diff : ∀ z : ℂ, ‖z‖ = R → DifferentiableAt ℂ h z)
    (h_image : ∀ z : ℂ, ‖z‖ = R → h z ∈ Complex.slitPlane) :
    (∮ z in C(0, R), deriv h z / h z) = 0 := by
  -- Convert sphere membership.
  have h_diff' : ∀ z ∈ Metric.sphere (0 : ℂ) R, DifferentiableAt ℂ h z := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact h_diff z hz
  have h_image' : ∀ z ∈ Metric.sphere (0 : ℂ) R, h z ∈ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact h_image z hz
  -- Apply FTC: deriv(log ∘ h) = deriv h / h on the sphere.
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
  intro z hz
  have h_in_slit : h z ∈ Complex.slitPlane := h_image' z hz
  have h_hasDerivAt : HasDerivAt h (deriv h z) z := (h_diff' z hz).hasDerivAt
  have h_clog := h_hasDerivAt.clog h_in_slit
  -- h_clog : HasDerivAt (fun t => Complex.log (h t)) (deriv h z / h z) z.
  exact h_clog.hasDerivWithinAt

/-- The Cauchy integral formula for `1/(z - u)` over a circle centered at the origin:
when `u` is strictly inside the disk, the integral equals `2πi`. -/
theorem circleIntegral_inv_sub_of_mem_ball
    {R : ℝ} {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) :
    (∮ z in C(0, R), (z - u)⁻¹) = 2 * Real.pi * Complex.I := by
  -- Apply Cauchy's formula with `f := fun _ => 1`.
  have h := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (E := ℂ) (f := fun _ => (1 : ℂ)) (c := 0) (w := u) (R := R)
    Set.countable_empty hu
    continuousOn_const
    (fun _ _ => differentiableAt_const _)
  simpa using h

/-- For an analytic non-vanishing function `G` on a closed disk, the contour integral
of its logarithmic derivative `G'/G` over the boundary circle vanishes.

This is a Cauchy–Goursat-style fact: `G'/G` is analytic on the closed disk (since
`G' / G = G' · G⁻¹` is a product of two analytic functions where `G ≠ 0`), and the
circle integral of an analytic function over a closed contour is zero. -/
theorem circleIntegral_logDeriv_analytic_nonvanishing
    {R : ℝ} (hR : 0 < R) {G : ℂ → ℂ}
    (hG_analytic : AnalyticOnNhd ℂ G (Metric.closedBall 0 R))
    (hG_nonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, G z ≠ 0) :
    (∮ z in C(0, R), deriv G z / G z) = 0 := by
  -- `deriv G / G` is differentiable on `closedBall(0, R)`.
  have hG_deriv_analytic : AnalyticOnNhd ℂ (deriv G) (Metric.closedBall 0 R) :=
    hG_analytic.deriv
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
  · -- ContinuousOn (fun z => deriv G z / G z) (closedBall 0 R)
    refine ContinuousOn.div hG_deriv_analytic.continuousOn hG_analytic.continuousOn ?_
    intro z hz
    exact hG_nonzero z hz
  · -- ∀ z ∈ ball 0 R \ ∅, DifferentiableAt (fun z => deriv G z / G z) z
    intro z hz
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R :=
      Metric.ball_subset_closedBall hz.1
    refine DifferentiableAt.div ?_ ?_ (hG_nonzero z hz_ball)
    · exact (hG_deriv_analytic z hz_ball).differentiableAt
    · exact (hG_analytic z hz_ball).differentiableAt

/-- **Central identity (specialized)**. If `F : ℂ → ℂ` is meromorphic on the universe,
analytic non-vanishing on an open neighbourhood of the sphere of radius `R`, and maps
the sphere into the open unit disk centered at `1`, then the total divisor sum of `F`
on the closed ball of radius `R` is zero.

This is a **specialization** of the general residue theorem: the strengthened hypothesis
"`F` analytic non-vanishing on a sphere-neighbourhood" rules out the value-vs-germ subtlety
that, in the fully general meromorphic setting, requires winding-number machinery (which
mathlib does not provide at this pin) to handle. The strengthened form is sufficient for
the Rouché challenge: in `rouche_total_divisor_diff_eq_zero` the function `F = (f+g)·f⁻¹`
inherits this property automatically from the strict inequality `‖g‖ < ‖f‖` on the sphere.

Proof (residue theorem, specialized):
1. `F` analytic non-vanishing on a sphere-neighbourhood ⟹ `divisor F` is supported strictly
   inside `ball(0, R)`.
2. By `extract_zeros_poles`, `F = (∏ᶠ u, (· − u)^{d_F u}) · G` modulo codiscrete equality,
   with `G` analytic non-vanishing on the closed disk.
3. `∮_{|z|=R} F'/F dz = 2πi · ∑ d_F` (factorization + Cauchy formula + Cauchy–Goursat).
4. `F` maps the sphere into `ball(1, 1) ⊂ slitPlane`, so the principal branch of `log F`
   yields a holomorphic primitive on the sphere-neighbourhood; FTC ⟹ `∮ F'/F dz = 0`.
5. Hence `∑ d_F = 0`. -/
theorem sum_divisor_eq_zero_of_image_in_ball_one
    {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : MeromorphicOn F Set.univ)
    (hF_analytic_nbhd_sphere : ∃ U : Set ℂ, IsOpen U ∧ Metric.sphere (0 : ℂ) R ⊆ U
        ∧ AnalyticOnNhd ℂ F U ∧ ∀ z ∈ U, F z ≠ 0)
    (h_image : ∀ z : ℂ, ‖z‖ = R → F z ∈ Metric.ball (1 : ℂ) 1) :
    (∑ᶠ z, divisor F (Metric.closedBall 0 R) z) = 0 := by
  set CB : Set ℂ := Metric.closedBall (0 : ℂ) R with hCB_def
  -- `F` is non-vanishing on the sphere (image is in `ball(1, 1)`, which excludes 0).
  have h_F_nonzero_sphere : ∀ z : ℂ, ‖z‖ = R → F z ≠ 0 := by
    intro z hz hFz
    have := h_image z hz
    rw [hFz, Metric.mem_ball, dist_eq_norm] at this
    simp at this
  -- `F` has finite order everywhere on `CB`.
  have h_order : ∀ z ∈ CB, meromorphicOrderAt F z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_nonzero_on_sphere hR hF h_F_nonzero_sphere
  -- Restrict to CB.
  have hF_ball : MeromorphicOn F CB := hF.mono_set (Set.subset_univ _)
  -- Divisor has finite support on the compact closed ball.
  have hCB_compact : IsCompact CB := isCompact_closedBall _ _
  have h_div_finite : (divisor F CB).support.Finite :=
    (divisor F CB).finiteSupport hCB_compact
  -- Apply `extract_zeros_poles`: `F = (∏ᶠ u, (· - u)^{d u}) · G` on `CB`, modulo
  -- codiscrete-within equality, with `G` analytic non-vanishing.
  obtain ⟨G, hG_analytic, hG_nonzero, h_factor⟩ :=
    hF_ball.extract_zeros_poles (fun u => h_order u.val u.property) h_div_finite
  -- Set `D := divisor F CB` and `φ := ∏ᶠ u, (· - u)^{D u}` (factorized rational).
  set D : Function.locallyFinsuppWithin CB ℤ := divisor F CB with hD_def
  set φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u with hφ_def
  -- `D` has finite support; coerce to a finset.
  have hD_finite : (D : ℂ → ℤ).support.Finite := h_div_finite
  let D_supp : Finset ℂ := hD_finite.toFinset
  -- Extract the analytic neighbourhood data.
  obtain ⟨U, hU_open, hU_sphere, hU_an, hU_nonzero⟩ := hF_analytic_nbhd_sphere
  -- Step B (single-valued log / FTC):
  --   `∮_{|z|=R} F'/F dz = 0` via the principal-branch logarithm on `U`.
  -- `F` is differentiable on the sphere (analytic on `U ⊇ sphere`).
  have h_F_diff_sphere : ∀ z : ℂ, ‖z‖ = R → DifferentiableAt ℂ F z := by
    intro z hz
    have : z ∈ U := hU_sphere (by rw [Metric.mem_sphere, dist_zero_right]; exact hz)
    exact (hU_an z this).differentiableAt
  -- `F z ∈ ball(1, 1) ⊂ slitPlane` for `z` on the sphere.
  have h_ball_slitPlane : Metric.ball (1 : ℂ) 1 ⊆ Complex.slitPlane := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    rw [Complex.mem_slitPlane_iff]
    left
    -- |w - 1| < 1 ⟹ Re(w - 1) ≥ -|w - 1| > -1 ⟹ Re w > 0.
    have h1 : -‖w - 1‖ ≤ (w - 1).re := by
      have := abs_re_le_norm (w - 1)
      have := neg_abs_le (w - 1).re
      linarith [abs_re_le_norm (w - 1)]
    have h2 : -1 < (w - 1).re := by linarith
    have : w.re - 1 = (w - 1).re := by simp [Complex.sub_re]
    linarith
  have h_F_image_slit : ∀ z : ℂ, ‖z‖ = R → F z ∈ Complex.slitPlane := by
    intro z hz
    exact h_ball_slitPlane (h_image z hz)
  -- Apply the FTC-based log-derivative integral helper.
  have h_int_zero : (∮ z in C(0, R), deriv F z / F z) = 0 :=
    circleIntegral_logDeriv_eq_zero_of_image_in_slitPlane hR h_F_diff_sphere h_F_image_slit
  -- Establish that divisor `D` is supported strictly inside the open ball:
  -- on the sphere, `F` is analytic non-vanishing, so its order (and hence divisor) vanishes.
  have h_div_sphere_zero : ∀ z, ‖z‖ = R → D z = 0 := by
    intro z hz
    have hz_U : z ∈ U := hU_sphere (by rw [Metric.mem_sphere, dist_zero_right]; exact hz)
    have hz_an : AnalyticAt ℂ F z := hU_an z hz_U
    have hz_ne : F z ≠ 0 := hU_nonzero z hz_U
    have hz_CB : z ∈ CB := by
      simp [CB, Metric.closedBall, dist_zero_right, hz]
    show divisor F CB z = 0
    rw [hF_ball.divisor_apply hz_CB,
      hz_an.meromorphicOrderAt_eq, hz_an.analyticOrderAt_eq_zero.mpr hz_ne]
    rfl
  have hD_supp_ball : (D : ℂ → ℤ).support ⊆ Metric.ball (0 : ℂ) R := by
    intro u hu
    have hu_CB : u ∈ CB := D.supportWithinDomain hu
    by_contra hu_not_ball
    have hu_sphere : ‖u‖ = R := by
      rw [Metric.mem_closedBall, dist_zero_right] at hu_CB
      rw [Metric.mem_ball, dist_zero_right] at hu_not_ball
      push Not at hu_not_ball
      linarith
    exact hu (h_div_sphere_zero u hu_sphere)
  -- Step A (residue theorem via factorization): `∮ F'/F = 2πi · ∑ d_F`.
  -- We define `H z := ∑ u ∈ D.support, D u · (z − u)⁻¹` and compute `∮ H` directly:
  --   each pole `u` lies in the open ball (`hD_supp_ball`), so Cauchy's formula gives
  --   `∮ (z − u)⁻¹ dz = 2πi`, and linearity of circle integral over the finite sum
  --   yields `∮ H = 2πi · ∑ᶠ D z`.
  let DF : Finset ℂ := hD_finite.toFinset
  -- Each `u ∈ DF` lies in the open ball.
  have h_u_open : ∀ u ∈ DF, u ∈ Metric.ball (0 : ℂ) R := fun u hu => by
    have hu_supp : u ∈ (D : ℂ → ℤ).support := by
      simpa [DF, Set.Finite.mem_toFinset] using hu
    exact hD_supp_ball hu_supp
  -- Each summand `(D u : ℂ) · (z − u)⁻¹` is circle-integrable on the sphere
  -- (continuous on the sphere because `z ≠ u` there, since `|u| < R = |z|`).
  have h_term_intble : ∀ u ∈ DF,
      CircleIntegrable (fun z => (D u : ℂ) * (z - u)⁻¹) 0 R := by
    intro u hu
    have hu_ball : u ∈ Metric.ball (0 : ℂ) R := h_u_open u hu
    apply ContinuousOn.circleIntegrable hR.le
    refine continuousOn_const.mul ?_
    refine ContinuousOn.inv₀ ((continuousOn_id (s := Metric.sphere (0 : ℂ) R)).sub
      continuousOn_const) ?_
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right] at hu_ball
    intro h_eq
    rw [sub_eq_zero] at h_eq
    have hzn : ‖z‖ = R := hz
    rw [← h_eq] at hu_ball
    rw [hzn] at hu_ball
    exact lt_irrefl R hu_ball
  -- Compute each term: `∮ (D u : ℂ) · (z − u)⁻¹ dz = (D u : ℂ) · 2πi`.
  have h_int_term : ∀ u ∈ DF,
      (∮ z in C(0, R), (D u : ℂ) * (z - u)⁻¹)
        = (D u : ℂ) * (2 * Real.pi * Complex.I) := by
    intro u hu
    rw [circleIntegral.integral_const_mul, circleIntegral_inv_sub_of_mem_ball (h_u_open u hu)]
  -- The full sum integral: `∮ H = 2πi · ∑ u ∈ DF, D u`.
  have h_int_sum_finset :
      (∮ z in C(0, R), ∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹)
        = (2 * Real.pi * Complex.I) * (∑ u ∈ DF, (D u : ℂ)) := by
    rw [circleIntegral.integral_fun_sum h_term_intble]
    rw [Finset.sum_congr rfl h_int_term]
    rw [← Finset.sum_mul, mul_comm]
  -- Convert finset sum `∑ u ∈ DF, (D u : ℂ)` to `((∑ᶠ z, D z : ℤ) : ℂ)`.
  have h_finset_eq_finsum : (∑ u ∈ DF, (D u : ℂ)) = ((∑ᶠ z, (D : ℂ → ℤ) z : ℤ) : ℂ) := by
    -- First compute the ℤ-sum as a finset sum.
    rw [finsum_eq_sum _ hD_finite]
    -- Now both sides are finset sums; just cast.
    show (∑ u ∈ DF, (D u : ℂ)) = ((∑ z ∈ hD_finite.toFinset, D z : ℤ) : ℂ)
    push_cast
    rfl
  -- The sum integral in ℂ-form: `∮ ∑ = 2πi · ((∑ᶠ D : ℤ) : ℂ)`.
  have h_int_sum_C :
      (∮ z in C(0, R), ∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹)
        = (2 * Real.pi * Complex.I) * ((∑ᶠ z, (D : ℂ → ℤ) z : ℤ) : ℂ) := by
    rw [h_int_sum_finset, h_finset_eq_finsum]
  -- Step A.1 sub-claim: codiscretely on the sphere,
  -- `deriv F z / F z = ∑ u ∈ DF, D u · (z − u)⁻¹ + deriv G z / G z`.
  -- Proof: from `F =ᶠ[codiscreteWithin CB] φ · G`, derivatives match where the equality
  -- holds in a neighbourhood, so `F'/F = (φ·G)'/(φ·G) = logDeriv φ + logDeriv G`. The
  -- finprod expansion `logDeriv φ z = ∑ u ∈ DF, D u · (z − u)⁻¹` follows from
  -- `logDeriv_prod` + `logDeriv_fun_zpow` + `logDeriv_id`. Restricted to the sphere,
  -- both sides agree on a codiscrete subset.
  have h_F_split_codiscrete :
      (fun z => deriv F z / F z) =ᶠ[Filter.codiscreteWithin (Metric.sphere (0 : ℂ) R)]
        (fun z => (∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) + deriv G z / G z) := by
    -- Strategy: prove pointwise equality at every `z ∈ sphere`, then upgrade via
    -- `self_mem_codiscreteWithin`.  At each sphere point, `F` and `φ·G` are both
    -- analytic and agree frequently in a punctured neighbourhood (since the codiscrete
    -- agreement set on the closed disk contains the open-disk side of any sphere
    -- neighbourhood); hence by `frequently_eq_iff_eventually_eq` they agree on a full
    -- neighbourhood, derivatives match, and the logarithmic-derivative arithmetic
    -- collapses to the desired sum.
    have h_pointwise : ∀ z ∈ Metric.sphere (0 : ℂ) R,
        deriv F z / F z = (∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) + deriv G z / G z := by
      intro z hz_sphere
      have hz : ‖z‖ = R := by
        rw [Metric.mem_sphere, dist_zero_right] at hz_sphere; exact hz_sphere
      have hz_CB : z ∈ CB := by
        simp only [CB, Metric.mem_closedBall, dist_zero_right, hz, le_refl]
      -- F analytic at z (from the sphere-neighbourhood hypothesis).
      have hz_U : z ∈ U := hU_sphere hz_sphere
      have h_F_an : AnalyticAt ℂ F z := hU_an z hz_U
      have h_F_ne : F z ≠ 0 := hU_nonzero z hz_U
      -- G analytic at z (from extract_zeros_poles' AnalyticOnNhd).
      have h_G_an : AnalyticAt ℂ G z := hG_analytic z hz_CB
      have h_G_ne : G z ≠ 0 := hG_nonzero ⟨z, hz_CB⟩
      -- Each (·-u)^(D u) for u ∈ DF is analytic at z and nonzero (z ≠ u since u ∈ open ball).
      have h_z_ne_u : ∀ u ∈ DF, z ≠ u := by
        intro u hu hzu
        have hu_ball : u ∈ Metric.ball (0 : ℂ) R := h_u_open u hu
        rw [Metric.mem_ball, dist_zero_right] at hu_ball
        rw [hzu] at hz; rw [hz] at hu_ball; exact lt_irrefl R hu_ball
      have h_factor_an : ∀ u ∈ DF, AnalyticAt ℂ (fun w => (w - u) ^ D u) z := by
        intro u hu
        apply AnalyticAt.fun_zpow
        · exact (analyticAt_id.sub analyticAt_const)
        · exact sub_ne_zero.mpr (h_z_ne_u u hu)
      have h_factor_ne : ∀ u ∈ DF, ((fun w => (w - u) ^ D u) z) ≠ 0 := by
        intro u hu
        exact zpow_ne_zero _ (sub_ne_zero.mpr (h_z_ne_u u hu))
      -- Define φ_finset := ∏ u ∈ DF, (·-u)^(D u). On sphere, φ z = φ_finset z (finprod = finprod over Finset).
      have hφ_eq_finset : ∀ w, φ w = ∏ u ∈ DF, (w - u) ^ D u := by
        intro w
        show (∏ᶠ u, (· - u) ^ (D : ℂ → ℤ) u) w = _
        rw [Function.FactorizedRational.finprod_eq_fun hD_finite]
        change (∏ᶠ u, (w - u) ^ D u) = ∏ u ∈ DF, (w - u) ^ D u
        rw [finprod_eq_prod_of_mulSupport_subset _ (s := DF)]
        intro u hu
        simp only [Finset.mem_coe, DF, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
        simp only [Function.mem_mulSupport, ne_eq] at hu
        intro hDu
        apply hu
        rw [hDu, zpow_zero]
      have hφ_ne : φ z ≠ 0 := by
        rw [hφ_eq_finset]
        exact Finset.prod_ne_zero_iff.mpr h_factor_ne
      have hφ_an : AnalyticAt ℂ φ z := by
        have : AnalyticAt ℂ (fun w => ∏ u ∈ DF, (w - u) ^ D u) z := by
          apply Finset.analyticAt_fun_prod
          intro u hu
          exact h_factor_an u hu
        rw [show φ = fun w => ∏ u ∈ DF, (w - u) ^ D u from funext hφ_eq_finset]
        exact this
      have hφG_an : AnalyticAt ℂ (φ * G) z := hφ_an.mul h_G_an
      -- Frequent agreement: F = φ·G in 𝓝[≠] z (frequently).
      have h_freq : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = (φ * G) w := by
        -- From h_factor (codiscrete on CB), {F = φ·G} ∪ CBᶜ ∈ 𝓝[≠] z.
        have h_eq_set_codisc : {w | F w = (φ * G) w} ∈ Filter.codiscreteWithin CB := by
          have := h_factor
          show {w | F w = (φ * G) w} ∈ Filter.codiscreteWithin CB
          filter_upwards [this] with w hw using by
            simp only [Pi.smul_apply', smul_eq_mul] at hw; exact hw
        have h_mem_nhdsNE :
            {w | F w = (φ * G) w} ∪ CBᶜ ∈ nhdsWithin z {z}ᶜ := by
          rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_eq_set_codisc
          exact h_eq_set_codisc z hz_CB
        -- Combine with: 𝓝[≠] z frequently has w ∈ open ball (since z ∈ closure of open ball).
        have h_freq_in_ball : ∃ᶠ w in nhdsWithin z {z}ᶜ, w ∈ Metric.ball (0 : ℂ) R := by
          rw [Filter.frequently_iff]
          intro V hV
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hV
          obtain ⟨V', hV', hV_subset⟩ := hV
          -- Find a point in V' \ {z} ∩ open ball.
          obtain ⟨V'', hV''_V', hV''_open, hz_V''⟩ := _root_.mem_nhds_iff.mp hV'
          -- Take w := z scaled inward.
          have : ∃ w, w ∈ V'' ∧ w ∈ Metric.ball (0 : ℂ) R := by
            have hcl : z ∈ closure (Metric.ball (0 : ℂ) R) := by
              rw [closure_ball (0 : ℂ) hR.ne']; exact hz_CB
            rw [_root_.mem_closure_iff] at hcl
            obtain ⟨w, hw_V'', hw_ball⟩ := hcl V'' hV''_open hz_V''
            exact ⟨w, hw_V'', hw_ball⟩
          obtain ⟨w, hw_V'', hw_ball⟩ := this
          -- We need w ≠ z for membership in {z}ᶜ.
          by_cases hwz : w = z
          · -- w = z: but then z ∈ open ball, contradicting z on sphere.
            rw [hwz] at hw_ball
            rw [Metric.mem_ball, dist_zero_right] at hw_ball
            linarith
          · refine ⟨w, hV_subset ?_, hw_ball⟩
            exact ⟨hV''_V' hw_V'', hwz⟩
        -- Combine eventually-(F=φG ∨ ¬CB) with frequently-(in open ball ⊂ CB).
        rw [Filter.frequently_iff]
        intro V hV
        have hV_inter : V ∩ ({w | F w = (φ * G) w} ∪ CBᶜ) ∈ nhdsWithin z {z}ᶜ :=
          Filter.inter_mem hV h_mem_nhdsNE
        rw [Filter.frequently_iff] at h_freq_in_ball
        obtain ⟨w, hw_V_inter, hw_ball⟩ := h_freq_in_ball hV_inter
        refine ⟨w, hw_V_inter.1, ?_⟩
        rcases hw_V_inter.2 with h_eq | h_outside
        · exact h_eq
        · exfalso
          apply h_outside
          exact Metric.ball_subset_closedBall hw_ball
      -- Apply identity theorem.
      have h_F_eq_φG_nhds : F =ᶠ[nhds z] (fun w => (φ * G) w) :=
        (h_F_an.frequently_eq_iff_eventually_eq hφG_an).mp h_freq
      -- Now use this to compute deriv F z / F z = deriv (φ•G) z / (φ•G) z.
      have h_F_z : F z = (φ * G) z := h_F_eq_φG_nhds.eq_of_nhds
      have h_deriv_F : deriv F z = deriv (φ * G) z := h_F_eq_φG_nhds.deriv_eq
      rw [h_deriv_F, h_F_z]
      -- deriv (φ * G) z / (φ * G) z = logDeriv (φ * G) z = logDeriv φ z + logDeriv G z
      change logDeriv (fun w => φ w * G w) z = (∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹)
        + logDeriv G z
      rw [logDeriv_mul z hφ_ne h_G_ne hφ_an.differentiableAt h_G_an.differentiableAt]
      -- logDeriv φ z = ∑ u ∈ DF, D u / (z - u). Use logDeriv_prod via finprod_eq.
      have h_logDeriv_φ : logDeriv φ z = ∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹ := by
        -- Define the per-factor function explicitly to avoid elaboration issues.
        let factor : ℂ → ℂ → ℂ := fun u w => (w - u) ^ D u
        have hφ_eq_factor : φ = (fun w => ∏ u ∈ DF, factor u w) := by
          funext w; exact hφ_eq_finset w
        rw [hφ_eq_factor]
        have h_factor_ne' : ∀ u ∈ DF, factor u z ≠ 0 := h_factor_ne
        have h_factor_diff : ∀ u ∈ DF, DifferentiableAt ℂ (factor u) z :=
          fun u hu => (h_factor_an u hu).differentiableAt
        rw [logDeriv_prod h_factor_ne' h_factor_diff]
        apply Finset.sum_congr rfl
        intro u _hu
        -- Compute logDeriv ((·-u) ^ D u) z = (D u) · (z - u)⁻¹ via chain rule.
        have h_zu_ne : z - u ≠ 0 := sub_ne_zero.mpr (h_z_ne_u u _hu)
        show logDeriv (fun w => (w - u) ^ D u) z = (D u : ℂ) * (z - u)⁻¹
        -- HasDerivAt for (·-u) at z: derivative is 1.
        have h_id_sub : HasDerivAt (fun w : ℂ => w - u) 1 z :=
          (hasDerivAt_id z).sub_const u
        -- HasDerivAt for (·^(D u)) at (z-u): derivative is (D u) * (z-u)^(D u - 1).
        have h_zpow : HasDerivAt (fun y : ℂ => y ^ (D u : ℤ))
            ((D u : ℂ) * (z - u) ^ (D u - 1)) (z - u) :=
          hasDerivAt_zpow (D u) (z - u) (Or.inl h_zu_ne)
        -- Compose: function = (·^(D u)) ∘ (·-u).
        have h_comp_eq : (fun w : ℂ => (w - u) ^ D u)
            = (fun y : ℂ => y ^ (D u : ℤ)) ∘ (fun w : ℂ => w - u) := by
          funext w; rfl
        rw [h_comp_eq]
        rw [logDeriv_apply]
        have h_comp : HasDerivAt ((fun y : ℂ => y ^ (D u : ℤ)) ∘ (fun w : ℂ => w - u))
            ((D u : ℂ) * (z - u) ^ (D u - 1) * 1) z :=
          h_zpow.comp z h_id_sub
        rw [h_comp.deriv, mul_one]
        -- (D u * (z-u)^(D u - 1)) / (z-u)^(D u) = (D u) * (z-u)⁻¹.
        show ((D u : ℤ) : ℂ) * (z - u) ^ (D u - 1) / ((fun y : ℂ => y ^ (D u : ℤ)) ∘
          (fun w : ℂ => w - u)) z = (D u : ℂ) * (z - u)⁻¹
        simp only [Function.comp]
        rw [show ((D u : ℤ) : ℂ) * (z - u) ^ (D u - 1) / (z - u) ^ D u
            = (D u : ℂ) * ((z - u) ^ (D u - 1) / (z - u) ^ D u) from by ring]
        congr 1
        rw [zpow_sub₀ h_zu_ne, zpow_one]
        field_simp
      rw [h_logDeriv_φ]
    -- Convert pointwise to codiscrete.
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.sphere (0 : ℂ) R, ?_, h_pointwise⟩
    exact Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) R)
  -- Apply codiscrete circle-integral congruence.
  have h_R_ne : R ≠ 0 := hR.ne'
  have h_int_F_eq_split :
      (∮ z in C(0, R), deriv F z / F z)
        = (∮ z in C(0, R), (∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) + deriv G z / G z) := by
    have h_R_abs_eq : Metric.sphere (0 : ℂ) |R| = Metric.sphere (0 : ℂ) R := by
      rw [abs_of_pos hR]
    -- The codiscrete equality is on `sphere 0 R`, but the lemma uses `sphere 0 |R|`.
    have h_codisc_abs : (fun z => deriv F z / F z) =ᶠ[Filter.codiscreteWithin
        (Metric.sphere (0 : ℂ) |R|)]
        (fun z => (∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) + deriv G z / G z) := by
      rw [h_R_abs_eq]; exact h_F_split_codiscrete
    exact circleIntegral.circleIntegral_congr_codiscreteWithin h_codisc_abs h_R_ne
  -- Split the integral via linearity.
  have h_split_intble_sum :
      CircleIntegrable (fun z => ∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) 0 R := by
    apply CircleIntegrable.fun_sum DF h_term_intble
  have h_split_intble_G :
      CircleIntegrable (fun z => deriv G z / G z) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    have hG_deriv_an : AnalyticOnNhd ℂ (deriv G) (Metric.closedBall 0 R) := hG_analytic.deriv
    refine ContinuousOn.div (hG_deriv_an.continuousOn.mono sphere_subset_closedBall)
      (hG_analytic.continuousOn.mono sphere_subset_closedBall) ?_
    intro z hz
    have hz_CB : z ∈ Metric.closedBall (0 : ℂ) R := sphere_subset_closedBall hz
    exact hG_nonzero ⟨z, hz_CB⟩
  have h_int_split :
      (∮ z in C(0, R), (∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) + deriv G z / G z)
        = (∮ z in C(0, R), ∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹)
          + (∮ z in C(0, R), deriv G z / G z) :=
    circleIntegral.integral_add h_split_intble_sum h_split_intble_G
  -- ∮ G'/G = 0 from the helper.
  have h_int_G : (∮ z in C(0, R), deriv G z / G z) = 0 :=
    circleIntegral_logDeriv_analytic_nonvanishing hR hG_analytic
      (fun z hz => hG_nonzero ⟨z, hz⟩)
  -- Combine: `∮ F'/F = 2πi · ((∑ᶠ D : ℤ) : ℂ)`, plus `∮ F'/F = 0`.
  have h_combine_C :
      (2 * Real.pi * Complex.I) * ((∑ᶠ z, (D : ℂ → ℤ) z : ℤ) : ℂ) = 0 := by
    rw [← h_int_sum_C]
    have : (∮ z in C(0, R), ∑ u ∈ DF, (D u : ℂ) * (z - u)⁻¹) = 0 := by
      have := h_int_F_eq_split
      rw [h_int_split, h_int_G, add_zero] at this
      rw [← this]
      exact h_int_zero
    exact this
  -- 2πi ≠ 0.
  have h_2pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  -- Therefore the sum (in ℂ) is zero.
  have h_sum_C_zero : ((∑ᶠ z, (D : ℂ → ℤ) z : ℤ) : ℂ) = 0 :=
    (mul_eq_zero.mp h_combine_C).resolve_left h_2pi_ne
  -- Cast back to ℤ.
  show (∑ᶠ z, divisor F CB z) = 0
  have : (∑ᶠ z, (D : ℂ → ℤ) z) = 0 := by exact_mod_cast h_sum_C_zero
  exact this

/-- Specialization of `sum_divisor_eq_zero_of_image_in_ball_one` to the Rouché setup:
the divisor of `(f + g) · f⁻¹` on the closed disk has total degree zero, given the
strict-inequality hypothesis on the boundary. The key intermediate fact is the divisor
identity `divisor ((f + g) · f⁻¹) = divisor (f + g) - divisor f`, which combines
`divisor_mul` and `divisor_inv` from mathlib. -/
theorem rouche_total_divisor_diff_eq_zero
    {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hfNF : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, divisor (f + g) (Metric.closedBall 0 R) z) =
      (∑ᶠ z, divisor f (Metric.closedBall 0 R) z) := by
  set CB : Set ℂ := Metric.closedBall (0 : ℂ) R with hCB_def
  -- Derive the plain `MeromorphicOn` form for use in the rest of the proof.
  have hf : MeromorphicOn f Set.univ := hfNF.meromorphicOn
  -- Setup: meromorphic structure for `f`, `g`, `f + g`, `f⁻¹`, `(f + g) · f⁻¹`.
  have hg_nhd_univ : AnalyticOnNhd ℂ g Set.univ :=
    (isOpen_univ.analyticOn_iff_analyticOnNhd).mp hg
  have hg_mero : MeromorphicOn g Set.univ := hg_nhd_univ.meromorphicOn
  have hfg_mero : MeromorphicOn (f + g) Set.univ := hf.add hg_mero
  have hf_inv_mero : MeromorphicOn f⁻¹ Set.univ := hf.inv
  have hF_mero : MeromorphicOn ((f + g) * f⁻¹) Set.univ := hfg_mero.mul hf_inv_mero
  -- Restrictions to `closedBall`.
  have hf_ball : MeromorphicOn f CB := hf.mono_set (Set.subset_univ _)
  have hfg_ball : MeromorphicOn (f + g) CB := hfg_mero.mono_set (Set.subset_univ _)
  have hf_inv_ball : MeromorphicOn f⁻¹ CB := hf_inv_mero.mono_set (Set.subset_univ _)
  have hF_ball : MeromorphicOn ((f + g) * f⁻¹) CB := hF_mero.mono_set (Set.subset_univ _)
  -- `f` and `f + g` are non-vanishing on the sphere.
  have h_f_nonzero : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0 := by
    intro z hz hfz
    have := hbound z hz
    rw [hfz, norm_zero] at this
    have := norm_nonneg (g z)
    linarith
  have h_fg_nonzero : ∀ z : ℂ, ‖z‖ = R → (f + g) z ≠ 0 := by
    intro z hz hfgz
    have hbnd := hbound z hz
    have : f z = -g z := by
      have h₁ : f z + g z = 0 := by simpa [Pi.add_apply] using hfgz
      linear_combination h₁
    rw [this, norm_neg] at hbnd
    linarith
  -- Hence `f`, `f + g` have finite order on `closedBall`.
  have h_ord_f : ∀ z ∈ CB, meromorphicOrderAt f z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_nonzero_on_sphere hR hf h_f_nonzero
  have h_ord_fg : ∀ z ∈ CB, meromorphicOrderAt (f + g) z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_nonzero_on_sphere hR hfg_mero h_fg_nonzero
  -- The order of `f⁻¹` is the negative of the order of `f`, so it's also ≠ ⊤.
  have h_ord_f_inv : ∀ z ∈ CB, meromorphicOrderAt f⁻¹ z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_inv]
    intro h_neg
    rw [LinearOrderedAddCommGroupWithTop.neg_eq_top] at h_neg
    exact h_ord_f z hz h_neg
  -- F = (f + g) * f⁻¹.
  -- Divisor identity: divisor F = divisor (f + g) + divisor f⁻¹ = divisor (f + g) - divisor f.
  have h_div_F : divisor ((f + g) * f⁻¹) CB
      = divisor (f + g) CB + divisor f⁻¹ CB :=
    divisor_mul hfg_ball hf_inv_ball h_ord_fg h_ord_f_inv
  have h_div_inv : divisor f⁻¹ CB = -divisor f CB := divisor_inv
  -- F maps sphere(0, R) into ball(1, 1).
  have h_F_image : ∀ z : ℂ, ‖z‖ = R → ((f + g) * f⁻¹) z ∈ Metric.ball (1 : ℂ) 1 := by
    intro z hz
    have hfz_ne : f z ≠ 0 := h_f_nonzero z hz
    have hbnd := hbound z hz
    -- Show |((f+g) * f⁻¹)(z) - 1| < 1.
    rw [Metric.mem_ball, Complex.dist_eq]
    have h_eq : ((f + g) * f⁻¹) z - 1 = g z / f z := by
      simp only [Pi.mul_apply, Pi.add_apply, Pi.inv_apply]
      field_simp
      ring
    rw [h_eq, norm_div]
    rwa [div_lt_one (by positivity)]
  -- Construct the analytic-non-vanishing neighbourhood of the sphere required by the
  -- specialized central identity. On `{z : ‖g z‖ < ‖f z‖}`, both `f` and `f + g` are
  -- non-vanishing (by the strict inequality + analyticity of `g`); since this set is
  -- open and contains the sphere by the hypothesis `hbound`, it provides the required
  -- neighbourhood. `F = (f+g) · f⁻¹` is analytic on this set (since `f` is non-vanishing
  -- and analytic, and `f + g` is mero with `f`-mero structure but order 0 here).
  have hF_analytic_nbhd_sphere :
      ∃ U : Set ℂ, IsOpen U ∧ Metric.sphere (0 : ℂ) R ⊆ U
        ∧ AnalyticOnNhd ℂ ((f + g) * f⁻¹) U
        ∧ ∀ z ∈ U, ((f + g) * f⁻¹) z ≠ 0 := by
    -- The set `U := { z | AnalyticAt ℂ f z ∧ ‖g z‖ < ‖f z‖ }` is the natural choice.
    -- It is open (analytic-at is open + strict inequality of continuous functions is open),
    -- contains the sphere by `hbound` and the specialization (`f` analytic near the sphere),
    -- and on it `F = (f+g)·f⁻¹` is analytic non-vanishing because `f ≠ 0` (from
    -- `‖g‖ < ‖f‖`), `f` is analytic, `f + g` is analytic, and `(f+g)/f` therefore inherits
    -- analyticity, while `|F - 1| = |g/f| < 1` keeps `F ≠ 0`.
    refine ⟨{z | AnalyticAt ℂ f z ∧ ‖g z‖ < ‖f z‖}, ?_, ?_, ?_, ?_⟩
    · -- Openness: at each `z₀` in the set, both conditions hold in a neighbourhood.
      rw [isOpen_iff_mem_nhds]
      intro z₀ hz₀
      have h_an_z₀ : AnalyticAt ℂ f z₀ := hz₀.1
      have h_lt_z₀ : ‖g z₀‖ < ‖f z₀‖ := hz₀.2
      have h_an_nbhd : ∀ᶠ z in nhds z₀, AnalyticAt ℂ f z :=
        (isOpen_analyticAt ℂ f).mem_nhds h_an_z₀
      have h_f_cont : ContinuousAt f z₀ := h_an_z₀.continuousAt
      have h_g_cont : ContinuousAt g z₀ := (hg_nhd_univ z₀ (Set.mem_univ _)).continuousAt
      have h_diff_cont : ContinuousAt (fun z => ‖f z‖ - ‖g z‖) z₀ :=
        h_f_cont.norm.sub h_g_cont.norm
      have h_diff_pos : (0 : ℝ) < ‖f z₀‖ - ‖g z₀‖ := by linarith
      have h_lt_nbhd : ∀ᶠ z in nhds z₀, ‖g z‖ < ‖f z‖ := by
        have h_event : ∀ᶠ z in nhds z₀, (0 : ℝ) < ‖f z‖ - ‖g z‖ := by
          have := h_diff_cont.tendsto
          exact (this.eventually (eventually_gt_nhds h_diff_pos))
        filter_upwards [h_event] with z hz; linarith
      filter_upwards [h_an_nbhd, h_lt_nbhd] with z hz_an hz_lt using ⟨hz_an, hz_lt⟩
    · -- Sphere ⊆ U: at sphere points, `f` is analytic and `‖g‖ < ‖f‖` from `hbound`.
      -- With `hfNF : MeromorphicNFOn f Set.univ`, every point of `f` is either analytic
      -- or a pole with `f z = 0` (NF convention). On the sphere, `‖g z‖ < ‖f z‖` implies
      -- `‖f z‖ > 0`, ruling out the pole case. So `f` is analytic at every sphere point.
      intro z hz
      have hz_norm : ‖z‖ = R := by
        rw [Metric.mem_sphere, dist_zero_right] at hz; exact hz
      have h_lt : ‖g z‖ < ‖f z‖ := hbound z hz_norm
      have h_f_ne : f z ≠ 0 := by
        intro h
        rw [h, norm_zero] at h_lt
        exact absurd h_lt (not_lt.mpr (norm_nonneg _))
      have h_NF : MeromorphicNFAt f z := hfNF (Set.mem_univ _)
      rw [meromorphicNFAt_iff_analyticAt_or] at h_NF
      have h_an_f : AnalyticAt ℂ f z := by
        rcases h_NF with h | ⟨_, _, h_eq_zero⟩
        · exact h
        · exact absurd h_eq_zero h_f_ne
      exact ⟨h_an_f, h_lt⟩
    · -- AnalyticOnNhd of F on U.
      intro z hz
      have hz_an_f : AnalyticAt ℂ f z := hz.1
      have hz_lt : ‖g z‖ < ‖f z‖ := hz.2
      have hz_f_ne : f z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz_lt
        have := norm_nonneg (g z)
        linarith
      have hz_an_g : AnalyticAt ℂ g z := hg_nhd_univ z (Set.mem_univ _)
      have hz_an_fg : AnalyticAt ℂ (f + g) z := hz_an_f.add hz_an_g
      have hz_an_inv_f : AnalyticAt ℂ f⁻¹ z := hz_an_f.inv hz_f_ne
      exact hz_an_fg.mul hz_an_inv_f
    · -- F ≠ 0 on U.
      intro z hz
      have hz_lt : ‖g z‖ < ‖f z‖ := hz.2
      have hz_f_ne : f z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz_lt
        have := norm_nonneg (g z)
        linarith
      -- (f+g)/f ≠ 0 ⟺ (f+g) ≠ 0 ⟺ |f+g| > 0. Use |f+g| ≥ |f| - |g| > 0.
      simp only [Pi.mul_apply, Pi.add_apply, Pi.inv_apply, ne_eq, mul_eq_zero, inv_eq_zero,
        not_or]
      refine ⟨?_, hz_f_ne⟩
      intro h_fg_zero
      have h_fz_eq_neg : f z = -g z := by linear_combination h_fg_zero
      rw [h_fz_eq_neg, norm_neg] at hz_lt
      linarith
  -- Apply the central identity.
  have h_sum_F_zero : (∑ᶠ z, divisor ((f + g) * f⁻¹) CB z) = 0 :=
    sum_divisor_eq_zero_of_image_in_ball_one hR hF_mero hF_analytic_nbhd_sphere h_F_image
  -- Translate: ∑ d_F = ∑ d_{f+g} + ∑ d_{f⁻¹} = ∑ d_{f+g} - ∑ d_f.
  -- Finite support on compact ball.
  have h_compact : IsCompact CB := isCompact_closedBall _ _
  have h_fin_fg : (Function.support
      ((divisor (f + g) CB).toFun : ℂ → ℤ)).Finite :=
    (divisor (f + g) CB).finiteSupport h_compact
  have h_fin_f : (Function.support
      ((divisor f CB).toFun : ℂ → ℤ)).Finite :=
    (divisor f CB).finiteSupport h_compact
  -- Compute the sum directly using the divisor identity.
  -- divisor F = divisor (f+g) + divisor f⁻¹ pointwise.
  -- divisor f⁻¹ = -divisor f as locallyFinsupp, hence pointwise.
  have h_F_pt : ∀ z, divisor ((f + g) * f⁻¹) CB z = divisor (f + g) CB z + divisor f⁻¹ CB z := by
    intro z
    rw [h_div_F]
    rfl
  have h_inv_pt : ∀ z, divisor f⁻¹ CB z = -(divisor f CB z) := fun z => by
    show (divisor f⁻¹ CB).toFun z = -(divisor f CB).toFun z
    rw [h_div_inv]; rfl
  -- Want to show: ∑ d_F = ∑ d_{f+g} - ∑ d_f.
  -- Equivalently: ∑ d_F + ∑ d_f = ∑ d_{f+g}.
  -- Use that ∑ (d_F + d_f) = ∑ d_{f+g} via pointwise equality.
  have h_pt_combined : ∀ z, divisor ((f + g) * f⁻¹) CB z + divisor f CB z =
      divisor (f + g) CB z := by
    intro z
    rw [h_F_pt z, h_inv_pt z]
    ring
  have h_sum_combined : (∑ᶠ z, divisor ((f + g) * f⁻¹) CB z) +
      (∑ᶠ z, divisor f CB z) = (∑ᶠ z, divisor (f + g) CB z) := by
    rw [← finsum_add_distrib]
    · exact finsum_congr h_pt_combined
    · -- support of divisor F is finite (subset of supp of d_{f+g} ∪ supp of d_f).
      have : (Function.support ((divisor ((f + g) * f⁻¹) CB).toFun : ℂ → ℤ)).Finite :=
        (divisor ((f + g) * f⁻¹) CB).finiteSupport h_compact
      exact this
    · exact h_fin_f
  rw [h_sum_F_zero] at h_sum_combined
  linarith

theorem rouche_zero_count_eq
    {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
  -- The `MeromorphicNFOn` hypothesis subsumes `MeromorphicOn`; derive the latter for use
  -- with the bookkeeping helpers (`mono_set`, `.add`, etc.).
  have hfMero : MeromorphicOn f Set.univ := hf.meromorphicOn
  -- Restrict the global (`Set.univ`) hypotheses to the closed ball.
  have hf_ball : MeromorphicOn f (Metric.closedBall 0 R) :=
    hfMero.mono_set (Set.subset_univ _)
  have hg_nhd_univ : AnalyticOnNhd ℂ g Set.univ :=
    (isOpen_univ.analyticOn_iff_analyticOnNhd).mp hg
  have hg_nhd_ball : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) :=
    fun x _ => hg_nhd_univ x (Set.mem_univ _)
  have hg_ball : MeromorphicOn g (Metric.closedBall 0 R) := hg_nhd_ball.meromorphicOn
  have hfg_ball : MeromorphicOn (f + g) (Metric.closedBall 0 R) := hf_ball.add hg_ball
  -- (a) Pole divisors match pointwise.
  have h_neg : (divisor (f + g) (Metric.closedBall 0 R))⁻
      = (divisor f (Metric.closedBall 0 R))⁻ :=
    negPart_divisor_add_of_analyticNhdOn_right hf_ball hg_nhd_ball
  -- (b) Total divisor sums match (Rouché identity).
  have h_total := rouche_total_divisor_diff_eq_zero hR hf hg hbound
  -- (c) Bookkeeping: `D⁺ = D + D⁻` pointwise; finite support on compact ball.
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have h_fin_fg : (Function.support
      ((divisor (f + g) (Metric.closedBall 0 R)).toFun : ℂ → ℤ)).Finite :=
    (divisor (f + g) (Metric.closedBall 0 R)).finiteSupport h_compact
  have h_fin_f : (Function.support
      ((divisor f (Metric.closedBall 0 R)).toFun : ℂ → ℤ)).Finite :=
    (divisor f (Metric.closedBall 0 R)).finiteSupport h_compact
  have h_split_fg : ∀ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z =
      (divisor (f + g) (Metric.closedBall 0 R)) z +
        ((divisor (f + g) (Metric.closedBall 0 R))⁻) z := by
    intro z
    simp only [Function.locallyFinsuppWithin.posPart_apply,
               Function.locallyFinsuppWithin.negPart_apply]
    linarith [posPart_sub_negPart ((divisor (f + g) (Metric.closedBall 0 R)) z)]
  have h_split_f : ∀ z, ((divisor f (Metric.closedBall 0 R))⁺) z =
      (divisor f (Metric.closedBall 0 R)) z +
        ((divisor f (Metric.closedBall 0 R))⁻) z := by
    intro z
    simp only [Function.locallyFinsuppWithin.posPart_apply,
               Function.locallyFinsuppWithin.negPart_apply]
    linarith [posPart_sub_negPart ((divisor f (Metric.closedBall 0 R)) z)]
  have h_neg_sum : (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁻) z)
      = (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁻) z) := by
    rw [h_neg]
  calc (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z)
      = (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R)) z +
              ((divisor (f + g) (Metric.closedBall 0 R))⁻) z)) := by
        apply finsum_congr; intro z; exact h_split_fg z
    _ = (∑ᶠ z, divisor (f + g) (Metric.closedBall 0 R) z)
        + (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁻) z) := by
        apply finsum_add_distrib
        · exact h_fin_fg
        · refine h_fin_fg.subset (fun z hz => ?_)
          simp only [Function.mem_support, ne_eq,
            Function.locallyFinsuppWithin.negPart_apply] at hz
          intro h_zero
          apply hz
          show ((divisor (f + g) (Metric.closedBall 0 R)) z)⁻ = 0
          rw [show (divisor (f + g) (Metric.closedBall 0 R)) z = 0 from h_zero]
          simp
    _ = (∑ᶠ z, divisor f (Metric.closedBall 0 R) z)
        + (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁻) z) := by
        rw [h_total, h_neg_sum]
    _ = (∑ᶠ z, ((divisor f (Metric.closedBall 0 R)) z +
              ((divisor f (Metric.closedBall 0 R))⁻) z)) := by
        symm
        apply finsum_add_distrib
        · exact h_fin_f
        · refine h_fin_f.subset (fun z hz => ?_)
          simp only [Function.mem_support, ne_eq,
            Function.locallyFinsuppWithin.negPart_apply] at hz
          intro h_zero
          apply hz
          show ((divisor f (Metric.closedBall 0 R)) z)⁻ = 0
          rw [show (divisor f (Metric.closedBall 0 R)) z = 0 from h_zero]
          simp
    _ = (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
        apply finsum_congr; intro z; exact (h_split_f z).symm

end Submission.Helpers
