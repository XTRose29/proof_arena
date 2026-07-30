import ChallengeDeps

open LeanEval.Analysis.ODE
open Real MeasureTheory

namespace Submission

section ProofSupport

open scoped Topology

/- Local copy of the parametric integral differentiation lemmas used below.
These lemmas are normally provided by `Mathlib.Analysis.Calculus.ParametricIntegral`; the
frozen import list for this benchmark does not import that file, so we include exactly the
needed specialization chain here. -/
open TopologicalSpace MeasureTheory Filter Metric

open scoped Topology Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

variable {F : H → α → E} {x₀ : H} {bound : α → ℝ} {s : Set H}

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming `F x₀` is
integrable, `‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖` for `x` in a neighborhood of `x₀` for ae `a`
integrable Lipschitz bound `bound` (with a neighborhood independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `hasFDerivAt_integral_of_dominated_loc_of_lip` for a
slightly less general but usually more useful version. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip' {F' : α → H →L[𝕜] E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.1 hs
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have nneg : ∀ x, 0 ≤ ‖x - x₀‖⁻¹ := fun x ↦ inv_nonneg.mpr (norm_nonneg _)
  set b : α → ℝ := fun a ↦ |bound a|
  have b_int : Integrable b μ := bound_integrable.norm
  have b_nonneg : ∀ a, 0 ≤ b a := fun a ↦ abs_nonneg _
  replace h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ :=
    h_lipsch.mono fun a ha x hx ↦
      (ha x (hε hx)).trans <| mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hF_int' : ∀ x ∈ ball x₀ ε, Integrable (F x) μ := fun x x_in ↦ by
    have : ∀ᵐ a ∂μ, ‖F x₀ a - F x a‖ ≤ ε * b a := by
      simp only [norm_sub_rev (F x₀ _)]
      refine h_lipsch.mono fun a ha ↦ (ha x x_in).trans ?_
      rw [mul_comm ε]
      rw [mem_ball, dist_eq_norm] at x_in
      gcongr
    exact integrable_of_norm_sub_le (hF_meas x (hε x_in)) hF_int
      (bound_integrable.norm.const_mul ε) this
  have hF'_int : Integrable F' μ :=
    have : ∀ᵐ a ∂μ, ‖F' a‖ ≤ b a := by
      apply (h_diff.and h_lipsch).mono
      rintro a ⟨ha_diff, ha_lip⟩
      exact ha_diff.le_of_lip' (b_nonneg a) (mem_of_superset (ball_mem_nhds _ ε_pos) <| ha_lip)
    b_int.mono' hF'_meas this
  refine ⟨hF'_int, ?_⟩
  /- Discard the trivial case where `E` is not complete, as all integrals vanish. -/
  by_cases hE : CompleteSpace E; swap
  · rcases subsingleton_or_nontrivial H with hH | hH
    · have : Subsingleton (H →L[𝕜] E) := inferInstance
      convert hasFDerivAt_of_subsingleton _ x₀
    · have : ¬(CompleteSpace (H →L[𝕜] E)) := by
        simpa [SeparatingDual.completeSpace_continuousLinearMap_iff] using hE
      simp only [integral, hE, ↓reduceDIte, this]
      exact hasFDerivAt_const 0 x₀
  have h_ball : ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos
  have : ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖⁻¹ * ‖((∫ a, F x a ∂μ) - ∫ a, F x₀ a ∂μ) - (∫ a, F' a ∂μ) (x - x₀)‖ =
      ‖∫ a, ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀)) ∂μ‖ := by
    apply mem_of_superset (ball_mem_nhds _ ε_pos)
    intro x x_in; simp only
    rw [Set.mem_setOf_eq, ← norm_smul_of_nonneg (nneg _), integral_smul, integral_sub, integral_sub,
      ← ContinuousLinearMap.integral_apply hF'_int]
    exacts [hF_int' x x_in, hF_int, (hF_int' x x_in).sub hF_int,
      hF'_int.apply_continuousLinearMap _]
  rw [hasFDerivAt_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero, ←
    show (∫ a : α, ‖x₀ - x₀‖⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ) = 0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence
  · filter_upwards [h_ball] with _ x_in
    apply AEStronglyMeasurable.const_smul
    exact ((hF_meas _ (hε x_in)).sub (hF_meas _ (hε x₀_in))).sub
      (hF'_meas.apply_continuousLinearMap _)
  · refine mem_of_superset h_ball fun x hx ↦ ?_
    apply (h_diff.and h_lipsch).mono
    on_goal 1 => rintro a ⟨-, ha_bound⟩
    show ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ ≤ b a + ‖F' a‖
    replace ha_bound : ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ := ha_bound x hx
    calc
      ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ =
          ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a) - ‖x - x₀‖⁻¹ • F' a (x - x₀)‖ := by rw [smul_sub]
      _ ≤ ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a)‖ + ‖‖x - x₀‖⁻¹ • F' a (x - x₀)‖ := norm_sub_le _ _
      _ = ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a‖ + ‖x - x₀‖⁻¹ * ‖F' a (x - x₀)‖ := by
        rw [norm_smul_of_nonneg, norm_smul_of_nonneg] <;> exact nneg _
      _ ≤ ‖x - x₀‖⁻¹ * (b a * ‖x - x₀‖) + ‖x - x₀‖⁻¹ * (‖F' a‖ * ‖x - x₀‖) := by
        gcongr; exact (F' a).le_opNorm _
      _ ≤ b a + ‖F' a‖ := ?_
    simp only [← div_eq_inv_mul]
    apply_rules [add_le_add, div_le_of_le_mul₀] <;> first | rfl | positivity
  · exact b_int.add hF'_int.norm
  · apply h_diff.mono
    intro a ha
    suffices Tendsto (fun x ↦ ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (𝓝 x₀) (𝓝 0) by simpa
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun x ↦ ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a - F' a (x - x₀)‖) = fun x ↦
        ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ := by
      ext x
      rw [norm_smul_of_nonneg (nneg _)]
    rwa [hasFDerivAt_iff_tendsto, this] at ha

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz in a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip {F' : α → H →L[𝕜] E}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ ball x₀ δ, AEStronglyMeasurable (F x) μ ∧ x ∈ s :=
    eventually_nhds_iff_ball.mp (hF_meas.and hs)
  choose hδ_meas hδε using hδ
  replace h_lip : ∀ᵐ a : α ∂μ, ∀ x ∈ ball x₀ δ, ‖F x a - F x₀ a‖ ≤ |bound a| * ‖x - x₀‖ :=
    h_lip.mono fun a lip x hx ↦ lip.norm_sub_le (hδε x hx) (mem_of_mem_nhds hs)
  replace bound_integrable := bound_integrable.norm
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' (ball_mem_nhds x₀ δ_pos) <;> assumption

section

variable {F : 𝕜 → α → E} {x₀ : 𝕜} {s : Set 𝕜}

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_integral_of_dominated_loc_of_lip {F' : α → E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  set L : E →L[𝕜] 𝕜 →L[𝕜] E := ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1
  replace h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (L (F' a)) x₀ :=
    h_diff.mono fun x hx ↦ hx.hasFDerivAt
  have hm : AEStronglyMeasurable (L ∘ F') μ := L.continuous.comp_aestronglyMeasurable hF'_meas
  obtain ⟨hF'_int, key⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    hs hF_meas hF_int hm h_lipsch bound_integrable h_diff
  replace hF'_int : Integrable F' μ := by
    rw [← integrable_norm_iff hm] at hF'_int
    simpa [L, (· ∘ ·), integrable_norm_iff hF'_meas] using hF'_int
  refine ⟨hF'_int, ?_⟩
  by_cases hE : CompleteSpace E; swap
  · simpa [integral, hE] using hasDerivAt_const x₀ 0
  simp_rw [hasDerivAt_iff_hasFDerivAt] at h_diff ⊢
  simpa only [(· ∘ ·), ContinuousLinearMap.integral_comp_comm _ hF'_int] using key

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, ε_pos, hε⟩
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ (hε x₀_in)
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 ↦ F x a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x x_in ↦ (ha_deriv x (hε x_in)).hasDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x (hε x_in)).trans (le_abs_self _)
  exact hasDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ ε_pos) hF_meas hF_int
    hF'_meas this bound_integrable diff_x₀

end

/-- A real-valued derivative-under-the-integral helper. -/
theorem local_hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℝ → α → ℝ} {F' : ℝ → α → ℝ} {x₀ : ℝ} {s : Set ℝ} {bound : α → ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧
      HasDerivAt (fun n => ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound bound_integrable h_diff

noncomputable def heatKernel (t r : ℝ) : ℝ :=
  (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(r ^ 2) / (4 * t))

noncomputable def heatKernelRDeriv (t r : ℝ) : ℝ :=
  -(r / (2 * t)) * heatKernel t r

noncomputable def heatPrefactor (t : ℝ) : ℝ :=
  (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)

lemma norm_heatKernelRDeriv (t r : ℝ) :
    ‖heatKernelRDeriv t r‖ =
      |(2 * t)⁻¹| * |r| * |heatPrefactor t| * Real.exp (-(r ^ 2) / (4 * t)) := by
  unfold heatKernelRDeriv heatKernel heatPrefactor
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_div, abs_mul, abs_mul, abs_exp]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  rw [show |r| / (2 * |t|) = |(2 * t)⁻¹| * |r| by
    rw [abs_inv, abs_mul, h2]
    ring]
  ring

lemma sq_ineq (u v : ℝ) : u ^ 2 / 2 - v ^ 2 ≤ (v - u) ^ 2 := by
  nlinarith [sq_nonneg (u - 2 * v)]

lemma abs_sq_le {z R : ℝ} (_hR : 0 ≤ R) (hz : |z| ≤ R) : z ^ 2 ≤ R ^ 2 := by
  nlinarith [abs_nonneg z, abs_mul_abs_self z, hz]

lemma exp_arg_bound {t R z y : ℝ} (ht : 0 < t) (_hR : 0 ≤ R) (hz : |z| ≤ R) :
    -((z - y) ^ 2) / (4 * t) ≤ R ^ 2 / (4 * t) - y ^ 2 / (8 * t) := by
  have hsq1 : y ^ 2 / 2 - z ^ 2 ≤ (z - y) ^ 2 := by
    simpa [sub_eq_add_neg, add_comm] using sq_ineq y z
  have hsqz : z ^ 2 ≤ R ^ 2 := abs_sq_le _hR hz
  have hmul : -(2 * ((z - y) ^ 2)) ≤ 2 * R ^ 2 - y ^ 2 := by nlinarith
  have hden8 : 0 ≤ 8 * t := by positivity
  have hdiv := div_le_div_of_nonneg_right hmul hden8
  convert hdiv using 1 <;> ring

lemma exp_bound {t R z y : ℝ} (ht : 0 < t) (hR : 0 ≤ R) (hz : |z| ≤ R) :
    Real.exp (-((z - y) ^ 2) / (4 * t)) ≤
      Real.exp (R ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
  calc
    Real.exp (-((z - y) ^ 2) / (4 * t))
        ≤ Real.exp (R ^ 2 / (4 * t) - y ^ 2 / (8 * t)) :=
      Real.exp_le_exp.mpr (exp_arg_bound ht hR hz)
    _ = Real.exp (R ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma poly_bound {R z y : ℝ} (_hR : 0 ≤ R) (hz : |z| ≤ R) :
    1 + |z - y| + (z - y) ^ 2 ≤ (4 * R ^ 2 + 4) * (1 + y ^ 2) := by
  have hzy : |z - y| ≤ R + |y| := by
    rw [abs_sub_le_iff]
    constructor
    · have hzle : z ≤ R := (abs_le.mp hz).2
      linarith [neg_le_abs y]
    · have hzge : -R ≤ z := (abs_le.mp hz).1
      linarith [le_abs_self y]
  have habs_non : 0 ≤ |z - y| := abs_nonneg _
  have hsq_abs : (z - y) ^ 2 = |z - y| ^ 2 := by rw [sq_abs]
  have hsq_bound : (z - y) ^ 2 ≤ (R + |y|) ^ 2 := by
    rw [hsq_abs]
    exact pow_le_pow_left₀ habs_non hzy 2
  have hlin_bound : |z - y| ≤ 1 + (R + |y|) ^ 2 := by
    have : R + |y| ≤ 1 + (R + |y|) ^ 2 := by
      nlinarith [sq_nonneg (R + |y|)]
    exact hzy.trans this
  have hquad : (R + |y|) ^ 2 ≤ 2 * (R ^ 2 + |y| ^ 2) := by
    exact (add_sq_le : (R + |y|) ^ 2 ≤ 2 * (R ^ 2 + |y| ^ 2))
  have hyabs : |y| ^ 2 = y ^ 2 := by rw [sq_abs]
  calc
    1 + |z - y| + (z - y) ^ 2
        ≤ 1 + (1 + (R + |y|) ^ 2) + (R + |y|) ^ 2 := by gcongr
    _ ≤ 2 + 2 * (2 * (R ^ 2 + |y| ^ 2)) := by nlinarith
    _ = 2 + 4 * R ^ 2 + 4 * y ^ 2 := by rw [hyabs]; ring
    _ ≤ (4 * R ^ 2 + 4) * (1 + y ^ 2) := by
      have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
      have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
      have hprod : 0 ≤ R ^ 2 * y ^ 2 := mul_nonneg hR2 hy2
      ring_nf
      nlinarith

lemma heatKernelRDeriv_mul_bound {B t R z y fy : ℝ} (hB : 0 ≤ B) (hfy : |fy| ≤ B)
    (ht : 0 < t) (hR : 0 ≤ R) (hz : |z| ≤ R) :
    ‖heatKernelRDeriv t (z - y) * fy‖ ≤
      (B * |(2 * t)⁻¹| * |heatPrefactor t| * Real.exp (R ^ 2 / (4 * t)) *
          (4 * R ^ 2 + 4)) *
        ((1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2)) := by
  have hC0 : 0 ≤ B * |(2 * t)⁻¹| * |heatPrefactor t| := by positivity
  calc
    ‖heatKernelRDeriv t (z - y) * fy‖
        ≤ ‖heatKernelRDeriv t (z - y)‖ * ‖fy‖ := norm_mul_le _ _
    _ = (|(2 * t)⁻¹| * |z - y| * |heatPrefactor t| *
          Real.exp (-((z - y) ^ 2) / (4 * t))) * |fy| := by
      rw [norm_heatKernelRDeriv, Real.norm_eq_abs]
    _ ≤ (|(2 * t)⁻¹| * |z - y| * |heatPrefactor t| *
          Real.exp (-((z - y) ^ 2) / (4 * t))) * B := by
      gcongr
    _ ≤ (B * |(2 * t)⁻¹| * |heatPrefactor t|) *
          ((1 + |z - y| + (z - y) ^ 2) *
            Real.exp (-((z - y) ^ 2) / (4 * t))) := by
      have habs_le : |z - y| ≤ 1 + |z - y| + (z - y) ^ 2 := by
        nlinarith [sq_nonneg (z - y)]
      have hmul :
          |z - y| * Real.exp (-((z - y) ^ 2) / (4 * t)) ≤
            (1 + |z - y| + (z - y) ^ 2) *
              Real.exp (-((z - y) ^ 2) / (4 * t)) :=
        mul_le_mul_of_nonneg_right habs_le (Real.exp_nonneg _)
      calc
        (|(2 * t)⁻¹| * |z - y| * |heatPrefactor t| *
            Real.exp (-((z - y) ^ 2) / (4 * t))) * B
            = (B * |(2 * t)⁻¹| * |heatPrefactor t|) *
                (|z - y| * Real.exp (-((z - y) ^ 2) / (4 * t))) := by ring
        _ ≤ (B * |(2 * t)⁻¹| * |heatPrefactor t|) *
              ((1 + |z - y| + (z - y) ^ 2) *
                Real.exp (-((z - y) ^ 2) / (4 * t))) :=
          mul_le_mul_of_nonneg_left hmul hC0
    _ ≤ (B * |(2 * t)⁻¹| * |heatPrefactor t|) *
          (((4 * R ^ 2 + 4) * (1 + y ^ 2)) *
            (Real.exp (R ^ 2 / (4 * t)) *
              Real.exp (-(1 / (8 * t)) * y ^ 2))) := by
      have hp := poly_bound hR hz (y := y)
      have he := exp_bound ht hR hz (y := y)
      have hbpoly : 0 ≤ (4 * R ^ 2 + 4) * (1 + y ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hp he (Real.exp_nonneg _) hbpoly) hC0
    _ = (B * |(2 * t)⁻¹| * |heatPrefactor t| * Real.exp (R ^ 2 / (4 * t)) *
          (4 * R ^ 2 + 4)) *
        ((1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2)) := by ring

noncomputable def heatKernelRRDeriv (t r : ℝ) : ℝ :=
  ((r ^ 2) / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t r

lemma norm_heatKernelRRDeriv_le (t r : ℝ) :
    ‖heatKernelRRDeriv t r‖ ≤
      (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * (1 + r ^ 2) *
        |heatPrefactor t| * Real.exp (-(r ^ 2) / (4 * t)) := by
  have hcoef :
      |r ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
        |(4 * t ^ 2)⁻¹| * r ^ 2 + |(2 * t)⁻¹| := by
    calc
      |r ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
          ≤ |r ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
      _ = |(4 * t ^ 2)⁻¹| * r ^ 2 + |(2 * t)⁻¹| := by
        rw [abs_div]
        rw [show |r ^ 2| = r ^ 2 by exact abs_of_nonneg (sq_nonneg r)]
        rw [show r ^ 2 / |4 * t ^ 2| = |(4 * t ^ 2)⁻¹| * r ^ 2 by
          rw [abs_inv]
          ring]
        rw [show |1 / (2 * t)| = |(2 * t)⁻¹| by rw [one_div]]
  have hpoly :
      |(4 * t ^ 2)⁻¹| * r ^ 2 + |(2 * t)⁻¹| ≤
        (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * (1 + r ^ 2) := by
    have hA : 0 ≤ |(4 * t ^ 2)⁻¹| := abs_nonneg _
    have hB : 0 ≤ |(2 * t)⁻¹| := abs_nonneg _
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith [mul_nonneg hA hr2, mul_nonneg hB hr2]
  calc
    ‖heatKernelRRDeriv t r‖ =
        |r ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * |heatPrefactor t| *
          Real.exp (-(r ^ 2) / (4 * t)) := by
      unfold heatKernelRRDeriv heatKernel heatPrefactor
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_exp]
      ring
    _ ≤ ((|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * (1 + r ^ 2)) *
          |heatPrefactor t| * Real.exp (-(r ^ 2) / (4 * t)) := by
      have hcoefpoly := hcoef.trans hpoly
      gcongr
    _ = (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * (1 + r ^ 2) *
          |heatPrefactor t| * Real.exp (-(r ^ 2) / (4 * t)) := by ring

lemma heatKernelRRDeriv_mul_bound {B t R z y fy : ℝ} (hB : 0 ≤ B) (hfy : |fy| ≤ B)
    (ht : 0 < t) (hR : 0 ≤ R) (hz : |z| ≤ R) :
    ‖heatKernelRRDeriv t (z - y) * fy‖ ≤
      (B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t| *
          Real.exp (R ^ 2 / (4 * t)) * (4 * R ^ 2 + 4)) *
        ((1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2)) := by
  have hrr := norm_heatKernelRRDeriv_le t (z - y)
  calc
    ‖heatKernelRRDeriv t (z - y) * fy‖
        ≤ ‖heatKernelRRDeriv t (z - y)‖ * ‖fy‖ := norm_mul_le _ _
    _ ≤ ((|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * (1 + (z - y) ^ 2) *
          |heatPrefactor t| * Real.exp (-((z - y) ^ 2) / (4 * t))) * B := by
      rw [Real.norm_eq_abs]
      exact mul_le_mul hrr hfy (abs_nonneg _) (by positivity)
    _ ≤ (B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t|) *
          (((4 * R ^ 2 + 4) * (1 + y ^ 2)) *
            (Real.exp (R ^ 2 / (4 * t)) *
              Real.exp (-(1 / (8 * t)) * y ^ 2))) := by
      have hp0 : 1 + (z - y) ^ 2 ≤ 1 + |z - y| + (z - y) ^ 2 := by
        nlinarith [abs_nonneg (z - y)]
      have hp := hp0.trans (poly_bound hR hz (y := y))
      have he := exp_bound ht hR hz (y := y)
      have hC : 0 ≤ B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t| := by
        positivity
      have hbpoly : 0 ≤ (4 * R ^ 2 + 4) * (1 + y ^ 2) := by positivity
      have hmul :
          (1 + (z - y) ^ 2) * Real.exp (-((z - y) ^ 2) / (4 * t)) ≤
            ((4 * R ^ 2 + 4) * (1 + y ^ 2)) *
              (Real.exp (R ^ 2 / (4 * t)) *
                Real.exp (-(1 / (8 * t)) * y ^ 2)) :=
        mul_le_mul hp he (Real.exp_nonneg _) hbpoly
      calc
        ((|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * (1 + (z - y) ^ 2) *
            |heatPrefactor t| * Real.exp (-((z - y) ^ 2) / (4 * t))) * B
            = (B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t|) *
                ((1 + (z - y) ^ 2) *
                  Real.exp (-((z - y) ^ 2) / (4 * t))) := by ring
        _ ≤ (B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t|) *
              (((4 * R ^ 2 + 4) * (1 + y ^ 2)) *
                (Real.exp (R ^ 2 / (4 * t)) *
                  Real.exp (-(1 / (8 * t)) * y ^ 2))) :=
          mul_le_mul_of_nonneg_left hmul hC
    _ = (B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t| *
          Real.exp (R ^ 2 / (4 * t)) * (4 * R ^ 2 + 4)) *
        ((1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2)) := by ring

lemma integrable_one_add_sq_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => (1 + y ^ 2) * Real.exp (-a * y ^ 2)) := by
  have h0 : Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) :=
    integrable_exp_neg_mul_sq ha
  have h2 : Integrable (fun y : ℝ => y ^ 2 * Real.exp (-a * y ^ 2)) := by
    simpa [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq ha (by norm_num : (-1 : ℝ) < 2)
  simpa [add_mul] using h0.add h2

lemma integrable_gaussian_shift_pos {t x : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => Real.exp (-((x - y) ^ 2) / (4 * t))) := by
  have hb : 0 < (4 * t)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) ht)
  have h0 : Integrable (fun y : ℝ => Real.exp (-((4 * t)⁻¹) * y ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have h1 : Integrable (fun y : ℝ => Real.exp (-((4 * t)⁻¹) * (y - x) ^ 2)) :=
    h0.comp_sub_right x
  convert h1 using 1
  ext y
  ring_nf

lemma integrable_heatSolution_integrand (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) {t x : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => Real.exp (-((x - y) ^ 2) / (4 * t)) * f y) := by
  rcases hf_bdd with ⟨M, hM⟩
  refine ((integrable_gaussian_shift_pos (t := t) (x := x) ht).const_mul M).mono' ?_ ?_
  · exact ((continuous_exp.comp (by fun_prop)).mul hf_cont).aestronglyMeasurable
  · filter_upwards with y
    have hgy_nonneg : 0 ≤ Real.exp (-((x - y) ^ 2) / (4 * t)) :=
      Real.exp_nonneg _
    calc
      ‖Real.exp (-((x - y) ^ 2) / (4 * t)) * f y‖
          = Real.exp (-((x - y) ^ 2) / (4 * t)) * |f y| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgy_nonneg]
      _ ≤ Real.exp (-((x - y) ^ 2) / (4 * t)) * M :=
        mul_le_mul_of_nonneg_left (hM y) hgy_nonneg
      _ = M * Real.exp (-((x - y) ^ 2) / (4 * t)) := by ring

lemma integrable_heatKernel_mul (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) {t x : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => heatKernel t (x - y) * f y) := by
  unfold heatKernel
  simpa [mul_assoc] using
    (integrable_heatSolution_integrand f hf_cont hf_bdd (t := t) (x := x) ht).const_mul
      ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))

lemma heatSolution_eq_integral_kernel (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y : ℝ, heatKernel t (x - y) * f y := by
  rw [heatSolution, if_pos ht]
  unfold heatKernel
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext y
  ring

lemma continuous_heatKernel_r (t : ℝ) : Continuous (fun r : ℝ => heatKernel t r) := by
  unfold heatKernel
  fun_prop

lemma continuous_heatKernelRDeriv_r (t : ℝ) :
    Continuous (fun r : ℝ => heatKernelRDeriv t r) := by
  unfold heatKernelRDeriv heatKernel
  fun_prop

lemma exp_quad_hasDerivAt (t r : ℝ) :
    HasDerivAt (fun r => Real.exp (-(r ^ 2) / (4 * t)))
      (Real.exp (-(r ^ 2) / (4 * t)) * (-(r / (2 * t)))) r := by
  have h : HasDerivAt (fun r => -(r ^ 2) / (4 * t)) (-(r / (2 * t))) r := by
    convert (((hasDerivAt_id r).pow 2).neg.div_const (4 * t)) using 1
    simp [id]
    ring_nf
  simpa using h.exp

lemma heatKernel_hasDerivAt_r (t r : ℝ) :
    HasDerivAt (fun r => heatKernel t r) (heatKernelRDeriv t r) r := by
  unfold heatKernelRDeriv heatKernel
  have h :=
    (hasDerivAt_const r ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))).mul
      (exp_quad_hasDerivAt t r)
  convert h using 1
  ring_nf

lemma heatKernel_shift_hasDerivAt_r (t x y : ℝ) :
    HasDerivAt (fun z => heatKernel t (z - y)) (heatKernelRDeriv t (x - y)) x := by
  simpa using
    (heatKernel_hasDerivAt_r t (x - y)).comp x ((hasDerivAt_id x).sub_const y)

lemma abs_le_of_mem_ball_one {z y : ℝ} (hz : z ∈ Metric.ball y (1 : ℝ)) :
    |z| ≤ |y| + 1 := by
  rw [Metric.mem_ball, Real.dist_eq] at hz
  apply abs_le.mpr
  constructor
  · have h1 : -(z - y) ≤ |z - y| := neg_le_abs (z - y)
    have hy : -y ≤ |y| := neg_le_abs y
    linarith
  · have h1 : z - y ≤ |z - y| := le_abs_self (z - y)
    have hy : y ≤ |y| := le_abs_self y
    linarith

noncomputable def heatSolutionUx (f : ℝ → ℝ) (t y : ℝ) : ℝ :=
  ∫ η : ℝ, heatKernelRDeriv t (y - η) * f η

lemma heatSolution_hasDerivAt_spatial
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z => heatSolution f t z) (heatSolutionUx f t y) y := by
  rcases hf_bdd with ⟨M, hM⟩
  let B := |M|
  have hB : 0 ≤ B := abs_nonneg M
  have hBbdd : ∀ x, |f x| ≤ B := fun x => (hM x).trans (le_abs_self M)
  let R := |y| + 1
  let C := B * |(2 * t)⁻¹| * |heatPrefactor t| * Real.exp (R ^ 2 / (4 * t)) *
    (4 * R ^ 2 + 4)
  let bound : ℝ → ℝ := fun η =>
    C * ((1 + η ^ 2) * Real.exp (-(1 / (8 * t)) * η ^ 2))
  have hbound_int : Integrable bound := by
    have ha : 0 < (1 / (8 * t)) := by positivity
    simpa [bound, C] using (integrable_one_add_sq_mul_exp_neg_mul_sq ha).const_mul C
  have hF_meas :
      ∀ᶠ z in nhds y,
        AEStronglyMeasurable (fun η : ℝ => heatKernel t (z - η) * f η) volume := by
    refine Filter.Eventually.of_forall ?_
    intro z
    exact ((continuous_heatKernel_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  have hF_int : Integrable (fun η : ℝ => heatKernel t (y - η) * f η) volume :=
    integrable_heatKernel_mul f hf_cont (by exact ⟨M, hM⟩) ht
  have hF'_meas :
      AEStronglyMeasurable (fun η : ℝ => heatKernelRDeriv t (y - η) * f η) volume := by
    exact ((continuous_heatKernelRDeriv_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  have h_bound :
      ∀ᵐ η ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball y (1 : ℝ),
        ‖heatKernelRDeriv t (z - η) * f η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall ?_
    intro η z hz
    have hzR : |z| ≤ R := by exact abs_le_of_mem_ball_one hz
    have hR : 0 ≤ R := by positivity
    simpa [bound, C] using heatKernelRDeriv_mul_bound hB (hBbdd η) ht hR hzR
  have h_diff :
      ∀ᵐ η ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball y (1 : ℝ),
        HasDerivAt (fun z => heatKernel t (z - η) * f η)
          (heatKernelRDeriv t (z - η) * f η) z := by
    refine Filter.Eventually.of_forall ?_
    intro η z hz
    exact (heatKernel_shift_hasDerivAt_r t z η).mul_const (f η)
  have h := local_hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z η => heatKernel t (z - η) * f η)
    (F' := fun z η => heatKernelRDeriv t (z - η) * f η)
    (x₀ := y) (s := Metric.ball y (1 : ℝ)) (bound := bound) (μ := (volume : Measure ℝ))
    (Metric.ball_mem_nhds y zero_lt_one) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hderiv :
      HasDerivAt (fun z => ∫ η : ℝ, heatKernel t (z - η) * f η)
        (heatSolutionUx f t y) y := by
    simpa [heatSolutionUx] using h.2
  exact hderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun z => heatSolution_eq_integral_kernel f ht z))

lemma neg_div_hasDerivAt (t r : ℝ) :
    HasDerivAt (fun r => -(r / (2 * t))) (-(1 / (2 * t))) r := by
  simpa using ((hasDerivAt_id r).div_const (2 * t)).neg

lemma heatKernelRDeriv_hasDerivAt (t r : ℝ) :
    HasDerivAt (fun r => heatKernelRDeriv t r) (heatKernelRRDeriv t r) r := by
  unfold heatKernelRDeriv heatKernelRRDeriv
  have h := (neg_div_hasDerivAt t r).mul (heatKernel_hasDerivAt_r t r)
  unfold heatKernelRDeriv at h
  convert h using 1
  unfold heatKernel
  ring_nf

lemma heatKernelRDeriv_shift_hasDerivAt (t x y : ℝ) :
    HasDerivAt (fun z => heatKernelRDeriv t (z - y)) (heatKernelRRDeriv t (x - y)) x := by
  simpa using
    (heatKernelRDeriv_hasDerivAt t (x - y)).comp x ((hasDerivAt_id x).sub_const y)

lemma continuous_heatKernelRRDeriv_r (t : ℝ) :
    Continuous (fun r : ℝ => heatKernelRRDeriv t r) := by
  unfold heatKernelRRDeriv heatKernel
  fun_prop

lemma integrable_heatKernelRDeriv_mul (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) {t x : ℝ} (ht : 0 < t) :
    Integrable (fun η : ℝ => heatKernelRDeriv t (x - η) * f η) := by
  rcases hf_bdd with ⟨M, hM⟩
  let B := |M|
  have hB : 0 ≤ B := abs_nonneg M
  have hBbdd : ∀ x, |f x| ≤ B := fun x => (hM x).trans (le_abs_self M)
  let R := |x| + 1
  let C := B * |(2 * t)⁻¹| * |heatPrefactor t| * Real.exp (R ^ 2 / (4 * t)) *
    (4 * R ^ 2 + 4)
  let bound : ℝ → ℝ := fun η =>
    C * ((1 + η ^ 2) * Real.exp (-(1 / (8 * t)) * η ^ 2))
  have hbound_int : Integrable bound := by
    have ha : 0 < (1 / (8 * t)) := by positivity
    simpa [bound, C] using (integrable_one_add_sq_mul_exp_neg_mul_sq ha).const_mul C
  refine hbound_int.mono' ?_ ?_
  · exact ((continuous_heatKernelRDeriv_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro η
    have hxR : |x| ≤ R := by simp [R]
    have hR : 0 ≤ R := by positivity
    simpa [bound, C] using heatKernelRDeriv_mul_bound hB (hBbdd η) ht hR hxR

lemma integrable_heatKernelRRDeriv_mul (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) {t x : ℝ} (ht : 0 < t) :
    Integrable (fun η : ℝ => heatKernelRRDeriv t (x - η) * f η) := by
  rcases hf_bdd with ⟨M, hM⟩
  let B := |M|
  have hB : 0 ≤ B := abs_nonneg M
  have hBbdd : ∀ x, |f x| ≤ B := fun x => (hM x).trans (le_abs_self M)
  let R := |x| + 1
  let C := B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t| *
    Real.exp (R ^ 2 / (4 * t)) * (4 * R ^ 2 + 4)
  let bound : ℝ → ℝ := fun η =>
    C * ((1 + η ^ 2) * Real.exp (-(1 / (8 * t)) * η ^ 2))
  have hbound_int : Integrable bound := by
    have ha : 0 < (1 / (8 * t)) := by positivity
    simpa [bound, C] using (integrable_one_add_sq_mul_exp_neg_mul_sq ha).const_mul C
  refine hbound_int.mono' ?_ ?_
  · exact ((continuous_heatKernelRRDeriv_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro η
    have hxR : |x| ≤ R := by simp [R]
    have hR : 0 ≤ R := by positivity
    simpa [bound, C] using heatKernelRRDeriv_mul_bound hB (hBbdd η) ht hR hxR

noncomputable def heatSolutionUxx (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ η : ℝ, heatKernelRRDeriv t (x - η) * f η

lemma heatSolutionUx_hasDerivAt
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatSolutionUx f t) (heatSolutionUxx f t x) x := by
  rcases hf_bdd with ⟨M, hM⟩
  let B := |M|
  have hB : 0 ≤ B := abs_nonneg M
  have hBbdd : ∀ x, |f x| ≤ B := fun x => (hM x).trans (le_abs_self M)
  let R := |x| + 1
  let C := B * (|(4 * t ^ 2)⁻¹| + |(2 * t)⁻¹|) * |heatPrefactor t| *
    Real.exp (R ^ 2 / (4 * t)) * (4 * R ^ 2 + 4)
  let bound : ℝ → ℝ := fun η =>
    C * ((1 + η ^ 2) * Real.exp (-(1 / (8 * t)) * η ^ 2))
  have hbound_int : Integrable bound := by
    have ha : 0 < (1 / (8 * t)) := by positivity
    simpa [bound, C] using (integrable_one_add_sq_mul_exp_neg_mul_sq ha).const_mul C
  have hF_meas :
      ∀ᶠ z in nhds x,
        AEStronglyMeasurable (fun η : ℝ => heatKernelRDeriv t (z - η) * f η) volume := by
    refine Filter.Eventually.of_forall ?_
    intro z
    exact ((continuous_heatKernelRDeriv_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  have hF_int : Integrable (fun η : ℝ => heatKernelRDeriv t (x - η) * f η) volume :=
    integrable_heatKernelRDeriv_mul f hf_cont (by exact ⟨M, hM⟩) ht
  have hF'_meas :
      AEStronglyMeasurable (fun η : ℝ => heatKernelRRDeriv t (x - η) * f η) volume := by
    exact ((continuous_heatKernelRRDeriv_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  have h_bound :
      ∀ᵐ η ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball x (1 : ℝ),
        ‖heatKernelRRDeriv t (z - η) * f η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall ?_
    intro η z hz
    have hzR : |z| ≤ R := by exact abs_le_of_mem_ball_one hz
    have hR : 0 ≤ R := by positivity
    simpa [bound, C] using heatKernelRRDeriv_mul_bound hB (hBbdd η) ht hR hzR
  have h_diff :
      ∀ᵐ η ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball x (1 : ℝ),
        HasDerivAt (fun z => heatKernelRDeriv t (z - η) * f η)
          (heatKernelRRDeriv t (z - η) * f η) z := by
    refine Filter.Eventually.of_forall ?_
    intro η z hz
    exact (heatKernelRDeriv_shift_hasDerivAt t z η).mul_const (f η)
  have h := local_hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z η => heatKernelRDeriv t (z - η) * f η)
    (F' := fun z η => heatKernelRRDeriv t (z - η) * f η)
    (x₀ := x) (s := Metric.ball x (1 : ℝ)) (bound := bound) (μ := (volume : Measure ℝ))
    (Metric.ball_mem_nhds x zero_lt_one) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [heatSolutionUx, heatSolutionUxx] using h.2

lemma heatKernelRRDeriv_mul_time_bound {B t R s x y fy : ℝ} (hB : 0 ≤ B)
    (hfy : |fy| ≤ B) (ht : 0 < t) (hR : 0 ≤ R) (hxR : |x| ≤ R)
    (hslo : t / 2 ≤ s) (hshi : s ≤ 3 * t / 2) :
    ‖heatKernelRRDeriv s (x - y) * fy‖ ≤
      (B * (|(t ^ 2)⁻¹| + |t⁻¹|) *
          |((2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))| *
          Real.exp (R ^ 2 / (2 * t)) * (4 * R ^ 2 + 4)) *
        ((1 + y ^ 2) * Real.exp (-(1 / (12 * t)) * y ^ 2)) := by
  have hspos : 0 < s := by linarith
  have hbase :=
    heatKernelRRDeriv_mul_bound (B := B) (t := s) (R := R) (z := x) (y := y)
      (fy := fy) hB hfy hspos hR hxR
  have hcoef1 : |(4 * s ^ 2)⁻¹| ≤ |(t ^ 2)⁻¹| := by
    have ht2pos : 0 < t ^ 2 := sq_pos_of_pos ht
    have hs2pos : 0 < 4 * s ^ 2 := by positivity
    have hden : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith [sq_nonneg (2 * s - t)]
    rw [abs_of_pos (inv_pos.mpr hs2pos), abs_of_pos (inv_pos.mpr ht2pos)]
    exact (inv_le_inv₀ hs2pos ht2pos).2 hden
  have hcoef2 : |(2 * s)⁻¹| ≤ |t⁻¹| := by
    have h2spos : 0 < 2 * s := by positivity
    rw [abs_of_pos (inv_pos.mpr h2spos), abs_of_pos (inv_pos.mpr ht)]
    exact (inv_le_inv₀ h2spos ht).2 (by linarith)
  have hcoef : |(4 * s ^ 2)⁻¹| + |(2 * s)⁻¹| ≤ |(t ^ 2)⁻¹| + |t⁻¹| :=
    add_le_add hcoef1 hcoef2
  have hpref :
      |heatPrefactor s| ≤ |((2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))| := by
    unfold heatPrefactor
    have hden1 : 2 * Real.pi * t ≤ 4 * Real.pi * s := by nlinarith [Real.pi_pos]
    have hpos1 : 0 < 2 * Real.pi * t := by positivity
    have hpos2 : 0 < 4 * Real.pi * s := by positivity
    have hinv : (4 * Real.pi * s)⁻¹ ≤ (2 * Real.pi * t)⁻¹ :=
      (inv_le_inv₀ hpos2 hpos1).2 hden1
    have hnon1 : 0 ≤ (4 * Real.pi * s)⁻¹ := le_of_lt (inv_pos.mpr hpos2)
    have hnon2 : 0 ≤ (2 * Real.pi * t)⁻¹ := le_of_lt (inv_pos.mpr hpos1)
    rw [abs_of_nonneg (Real.rpow_nonneg hnon1 _),
      abs_of_nonneg (Real.rpow_nonneg hnon2 _)]
    exact Real.rpow_le_rpow hnon1 hinv (by norm_num)
  have hexpC : Real.exp (R ^ 2 / (4 * s)) ≤ Real.exp (R ^ 2 / (2 * t)) := by
    apply Real.exp_le_exp.mpr
    have hden : 2 * t ≤ 4 * s := by linarith
    exact div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) hden
  have hexptail :
      Real.exp (-(1 / (8 * s)) * y ^ 2) ≤
        Real.exp (-(1 / (12 * t)) * y ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hden : 8 * s ≤ 12 * t := by linarith
    have h8s : 0 < 8 * s := by positivity
    have h12t : 0 < 12 * t := by positivity
    have hinv : (12 * t)⁻¹ ≤ (8 * s)⁻¹ := (inv_le_inv₀ h12t h8s).2 hden
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have hmul := mul_le_mul_of_nonneg_right hinv hy2
    rw [one_div, one_div]
    nlinarith
  calc
    ‖heatKernelRRDeriv s (x - y) * fy‖
        ≤ (B * (|(4 * s ^ 2)⁻¹| + |(2 * s)⁻¹|) * |heatPrefactor s| *
            Real.exp (R ^ 2 / (4 * s)) * (4 * R ^ 2 + 4)) *
          ((1 + y ^ 2) * Real.exp (-(1 / (8 * s)) * y ^ 2)) := hbase
    _ ≤ (B * (|(t ^ 2)⁻¹| + |t⁻¹|) *
            |((2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))| *
            Real.exp (R ^ 2 / (2 * t)) * (4 * R ^ 2 + 4)) *
          ((1 + y ^ 2) * Real.exp (-(1 / (12 * t)) * y ^ 2)) := by
      have hleft :
          B * (|(4 * s ^ 2)⁻¹| + |(2 * s)⁻¹|) * |heatPrefactor s| *
              Real.exp (R ^ 2 / (4 * s)) * (4 * R ^ 2 + 4)
            ≤ B * (|(t ^ 2)⁻¹| + |t⁻¹|) *
              |((2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))| *
              Real.exp (R ^ 2 / (2 * t)) * (4 * R ^ 2 + 4) := by
        gcongr
      have hright :
          (1 + y ^ 2) * Real.exp (-(1 / (8 * s)) * y ^ 2) ≤
            (1 + y ^ 2) * Real.exp (-(1 / (12 * t)) * y ^ 2) := by
        exact mul_le_mul_of_nonneg_left hexptail (by positivity)
      exact mul_le_mul hleft hright (by positivity) (by positivity)

lemma heatPrefactor_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt heatPrefactor (-(1 / (2 * t)) * heatPrefactor t) t := by
  unfold heatPrefactor
  have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  have hbase :
      HasDerivAt (fun s : ℝ => (4 * Real.pi * s)⁻¹)
        (-(4 * Real.pi) / (4 * Real.pi * t) ^ 2) t := by
    have hne : 4 * Real.pi * t ≠ 0 := by positivity
    convert (hlin.inv hne) using 1
  have hpos : 0 < (4 * Real.pi * t)⁻¹ := by positivity
  have hpow := hbase.rpow_const (p := ((1 : ℝ) / 2)) (Or.inl hpos.ne')
  convert hpow using 1
  rw [show (1 : ℝ) / 2 - 1 = -((1 : ℝ) / 2) by ring]
  rw [Real.rpow_neg (le_of_lt hpos) ((1 : ℝ) / 2)]
  rw [← Real.sqrt_eq_rpow ((4 * Real.pi * t)⁻¹)]
  have hsne : √((4 * Real.pi * t)⁻¹) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp [show 4 * Real.pi * t ≠ 0 by positivity, show t ≠ 0 by positivity,
    Real.pi_ne_zero, hsne]
  rw [show 1 / (t * 4 * Real.pi) = (4 * Real.pi * t)⁻¹ by ring]
  rw [Real.sq_sqrt (le_of_lt hpos)]
  field_simp [show 4 * Real.pi * t ≠ 0 by positivity, show t ≠ 0 by positivity,
    Real.pi_ne_zero]

lemma exp_quad_time_hasDerivAt {t r : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => Real.exp (-(r ^ 2) / (4 * t)))
      (Real.exp (-(r ^ 2) / (4 * t)) * (r ^ 2 / (4 * t ^ 2))) t := by
  have harg :
      HasDerivAt (fun t => -(r ^ 2) / (4 * t)) (r ^ 2 / (4 * t ^ 2)) t := by
    have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(1 : ℝ) / t ^ 2) t := by
      simpa using (hasDerivAt_id t).inv (ne_of_gt ht)
    have h := hinv.const_mul (-(r ^ 2 / 4))
    convert h using 1
    · funext s
      ring
    · ring
  simpa using harg.exp

lemma heatKernel_hasDerivAt_t {t r : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => heatKernel t r) (heatKernelRRDeriv t r) t := by
  unfold heatKernelRRDeriv heatKernel
  have h :=
    (heatPrefactor_hasDerivAt (t := t) ht).mul
      (exp_quad_time_hasDerivAt (t := t) (r := r) ht)
  unfold heatPrefactor at h
  convert h using 1
  ring_nf

lemma heatKernel_shift_hasDerivAt_t {t x y : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatKernel s (x - y)) (heatKernelRRDeriv t (x - y)) t := by
  simpa using heatKernel_hasDerivAt_t (t := t) (r := x - y) ht

lemma heatSolution_hasDerivAt_time
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution f s x) (heatSolutionUxx f t x) t := by
  rcases hf_bdd with ⟨M, hM⟩
  let B := |M|
  have hB : 0 ≤ B := abs_nonneg M
  have hBbdd : ∀ x, |f x| ≤ B := fun x => (hM x).trans (le_abs_self M)
  let R := |x| + 1
  let C :=
    B * (|(t ^ 2)⁻¹| + |t⁻¹|) *
      |((2 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))| *
      Real.exp (R ^ 2 / (2 * t)) * (4 * R ^ 2 + 4)
  let bound : ℝ → ℝ := fun η =>
    C * ((1 + η ^ 2) * Real.exp (-(1 / (12 * t)) * η ^ 2))
  have hbound_int : Integrable bound := by
    have ha : 0 < (1 / (12 * t)) := by positivity
    simpa [bound, C] using (integrable_one_add_sq_mul_exp_neg_mul_sq ha).const_mul C
  have hF_meas :
      ∀ᶠ s in nhds t,
        AEStronglyMeasurable (fun η : ℝ => heatKernel s (x - η) * f η) volume := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact ((continuous_heatKernel_r s).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  have hF_int : Integrable (fun η : ℝ => heatKernel t (x - η) * f η) volume :=
    integrable_heatKernel_mul f hf_cont (by exact ⟨M, hM⟩) ht
  have hF'_meas :
      AEStronglyMeasurable (fun η : ℝ => heatKernelRRDeriv t (x - η) * f η) volume := by
    exact ((continuous_heatKernelRRDeriv_r t).comp (by fun_prop)).mul hf_cont |>.aestronglyMeasurable
  have h_bound :
      ∀ᵐ η ∂(volume : Measure ℝ), ∀ s ∈ Metric.ball t (t / 2),
        ‖heatKernelRRDeriv s (x - η) * f η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall ?_
    intro η s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hslt := abs_lt.mp hs
    have hslo : t / 2 ≤ s := by linarith
    have hshi : s ≤ 3 * t / 2 := by linarith
    have hxR : |x| ≤ R := by simp [R]
    have hR : 0 ≤ R := by positivity
    simpa [bound, C] using
      heatKernelRRDeriv_mul_time_bound hB (hBbdd η) ht hR hxR hslo hshi
  have h_diff :
      ∀ᵐ η ∂(volume : Measure ℝ), ∀ s ∈ Metric.ball t (t / 2),
        HasDerivAt (fun s => heatKernel s (x - η) * f η)
          (heatKernelRRDeriv s (x - η) * f η) s := by
    refine Filter.Eventually.of_forall ?_
    intro η s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hslt := abs_lt.mp hs
    have hspos : 0 < s := by linarith
    exact (heatKernel_shift_hasDerivAt_t (t := s) (x := x) (y := η) hspos).mul_const
      (f η)
  have h := local_hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s η => heatKernel s (x - η) * f η)
    (F' := fun s η => heatKernelRRDeriv s (x - η) * f η)
    (x₀ := t) (s := Metric.ball t (t / 2)) (bound := bound) (μ := (volume : Measure ℝ))
    (Metric.ball_mem_nhds t (by positivity : 0 < t / 2)) hF_meas hF_int hF'_meas
    h_bound hbound_int h_diff
  have hderiv :
      HasDerivAt (fun s => ∫ η : ℝ, heatKernel s (x - η) * f η)
        (heatSolutionUxx f t x) t := by
    simpa [heatSolutionUxx] using h.2
  have hev :
      (fun s => heatSolution f s x) =ᶠ[nhds t]
        (fun s => ∫ η : ℝ, heatKernel s (x - η) * f η) := by
    filter_upwards [Metric.ball_mem_nhds t (by positivity : 0 < t / 2)] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hslt := abs_lt.mp hs
    have hspos : 0 < s := by linarith
    exact heatSolution_eq_integral_kernel f hspos x
  exact hderiv.congr_of_eventuallyEq hev

lemma heatPrefactor_eq_normalized_coeff {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) =
      (√Real.pi)⁻¹ * |(2 * √t)⁻¹| := by
  have hcpos : 0 < 2 * √t := by positivity
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_inv]
  rw [abs_of_pos (inv_pos.mpr hcpos)]
  have hsqrt : √(4 * Real.pi * t) = 2 * √Real.pi * √t := by
    rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
  rw [hsqrt]
  field_simp [show (2 : ℝ) ≠ 0 by norm_num,
    (ne_of_gt (Real.sqrt_pos_of_pos Real.pi_pos)),
    (ne_of_gt (Real.sqrt_pos_of_pos ht))]

lemma integral_gaussian_affine_change (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ z : ℝ, Real.exp (-(z ^ 2)) * f (x + (2 * √t) * z)) =
      |(2 * √t)⁻¹| *
        ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y := by
  let c : ℝ := 2 * √t
  let G : ℝ → ℝ := fun y => Real.exp (-((x - y) ^ 2) / (4 * t)) * f y
  have hmul := MeasureTheory.Measure.integral_comp_mul_left (fun w : ℝ => G (x + w)) c
  have hadd := MeasureTheory.integral_add_left_eq_self (μ := (volume : Measure ℝ)) G x
  calc
    (∫ z : ℝ, Real.exp (-(z ^ 2)) * f (x + (2 * √t) * z))
        = ∫ z : ℝ, G (x + c * z) := by
      congr with z
      have hsqt : (√t) ^ 2 = t := by rw [Real.sq_sqrt (le_of_lt ht)]
      have harg : -((2 * √t * z) ^ 2) / (4 * t) = -(z ^ 2) := by
        rw [show (2 * √t * z) ^ 2 = 4 * t * z ^ 2 by
          rw [mul_pow, mul_pow, hsqt]
          ring]
        field_simp [show t ≠ 0 by positivity]
      simp [G, c, harg]
    _ = |c⁻¹| * ∫ w : ℝ, G (x + w) := by
      simpa [smul_eq_mul] using hmul
    _ = |(2 * √t)⁻¹| *
          ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y := by
      rw [hadd]

lemma heatSolution_eq_normalized_gaussian (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x =
      ∫ z : ℝ, (√Real.pi)⁻¹ *
        (Real.exp (-(z ^ 2)) * f (x + (2 * √t) * z)) := by
  rw [heatSolution, if_pos ht]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_gaussian_affine_change f ht x]
  rw [heatPrefactor_eq_normalized_coeff ht]
  ring

lemma integral_normalized_gaussian_const (a : ℝ) :
    (∫ z : ℝ, (√Real.pi)⁻¹ * Real.exp (-(z ^ 2)) * a) = a := by
  have hgauss : (∫ z : ℝ, Real.exp (-(z ^ 2)) = √Real.pi) := by
    simpa [one_mul, div_one] using (integral_gaussian (1 : ℝ))
  calc
    (∫ z : ℝ, (√Real.pi)⁻¹ * Real.exp (-(z ^ 2)) * a)
        = ((√Real.pi)⁻¹ * a) * ∫ z : ℝ, Real.exp (-(z ^ 2)) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext z
      ring
    _ = a := by
      rw [hgauss]
      field_simp [(ne_of_gt (Real.sqrt_pos_of_pos Real.pi_pos))]

lemma heatSolution_tendsto_initial
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => heatSolution f t x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  rcases hf_bdd with ⟨M, hM⟩
  let B : ℝ := |M|
  have hB_nonneg : 0 ≤ B := abs_nonneg M
  have hBbdd : ∀ y, |f y| ≤ B := fun y => (hM y).trans (le_abs_self M)
  let F : ℝ → ℝ → ℝ :=
    fun t z => (√Real.pi)⁻¹ * Real.exp (-(z ^ 2)) * f (x + (2 * √t) * z)
  let bound : ℝ → ℝ := fun z => ((√Real.pi)⁻¹ * B) * Real.exp (-(z ^ 2))
  have hbound_int : Integrable bound := by
    have hbase : Integrable (fun z : ℝ => Real.exp (-(1 : ℝ) * z ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    convert hbase.const_mul ((√Real.pi)⁻¹ * B) using 1
    ext z
    simp [bound]
  have hF_meas :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), AEStronglyMeasurable (F t) volume := by
    refine Filter.Eventually.of_forall ?_
    intro t
    dsimp [F]
    exact ((continuous_const.mul (continuous_exp.comp (by fun_prop))).mul
      (hf_cont.comp (by fun_prop))).aestronglyMeasurable
  have h_bound :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ z ∂(volume : Measure ℝ), ‖F t z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall ?_
    intro t
    refine Filter.Eventually.of_forall ?_
    intro z
    have hexp_nonneg : 0 ≤ Real.exp (-(z ^ 2)) := Real.exp_nonneg _
    have hinv_nonneg : 0 ≤ (√Real.pi)⁻¹ := by positivity
    calc
      ‖F t z‖ =
          (√Real.pi)⁻¹ * Real.exp (-(z ^ 2)) *
            |f (x + (2 * √t) * z)| := by
        simp [F, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg, mul_assoc]
      _ ≤ (√Real.pi)⁻¹ * Real.exp (-(z ^ 2)) * B := by
        gcongr
        exact hBbdd (x + (2 * √t) * z)
      _ = bound z := by ring
  have h_cont :
      ∀ᵐ z ∂(volume : Measure ℝ),
        ContinuousWithinAt (fun t => F t z) (Set.Ioi 0) 0 := by
    refine Filter.Eventually.of_forall ?_
    intro z
    dsimp [F]
    fun_prop
  have hcont_int :
      ContinuousWithinAt (fun t : ℝ => ∫ z : ℝ, F t z) (Set.Ioi 0) 0 :=
    MeasureTheory.continuousWithinAt_of_dominated hF_meas h_bound hbound_int h_cont
  have hlim_int :
      Filter.Tendsto (fun t : ℝ => ∫ z : ℝ, F t z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
    have h0 : (∫ z : ℝ, F 0 z) = f x := by
      simpa [F] using integral_normalized_gaussian_const (f x)
    simpa [ContinuousWithinAt, h0] using hcont_int
  refine hlim_int.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t htpos
  simpa [F, mul_assoc] using (heatSolution_eq_normalized_gaussian f htpos x).symm

end ProofSupport



theorem heat_kernel_solves_heat_equation (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    -- The PDE on (0, ∞) × ℝ.
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    -- Initial condition recovered as a one-sided limit at t = 0.
    (∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  constructor
  · intro t ht x
    refine ⟨heatSolutionUx f t, heatSolutionUxx f t x, ?_, ?_, ?_⟩
    · intro y
      exact heatSolution_hasDerivAt_spatial f hf_cont hf_bdd ht y
    · exact heatSolutionUx_hasDerivAt f hf_cont hf_bdd ht x
    · exact heatSolution_hasDerivAt_time f hf_cont hf_bdd ht x
  · intro x
    exact heatSolution_tendsto_initial f hf_cont hf_bdd x


end Submission
