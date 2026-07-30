import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.RiemannMapping
import Submission.BoundedMomentReplacement
import Submission.Runge

open Filter Function Metric Set
open scoped Pointwise Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- A complex analytic germ which vanishes at the origin admits a
second-order Taylor expansion with a cubic norm remainder on a nontrivial
closed ball.  The coefficients are exposed as scalars because they become
the first two Laurent coefficients after precomposition with a resolvent. -/
theorem exists_cubic_taylor_bound_of_analyticAt
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0) :
    ∃ (c₁ c₂ : ℂ) (B ρ : ℝ),
      0 ≤ B ∧ 0 < ρ ∧
      deriv F 0 = c₁ ∧
      ∀ s : ℂ, ‖s‖ ≤ ρ →
        ‖F s - (s * c₁ + s ^ 2 * c₂)‖ ≤
          B * ‖s‖ ^ 3 := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨B, hB, hBO⟩ :=
    (hp.isBigO_sub_partialSum_pow 3).exists_pos
  obtain ⟨r, hr, hlocal⟩ :=
    Metric.eventually_nhds_iff_ball.mp hBO.bound
  let ρ : ℝ := min (r / 2) 1
  have hρ : 0 < ρ := by
    exact lt_min (half_pos hr) zero_lt_one
  let c₁ : ℂ := p.coeff 1
  let c₂ : ℂ := p.coeff 2
  refine ⟨c₁, c₂, B, ρ, hB.le, hρ, ?_, ?_⟩
  · change deriv F 0 = p.coeff 1
    rw [hp.deriv, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp
  · intro s hs
    have hsr : dist s 0 < r := by
      rw [dist_zero_right]
      calc
        ‖s‖ ≤ ρ := hs
        _ ≤ r / 2 := min_le_left _ _
        _ < r := half_lt_self hr
    have hsBound := hlocal s hsr
    have hp0 : p.coeff 0 = 0 := by
      change p 0 1 = 0
      rw [hp.coeff_zero (1 : Fin 0 → ℂ), hF0]
    have hpartial :
        p.partialSum 3 s = s * c₁ + s ^ 2 * c₂ := by
      simp [FormalMultilinearSeries.partialSum, hp0, c₁, c₂,
        Finset.sum_range_succ]
    simpa only [zero_add, hpartial, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg s) 3)] using hsBound

/-- A cubic Taylor estimate on a ball also gives a linear bound there.
The displayed constant is chosen to remain visibly nonnegative. -/
theorem norm_le_linear_of_cubic_taylor_bound
    (F : ℂ → ℂ) (c₁ c₂ : ℂ) (B ρ : ℝ)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hTaylor :
      ∀ s : ℂ, ‖s‖ ≤ ρ →
        ‖F s - (s * c₁ + s ^ 2 * c₂)‖ ≤
          B * ‖s‖ ^ 3)
    (s : ℂ) (hs : ‖s‖ ≤ ρ) :
    ‖F s‖ ≤
      (B * ρ ^ 2 + ‖c₁‖ + ρ * ‖c₂‖) * ‖s‖ := by
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hs2 : ‖s‖ ^ 2 ≤ ρ ^ 2 := by
    nlinarith
  have hs3 : ‖s‖ ^ 3 ≤ ρ ^ 2 * ‖s‖ := by
    calc
      ‖s‖ ^ 3 = ‖s‖ ^ 2 * ‖s‖ := by ring
      _ ≤ ρ ^ 2 * ‖s‖ :=
        mul_le_mul_of_nonneg_right hs2 hs0
  have hquadratic :
      ‖s‖ ^ 2 * ‖c₂‖ ≤
        (ρ * ‖c₂‖) * ‖s‖ := by
    calc
      ‖s‖ ^ 2 * ‖c₂‖ =
          (‖s‖ * ‖c₂‖) * ‖s‖ := by ring
      _ ≤ (ρ * ‖c₂‖) * ‖s‖ := by
        apply mul_le_mul_of_nonneg_right _ hs0
        exact mul_le_mul_of_nonneg_right hs (norm_nonneg c₂)
  calc
    ‖F s‖ =
        ‖(F s - (s * c₁ + s ^ 2 * c₂)) +
          (s * c₁ + s ^ 2 * c₂)‖ := by
      congr 1
      ring
    _ ≤
        ‖F s - (s * c₁ + s ^ 2 * c₂)‖ +
          ‖s * c₁ + s ^ 2 * c₂‖ :=
      norm_add_le _ _
    _ ≤
        B * ‖s‖ ^ 3 +
          (‖s‖ * ‖c₁‖ + ‖s‖ ^ 2 * ‖c₂‖) := by
      apply add_le_add (hTaylor s hs)
      calc
        ‖s * c₁ + s ^ 2 * c₂‖
            ≤ ‖s * c₁‖ + ‖s ^ 2 * c₂‖ :=
          norm_add_le _ _
        _ = ‖s‖ * ‖c₁‖ + ‖s‖ ^ 2 * ‖c₂‖ := by
          rw [norm_mul, norm_mul, norm_pow]
    _ ≤
        (B * ρ ^ 2) * ‖s‖ +
          (‖c₁‖ * ‖s‖ +
            (ρ * ‖c₂‖) * ‖s‖) := by
      apply add_le_add
      · calc
          B * ‖s‖ ^ 3 ≤ B * (ρ ^ 2 * ‖s‖) :=
            mul_le_mul_of_nonneg_left hs3 hB
          _ = (B * ρ ^ 2) * ‖s‖ := by ring
      · exact add_le_add (le_of_eq (mul_comm _ _)) hquadratic
    _ =
        (B * ρ ^ 2 + ‖c₁‖ + ρ * ‖c₂‖) * ‖s‖ := by
      ring

/-- A function analytic on a neighborhood of `K` restricts to the closed
polynomial algebra when the complement of `K` is connected.  This is the
neighborhood-holomorphic interface to the smooth compact-support Runge
lemma: two nested closed thickenings permit a compactly supported smooth
representative to agree with the analytic function near `K`. -/
theorem exists_analyticOnNhd_restriction_mem_polynomialClosure
    {K U : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ))
    (G : ℂ → ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hG : AnalyticOnNhd ℂ G U) :
    ∃ u : (polynomialFunctions K).topologicalClosure,
      ∀ z : K, (u : C(K, ℂ)) z = G z := by
  have hK : IsCompact K :=
    isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨δ, hδ, hδU⟩ :=
    hK.exists_cthickening_subset_open hU hKU
  let S : Set ℂ := Metric.cthickening (δ / 2) K
  let T : Set ℂ := Metric.cthickening (δ / 4) K
  have hScompact : IsCompact S := by
    exact hK.cthickening
  have hTclosed : IsClosed T :=
    Metric.isClosed_cthickening
  have hSU : S ⊆ U := by
    exact
      (Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) K).trans
        hδU
  have hTintS : T ⊆ interior S := by
    exact
      (Metric.cthickening_subset_thickening'
          (half_pos hδ) (by linarith : δ / 4 < δ / 2) K).trans
        (Metric.thickening_subset_interior_cthickening (δ / 2) K)
  have hKintT : K ⊆ interior T := by
    exact
      (Metric.self_subset_thickening (by positivity : 0 < δ / 4) K).trans
        (Metric.thickening_subset_interior_cthickening (δ / 4) K)
  have hGcontinuousS : ContinuousOn G S :=
    hG.continuousOn.mono hSU
  have hGanalyticInteriorS :
      AnalyticOnNhd ℂ G (interior S) :=
    hG.mono (interior_subset.trans hSU)
  obtain ⟨g, hg, hgc, _hgclose, hgG⟩ :=
    exists_smooth_compactSupport_approx_eqOn
      S T hScompact hTclosed hTintS G hGcontinuousS
        hGanalyticInteriorS 1 zero_lt_one
  have hgDiff :
      DifferentiableOn ℂ g (interior T) := by
    intro z hz
    have hzU : z ∈ U :=
      hSU (interior_subset (hTintS (interior_subset hz)))
    have heq : g =ᶠ[𝓝 z] G := by
      filter_upwards
        [isOpen_interior.mem_nhds hz] with w hw
      exact hgG (interior_subset hw)
    exact
      (heq.differentiableAt_iff.mpr
        (hG z hzU).differentiableAt).differentiableWithinAt
  have hmem :=
    mem_polynomialClosure_of_differentiableOn_nhd
      hKc g hg hgc isOpen_interior hKintT hgDiff
  let u : (polynomialFunctions K).topologicalClosure :=
    ⟨restrictTo g hg.continuous.continuousOn, hmem⟩
  refine ⟨u, fun z ↦ ?_⟩
  change g z = G z
  exact hgG (interior_subset (hKintT z.property))

/-- The pullback of an analytic function by a resolvent belongs to the
closed polynomial algebra whenever the relevant resolvent image stays in
its analytic domain. -/
theorem exists_resolventPullback_mem_polynomialClosure
    {K U V : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (a : ℂ)
    (F : ℂ → ℂ)
    (hU : IsOpen U) (hKU : K ⊆ U) (haU : a ∉ U)
    (hF : AnalyticOnNhd ℂ F V)
    (hmap : MapsTo (fun z : ℂ ↦ (a - z)⁻¹) U V) :
    ∃ u : (polynomialFunctions K).topologicalClosure,
      ∀ z : K,
        (u : C(K, ℂ)) z = F ((a - (z : ℂ))⁻¹) := by
  let r : ℂ → ℂ := fun z ↦ (a - z)⁻¹
  have hr : AnalyticOnNhd ℂ r U := by
    dsimp only [r]
    apply (analyticOnNhd_const.sub analyticOnNhd_id).inv
    intro z hz
    exact sub_ne_zero.mpr fun haz ↦ by
      apply haU
      have haz' : a = z := by
        simpa only using haz
      exact haz'.symm ▸ hz
  have hcomp : AnalyticOnNhd ℂ (F ∘ r) U :=
    hF.comp hr hmap
  obtain ⟨u, hu⟩ :=
    exists_analyticOnNhd_restriction_mem_polynomialClosure
      hKc (F ∘ r) hU hKU hcomp
  exact ⟨u, fun z ↦ hu z⟩

/-- The first bounded-map step used in Mathlib's partial Riemann mapping
development, restated here because that development currently keeps its
intermediate declarations module-private. -/
theorem exists_injective_not_dense_image_deriv_ne_zero
    {V : Set ℂ} (hV : IsOpen V)
    (hVc : IsSimplyConnected V) (hVproper : V ≠ univ) :
    ∃ φ : ℂ → ℂ,
      Injective φ ∧ ¬ Dense (φ '' V) ∧
      ∀ z ∈ V, deriv φ z ≠ 0 := by
  wlog hV0 : 0 ∉ V
  · rw [ne_univ_iff_exists_notMem] at hVproper
    rcases hVproper with ⟨a, ha⟩
    specialize this (hV.vadd (-a)) (by simpa)
      (by simp [hVproper])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨φ, hφinj, hφdense, hφderiv⟩
    refine
      ⟨φ ∘ (-a + ·), hφinj.comp (add_right_injective (-a)),
        ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hφdense
    · simpa [Function.comp_def, deriv_comp_const_add] using
        hφderiv (-a + z) (mapsTo_image _ _ hz)
  rcases
      Complex.exists_continuousOn_pow_eq hVc hV continuousOn_id
        (by rwa [image_id]) two_ne_zero with
    ⟨φ, hφcontinuous, hφinv⟩
  replace hφinv : LeftInverse (· ^ 2) φ :=
    hφinv
  have hφ0 : ∀ z ∈ V, φ z ≠ 0 := by
    intro z hz hφz
    simpa [hφz, (ne_of_mem_of_not_mem hz hV0).symm] using
      hφinv z
  have hφstrict :
      ∀ z ∈ V, HasStrictDerivAt φ (2 * φ z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hφcontinuous.continuousAt (hV.mem_nhds hz)
    · simpa using hasStrictDerivAt_pow 2 (φ z)
    · simpa using hφ0 z hz
    · exact .of_forall hφinv
  refine
    ⟨φ, hφinv.injective, ?_, fun z hz ↦ ?_⟩
  · simp only [Dense, not_forall, mem_closure_iff_frequently,
      not_frequently]
    rcases hVc.nonempty with ⟨x, hx⟩
    use -φ x
    have himage : φ '' V ∈ 𝓝 (φ x) := by
      rw [← (hφstrict x hx).map_nhds_eq (by simpa using hφ0 x hx)]
      exact Filter.image_mem_map (hV.mem_nhds hx)
    rw [nhds_neg, eventually_neg]
    filter_upwards [himage]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hφinv b, hab]
      simp [hφinv a]
    refine hφ0 a ha ?_
    linear_combination hab / 2
  · simpa [(hφstrict z hz).hasDerivAt.deriv] using hφ0 z hz

/-- A simply connected proper plane domain admits an injective
complex-differentiable map into the unit ball with nonzero derivative.
This is the second module-private step of Mathlib's partial Riemann mapping
development, using a Möbius transform of the preceding square-root map. -/
theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero
    {V : Set ℂ} (hV : IsOpen V)
    (hVc : IsSimplyConnected V) (hVproper : V ≠ univ) :
    ∃ φ : ℂ → ℂ,
      MapsTo φ V (ball 0 1) ∧ InjOn φ V ∧
      ∀ z ∈ V, deriv φ z ≠ 0 := by
  rcases
      exists_injective_not_dense_image_deriv_ne_zero
        hV hVc hVproper with
    ⟨φ, hφinj, hφdense, hφderiv⟩
  obtain ⟨x, e, he0, he⟩ :
      ∃ (x : ℂ) (e : ℝ), 0 < e ∧
        ∀ a ∈ V, e < dist (φ a) x := by
    simpa [Dense,
      mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using
      hφdense
  have hφx : ∀ z ∈ V, φ z ≠ x := fun z hz ↦ by
    simpa using he0.trans (he z hz)
  use fun z ↦ e / (φ z - x)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real,
      Real.norm_of_nonneg he0.le, div_lt_one₀]
    · simpa [dist_eq_norm] using he z hz
    · simpa [sub_eq_zero] using hφx z hz
  · intro z hz w hw hzw
    simpa [div_eq_mul_inv, he0.ne', hφinj.eq_iff] using hzw
  · intro z hz
    have hφdiff : DifferentiableAt ℂ φ z :=
      differentiableAt_of_deriv_ne_zero (hφderiv z hz)
    rw [
      (hasDerivAt_const z (e : ℂ)).fun_div
        (hφdiff.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

/-- Normalize Mathlib's bounded injective map on a simply connected plane
domain so that it vanishes at the origin.  Subtracting its value at zero
and dividing by two preserves a nonzero derivative and keeps the image in
the unit ball; no disc-automorphism API is needed. -/
theorem exists_normalized_unitBall_map
    {V : Set ℂ} (hV : IsOpen V) (hVc : IsSimplyConnected V)
    (hVproper : V ≠ univ) (h0V : 0 ∈ V) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F V ∧
      F 0 = 0 ∧ deriv F 0 ≠ 0 ∧
      MapsTo F V (Metric.ball 0 1) := by
  obtain ⟨φ, hφmap, _hφinj, hφderiv⟩ :=
    exists_mapsTo_unitBall_injOn_deriv_ne_zero
      hV hVc hVproper
  have hφdiff : DifferentiableOn ℂ φ V := by
    intro z hz
    exact
      (differentiableAt_of_deriv_ne_zero
        (hφderiv z hz)).differentiableWithinAt
  have hφanalytic : AnalyticOnNhd ℂ φ V :=
    hφdiff.analyticOnNhd hV
  let F : ℂ → ℂ := fun z ↦ (φ z - φ 0) / 2
  have hFanalytic : AnalyticOnNhd ℂ F V := by
    dsimp only [F]
    exact
      (hφanalytic.sub analyticOnNhd_const).div_const (c := (2 : ℂ))
  have hF0 : F 0 = 0 := by
    simp only [F, sub_self, zero_div]
  have hFderiv : deriv F 0 ≠ 0 := by
    have hφ0 : deriv φ 0 ≠ 0 :=
      hφderiv 0 h0V
    dsimp only [F]
    rw [deriv_div_const, deriv_sub_const]
    exact div_ne_zero hφ0 (by norm_num)
  have hFmap : MapsTo F V (Metric.ball 0 1) := by
    intro z hz
    have hφz : ‖φ z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hφmap hz
    have hφ0norm : ‖φ 0‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hφmap h0V
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [F]
    rw [norm_div]
    norm_num
    calc
      ‖φ z - φ 0‖ / 2 ≤ (‖φ z‖ + ‖φ 0‖) / 2 := by
        gcongr
        exact norm_sub_le _ _
      _ < (1 + 1) / 2 := by
        gcongr
      _ = 1 := by norm_num
  exact ⟨F, hFanalytic, hF0, hFderiv, hFmap⟩

/-- Pulling a bounded analytic germ back by the resolvent produces all of
the Laurent data required by `BoundedLaurentCapacity`.  Membership in the
closed polynomial algebra is kept as an explicit input: geometrically it is
obtained by extending the pullback holomorphically to a neighborhood of
`K` and invoking the local Runge layer. -/
theorem exists_boundedLaurentCapacity_of_analytic_germ
    {K : Set ℂ} [CompactSpace K] (a : ℂ)
    (F : ℂ → ℂ)
    (u : (polynomialFunctions K).topologicalClosure)
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hderiv : deriv F 0 ≠ 0)
    (hu :
      ∀ z : K,
        (u : C(K, ℂ)) z = F ((a - (z : ℂ))⁻¹))
    (hnorm :
      ∀ z : K, ‖F ((a - (z : ℂ))⁻¹)‖ ≤ 1) :
    ∃ R : ℝ, ∃ _d : BoundedLaurentCapacity K a R, 0 < R := by
  obtain ⟨c₁, c₂, B, ρ, hB, hρ, hc₁, hTaylor⟩ :=
    exists_cubic_taylor_bound_of_analyticAt F hF hF0
  let R : ℝ := ρ⁻¹
  let L : ℝ := B * ρ ^ 2 + ‖c₁‖ + ρ * ‖c₂‖
  have hR : 0 < R :=
    inv_pos.mpr hρ
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  refine ⟨R, {
    u := u
    c₁ := c₁
    c₂ := c₂
    c₁_ne_zero := ?_
    L := L
    B := B
    L_nonneg := hL
    B_nonneg := hB
    norm_le_one := ?_
    norm_le_inv := ?_
    norm_sub_laurent_le := ?_
  }, hR⟩
  · simpa only [← hc₁] using hderiv
  · intro z
    rw [hu z]
    exact hnorm z
  · intro z hz
    let D : ℝ := dist a (z : ℂ)
    let s : ℂ := (a - (z : ℂ))⁻¹
    have hD : 0 < D :=
      hR.trans_le hz
    have hsNorm : ‖s‖ = D⁻¹ := by
      dsimp only [s, D]
      rw [norm_inv, ← dist_eq_norm]
    have hsρ : ‖s‖ ≤ ρ := by
      rw [hsNorm]
      calc
        D⁻¹ ≤ R⁻¹ :=
          (inv_le_inv₀ hD hR).2 hz
        _ = ρ := by
          simp only [R, inv_inv]
    rw [hu z]
    calc
      ‖F s‖ ≤ L * ‖s‖ :=
        norm_le_linear_of_cubic_taylor_bound
          F c₁ c₂ B ρ hB hρ.le hTaylor s hsρ
      _ = L * D⁻¹ := by rw [hsNorm]
  · intro z hz
    let D : ℝ := dist a (z : ℂ)
    let s : ℂ := (a - (z : ℂ))⁻¹
    have hD : 0 < D :=
      hR.trans_le hz
    have hsNorm : ‖s‖ = D⁻¹ := by
      dsimp only [s, D]
      rw [norm_inv, ← dist_eq_norm]
    have hsρ : ‖s‖ ≤ ρ := by
      rw [hsNorm]
      calc
        D⁻¹ ≤ R⁻¹ :=
          (inv_le_inv₀ hD hR).2 hz
        _ = ρ := by
          simp only [R, inv_inv]
    rw [hu z]
    simpa only [s, D, hsNorm] using hTaylor s hsρ

/-- Normalizing the elementary resolvent by its distance from `K` gives a
bounded Laurent-capacity element without any auxiliary conformal geometry.
The leading coefficient records the pole clearance explicitly; this lemma is
therefore useful when that clearance can be retained in the surrounding
parameter selection. -/
theorem exists_normalizedResolvent_boundedLaurentCapacity
    {K : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (hKne : K.Nonempty)
    (a : ℂ) (ha : a ∉ K) :
    ∃ R : ℝ, ∃ _d : BoundedLaurentCapacity K a R, 0 < R := by
  have hKcompact : IsCompact K :=
    isCompact_iff_compactSpace.mpr inferInstance
  let q : ℝ := infDist a K
  have hq : 0 < q :=
    (hKcompact.isClosed.notMem_iff_infDist_pos hKne).mp ha
  obtain ⟨g, hg⟩ :=
    exists_resolvent_mem_polynomialClosure hKc ha
  let u : (polynomialFunctions K).topologicalClosure :=
    (q : ℂ) • g
  have hqdist (z : K) : q ≤ dist a (z : ℂ) := by
    exact (Metric.le_infDist hKne).mp le_rfl z.property
  refine ⟨1, {
    u := u
    c₁ := (q : ℂ)
    c₂ := 0
    c₁_ne_zero := ?_
    L := q
    B := 0
    L_nonneg := hq.le
    B_nonneg := le_rfl
    norm_le_one := ?_
    norm_le_inv := ?_
    norm_sub_laurent_le := ?_
  }, zero_lt_one⟩
  · exact_mod_cast hq.ne'
  · intro z
    have hdist : 0 < dist a (z : ℂ) :=
      hq.trans_le (hqdist z)
    change ‖(q : ℂ) * (g : C(K, ℂ)) z‖ ≤ 1
    rw [hg z, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le,
      norm_inv, ← dist_eq_norm, ← div_eq_mul_inv]
    exact (div_le_one hdist).2 (hqdist z)
  · intro z _hz
    change
      ‖(q : ℂ) * (g : C(K, ℂ)) z‖ ≤
        q * (dist a (z : ℂ))⁻¹
    rw [hg z, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le,
      norm_inv, ← dist_eq_norm]
  · intro z _hz
    change
      ‖(q : ℂ) * (g : C(K, ℂ)) z -
          ((a - (z : ℂ))⁻¹ * (q : ℂ) +
            (a - (z : ℂ))⁻¹ ^ 2 * 0)‖ ≤
        0 * (dist a (z : ℂ))⁻¹ ^ 3
    simp [hg z, mul_comm]

/-- Combined geometric interface: an analytic function on a resolvent-image
domain, bounded by one on `K`, vanishing at the inversion origin, and with
nonzero derivative there yields a bounded Laurent-capacity element in the
closed polynomial algebra. -/
theorem exists_boundedLaurentCapacity_of_resolvent_domain
    {K U V : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (a : ℂ)
    (F : ℂ → ℂ)
    (hU : IsOpen U) (hKU : K ⊆ U) (haU : a ∉ U)
    (hFV : AnalyticOnNhd ℂ F V)
    (hmap : MapsTo (fun z : ℂ ↦ (a - z)⁻¹) U V)
    (hF0 : F 0 = 0) (hFanalytic0 : AnalyticAt ℂ F 0)
    (hderiv : deriv F 0 ≠ 0)
    (hnorm :
      ∀ z : K, ‖F ((a - (z : ℂ))⁻¹)‖ ≤ 1) :
    ∃ R : ℝ, ∃ _d : BoundedLaurentCapacity K a R, 0 < R := by
  obtain ⟨u, hu⟩ :=
    exists_resolventPullback_mem_polynomialClosure
      hKc a F hU hKU haU hFV hmap
  exact
    exists_boundedLaurentCapacity_of_analytic_germ
      a F u hFanalytic0 hF0 hderiv hu hnorm

/-- A simply connected inversion domain containing the origin supplies a
bounded Laurent-capacity element on `K`.  This is the complete analytic
half of the local continuum construction; the remaining hypotheses are
purely planar geometry of the chosen inversion domain. -/
theorem exists_boundedLaurentCapacity_of_simplyConnected_inversion
    {K U V : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (a : ℂ)
    (hU : IsOpen U) (hKU : K ⊆ U) (haU : a ∉ U)
    (hV : IsOpen V) (hVc : IsSimplyConnected V)
    (hVproper : V ≠ univ) (h0V : 0 ∈ V)
    (hmap : MapsTo (fun z : ℂ ↦ (a - z)⁻¹) U V) :
    ∃ R : ℝ, ∃ _d : BoundedLaurentCapacity K a R, 0 < R := by
  obtain ⟨F, hFanalytic, hF0, hFderiv, hFmap⟩ :=
    exists_normalized_unitBall_map hV hVc hVproper h0V
  have hnorm :
      ∀ z : K, ‖F ((a - (z : ℂ))⁻¹)‖ ≤ 1 := by
    intro z
    have hzV :=
      hFmap (hmap (hKU z.property))
    exact (mem_ball_zero_iff.mp hzV).le
  exact
    exists_boundedLaurentCapacity_of_resolvent_domain
      hKc a F hU hKU haU hFanalytic hmap hF0
        (hFanalytic 0 h0V) hFderiv hnorm

end Submission.Helpers
