import Submission.FinalFrontier

open Function Metric Set
open scoped ContDiff Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- The scale-independent factor in the aggregate raw-correction estimate. -/
def frontierAggregateConstant
    (C : NNReal) (c₂ : ℂ) (B ρ M D : ℝ) : ℝ :=
  4 * M ^ 2 * (C : ℝ) *
      (∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖) +
    28 * scaleReplacementGlobalConstant c₂ *
      Real.pi * (D + 3) ^ 2 * M ^ 2 * (C : ℝ) +
    576 * M ^ 2 * (C : ℝ) *
      (∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
        ‖w‖⁻¹ ^ 3) +
    224 * scaleReplacementFarConstant c₂ B ρ *
      M ^ 2 * (C : ℝ) *
        (∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
          ‖w‖⁻¹ ^ 3)

theorem frontierAggregateConstant_nonneg
    (C : NNReal) (c₂ : ℂ) {B ρ M D : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    0 ≤ frontierAggregateConstant C c₂ B ρ M D := by
  have hnear :
      0 ≤ ∫ w : ℂ in Metric.ball 0 (D + 3), ‖w⁻¹‖ :=
    MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _
  have hfar :
      0 ≤ ∫ w : ℂ in (Metric.ball 0 (D - 3))ᶜ,
          ‖w‖⁻¹ ^ 3 :=
    MeasureTheory.integral_nonneg fun _ ↦ by positivity
  have hglobal :=
    scaleReplacementGlobalConstant_nonneg c₂
  have hreplacement :=
    scaleReplacementFarConstant_nonneg c₂ hB hρ
  dsimp only [frontierAggregateConstant]
  positivity

/-- The quantitative frontier construction, with all universal constants
chosen before the final localization scale. -/
theorem exists_mergelyan_polynomial
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (hfh : AnalyticOnNhd ℂ f (interior K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  classical
  by_cases hKempty : K = ∅
  · subst K
    exact ⟨0, by simp⟩
  have hKne : K.Nonempty :=
    nonempty_iff_ne_empty.mpr hKempty
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp hK
  obtain ⟨c₂, B, ρ, hB, hρ, hTaylor⟩ :=
    exists_baseCapacityGerm_cubic_data
  have hrefSmooth :
      ContDiff ℝ ∞ referenceComplexBump := by
    change
      ContDiff ℝ ∞
        (complexUniformBump 0 1 zero_lt_one)
    exact
      contDiff_complexUniformBump 0 1 zero_lt_one
  have hrefCompact :
      HasCompactSupport referenceComplexBump := by
    change
      HasCompactSupport
        (complexUniformBump 0 1 zero_lt_one)
    exact
      hasCompactSupport_complexUniformBump
        0 1 zero_lt_one
  obtain ⟨Cb, hCb⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      hrefCompact hrefSmooth (by simp)
  obtain ⟨N, τ, hτ, hN⟩ :
      ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧
        IsEmpty (Besicovitch.SatelliteConfig ℂ N τ) :=
    HasBesicovitchCovering.no_satelliteConfig
  let M : ℝ := N * 25
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  let D : ℝ := scaleCapacityRadius ρ + 10
  have hD : 9 < D := by
    have hRpos := scaleCapacityRadius_pos ρ
    dsimp only [D]
    linarith
  have hDcap : scaleCapacityRadius ρ + 3 ≤ D := by
    dsimp only [D]
    linarith
  let E : ℝ :=
    frontierAggregateConstant Cb c₂ B ρ M D
  have hE : 0 ≤ E := by
    exact
      frontierAggregateConstant_nonneg Cb c₂ hB hρ.le
  let κ : ℝ := ‖(2 * Real.pi * Complex.I : ℂ)‖
  have hκ : 0 < κ := by
    dsimp only [κ]
    rw [norm_pos_iff]
    exact
      mul_ne_zero
        (by norm_num [ne_of_gt Real.pi_pos])
        Complex.I_ne_zero
  let Q : ℝ := κ + E + 1
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  let osc : ℝ := κ * ε / (16 * Q)
  have hoscPos : 0 < osc := by
    dsimp only [osc]
    positivity
  have hbudget :
      κ * osc + osc * E < κ * (ε / 4) := by
    have hκE : κ + E < 4 * Q := by
      dsimp only [Q]
      linarith
    have hκε : 0 < κ * ε :=
      mul_pos hκ hε
    calc
      κ * osc + osc * E =
          (κ * ε) * (κ + E) / (16 * Q) := by
        dsimp only [osc]
        ring
      _ < (κ * ε) * (4 * Q) / (16 * Q) := by
        exact
          div_lt_div_of_pos_right
            (mul_lt_mul_of_pos_left hκE hκε)
            (by positivity)
      _ = κ * (ε / 4) := by
        field_simp [hQ.ne']
        ring
  let ηref : ℝ := osc / 16
  have hηref : 0 < ηref := by
    dsimp only [ηref]
    positivity
  obtain ⟨H, Cf, hHsmooth, hHcompact, hHCf, hfamily⟩ :=
    exists_lipschitz_reference_and_arbitrarily_close_smooth_core
      K hK f hfc hfh ηref hηref
  let r : ℝ :=
    min 1 (osc / (48 * ((Cf : ℝ) + 1)))
  have hr : 0 < r := by
    dsimp only [r]
    exact
      lt_min zero_lt_one
        (div_pos hoscPos (by positivity))
  have hrScale :
      r ≤ osc / (48 * ((Cf : ℝ) + 1)) := by
    exact min_le_right _ _
  have hCr :
      3 * (Cf : ℝ) * r ≤ osc / 16 := by
    have hCr' :
        (Cf : ℝ) * r ≤ osc / 48 := by
      calc
        (Cf : ℝ) * r ≤ ((Cf : ℝ) + 1) * r := by
          exact
            mul_le_mul_of_nonneg_right
              (by linarith) hr.le
        _ ≤ ((Cf : ℝ) + 1) *
              (osc / (48 * ((Cf : ℝ) + 1))) := by
          gcongr
        _ = osc / 48 := by
          field_simp
    linarith
  let δ : ℝ := r / 8
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hδr : δ < r / 2 := by
    dsimp only [δ]
    linarith
  let σ : ℝ := min (ε / 4) (osc / 16)
  have hσ : 0 < σ := by
    dsimp only [σ]
    exact lt_min (by positivity) (by positivity)
  have hσε : σ ≤ ε / 4 :=
    min_le_left _ _
  have hσosc : σ ≤ osc / 16 :=
    min_le_right _ _
  obtain ⟨g, hgsmooth, hgcompact, hfg, hgf, hgosc⟩ :=
    hfamily δ hδ σ hσ
  have hosc :
      ∀ (i : ℂ) (w : ℂ),
        w ∈ Metric.ball i (3 * r) →
          ‖g w - g i‖ ≤ osc := by
    intro i w hw
    have hd :
        dist w i < 3 * r :=
      Metric.mem_ball.mp hw
    have hgo := hgosc w i
    rw [dist_eq_norm] at hgo
    have hCd :
        (Cf : ℝ) * dist w i ≤
          3 * (Cf : ℝ) * r := by
      have hCnonneg : 0 ≤ (Cf : ℝ) :=
        NNReal.coe_nonneg Cf
      nlinarith
    have hηeq : 2 * ηref = osc / 8 := by
      dsimp only [ηref]
      ring
    linarith
  obtain ⟨ψ, hψsmooth, hψcompact, hψnorm,
      hnearSupport, hfarDisjoint, hDψDisjoint⟩ :=
    exists_frontierCutoff_locallyOne
      K hK hKne hδ hr hδr hfh hgf
  let S : Set ℂ :=
    Metric.thickening (r / 2) (frontier K)
  have hfrontier : IsCompact (frontier K) :=
    hK.of_isClosed_subset
      isClosed_frontier hK.isClosed.frontier_subset
  obtain ⟨A, t, _hAdisjoint, htight, hcardNat⟩ :=
    exists_tight_uniform_besicovitch_cover_of_no_satelliteConfig
      (frontier K) hfrontier r hr N τ hτ hN
  let c : t → ℂ :=
    fun i ↦ (i.1.2.1 : ℂ)
  have hcover :
      S ⊆ ⋃ i : t,
        Metric.ball (c i) (3 * r / 2) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ :=
      Metric.mem_thickening_iff.mp hz
    rcases mem_iUnion.mp (htight hx) with ⟨i, hxi⟩
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [Metric.mem_ball]
    have hxi' :
        dist x (c i) < r := by
      exact Metric.mem_ball.mp hxi
    exact
      (dist_triangle z x (c i)).trans_lt
        (by linarith)
  have hcard :
      ∀ w : ℂ,
        (activeUniformBumps c r hr w).card ≤ M := by
    intro w
    dsimp only [M]
    exact_mod_cast hcardNat w
  choose q₀ a R d _hq ha hδlow hδhigh hRadiusRaw
      hc₁ hc₂ hLinearRaw hCubic using
    fun i : t ↦
      exists_scaleControlled_polygonalCapacity
        hK hKc c₂ B ρ hB hρ hTaylor
          i.1.2.1.property r hr
  have hRadius :
      ∀ i, R i = scaleCapacityRadius ρ * r := by
    intro i
    rw [hRadiusRaw i]
    dsimp only [scaleCapacityRadius]
    have hr0 : 0 ≤ r := hr.le
    calc
      max (7 * r) (4 * r * ρ⁻¹) =
          max (7 * r) ((4 * ρ⁻¹) * r) := by
        rw [show 4 * r * ρ⁻¹ = (4 * ρ⁻¹) * r by ring]
      _ = max 7 (4 * ρ⁻¹) * r :=
        (max_mul_of_nonneg 7 (4 * ρ⁻¹) hr0).symm
  have hLinear :
      ∀ i, (d i).L =
        4 * scaleCapacityLinearConstant c₂ B ρ * r := by
    intro i
    simpa only [scaleCapacityLinearConstant] using
      hLinearRaw i
  let χ :=
    uniformSmoothPartition S c r hr hcover
  let b : t → ℂ :=
    fun i ↦ g (c i)
  have hχ :
      χ.IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) := by
    exact
      uniformSmoothPartition_isSubordinate
        S c r hr hcover
  have hres :
      ‖frontierLocalizationResidualMap (K := K)
          χ ψ g b hψsmooth hgsmooth‖ ≤ osc := by
    apply
      norm_frontierLocalizationResidualMap_le_of_subordinate
        χ ψ g c (3 * r) osc hψsmooth hgsmooth hχ
          hoscPos.le hψnorm
    intro i z hz
    exact
      hosc (c i) z
        (Metric.mem_ball.mpr hz)
  let u :
      t → (polynomialFunctions K).topologicalClosure :=
    fun i ↦
      boundedMomentReplacement (d i)
        (∫ w : ℂ,
          rawPartitionCorrectionDensity
            χ ψ g b i w)
        (∫ w : ℂ,
          (w - a i) *
            rawPartitionCorrectionDensity
              χ ψ g b i w)
  have hraw :
      ∀ z : K,
        ‖∑ i,
            ((∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  rawPartitionCorrectionDensity
                    χ ψ g b i w) -
              (u i : C(K, ℂ)) z)‖ ≤
          osc * E := by
    intro z
    simpa only [χ, b, u, E,
      frontierAggregateConstant] using
      norm_sum_rawPartitionCorrection_sub_boundedReplacement_le
        S Cb hCb c q₀ a r hr hcover ψ g b
          hψsmooth hgsmooth osc M D hψnorm hoscPos.le hM hD
            (fun i w hw ↦ hosc (c i) w hw)
            hcard ha c₂ B ρ hB hρ R d hδlow hδhigh
              hRadius hc₁ hc₂ hLinear hCubic hDcap z
  have he₁ : 0 ≤ osc * E :=
    mul_nonneg hoscPos.le hE
  have hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S := by
    exact hnearSupport
  have hfinalError :
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * osc +
          osc * E <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ *
          ((ε / 2) / 2) := by
    change κ * osc + osc * E < κ * ((ε / 2) / 2)
    rw [show (ε / 2) / 2 = ε / 4 by ring]
    exact hbudget
  obtain ⟨p, hp⟩ :=
    exists_polynomial_approx_of_rawCorrectionAggregate
      hKc χ ψ g c b (3 * r)
        hψsmooth hψcompact hgsmooth hgcompact hχ
          hnearS hfarDisjoint hDψDisjoint u
            osc (osc * E) he₁ hres hraw
              (ε / 2) (by positivity) hfinalError
  refine ⟨p, ?_⟩
  intro z hz
  calc
    ‖f z - p.eval z‖ ≤
        ‖f z - g z‖ + ‖g z - p.eval z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < σ + ε / 2 :=
      add_lt_add (hfg z hz) (hp z hz)
    _ ≤ ε / 4 + ε / 2 := by
      gcongr
    _ < ε := by
      linarith

end Submission.Helpers
