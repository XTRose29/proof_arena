import Submission.SectionHits

open Filter Function Metric Set Topology
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.SectionHitFamily

noncomputable section

/-- One flow-box section works uniformly for all nearby omega-limit points
which already lie on that section.  Each such point is approached by exact,
arbitrarily late hits of the original trajectory. -/
theorem exists_radius_exact_hits_near_section
    {F G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G) (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    {q : Plane} (hqreg : G q ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ⦃z : Plane⦄,
        z ∈ Helpers.omegaSet γ →
        z ∈ ball q ρ →
        Transversal.transverseValue (G q) q z = 0 →
        ∃ σ : ℕ → ℝ,
          (∀ n, 0 ≤ σ n) ∧
          Tendsto σ atTop atTop ∧
          Tendsto (γ ∘ σ) atTop (𝓝 z) ∧
          ∀ n,
            Transversal.transverseValue (G q) q (γ (σ n)) = 0 := by
  obtain ⟨δ, hδ, ρ, hρ, hcross⟩ :=
    FlowBox.exists_unique_transverse_time
      hGcompact hGcont hG hΦ0 hΦ hqreg
        (R := (1 : ℝ)) zero_lt_one
  refine ⟨ρ, hρ, ?_⟩
  intro z hzOmega hzBall hzLine
  rw [Helpers.mem_omegaSet_iff_mapClusterPt] at hzOmega
  obtain ⟨τ, hγτ, hτ⟩ := hzOmega.exists_seq_tendsto
  have hnear : ∀ᶠ n in atTop, γ (τ n) ∈ ball q ρ :=
    hγτ.eventually (isOpen_ball.mem_nhds hzBall)
  have hlarge : ∀ᶠ n in atTop, δ ≤ τ n :=
    hτ.eventually (eventually_ge_atTop δ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hnear.and hlarge)
  let τ' : ℕ → ℝ := fun n ↦ τ (n + N)
  have hτ' : Tendsto τ' atTop atTop :=
    hτ.comp (tendsto_add_atTop_nat N)
  have hγτ' : Tendsto (γ ∘ τ') atTop (𝓝 z) := by
    simpa only [τ', Function.comp_def] using
      hγτ.comp (tendsto_add_atTop_nat N)
  have hτ'near (n : ℕ) : γ (τ' n) ∈ ball q ρ :=
    (hN (n + N) (by omega)).1
  have hτ'large (n : ℕ) : δ ≤ τ' n :=
    (hN (n + N) (by omega)).2
  choose u hu _hunique using fun n ↦ hcross (γ (τ' n)) (hτ'near n)
  have hvalueLim :
      Tendsto
        (fun n ↦
          Transversal.transverseValue (G q) q (γ (τ' n)))
        atTop (𝓝 0) := by
    have hcont :
        Continuous
          (fun y ↦ Transversal.transverseValue (G q) q y) :=
      (Transversal.transverseFunctional (G q)).continuous.comp
        (continuous_id.sub continuous_const)
    have hlim := hcont.tendsto z |>.comp hγτ'
    simpa only [Function.comp_def, hzLine] using hlim
  have huLim : Tendsto u atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    · exact Eventually.of_forall fun n ↦ by
        simpa only [Real.dist_eq, sub_zero] using hu n |>.2.2.2
    · simpa using hvalueLim.abs.const_mul 2
  let σ : ℕ → ℝ := fun n ↦ τ' n + u n
  have hσ : Tendsto σ atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    filter_upwards [hτ'.eventually (eventually_ge_atTop (B + δ))]
      with n hn
    dsimp only [σ]
    linarith [(hu n).1.1]
  have hσnonneg (n : ℕ) : 0 ≤ σ n := by
    dsimp only [σ]
    linarith [(hu n).1.1, hτ'large n]
  have hshift (n : ℕ) :
      Φ (γ (τ' n)) (u n) = γ (σ n) := by
    apply SectionHits.globalFlow_eq_shift hG γ hγ hEq hΦ0 hΦ
    · linarith [hδ, hτ'large n]
    · linarith [(hu n).1.1, hτ'large n]
  have hpointLim :
      Tendsto (fun n ↦ Φ (γ (τ' n)) (u n))
        atTop (𝓝 z) := by
    have hjoint :=
      (GlobalFlow.continuous_globalFlow
        hGcompact hGcont hG hΦ0 hΦ).tendsto (z, 0)
    have hpair := hγτ'.prodMk_nhds huLim
    have := hjoint.comp hpair
    simpa only [Function.comp_def, Function.uncurry_apply_pair,
      hΦ0] using this
  refine ⟨σ, hσnonneg, hσ, ?_, ?_⟩
  · simpa only [Function.comp_def, ← hshift] using hpointLim
  · intro n
    rw [← hshift]
    exact (hu n).2.2.1

end

end Submission.SectionHitFamily
