import Submission.FlowBox

open Filter Metric Set Topology
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.PeriodicFromSection

theorem exists_pos_time_eq_cluster
    {G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G)
    {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    {A : Set Plane} (hAinv : ∀ x ∈ A, ∀ t, Φ x t ∈ A)
    {p q : Plane} (hpA : p ∈ A) (hqreg : G q ≠ 0)
    (hqcluster : MapClusterPt q atTop (Φ p))
    (hsection : ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ A, z ∈ ball q R →
        Transversal.transverseValue (G q) q z = 0 → z = q) :
    ∃ T : ℝ, 0 < T ∧ Φ p T = q := by
  obtain ⟨R, hR, hsection⟩ := hsection
  obtain ⟨δ, hδ, ρ, hρ, hcross⟩ :=
    FlowBox.exists_unique_transverse_time
      hGcompact hGcont hG hΦ0 hΦ hqreg hR
  obtain ⟨τ, hΦτ, hτ⟩ := hqcluster.exists_seq_tendsto
  have hnear : ∀ᶠ n in atTop, Φ p (τ n) ∈ ball q ρ := by
    exact hΦτ.eventually (ball_mem_nhds q hρ)
  have hlarge : ∀ᶠ n in atTop, δ < τ n :=
    hτ.eventually (eventually_gt_atTop δ)
  obtain ⟨n, hnnear, hnlarge⟩ := (hnear.and hlarge).exists
  obtain ⟨u, hu, _hunique⟩ := hcross (Φ p (τ n)) hnnear
  let T : ℝ := τ n + u
  have hT : 0 < T := by
    dsimp [T]
    linarith [hu.1.1]
  have hpointA : Φ (Φ p (τ n)) u ∈ A :=
    hAinv (Φ p (τ n)) (hAinv p hpA (τ n)) u
  have hpointq : Φ (Φ p (τ n)) u = q :=
    hsection _ hpointA hu.2.1 hu.2.2.1
  refine ⟨T, hT, ?_⟩
  rw [GlobalFlow.globalFlow_add hG hΦ0 hΦ]
  exact hpointq

theorem periodic_of_cluster_and_section_unique
    {G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G)
    {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    {A : Set Plane} (hAinv : ∀ x ∈ A, ∀ t, Φ x t ∈ A)
    {p q : Plane} (hpA : p ∈ A) (hqreg : G q ≠ 0)
    (hqcluster : MapClusterPt q atTop (Φ p))
    (hsection : ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ A, z ∈ ball q R →
        Transversal.transverseValue (G q) q z = 0 → z = q) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic (Φ p) T := by
  obtain ⟨s, hs, hps⟩ :=
    exists_pos_time_eq_cluster hGcompact hGcont hG hΦ0 hΦ
      hAinv hpA hqreg hqcluster hsection
  obtain ⟨τ, hΦτ, hτ⟩ := hqcluster.exists_seq_tendsto
  let σ : ℕ → ℝ := fun n ↦ τ n - s
  have hσ : Tendsto σ atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    filter_upwards
      [hτ.eventually (eventually_ge_atTop (B + s))]
      with n hn
    dsimp only [σ]
    linarith
  have hshift :
      (Φ q ∘ σ) = Φ p ∘ τ := by
    funext n
    dsimp only [Function.comp_apply, σ]
    rw [← hps]
    rw [← GlobalFlow.globalFlow_add hG hΦ0 hΦ]
    congr 2
    ring
  have hqself : MapClusterPt q atTop (Φ q) := by
    apply MapClusterPt.of_comp hσ
    apply Filter.Tendsto.mapClusterPt
    rw [hshift]
    exact hΦτ
  have hqA : q ∈ A := hps ▸ hAinv p hpA s
  obtain ⟨T, hT, hqT⟩ :=
    exists_pos_time_eq_cluster hGcompact hGcont hG hΦ0 hΦ
      hAinv hqA hqreg hqself hsection
  have hpcycle : Φ p (s + T) = Φ p s := by
    rw [GlobalFlow.globalFlow_add hG hΦ0 hΦ, hps, hqT]
  have hperiodic : Function.Periodic (Φ p) T := by
    simpa only [add_sub_cancel_left] using
      Helpers.integralCurve_periodic_of_eq_of_lipschitz
        hG (hΦ p) hpcycle
  exact ⟨T, hT, hperiodic⟩

end Submission.PeriodicFromSection
