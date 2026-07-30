import Submission.Helpers
import Submission.GlobalFlow

open Filter Metric Set Topology
open scoped NNReal Pointwise

open LeanEval.Dynamics

namespace Submission.OmegaInvariant

/-- A forward tail of the original trajectory stays exponentially close to a
global trajectory through its limiting initial point. -/
theorem dist_shift_le {F G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) (γ β : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hβ : IsIntegralCurve β (fun _ x ↦ G x))
    {x : Plane} (hβ0 : β 0 = x)
    {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    dist (γ (τ + t)) (β t) ≤
      dist (γ τ) x * Real.exp ((K : ℝ) * t) := by
  have hshiftRaw := hγ.comp_add τ
  have hshift :
      IsIntegralCurveOn (γ ∘ (· + τ)) (fun _ x ↦ G x) (Ici 0) := by
    intro u hu
    have huRaw : u ∈ -τ +ᵥ Ici (0 : ℝ) := by
      rw [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm]
      simpa using add_nonneg hu hτ
    have hsub : Ici (0 : ℝ) ⊆ -τ +ᵥ Ici (0 : ℝ) := by
      intro q hq
      rw [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm]
      simpa using add_nonneg hq hτ
    have hderiv := (hshiftRaw u huRaw).mono hsub
    have hmem : γ (u + τ) ∈ γ '' Ici (0 : ℝ) :=
      ⟨u + τ, add_nonneg hu hτ, rfl⟩
    simpa [Function.comp_def, hEq hmem] using hderiv
  have hbound :=
    dist_le_of_trajectories_ODE
      (a := (0 : ℝ)) (b := t) (K := K)
      (v := fun _ x ↦ G x)
      (f := γ ∘ (· + τ)) (g := β)
      (δ := dist (γ τ) x)
      (fun _ ↦ hG)
      (hshift.continuousOn.mono (by
        intro u hu
        exact hu.1))
      (fun u hu ↦ (hshift u hu.1).mono (Ici_subset_Ici.mpr hu.1))
      hβ.continuous.continuousOn
      (fun u _ ↦ (hβ u).hasDerivWithinAt)
      (by simp [hβ0])
      t ⟨ht, le_rfl⟩
  simpa [Function.comp_def, add_comm] using hbound

/-- Every nonnegative point of a global comparison trajectory through an
omega-limit point is again an omega-limit point. -/
theorem nonneg_mem_omegaSet {F G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) (γ β : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hβ : IsIntegralCurve β (fun _ x ↦ G x))
    {x : Plane} (hβ0 : β 0 = x)
    (hx : x ∈ Helpers.omegaSet γ) {t : ℝ} (ht : 0 ≤ t) :
    β t ∈ Helpers.omegaSet γ := by
  rw [Helpers.mem_omegaSet_iff_mapClusterPt] at hx ⊢
  obtain ⟨τ, hγτ, hτ⟩ := hx.exists_seq_tendsto
  have hτnonneg : ∀ᶠ n in atTop, 0 ≤ τ n :=
    hτ.eventually (eventually_ge_atTop (0 : ℝ))
  have hdist0 :
      Tendsto (fun n ↦ dist (γ (τ n)) x) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_iff_dist_tendsto_zero.mp hγτ)
  have hmajor :
      Tendsto
        (fun n ↦
          dist (γ (τ n)) x * Real.exp ((K : ℝ) * t))
        atTop (𝓝 0) := by
    simpa using hdist0.mul_const (Real.exp ((K : ℝ) * t))
  have hshiftlim :
      Tendsto (γ ∘ fun n ↦ τ n + t) atTop (𝓝 (β t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    · filter_upwards [hτnonneg] with n hn
      simpa [Function.comp_def] using
        dist_shift_le hG γ β hγ hEq hβ hβ0 hn ht
    · exact hmajor
  apply MapClusterPt.of_comp
    (tendsto_atTop_add_const_right atTop t hτ)
  exact hshiftlim.mapClusterPt

/-- The reverse-time analogue of `dist_shift_le`.  The original trajectory is
only used at nonnegative times, while the global comparison trajectory may be
followed backwards. -/
theorem dist_reverse_shift_le {F G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) (γ β : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hβ : IsIntegralCurve β (fun _ x ↦ G x))
    {x : Plane} (hβ0 : β 0 = x)
    {τ t : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) :
    dist (γ (τ - t)) (β (-t)) ≤
      dist (γ τ) x * Real.exp ((K : ℝ) * t) := by
  have hneg : LipschitzWith K (fun z ↦ -G z) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_neg_neg] using hG.dist_le_mul y z
  have hfcont :
      ContinuousOn (fun u ↦ γ (τ - u)) (Icc (0 : ℝ) t) := by
    exact hγ.continuousOn.comp
      (continuous_const.sub continuous_id).continuousOn (by
        intro u hu
        exact sub_nonneg.mpr (hu.2.trans htτ))
  have hfderiv (u : ℝ) (hu : u ∈ Ico (0 : ℝ) t) :
      HasDerivWithinAt (fun q ↦ γ (τ - q))
        (-G (γ (τ - u))) (Ici u) u := by
    have hpos : 0 < τ - u := sub_pos.mpr (hu.2.trans_le htτ)
    have hbase :
        HasDerivAt γ (F (γ (τ - u))) (τ - u) :=
      (hγ (τ - u) hpos.le).hasDerivAt (Ici_mem_nhds hpos)
    have hmem : γ (τ - u) ∈ γ '' Ici (0 : ℝ) :=
      ⟨τ - u, hpos.le, rfl⟩
    simpa [hEq hmem] using
      (hbase.comp_const_sub τ u).hasDerivWithinAt
  have hgcont :
      ContinuousOn (fun u ↦ β (-u)) (Icc (0 : ℝ) t) := by
    exact (hβ.continuous.comp continuous_neg).continuousOn
  have hgderiv (u : ℝ) (_hu : u ∈ Ico (0 : ℝ) t) :
      HasDerivWithinAt (fun q ↦ β (-q))
        (-G (β (-u))) (Ici u) u := by
    simpa only [zero_sub] using
      ((hβ (0 - u)).comp_const_sub 0 u).hasDerivWithinAt
  have hbound :=
    dist_le_of_trajectories_ODE
      (a := (0 : ℝ)) (b := t) (K := K)
      (v := fun _ z ↦ -G z)
      (f := fun u ↦ γ (τ - u)) (g := fun u ↦ β (-u))
      (δ := dist (γ τ) x)
      (fun _ ↦ hneg) hfcont hfderiv hgcont hgderiv
      (by simp [hβ0])
      t ⟨ht, le_rfl⟩
  simpa using hbound

/-- Every nonpositive point of the global comparison trajectory through an
omega-limit point is again an omega-limit point. -/
theorem nonpos_mem_omegaSet {F G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) (γ β : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hβ : IsIntegralCurve β (fun _ x ↦ G x))
    {x : Plane} (hβ0 : β 0 = x)
    (hx : x ∈ Helpers.omegaSet γ) {t : ℝ} (ht : t ≤ 0) :
    β t ∈ Helpers.omegaSet γ := by
  rw [Helpers.mem_omegaSet_iff_mapClusterPt] at hx ⊢
  obtain ⟨τ, hγτ, hτ⟩ := hx.exists_seq_tendsto
  have hτlarge : ∀ᶠ n in atTop, -t ≤ τ n :=
    hτ.eventually (eventually_ge_atTop (-t))
  have hdist0 :
      Tendsto (fun n ↦ dist (γ (τ n)) x) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_iff_dist_tendsto_zero.mp hγτ)
  have hmajor :
      Tendsto
        (fun n ↦
          dist (γ (τ n)) x * Real.exp ((K : ℝ) * (-t)))
        atTop (𝓝 0) := by
    simpa using hdist0.mul_const (Real.exp ((K : ℝ) * (-t)))
  have hshiftlim :
      Tendsto (γ ∘ fun n ↦ τ n + t) atTop (𝓝 (β t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    · filter_upwards [hτlarge] with n hn
      simpa [Function.comp_def] using
        dist_reverse_shift_le hG γ β hγ hEq hβ hβ0
          (neg_nonneg.mpr ht) hn
    · simpa only [mul_neg] using hmajor
  apply MapClusterPt.of_comp
    (tendsto_atTop_add_const_right atTop t hτ)
  exact hshiftlim.mapClusterPt

/-- A global comparison trajectory through an omega-limit point remains in the
omega-limit set for every real time. -/
theorem mem_omegaSet {F G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) (γ β : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hβ : IsIntegralCurve β (fun _ x ↦ G x))
    {x : Plane} (hβ0 : β 0 = x)
    (hx : x ∈ Helpers.omegaSet γ) (t : ℝ) :
    β t ∈ Helpers.omegaSet γ := by
  rcases le_total 0 t with ht | ht
  · exact nonneg_mem_omegaSet hG γ β hγ hEq hβ hβ0 hx ht
  · exact nonpos_mem_omegaSet hG γ β hγ hEq hβ hβ0 hx ht

theorem range_subset_omegaSet {F G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) (γ β : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hβ : IsIntegralCurve β (fun _ x ↦ G x))
    {x : Plane} (hβ0 : β 0 = x)
    (hx : x ∈ Helpers.omegaSet γ) :
    range β ⊆ Helpers.omegaSet γ := by
  rintro _ ⟨t, rfl⟩
  exact mem_omegaSet hG γ β hγ hEq hβ hβ0 hx t

end Submission.OmegaInvariant
