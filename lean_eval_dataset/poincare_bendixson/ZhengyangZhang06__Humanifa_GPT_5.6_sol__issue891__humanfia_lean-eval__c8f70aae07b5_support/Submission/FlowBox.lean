import Submission.Transversal

open Filter Metric Set Topology
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.FlowBox

noncomputable section

/-- Nearby points admit a unique small time correction onto the affine
transversal through a regular point. -/
theorem exists_unique_transverse_time
    {G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G)
    {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    {p : Plane} (hp : G p ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ y ∈ ball p ρ,
        ∃! t : ℝ, t ∈ Icc (-δ) δ ∧
          Φ y t ∈ ball p R ∧
          Transversal.transverseValue (G p) p (Φ y t) = 0 ∧
          |t| ≤
            2 * |Transversal.transverseValue (G p) p y| := by
  obtain ⟨r₀, hr₀, hvel₀⟩ :=
    Transversal.exists_ball_velocityValue_pos hGcont hp
  let r : ℝ := min r₀ R
  have hr : 0 < r := lt_min hr₀ hR
  have hvel :
      ∀ y ∈ ball p r, (1 / 2 : ℝ) <
        Transversal.velocityValue G p y := by
    intro y hy
    change dist y p < r at hy
    apply hvel₀ y
    change dist y p < r₀
    exact hy.trans_le (min_le_left _ _)
  obtain ⟨D, hD⟩ :=
    GlobalFlow.exists_globalFlow_time_lipschitzWith
      hGcompact hGcont hΦ
  let δ : ℝ := r / (8 * ((D : ℝ) + 1))
  have hD1 : 0 < (D : ℝ) + 1 := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let E : ℝ := Real.exp ((K : ℝ) * δ)
  have hE : 0 < E := Real.exp_pos _
  let ρstate : ℝ := r / (8 * (E + 1))
  have hρstate : 0 < ρstate := by
    dsimp [ρstate]
    positivity
  let f₀ : Plane → ℝ :=
    fun y ↦ Transversal.transverseValue (G p) p y
  have hf₀cont : Continuous f₀ := by
    exact
      (Transversal.transverseFunctional (G p)).continuous.comp
        (continuous_id.sub continuous_const)
  have hf₀p : f₀ p = 0 := by
    simp [f₀, Transversal.transverseValue]
  obtain ⟨ρvalue, hρvalue, hvalue⟩ :=
    Metric.continuousAt_iff.mp hf₀cont.continuousAt
      (δ / 4) (by positivity)
  let ρ : ℝ := min ρstate ρvalue
  have hρ : 0 < ρ := lt_min hρstate hρvalue
  refine ⟨δ, hδ, ρ, hρ, ?_⟩
  intro y hy
  have hy_state : dist y p < ρstate :=
    hy.trans_le (min_le_left _ _)
  have hy_value : dist y p < ρvalue :=
    hy.trans_le (min_le_right _ _)
  have hvalue_small : |f₀ y| < δ / 4 := by
    have h := hvalue hy_value
    rw [hf₀p, Real.dist_eq, sub_zero] at h
    exact h
  have hstay (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      Φ y t ∈ ball p r := by
    have habs : |t| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have htime :
        dist (Φ p t) p ≤ (D : ℝ) * |t| := by
      have h' := (hD p).dist_le_mul t 0
      rw [hΦ0] at h'
      simpa only [Real.dist_eq, sub_zero] using h'
    have htime' : dist (Φ p t) p ≤ r / 8 := by
      calc
        dist (Φ p t) p ≤ (D : ℝ) * |t| := htime
        _ ≤ (D : ℝ) * δ :=
          mul_le_mul_of_nonneg_left habs D.coe_nonneg
        _ ≤ ((D : ℝ) + 1) * δ := by
          gcongr
          linarith
        _ = r / 8 := by
          dsimp [δ]
          field_simp
    have hexp :
        Real.exp ((K : ℝ) * |t|) ≤ E := by
      dsimp [E]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left habs K.coe_nonneg)
    have hstate0 :=
      (GlobalFlow.globalFlow_lipschitzWith hG hΦ0 hΦ t)
        |>.dist_le_mul y p
    change dist (Φ y t) (Φ p t) ≤
      Real.exp ((K : ℝ) * |t|) * dist y p at hstate0
    have hstate : dist (Φ y t) (Φ p t) < r / 8 := by
      calc
        dist (Φ y t) (Φ p t) ≤
            Real.exp ((K : ℝ) * |t|) * dist y p :=
          hstate0
        _ < Real.exp ((K : ℝ) * |t|) * ρstate :=
          mul_lt_mul_of_pos_left hy_state (Real.exp_pos _)
        _ ≤ E * ρstate :=
          mul_le_mul_of_nonneg_right hexp hρstate.le
        _ ≤ (E + 1) * ρstate := by
          gcongr
          linarith
        _ = r / 8 := by
          dsimp [ρstate]
          field_simp
    calc
      dist (Φ y t) p ≤
          dist (Φ y t) (Φ p t) + dist (Φ p t) p :=
        dist_triangle _ _ _
      _ < r / 8 + r / 8 := add_lt_add_of_lt_of_le hstate htime'
      _ < r := by linarith
  let f : ℝ → ℝ :=
    fun t ↦ Transversal.transverseValue (G p) p (Φ y t)
  have hfcont : Continuous f := by
    exact
      (Transversal.transverseFunctional (G p)).continuous.comp
        ((hΦ y).continuous.sub continuous_const)
  have hf0 : f 0 = f₀ y := by simp [f, f₀, hΦ0]
  have hgrowth_pos :
      (1 / 2 : ℝ) * (δ - 0) ≤ f δ - f 0 := by
    exact
      Transversal.half_mul_sub_le_transverseValue_sub
        (hΦ y) hvel hstay
        ⟨by linarith, hδ.le⟩ ⟨by linarith [hδ], le_rfl⟩ hδ.le
  have hgrowth_neg :
      (1 / 2 : ℝ) * (0 - -δ) ≤ f 0 - f (-δ) := by
    exact
      Transversal.half_mul_sub_le_transverseValue_sub
        (hΦ y) hvel hstay
        ⟨le_rfl, by linarith⟩ ⟨by linarith, hδ.le⟩
        (neg_nonpos.mpr hδ.le)
  have hfneg : f (-δ) < 0 := by
    have habs := abs_lt.mp hvalue_small
    rw [hf0] at hgrowth_neg
    linarith
  have hfpos : 0 < f δ := by
    have habs := abs_lt.mp hvalue_small
    rw [hf0] at hgrowth_pos
    linarith
  obtain ⟨t, ht, hft⟩ :
      ∃ t ∈ Icc (-δ) δ, f t = 0 := by
    have hzero : (0 : ℝ) ∈ Icc (f (-δ)) (f δ) :=
      ⟨hfneg.le, hfpos.le⟩
    exact
      (intermediate_value_Icc (by linarith [hδ])
        hfcont.continuousOn hzero)
  have htbound :
      |t| ≤ 2 * |f₀ y| := by
    rcases le_total 0 t with ht0 | ht0
    · have hgrowth :
          (1 / 2 : ℝ) * (t - 0) ≤ f t - f 0 :=
        Transversal.half_mul_sub_le_transverseValue_sub
          (hΦ y) hvel hstay
          ⟨by linarith [hδ], hδ.le⟩ ht ht0
      rw [hft, hf0] at hgrowth
      rw [abs_of_nonneg ht0]
      linarith [neg_le_abs (f₀ y)]
    · have hgrowth :
          (1 / 2 : ℝ) * (0 - t) ≤ f 0 - f t :=
        Transversal.half_mul_sub_le_transverseValue_sub
          (hΦ y) hvel hstay
          ht ⟨by linarith [hδ], hδ.le⟩ ht0
      rw [hft, hf0] at hgrowth
      rw [abs_of_nonpos ht0]
      linarith [le_abs_self (f₀ y)]
  have hstayR : Φ y t ∈ ball p R := by
    change dist (Φ y t) p < R
    exact (hstay t ht).trans_le (min_le_right _ _)
  refine
    ⟨t, ⟨ht, hstayR, hft, htbound⟩, ?_⟩
  intro u hu
  have hmono :=
    Transversal.strictMonoOn_transverseValue
      (hΦ y) hvel hstay
  exact hmono.injOn hu.1 ht (hu.2.2.1.trans hft.symm)

end

end Submission.FlowBox
