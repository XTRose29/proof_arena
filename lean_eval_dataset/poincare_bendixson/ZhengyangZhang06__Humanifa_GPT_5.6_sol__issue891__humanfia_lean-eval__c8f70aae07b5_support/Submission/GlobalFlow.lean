import Submission.Helpers

open Filter Metric Set Topology
open scoped Manifold NNReal

open LeanEval.Dynamics

namespace Submission.GlobalFlow

set_option backward.isDefEq.respectTransparency false in
theorem isMIntegralCurveOn_iff_isIntegralCurveOn
    {G : Plane → Plane} {γ : ℝ → Plane} {s : Set ℝ} :
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) γ G s ↔
      IsIntegralCurveOn γ (fun _ x ↦ G x) s := by
  constructor
  · intro h t ht
    have hderiv := (h t ht).hasFDerivWithinAt
    change HasFDerivWithinAt γ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (G (γ t))) s t at hderiv
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    simpa only [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using hderiv
  · intro h t ht
    have hderiv := h t ht
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at hderiv
    apply HasFDerivWithinAt.hasMFDerivWithinAt
    change HasFDerivWithinAt γ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (G (γ t))) s t
    simpa only [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using hderiv

theorem isMIntegralCurve_iff_isIntegralCurve
    {G : Plane → Plane} {γ : ℝ → Plane} :
    IsMIntegralCurve (I := 𝓘(ℝ, Plane)) γ G ↔
      IsIntegralCurve γ (fun _ x ↦ G x) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← isIntegralCurveOn_univ]
  exact isMIntegralCurveOn_iff_isIntegralCurveOn

theorem exists_global_integralCurve_of_compactSupport
    (G : Plane → Plane) (hGcompact : HasCompactSupport G)
    (hG : ContDiff ℝ 1 G) (x : Plane) :
    ∃ β : ℝ → Plane, β 0 = x ∧
      IsIntegralCurve β (fun _ y ↦ G y) := by
  obtain ⟨K, hK⟩ :=
    hG.lipschitzWith_of_hasCompactSupport hGcompact one_ne_zero
  obtain ⟨C, hC⟩ :=
    hGcompact.exists_bound_of_continuous hG.continuous
  let L : ℝ≥0 := ⟨max C 0 + 1, by positivity⟩
  have hLpos : 0 < (L : ℝ) := by
    change 0 < max C 0 + 1
    linarith [le_max_right C 0]
  let ε : ℝ := 1 / (L : ℝ)
  have hε : 0 < ε := one_div_pos.mpr hLpos
  have hlocal : ∀ z : Plane, ∃ α : ℝ → Plane, α 0 = z ∧
      IsIntegralCurveOn α (fun _ y ↦ G y) (Ioo (-ε) ε) := by
    intro z
    let tzero : Icc (-ε) ε := ⟨0, by constructor <;> linarith⟩
    have hpl :
        IsPicardLindelof (fun _ y ↦ G y) tzero z 1 0 L K := by
      refine
        { lipschitzOnWith := ?_
          continuousOn := ?_
          norm_le := ?_
          mul_max_le := ?_ }
      · intro _ _
        exact hK.lipschitzOnWith
      · intro _ _
        exact continuous_const.continuousOn
      · intro _ _ y _
        change ‖G y‖ ≤ max C 0 + 1
        exact (hC y).trans (by linarith [le_max_left C 0])
      · change (L : ℝ) * max (ε - 0) (0 - -ε) ≤ (1 : ℝ) - 0
        simp only [sub_zero, zero_sub, neg_neg, max_self]
        dsimp [ε]
        field_simp [ne_of_gt hLpos]
        exact le_rfl
    obtain ⟨α, hα0, hα⟩ :=
      hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨α, hα0, ?_⟩
    intro t ht
    exact (hα t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
  let V : (z : Plane) → TangentSpace 𝓘(ℝ, Plane) z := fun z ↦ G z
  have hlocalM : ∀ z : Plane, ∃ α : ℝ → Plane, α 0 = z ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) α V (Ioo (-ε) ε) := by
    intro z
    obtain ⟨α, hα0, hα⟩ := hlocal z
    exact
      ⟨α, hα0, isMIntegralCurveOn_iff_isIntegralCurveOn.mpr hα⟩
  have hGM :=
    (contMDiff_vectorSpace_iff_contDiff (V := V)).mpr hG
  obtain ⟨β, hβ0, hβ⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn
      (I := 𝓘(ℝ, Plane)) hGM hε hlocalM x
  exact ⟨β, hβ0, isMIntegralCurve_iff_isIntegralCurve.mp hβ⟩

theorem exists_globalFlow
    (G : Plane → Plane) (hGcompact : HasCompactSupport G)
    (hG : ContDiff ℝ 1 G) :
    ∃ Φ : Plane → ℝ → Plane,
      (∀ x, Φ x 0 = x) ∧
      ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y) := by
  choose Φ hΦ0 hΦ using fun x ↦
    exists_global_integralCurve_of_compactSupport G hGcompact hG x
  exact ⟨Φ, hΦ0, hΦ⟩

theorem globalFlow_add {G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    (x : Plane) (s t : ℝ) :
    Φ x (s + t) = Φ (Φ x s) t := by
  have hshift :
      IsIntegralCurve (Φ x ∘ (· + s)) (fun _ y ↦ G y) := by
    simpa [Function.comp_def] using (hΦ x).comp_add s
  have heq :
      Φ x ∘ (· + s) = Φ (Φ x s) :=
    Helpers.integralCurve_eq_of_lipschitz (t₀ := 0)
      hG hshift (hΦ (Φ x s))
      (by simp only [Function.comp_apply, zero_add, hΦ0])
  calc
    Φ x (s + t) = Φ x (t + s) := by rw [add_comm]
    _ = Φ (Φ x s) t := congrFun heq t

/-- Exponential dependence of global trajectories on their initial points,
valid in both time directions. -/
theorem dist_global_integralCurves_le {G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) {α β : ℝ → Plane}
    (hα : IsIntegralCurve α (fun _ y ↦ G y))
    (hβ : IsIntegralCurve β (fun _ y ↦ G y)) (t : ℝ) :
    dist (α t) (β t) ≤
      dist (α 0) (β 0) * Real.exp ((K : ℝ) * |t|) := by
  rcases le_total 0 t with ht | ht
  · have hbound :=
      dist_le_of_trajectories_ODE
        (a := (0 : ℝ)) (b := t) (K := K)
        (v := fun _ z ↦ G z) (f := α) (g := β)
        (δ := dist (α 0) (β 0))
        (fun _ ↦ hG) hα.continuous.continuousOn
        (fun u _ ↦ (hα u).hasDerivWithinAt)
        hβ.continuous.continuousOn
        (fun u _ ↦ (hβ u).hasDerivWithinAt)
        le_rfl t ⟨ht, le_rfl⟩
    simpa [abs_of_nonneg ht] using hbound
  · have hneg : LipschitzWith K (fun z ↦ -G z) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      simpa only [dist_neg_neg] using hG.dist_le_mul y z
    have hαrev :
        IsIntegralCurve (fun u ↦ α (-u)) (fun _ z ↦ -G z) := by
      intro u
      simpa only [zero_sub] using (hα (0 - u)).comp_const_sub 0 u
    have hβrev :
        IsIntegralCurve (fun u ↦ β (-u)) (fun _ z ↦ -G z) := by
      intro u
      simpa only [zero_sub] using (hβ (0 - u)).comp_const_sub 0 u
    have hnt : 0 ≤ -t := neg_nonneg.mpr ht
    have hbound :=
      dist_le_of_trajectories_ODE
        (a := (0 : ℝ)) (b := -t) (K := K)
        (v := fun _ z ↦ -G z)
        (f := fun u ↦ α (-u)) (g := fun u ↦ β (-u))
        (δ := dist (α 0) (β 0))
        (fun _ ↦ hneg) hαrev.continuous.continuousOn
        (fun u _ ↦ (hαrev u).hasDerivWithinAt)
        hβrev.continuous.continuousOn
        (fun u _ ↦ (hβrev u).hasDerivWithinAt)
        (by simp) (-t) ⟨hnt, le_rfl⟩
    simpa [abs_of_nonpos ht] using hbound

theorem globalFlow_lipschitzWith {G : Plane → Plane} {K : ℝ≥0}
    (hG : LipschitzWith K G) {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    (t : ℝ) :
    LipschitzWith
      ⟨Real.exp ((K : ℝ) * |t|), Real.exp_pos _ |>.le⟩
      (fun x ↦ Φ x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Φ x t) (Φ y t) ≤
    Real.exp ((K : ℝ) * |t|) * dist x y
  simpa only [hΦ0, mul_comm] using
    dist_global_integralCurves_le hG (hΦ x) (hΦ y) t

theorem exists_globalFlow_time_lipschitzWith
    {G : Plane → Plane} (hGcompact : HasCompactSupport G)
    (hG : Continuous G) {Φ : Plane → ℝ → Plane}
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y)) :
    ∃ D : ℝ≥0, ∀ x, LipschitzWith D (Φ x) := by
  obtain ⟨C, hC⟩ :=
    hGcompact.exists_bound_of_continuous hG
  let D : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  refine ⟨D, fun x ↦ lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hΦ x t).differentiableAt) ?_⟩
  intro t
  rw [(hΦ x t).deriv]
  change ‖G (Φ x t)‖ ≤ (D : ℝ)
  exact (hC (Φ x t)).trans (by
    change C ≤ max C 0
    exact le_max_left C 0)

theorem continuous_globalFlow {G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G) {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y)) :
    Continuous (Function.uncurry Φ) := by
  obtain ⟨D, hD⟩ :=
    exists_globalFlow_time_lipschitzWith hGcompact hGcont hΦ
  rw [continuous_iff_continuousAt]
  rintro ⟨x, t⟩
  apply continuousAt_of_locally_lipschitz one_pos
    ((D : ℝ) + Real.exp ((K : ℝ) * |t|))
  rintro ⟨y, s⟩ _hnear
  have htime :
      dist (Φ y s) (Φ y t) ≤ (D : ℝ) * dist s t :=
    (hD y).dist_le_mul s t
  have hstate :
      dist (Φ y t) (Φ x t) ≤
        Real.exp ((K : ℝ) * |t|) * dist y x := by
    have h :=
      (globalFlow_lipschitzWith hG hΦ0 hΦ t).dist_le_mul y x
    change dist (Φ y t) (Φ x t) ≤
      Real.exp ((K : ℝ) * |t|) * dist y x at h
    exact h
  calc
    dist (Function.uncurry Φ (y, s))
        (Function.uncurry Φ (x, t)) ≤
        dist (Φ y s) (Φ y t) + dist (Φ y t) (Φ x t) :=
      dist_triangle _ _ _
    _ ≤ (D : ℝ) * dist s t +
        Real.exp ((K : ℝ) * |t|) * dist y x :=
      add_le_add htime hstate
    _ ≤ ((D : ℝ) + Real.exp ((K : ℝ) * |t|)) *
        dist (y, s) (x, t) := by
      rw [Prod.dist_eq]
      have hy : dist y x ≤ max (dist y x) (dist s t) :=
        le_max_left _ _
      have hs : dist s t ≤ max (dist y x) (dist s t) :=
        le_max_right _ _
      nlinarith [D.coe_nonneg, (Real.exp_pos ((K : ℝ) * |t|)).le]

end Submission.GlobalFlow
