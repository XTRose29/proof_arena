import Submission.Action

namespace Submission.Helpers

open Function Metric ODE Set Topology
open scoped NNReal Topology

section VariationalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E}

/-- Complete-field data together with global first- and second-order bounds. -/
structure C2CompleteFieldData (X : E → E) extends CompleteFieldData X where
  D : ℝ≥0
  R : ℝ≥0
  differentiable : Differentiable ℝ X
  fderiv_lipschitzWith : LipschitzWith D (fderiv ℝ X)
  fderiv_norm_le : ∀ x, ‖fderiv ℝ X x‖ ≤ R

namespace C2CompleteFieldData

omit [CompleteSpace E] in
/-- A `C³`, compactly supported vector field has all quantitative data used below. -/
theorem nonempty_of_contDiff_hasCompactSupport
    (hX : ContDiff ℝ 3 X) (hXcompact : HasCompactSupport X) :
    Nonempty (C2CompleteFieldData X) := by
  obtain ⟨base⟩ := nonempty_completeFieldData_of_contDiff_hasCompactSupport
    (hX.of_le (by norm_num)) hXcompact
  have hDX : ContDiff ℝ 2 (fderiv ℝ X) :=
    hX.fderiv_right (m := 2) (by norm_num)
  obtain ⟨D, R, hD, hR⟩ :=
    exists_lipschitzWith_and_bound_of_contDiff_hasCompactSupport
      hDX (hXcompact.fderiv ℝ)
  exact ⟨⟨base, D, R, hX.differentiable (by norm_num), hD, hR⟩⟩

/-- A uniform positive time on which the variational Picard problem stays in a fixed ball. -/
noncomputable def shortTime (d : C2CompleteFieldData X) : ℝ :=
  1 / (4 * ((d.R : ℝ) + 1))

omit [CompleteSpace E] in
theorem shortTime_pos (d : C2CompleteFieldData X) : 0 < d.shortTime := by
  unfold shortTime
  positivity

/-- The time-dependent linear vector field in the first variational equation. -/
noncomputable def variationalField (d : C2CompleteFieldData X) (x : E)
    (t : ℝ) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  (fderiv ℝ X (d.flow t x)).comp A

theorem variationalField_lipschitzWith (d : C2CompleteFieldData X) (x : E) (t : ℝ) :
    LipschitzWith d.R (d.variationalField x t) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro A B
  change ‖(fderiv ℝ X (d.flow t x)).comp A -
      (fderiv ℝ X (d.flow t x)).comp B‖ ≤ (d.R : ℝ) * ‖A - B‖
  rw [show (fderiv ℝ X (d.flow t x)).comp A -
      (fderiv ℝ X (d.flow t x)).comp B =
      (fderiv ℝ X (d.flow t x)).comp (A - B) by ext; simp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (d.fderiv_norm_le _) (norm_nonneg _))

theorem continuous_variationalField (d : C2CompleteFieldData X) (x : E) (A : E →L[ℝ] E) :
    Continuous (fun t ↦ d.variationalField x t A) := by
  exact (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) A).continuous.comp
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp
      (d.fderiv_lipschitzWith.continuous.comp
        (d.flow.continuous continuous_id continuous_const)))

theorem norm_variationalField_le (d : C2CompleteFieldData X) (x : E) (t : ℝ)
    {A : E →L[ℝ] E} (hA : A ∈ closedBall 0 2) :
    ‖d.variationalField x t A‖ ≤ (2 * d.R : ℝ≥0) := by
  have hAnorm : ‖A‖ ≤ 2 := by
    simpa [mem_closedBall, dist_eq_norm] using hA
  calc
    ‖d.variationalField x t A‖ ≤ ‖fderiv ℝ X (d.flow t x)‖ * ‖A‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (d.R : ℝ) * 2 := mul_le_mul (d.fderiv_norm_le _) hAnorm (norm_nonneg _) d.R.2
    _ = (2 * d.R : ℝ≥0) := by simp [mul_comm]

omit [CompleteSpace E] in
private theorem variational_mul_max_le (d : C2CompleteFieldData X) :
    ((2 * d.R : ℝ≥0) : ℝ) *
        max (d.shortTime - 0) (0 - 0) ≤ (2 : ℝ) - 1 := by
  have hden : 0 < 4 * ((d.R : ℝ) + 1) := by positivity
  have hR : 0 ≤ (d.R : ℝ) := d.R.2
  simp only [sub_zero, max_eq_left (d.shortTime_pos.le), NNReal.coe_mul,
    NNReal.coe_ofNat]
  unfold shortTime
  have hgoal : 2 * (d.R : ℝ) * (1 / (4 * ((d.R : ℝ) + 1))) ≤ 1 := by
    have hnum : 2 * (d.R : ℝ) ≤ 1 * (4 * ((d.R : ℝ) + 1)) := by
      nlinarith
    simpa [div_eq_mul_inv] using (div_le_iff₀ hden).2 hnum
  norm_num at hgoal ⊢
  exact hgoal

/-- On the uniform short interval, the first variational equation has a solution starting at the
identity, and that solution has operator norm at most two. -/
theorem exists_variation (d : C2CompleteFieldData X) (x : E) :
    ∃ A : ℝ → (E →L[ℝ] E),
      A 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc 0 d.shortTime,
        HasDerivWithinAt A (d.variationalField x t (A t)) (Icc 0 d.shortTime) t) ∧
      ∀ t ∈ Icc 0 d.shortTime, ‖A t‖ ≤ 2 := by
  let t0 : Icc (0 : ℝ) d.shortTime :=
    ⟨0, by exact ⟨le_rfl, d.shortTime_pos.le⟩⟩
  have hpl : IsPicardLindelof (d.variationalField x) t0 0 2 1 (2 * d.R) d.R := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact (d.variationalField_lipschitzWith x t).lipschitzOnWith
    · intro A hA
      exact (d.continuous_variationalField x A).continuousOn
    · intro t ht A hA
      exact d.norm_variationalField_le x t hA
    · simpa [t0] using variational_mul_max_le d
  have hid : ContinuousLinearMap.id ℝ E ∈ closedBall (0 : E →L[ℝ] E) 1 := by
    rw [mem_closedBall, dist_zero_right]
    exact ContinuousLinearMap.norm_id_le
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hid
  let A : ℝ → (E →L[ℝ] E) := α.compProj
  refine ⟨A, ?_, ?_, ?_⟩
  · have hzero : α.compProj (t0 : ℝ) = ContinuousLinearMap.id ℝ E := by
      rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
    simpa [A, t0] using hzero
  · intro t ht
    change HasDerivWithinAt α.compProj
      (d.variationalField x t (α.compProj t)) (Icc 0 d.shortTime) t
    apply hasDerivWithinAt_picard_Icc t0.2 hpl.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ ↦ α.compProj_mem_closedBall hpl.mul_max_le)
      (ContinuousLinearMap.id ℝ E) ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t ht
    have hmem : α.compProj t ∈ closedBall (0 : E →L[ℝ] E) 2 :=
      α.compProj_mem_closedBall hpl.mul_max_le
    change ‖α.compProj t‖ ≤ 2
    simpa [mem_closedBall, dist_zero_right] using hmem

omit [CompleteSpace E] in
/-- Quadratic Taylor control supplied by the global Lipschitz bound on the derivative. -/
theorem norm_sub_linearization_le (d : C2CompleteFieldData X) (x z : E) :
    ‖X (x + z) - X x - fderiv ℝ X x z‖ ≤
      (d.D : ℝ) * ‖z‖ * ‖z‖ := by
  have hbound (y : E) (hy : y ∈ closedBall x ‖z‖) :
      ‖fderiv ℝ X y - fderiv ℝ X x‖ ≤ (d.D : ℝ) * ‖z‖ := by
    exact (d.fderiv_lipschitzWith.norm_sub_le y x).trans
      (mul_le_mul_of_nonneg_left (by simpa [mem_closedBall, dist_eq_norm] using hy) d.D.2)
  simpa using (convex_closedBall x ‖z‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ ↦ d.differentiable y) hbound
    (show x ∈ closedBall x ‖z‖ by simp)
    (show x + z ∈ closedBall x ‖z‖ by simp [mem_closedBall, dist_eq_norm])

private theorem gronwallBound_zero_scale (K q e t : ℝ) :
    gronwallBound 0 K (q * e) t = q * gronwallBound 0 K e t := by
  unfold gronwallBound
  split_ifs <;> ring

omit [CompleteSpace E] in
private theorem gronwallBound_nonneg (d : C2CompleteFieldData X)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t := by
  have hm := gronwallBound_mono (δ := 0) (K := (d.K : ℝ))
    (ε := 4 * (d.D : ℝ)) (by norm_num) (by positivity) d.K.2
  calc
    0 = gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) 0 :=
      (gronwallBound_x0 0 (d.K : ℝ) (4 * (d.D : ℝ))).symm
    _ ≤ gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t := hm ht

private theorem short_flow_remainder_le (d : C2CompleteFieldData X) (x z : E)
    {t : ℝ} (ht : t ∈ Icc 0 d.shortTime)
    (A : ℝ → (E →L[ℝ] E))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAderiv : ∀ s ∈ Icc 0 d.shortTime,
      HasDerivWithinAt A (d.variationalField x s (A s)) (Icc 0 d.shortTime) s)
    (hAnorm : ∀ s ∈ Icc 0 d.shortTime, ‖A s‖ ≤ 2) :
    ‖d.flow t (x + z) - d.flow t x - A t z‖ ≤
      gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t * ‖z‖ * ‖z‖ := by
  let f : ℝ → E := fun s ↦ d.flow s (x + z)
  let g : ℝ → E := fun s ↦ d.flow s x + A s z
  let f' : ℝ → E := fun s ↦ X (d.flow s (x + z))
  let g' : ℝ → E := fun s ↦
    X (d.flow s x) + d.variationalField x s (A s) z
  have hfcont : ContinuousOn f (Icc 0 t) :=
    (d.flow.continuous continuous_id continuous_const).continuousOn
  have hAcont : ContinuousOn A (Icc 0 t) := by
    intro s hs
    have hs' : s ∈ Icc 0 d.shortTime := ⟨hs.1, hs.2.trans ht.2⟩
    exact (hAderiv s hs').continuousWithinAt.mono
      (Icc_subset_Icc_right ht.2)
  have hgcont : ContinuousOn g (Icc 0 t) := by
    exact (d.flow.continuous continuous_id continuous_const).continuousOn.add
      ((ContinuousLinearMap.apply ℝ E z).continuous.comp_continuousOn hAcont)
  have hfderiv (s : ℝ) (hs : s ∈ Ico 0 t) :
      HasDerivWithinAt f (f' s) (Ici s) s := by
    exact (d.flow_hasDerivAt (x + z) s).hasDerivWithinAt
  have hgderiv (s : ℝ) (hs : s ∈ Ico 0 t) :
      HasDerivWithinAt g (g' s) (Ici s) s := by
    have hs' : s ∈ Ico 0 d.shortTime := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hAv := (hAderiv s (Ico_subset_Icc_self hs')).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs')
    exact (d.flow_hasDerivAt x s).hasDerivWithinAt.add
      ((ContinuousLinearMap.apply ℝ E z).hasFDerivAt.comp_hasDerivWithinAt s hAv)
  have hfres (s : ℝ) (hs : s ∈ Ico 0 t) :
      dist (f' s) (X (f s)) ≤ 0 := by
    simp [f, f']
  have hgres (s : ℝ) (hs : s ∈ Ico 0 t) :
      dist (g' s) (X (g s)) ≤ 4 * (d.D : ℝ) * ‖z‖ * ‖z‖ := by
    have hsIcc : s ∈ Icc 0 d.shortTime := ⟨hs.1, hs.2.le.trans ht.2⟩
    have hAz : ‖A s z‖ ≤ 2 * ‖z‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hAnorm s hsIcc) (norm_nonneg z))
    have hTaylor := d.norm_sub_linearization_le (d.flow s x) (A s z)
    calc
      dist (g' s) (X (g s)) =
          ‖X (d.flow s x + A s z) - X (d.flow s x) -
            fderiv ℝ X (d.flow s x) (A s z)‖ := by
        simp only [g, g', variationalField, dist_eq_norm]
        rw [norm_sub_rev]
        congr 1
        abel
      _ ≤ (d.D : ℝ) * ‖A s z‖ * ‖A s z‖ := hTaylor
      _ ≤ (d.D : ℝ) * (2 * ‖z‖) * (2 * ‖z‖) := by
        gcongr
      _ = 4 * (d.D : ℝ) * ‖z‖ * ‖z‖ := by ring
  have hzero : dist (f 0) (g 0) ≤ 0 := by
    simp [f, g, hA0]
  have hdist := dist_le_of_approx_trajectories_ODE
    (v := fun _ : ℝ ↦ X) (K := d.K) (a := 0) (b := t)
    (f := f) (g := g) (f' := f') (g' := g')
    (εf := 0) (εg := 4 * (d.D : ℝ) * ‖z‖ * ‖z‖) (δ := 0)
    (fun _ ↦ d.lipschitzWith) hfcont hfderiv hfres hgcont hgderiv hgres hzero
    t ⟨ht.1, le_rfl⟩
  have hscale :
      gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ) * ‖z‖ * ‖z‖) t =
        ‖z‖ * ‖z‖ * gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t := by
    rw [show 4 * (d.D : ℝ) * ‖z‖ * ‖z‖ =
        (‖z‖ * ‖z‖) * (4 * (d.D : ℝ)) by ring,
      gronwallBound_zero_scale]
  rw [zero_add, sub_zero, hscale] at hdist
  calc
    ‖d.flow t (x + z) - d.flow t x - A t z‖ = dist (f t) (g t) := by
      rw [dist_eq_norm]
      simp only [f, g]
      congr 1
      abel
    _ ≤ ‖z‖ * ‖z‖ * gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t := hdist
    _ = gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t * ‖z‖ * ‖z‖ := by ring

/-- On the uniform short interval, the variational solution is the Fréchet derivative of the
flow with respect to its initial point. -/
theorem exists_variation_hasFDerivAt (d : C2CompleteFieldData X) (x : E)
    {t : ℝ} (ht : t ∈ Icc 0 d.shortTime) :
    ∃ A : ℝ → (E →L[ℝ] E),
      A 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ s ∈ Icc 0 d.shortTime,
        HasDerivWithinAt A (d.variationalField x s (A s)) (Icc 0 d.shortTime) s) ∧
      (∀ s ∈ Icc 0 d.shortTime, ‖A s‖ ≤ 2) ∧
      HasFDerivAt (fun y ↦ d.flow t y) (A t) x := by
  obtain ⟨A, hA0, hAderiv, hAnorm⟩ := d.exists_variation x
  refine ⟨A, hA0, hAderiv, hAnorm, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let C : ℝ := gronwallBound 0 (d.K : ℝ) (4 * (d.D : ℝ)) t
  have hC : 0 ≤ C := d.gronwallBound_nonneg ht.1
  have hCp : 0 < C + 1 := by linarith
  filter_upwards [ball_mem_nhds 0 (div_pos hc hCp)] with z hz
  have hzlt : ‖z‖ < c / (C + 1) := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hfactor : C * ‖z‖ ≤ c := by
    calc
      C * ‖z‖ ≤ (C + 1) * ‖z‖ := by gcongr; linarith
      _ ≤ (C + 1) * (c / (C + 1)) :=
        (mul_le_mul_of_nonneg_left hzlt.le hCp.le)
      _ = c := by field_simp
  calc
    ‖d.flow t (x + z) - d.flow t x - A t z‖ ≤ C * ‖z‖ * ‖z‖ :=
      d.short_flow_remainder_le x z ht A hA0 hAderiv hAnorm
    _ ≤ c * ‖z‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)

section Commutation

variable {Y : E → E} {M : Set E}

/-- A short-time flow carries a commuting vector field to itself. -/
theorem short_flow_pushforward (dX : C2CompleteFieldData X)
    (dY : C2CompleteFieldData Y) (hMY : IsInvariant dY.flow M)
    (hbracket : ∀ p ∈ M, VectorField.lieBracket ℝ X Y p = 0)
    {s : ℝ} (hs : s ∈ Icc 0 dY.shortTime) {y : E} (hy : y ∈ M) :
    ∃ A : E →L[ℝ] E,
      HasFDerivAt (fun z ↦ dY.flow s z) A y ∧ A (X y) = X (dY.flow s y) := by
  obtain ⟨A, hA0, hAderiv, hAnorm, hflowDeriv⟩ :=
    dY.exists_variation_hasFDerivAt y hs
  let a : ℝ → E := fun r ↦ A r (X y)
  let b : ℝ → E := fun r ↦ X (dY.flow r y)
  let e : ℝ → E := fun r ↦ a r - b r
  have hAcont : ContinuousOn A (Icc 0 s) := by
    intro r hr
    have hr' : r ∈ Icc 0 dY.shortTime := ⟨hr.1, hr.2.trans hs.2⟩
    exact (hAderiv r hr').continuousWithinAt.mono (Icc_subset_Icc_right hs.2)
  have hacont : ContinuousOn a (Icc 0 s) :=
    (ContinuousLinearMap.apply ℝ E (X y)).continuous.comp_continuousOn hAcont
  have hbcont : ContinuousOn b (Icc 0 s) :=
    dX.differentiable.continuous.comp_continuousOn
      (dY.flow.continuous continuous_id continuous_const).continuousOn
  have hecont : ContinuousOn e (Icc 0 s) := hacont.sub hbcont
  have hederiv (r : ℝ) (hr : r ∈ Ico 0 s) :
      HasDerivWithinAt e
        (fderiv ℝ Y (dY.flow r y) (e r)) (Ici r) r := by
    have hr' : r ∈ Ico 0 dY.shortTime := ⟨hr.1, hr.2.trans_le hs.2⟩
    have hAv := (hAderiv r (Ico_subset_Icc_self hr')).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hr')
    have haDeriv : HasDerivWithinAt a
        (fderiv ℝ Y (dY.flow r y) (a r)) (Ici r) r := by
      change HasDerivWithinAt (fun q ↦ A q (X y))
        (fderiv ℝ Y (dY.flow r y) (A r (X y))) (Ici r) r
      have hraw :=
        (ContinuousLinearMap.apply ℝ E (X y)).hasFDerivAt.comp_hasDerivWithinAt r hAv
      have hraw' := hraw.congr (f₁ := fun q ↦ A q (X y)) (fun q _ ↦ rfl) rfl
      apply hraw'.congr_deriv
      simp [variationalField]
    have hp : dY.flow r y ∈ M := hMY r hy
    have hcomm : fderiv ℝ X (dY.flow r y) (Y (dY.flow r y)) =
        fderiv ℝ Y (dY.flow r y) (X (dY.flow r y)) := by
      have := hbracket (dY.flow r y) hp
      simp only [VectorField.lieBracket, sub_eq_zero] at this
      exact this.symm
    have hbDeriv : HasDerivWithinAt b
        (fderiv ℝ Y (dY.flow r y) (b r)) (Ici r) r := by
      have hcomp := (dX.differentiable (dY.flow r y)).hasFDerivAt.comp_hasDerivAt r
        (dY.flow_hasDerivAt y r)
      rw [hcomm] at hcomp
      exact hcomp.hasDerivWithinAt
    have hsub := (haDeriv.sub hbDeriv).congr (fun q _ ↦ rfl) rfl
    apply hsub.congr_deriv
    simp [e]
  have he0 : e 0 = 0 := by
    simp [e, a, b, hA0]
  have hebound (r : ℝ) (hr : r ∈ Ico 0 s) :
      ‖fderiv ℝ Y (dY.flow r y) (e r)‖ ≤ (dY.R : ℝ) * ‖e r‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (dY.fderiv_norm_le _) (norm_nonneg _))
  have heq := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hecont hederiv he0 hebound s ⟨hs.1, le_rfl⟩
  refine ⟨A s, hflowDeriv, ?_⟩
  have := heq
  simp only [e, a, b, sub_eq_zero] at this
  exact this

/-- The short nonnegative flow of one field commutes on an invariant set with the full flow of a
field whose Lie bracket with it vanishes there. -/
theorem short_flows_commute_on (dX : C2CompleteFieldData X)
    (dY : C2CompleteFieldData Y) (hMX : IsInvariant dX.flow M)
    (hMY : IsInvariant dY.flow M)
    (hbracket : ∀ p ∈ M, VectorField.lieBracket ℝ X Y p = 0)
    {s : ℝ} (hs : s ∈ Icc 0 dY.shortTime) (t : ℝ) {y : E} (hy : y ∈ M) :
    dY.flow s (dX.flow t y) = dX.flow t (dY.flow s y) := by
  let g : ℝ → E := fun r ↦ dY.flow s (dX.flow r y)
  have hg0 : g 0 = dY.flow s y := by simp [g]
  have hgderiv (r : ℝ) : HasDerivAt g (X (g r)) r := by
    have hp : dX.flow r y ∈ M := hMX r hy
    obtain ⟨A, hA, hAX⟩ := dX.short_flow_pushforward dY hMY hbracket hs hp
    have hcomp := hA.comp_hasDerivAt r (dX.flow_hasDerivAt y r)
    change HasDerivAt (fun q ↦ dY.flow s (dX.flow q y))
      (A (X (dX.flow r y))) r at hcomp
    rw [hAX] at hcomp
    exact hcomp
  have heq := globalIntegralCurve_unique dX.lipschitzWith dX.norm_le hg0 hgderiv
  simpa [g, CompleteFieldData.flow_apply] using congrFun heq t

/-- Complete `C²` vector fields with vanishing Lie bracket commute on every common invariant set. -/
theorem flows_commute_on (dX : C2CompleteFieldData X)
    (dY : C2CompleteFieldData Y) (hMX : IsInvariant dX.flow M)
    (hMY : IsInvariant dY.flow M)
    (hbracket : ∀ p ∈ M, VectorField.lieBracket ℝ X Y p = 0)
    (s t : ℝ) {y : E} (hy : y ∈ M) :
    dY.flow s (dX.flow t y) = dX.flow t (dY.flow s y) := by
  have hnonneg (r : ℝ) (hr : 0 ≤ r) {z : E} (hz : z ∈ M) :
      dY.flow r (dX.flow t z) = dX.flow t (dY.flow r z) := by
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (r / dY.shortTime)
    have hrdiv : 0 ≤ r / dY.shortTime := div_nonneg hr dY.shortTime_pos.le
    have hNreal : 0 < (N : ℝ) := hrdiv.trans_lt hN
    let u : ℝ := r / (N : ℝ)
    have hu0 : 0 ≤ u := div_nonneg hr hNreal.le
    have hru : r < (N : ℝ) * dY.shortTime :=
      (div_lt_iff₀ dY.shortTime_pos).mp hN
    have huT : u ≤ dY.shortTime := by
      apply (div_le_iff₀ hNreal).2
      simpa [mul_comm] using hru.le
    have hu : u ∈ Icc 0 dY.shortTime := ⟨hu0, huT⟩
    have hind (k : ℕ) :
        dY.flow ((k : ℝ) * u) (dX.flow t z) =
          dX.flow t (dY.flow ((k : ℝ) * u) z) := by
      induction k with
      | zero => simp
      | succ k ih =>
          have hzk : dY.flow ((k : ℝ) * u) z ∈ M := hMY _ hz
          calc
            dY.flow ((k.succ : ℝ) * u) (dX.flow t z) =
                dY.flow u (dY.flow ((k : ℝ) * u) (dX.flow t z)) := by
              rw [show (k.succ : ℝ) * u = u + (k : ℝ) * u by
                push_cast; ring, dY.flow.map_add]
            _ = dY.flow u (dX.flow t (dY.flow ((k : ℝ) * u) z)) :=
              congrArg (dY.flow u) ih
            _ = dX.flow t (dY.flow u (dY.flow ((k : ℝ) * u) z)) :=
              dX.short_flows_commute_on dY hMX hMY hbracket hu t hzk
            _ = dX.flow t (dY.flow ((k.succ : ℝ) * u) z) := by
              congr 1
              rw [show (k.succ : ℝ) * u = u + (k : ℝ) * u by
                push_cast; ring, dY.flow.map_add]
    have hNr : (N : ℝ) * u = r := by
      dsimp [u]
      field_simp
    simpa [hNr] using hind N
  by_cases hs : 0 ≤ s
  · exact hnonneg s hs hy
  · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
    have hys : dY.flow s y ∈ M := hMY s hy
    have hpos := hnonneg (-s) hs' hys
    have hcancel : dY.flow (-s) (dY.flow s y) = y := by
      rw [← dY.flow.map_add]
      simp
    rw [hcancel] at hpos
    calc
      dY.flow s (dX.flow t y) =
          dY.flow s (dY.flow (-s) (dX.flow t (dY.flow s y))) :=
        congrArg (dY.flow s) hpos.symm
      _ = dY.flow (s + -s) (dX.flow t (dY.flow s y)) :=
        (dY.flow.map_add s (-s) _).symm
      _ = dX.flow t (dY.flow s y) := by simp

end Commutation

end C2CompleteFieldData

end VariationalFlow

end Submission.Helpers
