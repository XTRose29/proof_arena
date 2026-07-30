import ChallengeDeps

open LeanEval.Geometry.HopfUmlaufsatz

namespace Submission.Helpers

open Set MeasureTheory

theorem period_pos : 0 < period := by
  simp [period, Real.pi_pos]

theorem totalCurvature_eq_angle_sub {r : ℝ → Plane} {α : ℝ → ℝ}
    (hα : IsTangentAngleLift r α) :
    totalCurvature α = α period - α 0 := by
  rw [totalCurvature]
  change (∫ t in (0 : ℝ)..period, deriv α t) = _
  exact intervalIntegral.integral_deriv_of_contDiffOn_Icc
    hα.smooth.contDiffOn period_pos.le

theorem velocity_periodic {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Function.Periodic (velocity r) period := by
  intro t
  have hfun : (fun x ↦ r (x + period)) = r := funext hr.periodic
  have hderiv := congrArg (fun f : ℝ → Plane ↦ deriv f t) hfun
  simpa [velocity, deriv_comp_add_const] using hderiv

theorem angle_sub_eq_int_mul_period {r : ℝ → Plane} {α : ℝ → ℝ}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (hα : IsTangentAngleLift r α) :
    ∃ n : ℤ, α period - α 0 = n * period := by
  have hv : velocity r period = velocity r 0 := by
    simpa using velocity_periodic hr 0
  have hvec :
      !₂[Real.cos (α period), Real.sin (α period)] =
        !₂[Real.cos (α 0), Real.sin (α 0)] := by
    rw [← hα.velocity_eq, ← hα.velocity_eq]
    exact hv
  have hcos : Real.cos (α period) = Real.cos (α 0) := by
    simpa using congrArg (fun v : Plane => v 0) hvec
  have hsin : Real.sin (α period) = Real.sin (α 0) := by
    simpa using congrArg (fun v : Plane => v 1) hvec
  have hone : Real.cos (α period - α 0) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    simpa [pow_two] using Real.cos_sq_add_sin_sq (α 0)
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hone
  refine ⟨n, ?_⟩
  simpa [period, mul_comm] using hn.symm

/-- A periodic parametrization which is injective on one half-open period
descends to an embedding of the additive circle. -/
theorem periodicLift_injective {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Function.Injective hr.periodic.lift := by
  letI : Fact (0 < period) := ⟨period_pos⟩
  intro x y hxy
  let x₀ := AddCircle.equivIco period 0 x
  let y₀ := AddCircle.equivIco period 0 y
  have hx₀ : (x₀ : ℝ) ∈ Ico (0 : ℝ) period := by
    simpa [x₀] using x₀.2
  have hy₀ : (y₀ : ℝ) ∈ Ico (0 : ℝ) period := by
    simpa [y₀] using y₀.2
  have hrxy : r x₀ = r y₀ := by
    calc
      r x₀ = hr.periodic.lift ((x₀ : ℝ) : AddCircle period) :=
        (hr.periodic.lift_coe _).symm
      _ = hr.periodic.lift x := by
        rw [AddCircle.coe_equivIco (p := period) (a := 0) (y := x)]
      _ = hr.periodic.lift y := hxy
      _ = hr.periodic.lift ((y₀ : ℝ) : AddCircle period) := by
        rw [AddCircle.coe_equivIco (p := period) (a := 0) (y := y)]
      _ = r y₀ := hr.periodic.lift_coe _
  have hxy₀ : (x₀ : ℝ) = y₀ := hr.injective_on_period hx₀ hy₀ hrxy
  rw [← AddCircle.coe_equivIco (p := period) (a := 0) (y := x),
    ← AddCircle.coe_equivIco (p := period) (a := 0) (y := y), hxy₀]

/-- Two parameters separated by strictly less than one positive period give
different points of a simple periodic curve. -/
theorem ne_of_subparameter_mem_Ioo {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) period) :
    r (s + δ) ≠ r s := by
  letI : Fact (0 < period) := ⟨period_pos⟩
  have hδIco : δ ∈ Ico (0 : ℝ) period := ⟨hδ.1.le, hδ.2⟩
  have hδ0 : (δ : AddCircle period) ≠ 0 := by
    intro h
    exact hδ.1.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico hδIco).mp h)
  have hclasses : ((s + δ : ℝ) : AddCircle period) ≠ (s : AddCircle period) := by
    intro h
    apply hδ0
    apply add_left_cancel (a := (s : AddCircle period))
    simpa only [AddCircle.coe_add, add_zero] using h
  intro hrs
  apply hclasses
  apply periodicLift_injective hr
  simpa only [hr.periodic.lift_coe] using hrs

theorem velocity_continuous {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Continuous (velocity r) := by
  have h := hr.smooth.continuous_fderiv_apply
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hc : Continuous (fun t : ℝ => (fderiv ℝ r t : ℝ → Plane) 1) :=
    h.comp (continuous_id.prodMk continuous_const)
  change Continuous (fun t => deriv r t)
  simpa only [deriv] using hc

/-- The average velocity along the parameter interval from `s` to `s + δ`. -/
noncomputable def averageVelocity (r : ℝ → Plane) (s δ : ℝ) : Plane :=
  ∫ u in (0 : ℝ)..1, velocity r (s + u * δ)

theorem smul_averageVelocity_eq_sub {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ) :
    δ • averageVelocity r s δ = r (s + δ) - r s := by
  rw [averageVelocity]
  calc
    δ • ∫ u in (0 : ℝ)..1, velocity r (s + u * δ) =
        ∫ t in s..s + δ, velocity r t := by
      simpa only [mul_comm, mul_zero, mul_one, add_zero] using
        intervalIntegral.smul_integral_comp_add_mul
          (f := velocity r) (a := (0 : ℝ)) (b := 1) δ s
    _ = r (s + δ) - r s := by
      exact intervalIntegral.integral_deriv_eq_sub
        (fun t _ => (hr.smooth.differentiable (by norm_num)) t)
        ((velocity_continuous hr).intervalIntegrable _ _)

theorem averageVelocity_continuous {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Continuous (fun p : ℝ × ℝ => averageVelocity r p.1 p.2) := by
  simp only [averageVelocity, intervalIntegral.integral_of_le zero_le_one]
  apply MeasureTheory.continuous_of_dominated
      (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (bound := fun _ => (1 : ℝ))
  · intro p
    exact ((velocity_continuous hr).comp
      (continuous_const.add (continuous_id.mul continuous_const))).aestronglyMeasurable
  · intro p
    filter_upwards with u
    simp [hr.unit_speed]
  · simp
  · filter_upwards with u
    exact (velocity_continuous hr).comp
      (continuous_fst.add (continuous_const.mul continuous_snd))

theorem averageVelocity_zero (r : ℝ → Plane) (s : ℝ) :
    averageVelocity r s 0 = velocity r s := by
  simp [averageVelocity]

theorem averageVelocity_periodic {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ) :
    averageVelocity r (s + period) δ = averageVelocity r s δ := by
  apply intervalIntegral.integral_congr
  intro u _
  have h := velocity_periodic hr (s + u * δ)
  change velocity r (s + period + u * δ) = velocity r (s + u * δ)
  rw [show s + period + u * δ = s + u * δ + period by ring]
  exact h

theorem averageVelocity_reverse {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ) :
    averageVelocity r (s + δ) (-δ) = averageVelocity r s δ := by
  by_cases hδ : δ = 0
  · simp [hδ, averageVelocity_zero]
  apply smul_right_injective Plane hδ
  calc
    δ • averageVelocity r (s + δ) (-δ) =
        -((-δ) • averageVelocity r (s + δ) (-δ)) := by simp
    _ = -(r (s + δ - δ) - r (s + δ)) := by
      rw [smul_averageVelocity_eq_sub hr]
      congr 2
    _ = r (s + δ) - r s := by
      rw [neg_sub, show s + δ - δ = s by ring]
    _ = δ • averageVelocity r s δ :=
      (smul_averageVelocity_eq_sub hr s δ).symm

theorem averageVelocity_half_eq_neg_backward {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s : ℝ) :
    averageVelocity r s (period / 2) =
      -averageVelocity r s (period / 2 - period) := by
  have ha : period / 2 ≠ 0 := (half_pos period_pos).ne'
  apply smul_right_injective Plane ha
  dsimp
  calc
    (period / 2) • averageVelocity r s (period / 2) =
        r (s + period / 2) - r s :=
      smul_averageVelocity_eq_sub hr _ _
    _ = r (s + (period / 2 - period)) - r s := by
      have hp := hr.periodic (s + (period / 2 - period))
      have heq : r (s + period / 2) = r (s + (period / 2 - period)) := by
        calc
          r (s + period / 2) =
              r (s + (period / 2 - period) + period) := by
            congr 1
            ring
          _ = r (s + (period / 2 - period)) := hp
      rw [heq]
    _ = (period / 2 - period) •
        averageVelocity r s (period / 2 - period) :=
      (smul_averageVelocity_eq_sub hr _ _).symm
    _ = (period / 2) •
        -averageVelocity r s (period / 2 - period) := by
      rw [smul_neg, ← neg_smul]
      congr 1
      ring

/-- A nonzero secant field on the closed strip. At the lower boundary it is
the velocity, and at the upper boundary it is the negative velocity. -/
noncomputable def extendedSecant (r : ℝ → Plane) (s δ : ℝ) : Plane :=
  if δ ≤ period / 2 then averageVelocity r s δ
  else -averageVelocity r s (δ - period)

theorem extendedSecant_continuous {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    Continuous (fun p : ℝ × ℝ => extendedSecant r p.1 p.2) := by
  unfold extendedSecant
  refine Continuous.if_le (averageVelocity_continuous hr) ?_
    continuous_snd continuous_const ?_
  · exact ((averageVelocity_continuous hr).comp
      (continuous_fst.prodMk (continuous_snd.sub continuous_const))).neg
  · intro p hp
    simpa [hp] using averageVelocity_half_eq_neg_backward hr p.1

theorem extendedSecant_zero (r : ℝ → Plane) (s : ℝ) :
    extendedSecant r s 0 = velocity r s := by
  have hhalf : (0 : ℝ) ≤ period / 2 := (half_pos period_pos).le
  rw [extendedSecant, if_pos hhalf, averageVelocity_zero]

theorem extendedSecant_period (r : ℝ → Plane) (s : ℝ) :
    extendedSecant r s period = -velocity r s := by
  have hhalf : ¬period ≤ period / 2 := not_le.mpr (half_lt_self period_pos)
  rw [extendedSecant, if_neg hhalf, sub_self, averageVelocity_zero]

theorem extendedSecant_periodic {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ) :
    extendedSecant r (s + period) δ = extendedSecant r s δ := by
  unfold extendedSecant
  split_ifs <;> simp only [averageVelocity_periodic hr]

theorem extendedSecant_flip {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ)
    (hδ : δ ∈ Icc (0 : ℝ) period) :
    extendedSecant r (s + δ) (period - δ) = -extendedSecant r s δ := by
  rcases lt_trichotomy δ (period / 2) with hlt | heq | hgt
  · have hδhalf : δ ≤ period / 2 := hlt.le
    have hfliphalf : ¬period - δ ≤ period / 2 := by linarith
    simp only [extendedSecant, if_neg hfliphalf, if_pos hδhalf]
    rw [show period - δ - period = -δ by ring,
      averageVelocity_reverse hr s δ]
  · subst δ
    have hhalf : period - period / 2 = period / 2 := by ring
    simp only [extendedSecant, hhalf, if_pos le_rfl]
    rw [averageVelocity_half_eq_neg_backward hr (s + period / 2)]
    congr 1
    have hrev := averageVelocity_reverse hr s (period / 2)
    rw [show -(period / 2) = period / 2 - period by ring] at hrev
    exact hrev
  · have hδhalf : ¬δ ≤ period / 2 := not_le.mpr hgt
    have hfliphalf : period - δ ≤ period / 2 := by linarith
    simp only [extendedSecant, if_pos hfliphalf, if_neg hδhalf, neg_neg]
    calc
      averageVelocity r (s + δ) (period - δ) =
          averageVelocity r (s + period) (δ - period) := by
        have hrev :=
          (averageVelocity_reverse hr (s + δ) (period - δ)).symm
        rw [show s + δ + (period - δ) = s + period by ring,
          show -(period - δ) = δ - period by ring] at hrev
        exact hrev
      _ = averageVelocity r s (δ - period) :=
        averageVelocity_periodic hr s (δ - period)

theorem extendedSecant_ne_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ)
    (hδ : δ ∈ Icc (0 : ℝ) period) :
    extendedSecant r s δ ≠ 0 := by
  have hv (t : ℝ) : velocity r t ≠ 0 := by
    intro hzero
    have hnorm := hr.unit_speed t
    simp [hzero] at hnorm
  by_cases hhalf : δ ≤ period / 2
  · rw [extendedSecant, if_pos hhalf]
    by_cases hzero : δ = 0
    · simpa [hzero, averageVelocity_zero] using hv s
    · intro havg
      have hchord := smul_averageVelocity_eq_sub hr s δ
      rw [havg, smul_zero] at hchord
      apply ne_of_subparameter_mem_Ioo hr s δ
        ⟨lt_of_le_of_ne hδ.1 (Ne.symm hzero),
          hhalf.trans_lt (half_lt_self period_pos)⟩
      exact sub_eq_zero.mp hchord.symm
  · rw [extendedSecant, if_neg hhalf]
    by_cases hend : δ = period
    · simpa [hend, averageVelocity_zero] using neg_ne_zero.mpr (hv s)
    · intro havg
      have havg' : averageVelocity r s (δ - period) = 0 := neg_eq_zero.mp havg
      have hback := smul_averageVelocity_eq_sub hr s (δ - period)
      rw [havg', smul_zero] at hback
      have hback' : r (s + (δ - period)) = r s := sub_eq_zero.mp hback.symm
      have hp := hr.periodic (s + (δ - period))
      have hpoint : r (s + δ) = r s := by
        calc
          r (s + δ) = r (s + (δ - period) + period) := by
            congr 1
            ring
          _ = r (s + (δ - period)) := hp
          _ = r s := hback'
      apply ne_of_subparameter_mem_Ioo hr s δ
        ⟨(half_pos period_pos).trans (lt_of_not_ge hhalf),
          lt_of_le_of_ne hδ.2 hend⟩
      exact hpoint

/-- The coordinate-preserving real-linear identification of the Euclidean
plane with the complex plane. -/
noncomputable def planeToComplex : Plane ≃L[ℝ] ℂ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans
      Complex.equivRealProdCLM.symm)

@[simp]
theorem planeToComplex_apply (v : Plane) :
    planeToComplex v = v 0 + v 1 * Complex.I := by
  simp [planeToComplex, Complex.equivRealProdCLM_symm_apply]

@[simp]
theorem planeToComplex_re (v : Plane) : (planeToComplex v).re = v 0 := by
  simp [planeToComplex_apply]

@[simp]
theorem planeToComplex_im (v : Plane) : (planeToComplex v).im = v 1 := by
  simp [planeToComplex_apply]

theorem planeToComplex_tangent (a : ℝ) :
    planeToComplex !₂[Real.cos a, Real.sin a] =
      Complex.exp (a * Complex.I) := by
  rw [planeToComplex_apply, Complex.exp_mul_I]
  norm_num

def secantStrip : Set (ℝ × ℝ) :=
  univ ×ˢ Icc (0 : ℝ) period

theorem secantStrip_convex : Convex ℝ secantStrip := by
  simpa [secantStrip] using
    (convex_univ.prod (convex_Icc (0 : ℝ) period))

theorem secantStrip_nonempty : secantStrip.Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp [secantStrip, period_pos.le]

noncomputable instance secantStripContractible : ContractibleSpace secantStrip :=
  secantStrip_convex.contractibleSpace secantStrip_nonempty

noncomputable instance secantStripLocPathConnected : LocPathConnectedSpace secantStrip :=
  secantStrip_convex.locPathConnectedSpace

/-- Two continuous logarithms on a simply connected, locally path-connected
space which agree at one point agree everywhere. -/
theorem continuousMap_eq_of_exp_eq {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocPathConnectedSpace A]
    (f g : C(A, ℂ)) (a₀ : A) (h₀ : f a₀ = g a₀)
    (hexp : ∀ a, Complex.exp (f a) = Complex.exp (g a)) :
    f = g := by
  let target : C(A, {z : ℂ // z ≠ 0}) :=
    { toFun := fun a => ⟨Complex.exp (f a), Complex.exp_ne_zero _⟩
      continuous_toFun := Continuous.subtype_mk
        (Complex.continuous_exp.comp f.continuous) _ }
  obtain ⟨F, hF, huniq⟩ :=
    Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      target a₀ (f a₀) (by rfl)
  have hf : f a₀ = f a₀ ∧
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ :
        {z : ℂ // z ≠ 0})) ∘ f = target := by
    refine ⟨rfl, ?_⟩
    ext a
    rfl
  have hg : g a₀ = f a₀ ∧
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ :
        {z : ℂ // z ≠ 0})) ∘ g = target := by
    refine ⟨h₀.symm, ?_⟩
    funext a
    apply Subtype.ext
    exact (hexp a).symm
  exact (huniq f hf).trans (huniq g hg).symm

theorem exists_secantLog {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    ∃ F : C(secantStrip, ℂ), ∀ p : secantStrip,
      Complex.exp (F p) = planeToComplex (extendedSecant r p.1.1 p.1.2) := by
  let q₀ : secantStrip → ℂ := fun p =>
    planeToComplex (extendedSecant r p.1.1 p.1.2)
  have hq₀_ne (p : secantStrip) : q₀ p ≠ 0 := by
    intro hzero
    apply extendedSecant_ne_zero hr p.1.1 p.1.2 p.property.2
    apply planeToComplex.injective
    simpa [q₀] using hzero
  have hq₀_cont : Continuous q₀ :=
    planeToComplex.continuous.comp
      ((extendedSecant_continuous hr).comp continuous_subtype_val)
  let q : C(secantStrip, {z : ℂ // z ≠ 0}) :=
    { toFun := fun p => ⟨q₀ p, hq₀_ne p⟩
      continuous_toFun := hq₀_cont.subtype_mk hq₀_ne }
  let p₀ : secantStrip := ⟨(0, 0), by simp [secantStrip, period_pos.le]⟩
  let z₀ : ℂ := Complex.log (q p₀)
  have hz₀ :
      (⟨Complex.exp z₀, Complex.exp_ne_zero z₀⟩ : {z : ℂ // z ≠ 0}) = q p₀ := by
    apply Subtype.ext
    exact Complex.exp_log (q p₀).property
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      q p₀ z₀ hz₀ with ⟨F, hF, _hFuniq⟩
  refine ⟨F, fun p => ?_⟩
  change Complex.exp (F p) = (q p).1
  exact congrArg
    (fun z : {z : ℂ // z ≠ 0} => (z : ℂ)) (congrFun hF.2 p)

noncomputable def stripBottom (s : ℝ) : secantStrip :=
  ⟨(s, 0), by simp [secantStrip, period_pos.le]⟩

noncomputable def stripTop (s : ℝ) : secantStrip :=
  ⟨(s, period), by simp [secantStrip, period_pos.le]⟩

noncomputable def stripFlip (p : secantStrip) : secantStrip :=
  ⟨(p.1.1 + p.1.2, period - p.1.2), by
    refine ⟨mem_univ _, ?_⟩
    exact ⟨sub_nonneg.mpr p.property.2.2,
      sub_le_self _ p.property.2.1⟩⟩

noncomputable def stripBottomMap : C(ℝ, secantStrip) :=
  { toFun := stripBottom
    continuous_toFun := Continuous.subtype_mk
      (continuous_id.prodMk continuous_const) _ }

noncomputable def stripFlipMap : C(secantStrip, secantStrip) :=
  { toFun := stripFlip
    continuous_toFun := Continuous.subtype_mk
      ((continuous_fst.comp continuous_subtype_val).add
        (continuous_snd.comp continuous_subtype_val) |>.prodMk
        (continuous_const.sub (continuous_snd.comp continuous_subtype_val))) _ }

@[simp]
theorem stripFlip_bottom (s : ℝ) : stripFlip (stripBottom s) = stripTop s := by
  apply Subtype.ext
  simp [stripFlip, stripBottom, stripTop]

theorem stripFlip_flip (p : secantStrip) :
    stripFlip (stripFlip p) =
      ⟨(p.1.1 + period, p.1.2), by
        exact ⟨mem_univ _, p.property.2⟩⟩ := by
  apply Subtype.ext
  apply Prod.ext <;> dsimp [stripFlip] <;> ring

@[simp]
theorem stripFlip_flip_bottom (s : ℝ) :
    stripFlip (stripFlip (stripBottom s)) = stripBottom (s + period) := by
  apply Subtype.ext
  simp [stripFlip, stripBottom]

theorem secantLog_flip_add_constant {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (F : C(secantStrip, ℂ))
    (hF : ∀ p : secantStrip,
      Complex.exp (F p) = planeToComplex (extendedSecant r p.1.1 p.1.2))
    (p₀ : secantStrip) (p : secantStrip) :
    F (stripFlip p) = F p + (F (stripFlip p₀) - F p₀) := by
  let C : ℂ := F (stripFlip p₀) - F p₀
  let FT : C(secantStrip, ℂ) := F.comp stripFlipMap
  let G : C(secantStrip, ℂ) := F + ContinuousMap.const secantStrip C
  have hq_ne (x : secantStrip) :
      planeToComplex (extendedSecant r x.1.1 x.1.2) ≠ 0 := by
    intro hzero
    apply extendedSecant_ne_zero hr x.1.1 x.1.2 x.property.2
    apply planeToComplex.injective
    simpa using hzero
  have hq_flip (x : secantStrip) :
      planeToComplex
          (extendedSecant r (stripFlip x).1.1 (stripFlip x).1.2) =
        -planeToComplex (extendedSecant r x.1.1 x.1.2) := by
    change planeToComplex
        (extendedSecant r (x.1.1 + x.1.2) (period - x.1.2)) = _
    rw [extendedSecant_flip hr x.1.1 x.1.2 x.property.2]
    exact map_neg planeToComplex _
  have hC : Complex.exp C = -1 := by
    simp only [C, Complex.exp_sub, hF, hq_flip]
    exact neg_div_self (hq_ne p₀)
  have hbase : FT p₀ = G p₀ := by
    change F (stripFlip p₀) = F p₀ + C
    simp [C]
  have hexp (x : secantStrip) : Complex.exp (FT x) = Complex.exp (G x) := by
    change Complex.exp (F (stripFlip x)) = Complex.exp (F x + C)
    rw [Complex.exp_add, hF, hF, hq_flip, hC]
    ring
  have hmaps := continuousMap_eq_of_exp_eq FT G p₀ hbase hexp
  have hp := congrArg (fun H : C(secantStrip, ℂ) => H p) hmaps
  simpa [FT, G, C, stripFlipMap] using hp

theorem secantLog_bottom_period {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (F : C(secantStrip, ℂ))
    (hF : ∀ p : secantStrip,
      Complex.exp (F p) = planeToComplex (extendedSecant r p.1.1 p.1.2))
    (p₀ : secantStrip) (s : ℝ) :
    F (stripBottom (s + period)) - F (stripBottom s) =
      2 * (F (stripFlip p₀) - F p₀) := by
  have h₁ := secantLog_flip_add_constant hr F hF p₀ (stripBottom s)
  have h₂ := secantLog_flip_add_constant hr F hF p₀
    (stripFlip (stripBottom s))
  rw [stripFlip_flip_bottom] at h₂
  rw [h₁] at h₂
  calc
    F (stripBottom (s + period)) - F (stripBottom s) =
        ((F (stripBottom s) + (F (stripFlip p₀) - F p₀)) +
          (F (stripFlip p₀) - F p₀)) - F (stripBottom s) := by rw [h₂]
    _ = 2 * (F (stripFlip p₀) - F p₀) := by ring

theorem secantLog_bottom_eq_tangentLog {r : ℝ → Plane} {α : ℝ → ℝ}
    (hα : IsTangentAngleLift r α)
    (F : C(secantStrip, ℂ))
    (hF : ∀ p : secantStrip,
      Complex.exp (F p) = planeToComplex (extendedSecant r p.1.1 p.1.2))
    (s : ℝ) :
    F (stripBottom s) =
      F (stripBottom 0) + (α s - α 0) * Complex.I := by
  let FB : C(ℝ, ℂ) := F.comp stripBottomMap
  let G : C(ℝ, ℂ) :=
    { toFun := fun t => F (stripBottom 0) + (α t - α 0) * Complex.I
      continuous_toFun := by
        have hcα : Continuous (fun t : ℝ => (α t : ℂ)) :=
          RCLike.continuous_ofReal.comp hα.smooth.continuous
        exact continuous_const.add
          ((hcα.sub continuous_const).mul continuous_const) }
  have hbase : FB 0 = G 0 := by
    simp [FB, G, stripBottomMap]
  have hexp (t : ℝ) : Complex.exp (FB t) = Complex.exp (G t) := by
    have htangent (u : ℝ) : Complex.exp (F (stripBottom u)) =
        Complex.exp (α u * Complex.I) := by
      rw [hF]
      change planeToComplex (extendedSecant r u 0) = _
      rw [extendedSecant_zero, hα.velocity_eq,
        planeToComplex_tangent]
    change Complex.exp (F (stripBottom t)) =
      Complex.exp (F (stripBottom 0) + (α t - α 0) * Complex.I)
    rw [htangent t, Complex.exp_add, htangent 0,
      ← Complex.exp_add]
    congr 1
    ring
  have hmaps := continuousMap_eq_of_exp_eq FB G 0 hbase hexp
  have hs := congrArg (fun H : C(ℝ, ℂ) => H s) hmaps
  simpa [FB, G, stripBottomMap] using hs

theorem secantLog_bottom_period_eq_angle {r : ℝ → Plane} {α : ℝ → ℝ}
    (hα : IsTangentAngleLift r α)
    (F : C(secantStrip, ℂ))
    (hF : ∀ p : secantStrip,
      Complex.exp (F p) = planeToComplex (extendedSecant r p.1.1 p.1.2))
    (s : ℝ) :
    F (stripBottom (s + period)) - F (stripBottom s) =
      (α (s + period) - α s) * Complex.I := by
  rw [secantLog_bottom_eq_tangentLog hα F hF (s + period),
    secantLog_bottom_eq_tangentLog hα F hF s]
  ring

theorem exists_support_parameter {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    ∃ a : ℝ, ∀ t : ℝ, (r a) 0 ≤ (r t) 0 := by
  have hc : Continuous (fun t : ℝ => (r t) 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp hr.smooth.continuous
  obtain ⟨a, _, ha⟩ := isCompact_Icc.exists_isMinOn
    ⟨(0 : ℝ), by exact ⟨le_rfl, period_pos.le⟩⟩ hc.continuousOn
  refine ⟨a, fun t => ?_⟩
  letI : Fact (0 < period) := ⟨period_pos⟩
  let t₀ := AddCircle.equivIco period 0 (t : AddCircle period)
  have ht₀ : (t₀ : ℝ) ∈ Ico (0 : ℝ) period := by
    simpa [t₀] using t₀.2
  have hclass : ((t₀ : ℝ) : AddCircle period) = (t : AddCircle period) := by
    exact AddCircle.coe_equivIco (p := period) (a := 0) (y := (t : AddCircle period))
  have hrt : r t₀ = r t := by
    have h := congrArg hr.periodic.lift hclass
    simpa [t₀] using h
  rw [← hrt]
  exact ha (Ico_subset_Icc_self ht₀)

theorem support_velocity_first_eq_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ)
    (ha : ∀ t : ℝ, (r a) 0 ≤ (r t) 0) :
    (velocity r a) 0 = 0 := by
  have hmin : IsLocalMin (fun t : ℝ => (r t) 0) a :=
    Filter.Eventually.of_forall ha
  have hdr : HasDerivAt r (velocity r a) a := by
    simpa [velocity] using
      ((hr.smooth.differentiable (by norm_num)) a).hasDerivAt
  have hcoord : HasDerivAt (fun t : ℝ => (r t) 0) ((velocity r a) 0) a := by
    simpa [Function.comp_def] using
      ((EuclideanSpace.proj 0).hasFDerivAt.comp_hasDerivAt a hdr)
  exact hmin.hasDerivAt_eq_zero hcoord

theorem hasDerivAt_coord {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (i : Fin 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (r s) i) ((velocity r t) i) t := by
  have hdr : HasDerivAt r (velocity r t) t := by
    simpa [velocity] using
      ((hr.smooth.differentiable (by norm_num)) t).hasDerivAt
  simpa [Function.comp_def] using
    ((EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hdr)

theorem velocity_coord_intervalIntegrable {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (i : Fin 2) (a b : ℝ) :
    IntervalIntegrable (fun t => (velocity r t) i) volume a b := by
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp
    (velocity_continuous hr)).intervalIntegrable a b

/-- For a closed curve, the two usual coordinate forms of its signed area
agree. This is integration by parts with the periodic endpoint term removed. -/
theorem integral_coord_mul_velocity_eq_neg {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    (∫ t in (0 : ℝ)..period, (r t) 0 * (velocity r t) 1) =
      -(∫ t in (0 : ℝ)..period, (r t) 1 * (velocity r t) 0) := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := period)
    (u := fun t => (r t) 0) (v := fun t => (r t) 1)
    (u' := fun t => (velocity r t) 0)
    (v' := fun t => (velocity r t) 1)
    (fun t _ => hasDerivAt_coord hr 0 t)
    (fun t _ => hasDerivAt_coord hr 1 t)
    (velocity_coord_intervalIntegrable hr 0 0 period)
    (velocity_coord_intervalIntegrable hr 1 0 period)
  have hend : r period = r 0 := by
    simpa using hr.periodic 0
  rw [hend] at hparts
  simpa [mul_comm] using hparts

theorem signedArea_eq_integral_coord_mul_velocity {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    signedArea r =
      ∫ t in (0 : ℝ)..period, (r t) 0 * (velocity r t) 1 := by
  have hxy : IntervalIntegrable
      (fun t => (r t) 0 * (velocity r t) 1) volume 0 period :=
    (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
        hr.smooth.continuous).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
        (velocity_continuous hr))).intervalIntegrable _ _
  have hyx : IntervalIntegrable
      (fun t => (r t) 1 * (velocity r t) 0) volume 0 period :=
    (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
        hr.smooth.continuous).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
        (velocity_continuous hr))).intervalIntegrable _ _
  rw [signedArea, show
    (fun t => det2 (r t) (velocity r t)) =
      fun t => (r t) 0 * (velocity r t) 1 -
        (r t) 1 * (velocity r t) 0 by rfl,
    intervalIntegral.integral_sub hxy hyx,
    integral_coord_mul_velocity_eq_neg hr]
  ring

theorem integral_velocity_coord_eq_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (i : Fin 2) :
    (∫ t in (0 : ℝ)..period, (velocity r t) i) = 0 := by
  have hderiv (t : ℝ) :
      deriv (fun s : ℝ => (r s) i) t = (velocity r t) i :=
    (hasDerivAt_coord hr i t).deriv
  have hint : IntervalIntegrable
      (deriv fun s : ℝ => (r s) i) volume 0 period := by
    rw [show (deriv fun s : ℝ => (r s) i) =
        fun t => (velocity r t) i by
      funext t
      exact hderiv t]
    exact velocity_coord_intervalIntegrable hr i 0 period
  calc
    (∫ t in (0 : ℝ)..period, (velocity r t) i) =
        ∫ t in (0 : ℝ)..period, deriv (fun s : ℝ => (r s) i) t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (hderiv t).symm
    _ =
        (r period) i - (r 0) i := by
      exact intervalIntegral.integral_deriv_eq_sub
        (fun t _ => (hasDerivAt_coord hr i t).differentiableAt)
        hint
    _ = 0 := by
      have hend : r period = r 0 := by
        simpa using hr.periodic 0
      rw [hend, sub_self]

/-- Translating the first coordinate to a vertical supporting line does not
change the signed-area integral. This places the analytic orientation
hypothesis in the same coordinates as the supporting-secant argument. -/
theorem signedArea_eq_integral_sub_support_mul_velocity {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) :
    signedArea r =
      ∫ t in (0 : ℝ)..period,
        ((r t) 0 - (r a) 0) * (velocity r t) 1 := by
  rw [signedArea_eq_integral_coord_mul_velocity hr]
  have hxv : IntervalIntegrable
      (fun t => (r t) 0 * (velocity r t) 1) volume 0 period :=
    (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
        hr.smooth.continuous).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
        (velocity_continuous hr))).intervalIntegrable _ _
  have hv : IntervalIntegrable
      (fun t => (r a) 0 * (velocity r t) 1) volume 0 period :=
    (velocity_coord_intervalIntegrable hr 1 0 period).const_mul _
  rw [show
    (fun t => ((r t) 0 - (r a) 0) * (velocity r t) 1) =
      fun t => (r t) 0 * (velocity r t) 1 -
        (r a) 0 * (velocity r t) 1 by
      funext t
      ring,
    intervalIntegral.integral_sub hxv hv,
    intervalIntegral.integral_const_mul,
    integral_velocity_coord_eq_zero hr 1,
    mul_zero, sub_zero]

theorem positive_integral_sub_support_mul_velocity {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ) :
    0 < ∫ t in (0 : ℝ)..period,
      ((r t) 0 - (r a) 0) * (velocity r t) 1 := by
  rw [← signedArea_eq_integral_sub_support_mul_velocity hr a]
  exact hr.positive_orientation

theorem subperiod_smul_extendedSecant_eq_sub {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (s δ : ℝ)
    (hhalf : ¬δ ≤ period / 2) :
    (period - δ) • extendedSecant r s δ = r (s + δ) - r s := by
  rw [extendedSecant, if_neg hhalf]
  calc
    (period - δ) • -averageVelocity r s (δ - period) =
        (δ - period) • averageVelocity r s (δ - period) := by
      rw [smul_neg, ← neg_smul]
      congr 1
      ring
    _ = r (s + (δ - period)) - r s :=
      smul_averageVelocity_eq_sub hr _ _
    _ = r (s + δ) - r s := by
      have hp := hr.periodic (s + (δ - period))
      have heq : r (s + δ) = r (s + (δ - period)) := by
        calc
          r (s + δ) = r (s + (δ - period) + period) := by
            congr 1
            ring
          _ = r (s + (δ - period)) := hp
      rw [heq]

theorem support_extendedSecant_first_nonneg {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (a : ℝ)
    (ha : ∀ t : ℝ, (r a) 0 ≤ (r t) 0)
    (δ : ℝ) (hδ : δ ∈ Icc (0 : ℝ) period) :
    0 ≤ (extendedSecant r a δ) 0 := by
  have hvzero := support_velocity_first_eq_zero hr a ha
  have hchord : 0 ≤ (r (a + δ) - r a) 0 := by
    change 0 ≤ (r (a + δ)) 0 - (r a) 0
    exact sub_nonneg.mpr (ha (a + δ))
  by_cases hhalf : δ ≤ period / 2
  · by_cases hzero : δ = 0
    · simp [hzero, extendedSecant_zero, hvzero]
    · have hscale := congrArg (fun v : Plane => v 0)
        (smul_averageVelocity_eq_sub hr a δ)
      rw [extendedSecant, if_pos hhalf]
      simp only [PiLp.smul_apply, smul_eq_mul] at hscale
      rw [← hscale] at hchord
      exact nonneg_of_mul_nonneg_right hchord
        (lt_of_le_of_ne hδ.1 (Ne.symm hzero))
  · by_cases hend : δ = period
    · simp [hend, extendedSecant_period, hvzero]
    · have hscale := congrArg (fun v : Plane => v 0)
        (subperiod_smul_extendedSecant_eq_sub hr a δ hhalf)
      simp only [PiLp.smul_apply, smul_eq_mul] at hscale
      rw [← hscale] at hchord
      exact nonneg_of_mul_nonneg_right hchord
        (sub_pos.mpr (lt_of_le_of_ne hδ.2 hend))

noncomputable def stripVerticalMap (a : ℝ) : C(Icc (0 : ℝ) period, secantStrip) :=
  { toFun := fun δ => ⟨(a, δ), ⟨mem_univ _, δ.property⟩⟩
    continuous_toFun := Continuous.subtype_mk
      (continuous_const.prodMk continuous_subtype_val) _ }

theorem secantLog_support_vertical_im {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (F : C(secantStrip, ℂ))
    (hF : ∀ p : secantStrip,
      Complex.exp (F p) = planeToComplex (extendedSecant r p.1.1 p.1.2))
    (a : ℝ) (ha : ∀ t : ℝ, (r a) 0 ≤ (r t) 0) :
    (F (stripTop a) - F (stripBottom a)).im = Real.pi ∨
      (F (stripTop a) - F (stripBottom a)).im = -Real.pi := by
  let J : Set ℝ := Icc (0 : ℝ) period
  letI : ContractibleSpace J := by
    exact convex_Icc (0 : ℝ) period |>.contractibleSpace
      ⟨0, le_rfl, period_pos.le⟩
  letI : LocPathConnectedSpace J :=
    (convex_Icc (0 : ℝ) period).locPathConnectedSpace
  let V : C(J, ℂ) := F.comp (stripVerticalMap a)
  let Q : C(J, ℂ) :=
    { toFun := fun δ => planeToComplex (extendedSecant r a δ)
      continuous_toFun := planeToComplex.continuous.comp
        ((extendedSecant_continuous hr).comp
          (continuous_const.prodMk continuous_subtype_val)) }
  have hQ_ne (δ : J) : Q δ ≠ 0 := by
    intro hzero
    apply extendedSecant_ne_zero hr a δ δ.property
    apply planeToComplex.injective
    simpa [Q] using hzero
  have hQ_re (δ : J) : 0 ≤ (Q δ).re := by
    simpa [Q] using support_extendedSecant_first_nonneg hr a ha δ δ.property
  have hQ_slit (δ : J) : Q δ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hpos : 0 < (Q δ).re
    · exact Or.inl hpos
    · refine Or.inr ?_
      intro him
      apply hQ_ne δ
      apply Complex.ext
      · simpa using le_antisymm (le_of_not_gt hpos) (hQ_re δ)
      · simpa using him
  let P : C(J, ℂ) :=
    { toFun := fun δ => Complex.log (Q δ)
      continuous_toFun := Q.continuous.clog hQ_slit }
  let d₀ : J := ⟨0, le_rfl, period_pos.le⟩
  let dL : J := ⟨period, period_pos.le, le_rfl⟩
  have hV (δ : J) : Complex.exp (V δ) = Q δ := by
    simpa [V, Q, stripVerticalMap] using hF (stripVerticalMap a δ)
  have hP (δ : J) : Complex.exp (P δ) = Q δ := by
    exact Complex.exp_log (hQ_ne δ)
  let D : ℂ := V d₀ - P d₀
  let G : C(J, ℂ) := V * 0 + P + ContinuousMap.const J D
  have hD : Complex.exp D = 1 := by
    dsimp [D]
    rw [Complex.exp_sub, hV, hP, div_self (hQ_ne d₀)]
  have hbase : V d₀ = G d₀ := by
    simp [G, D]
  have hexp (δ : J) : Complex.exp (V δ) = Complex.exp (G δ) := by
    simp only [G, ContinuousMap.add_apply,
      ContinuousMap.const_apply, mul_zero, zero_add, Complex.exp_add, hV, hP, hD,
      mul_one]
  have hmaps := continuousMap_eq_of_exp_eq V G d₀ hbase hexp
  have hdiff : V dL - V d₀ = P dL - P d₀ := by
    have hL := congrArg (fun H : C(J, ℂ) => H dL) hmaps
    have h0 := congrArg (fun H : C(J, ℂ) => H d₀) hmaps
    simp only [G, ContinuousMap.add_apply, ContinuousMap.const_apply,
      mul_zero, zero_add] at hL h0
    rw [hL, h0]
    ring
  have hQ0 : Q d₀ = planeToComplex (velocity r a) := by
    simp [Q, d₀, extendedSecant_zero]
  have hQL : Q dL = -planeToComplex (velocity r a) := by
    change planeToComplex (extendedSecant r a period) = _
    rw [extendedSecant_period]
    exact map_neg planeToComplex _
  have him : (F (stripTop a) - F (stripBottom a)).im =
      (Q dL).arg - (Q d₀).arg := by
    have h := congrArg Complex.im hdiff
    simpa [V, P, d₀, dL, stripVerticalMap, stripTop, stripBottom,
      Complex.log_im] using h
  let z : ℂ := planeToComplex (velocity r a)
  have hz_ne : z ≠ 0 := by
    intro hzero
    have hvzero : velocity r a = 0 := by
      apply planeToComplex.injective
      simpa [z] using hzero
    have hnorm := hr.unit_speed a
    simp [hvzero] at hnorm
  have hz_re : z.re = 0 := by
    simpa [z] using support_velocity_first_eq_zero hr a ha
  have hz_im_ne : z.im ≠ 0 := by
    intro himzero
    apply hz_ne
    apply Complex.ext <;> simp [hz_re, himzero]
  rcases lt_or_gt_of_ne hz_im_ne with hneg | hpos
  · left
    rw [hQL, hQ0] at him
    have hargz : z.arg = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hz_re, hneg⟩
    have hargneg : (-z).arg = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp [hz_re], by simpa using hneg⟩
    rw [hargz, hargneg] at him
    linarith
  · right
    rw [hQL, hQ0] at him
    have hargz : z.arg = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨hz_re, hpos⟩
    have hargneg : (-z).arg = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by simp [hz_re], by simpa using hpos⟩
    rw [hargz, hargneg] at him
    linarith

theorem angle_period_sub_eq_period_or_neg {r : ℝ → Plane} {α : ℝ → ℝ}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (hα : IsTangentAngleLift r α) :
    α period - α 0 = period ∨ α period - α 0 = -period := by
  obtain ⟨F, hF⟩ := exists_secantLog hr
  obtain ⟨a, ha⟩ := exists_support_parameter hr
  have hvertical := secantLog_support_vertical_im hr F hF a ha
  let p₀ : secantStrip := stripBottom a
  have hperiod := secantLog_bottom_period hr F hF p₀ 0
  have hangle := secantLog_bottom_period_eq_angle hα F hF 0
  have hperiod' :
      F (stripBottom period) - F (stripBottom 0) =
        2 * (F (stripTop a) - F (stripBottom a)) := by
    simpa [p₀] using hperiod
  have hangle' :
      F (stripBottom period) - F (stripBottom 0) =
        (α period - α 0) * Complex.I := by
    simpa using hangle
  have hcomplex :
      (α period - α 0) * Complex.I =
        2 * (F (stripTop a) - F (stripBottom a)) := by
    exact hangle'.symm.trans hperiod'
  have him := congrArg Complex.im hcomplex
  norm_num at him
  rcases hvertical with hpos | hneg
  · left
    have hpos' : (F (stripTop a)).im - (F (stripBottom a)).im = Real.pi := by
      simpa using hpos
    rw [hpos'] at him
    simpa [period] using him
  · right
    have hneg' : (F (stripTop a)).im - (F (stripBottom a)).im = -Real.pi := by
      simpa using hneg
    rw [hneg'] at him
    simpa [period] using him

end Submission.Helpers
