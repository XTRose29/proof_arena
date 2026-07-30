import ChallengeDeps
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.CircleIntegral

open LeanEval.KnotTheory
open Complex MeasureTheory Set Topology
open scoped unitInterval Interval

namespace Submission

noncomputable def invForm (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) z⁻¹

noncomputable def dInvForm (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) ∘L
    (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)).restrictScalars ℝ

theorem invForm_homotopy_invariant
    {a c : ℂ} {γ₁ : Path a a} {γ₂ : Path c c}
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hne : ∀ p : I × I, φ p ≠ 0)
    (hloop : ∀ s : I, φ (s, 1) = φ (s, 0))
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    curveIntegral invForm γ₁ = curveIntegral invForm γ₂ := by
  have hsides : curveIntegral invForm (φ.evalAt 1) =
      curveIntegral invForm (φ.evalAt 0) := by
    let e : Path (γ₁ 0) (γ₂ 0) := (φ.evalAt 1).cast (by simp) (by simp)
    calc
      curveIntegral invForm (φ.evalAt 1) = curveIntegral invForm e := by
        symm
        exact curveIntegral_cast invForm (φ.evalAt 1) (by simp) (by simp)
      _ = curveIntegral invForm (φ.evalAt 0) := by
        congr 1
        ext s
        exact hloop s
  have hclosed : IsClosed (range φ) :=
    (isCompact_range (map_continuous φ)).isClosed
  have hmain := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := range φ) (ω := invForm) (dω := dInvForm)
    (fun _ _ _ _ => mem_range_self _)
    (fun z hz => by
      rcases hz with ⟨p, rfl⟩
      exact ((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp (φ p)
        ((hasFDerivAt_inv (hne p)).restrictScalars ℝ)).hasFDerivWithinAt)
    (by
      rw [hclosed.closure_eq]
      rintro _ ⟨p, rfl⟩
      exact (((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp (φ p)
        ((hasFDerivAt_inv (hne p)).restrictScalars ℝ)).continuousAt.continuousWithinAt))
    (fun z _ u _ v _ => by simp [dInvForm, mul_left_comm, mul_comm])
    hcontdiff
  rw [hsides] at hmain
  exact add_right_cancel hmain

noncomputable def xyCircle (height : ℝ) (t : ℝ) : R3 :=
  WithLp.toLp 2 ![(circleMap 0 1 t).re, (circleMap 0 1 t).im, height]

noncomputable def xzCircle (t : ℝ) : R3 :=
  WithLp.toLp 2 ![(circleMap 1 1 t).re, 0, (circleMap 1 1 t).im]

noncomputable def xyProj : R3 →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap ∘L
    ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).prod
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1))

noncomputable def xzProj : R3 →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap ∘L
    ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).prod
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2))

noncomputable def detector (p : R3) : ℂ :=
  ⟨p.ofLp 0 ^ 2 + p.ofLp 1 ^ 2 + p.ofLp 2 ^ 2 - 1, 2 * p.ofLp 2⟩

theorem xyCircle_smooth (height : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (xyCircle height) := by
  apply contDiff_piLp'
  intro i
  fin_cases i
  · simpa [xyCircle, Function.comp_def] using
      Complex.reCLM.contDiff.comp (contDiff_circleMap 0 1)
  · simpa [xyCircle, Function.comp_def] using
      Complex.imCLM.contDiff.comp (contDiff_circleMap 0 1)
  · exact contDiff_const

theorem xyCircle_periodic (height t : ℝ) :
    xyCircle height (t + 2 * Real.pi) = xyCircle height t := by
  unfold xyCircle
  rw [periodic_circleMap 0 1 t]

theorem xyCircle_injOn (height : ℝ) :
    Set.InjOn (xyCircle height) (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht hst
  apply (injOn_circleMap_of_abs_sub_le' one_ne_zero (by norm_num)) hs ht
  apply Complex.ext
  · simpa [xyCircle] using congrArg (fun p : R3 => p.ofLp 0) hst
  · simpa [xyCircle] using congrArg (fun p : R3 => p.ofLp 1) hst

theorem xyCircle_immersion (height t : ℝ) : deriv (xyCircle height) t ≠ 0 := by
  intro hzero
  have hcomp : (⇑xyProj ∘ xyCircle height) = circleMap 0 1 := by
    funext s
    apply Complex.ext <;> simp [xyProj, xyCircle]
  have hder := (xyProj.hasFDerivAt.comp_hasDerivAt t
    ((xyCircle_smooth height).differentiable (by simp) t).hasDerivAt).deriv
  rw [hcomp, hzero, map_zero] at hder
  exact deriv_circleMap_ne_zero one_ne_zero hder

theorem xzCircle_smooth : ContDiff ℝ (⊤ : ℕ∞) xzCircle := by
  apply contDiff_piLp'
  intro i
  fin_cases i
  · simpa [xzCircle, Function.comp_def] using
      Complex.reCLM.contDiff.comp (contDiff_circleMap 1 1)
  · exact contDiff_const
  · simpa [xzCircle, Function.comp_def] using
      Complex.imCLM.contDiff.comp (contDiff_circleMap 1 1)

theorem xzCircle_periodic (t : ℝ) : xzCircle (t + 2 * Real.pi) = xzCircle t := by
  unfold xzCircle
  rw [periodic_circleMap 1 1 t]

theorem xzCircle_injOn : Set.InjOn xzCircle (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht hst
  apply (injOn_circleMap_of_abs_sub_le' one_ne_zero (by norm_num)) hs ht
  apply Complex.ext
  · simpa [xzCircle] using congrArg (fun p : R3 => p.ofLp 0) hst
  · simpa [xzCircle] using congrArg (fun p : R3 => p.ofLp 2) hst

theorem xzCircle_immersion (t : ℝ) : deriv xzCircle t ≠ 0 := by
  intro hzero
  have hcomp : (⇑xzProj ∘ xzCircle) = circleMap 1 1 := by
    funext s
    apply Complex.ext <;> simp [xzProj, xzCircle]
  have hder := (xzProj.hasFDerivAt.comp_hasDerivAt t
    (xzCircle_smooth.differentiable (by simp) t).hasDerivAt).deriv
  rw [hcomp, hzero, map_zero] at hder
  exact deriv_circleMap_ne_zero one_ne_zero hder

noncomputable def horizontalKnot (height : ℝ) : Knot where
  curve := xyCircle height
  smooth := xyCircle_smooth height
  periodic := xyCircle_periodic height
  injOn := xyCircle_injOn height
  immersion := xyCircle_immersion height

noncomputable def verticalKnot : Knot where
  curve := xzCircle
  smooth := xzCircle_smooth
  periodic := xzCircle_periodic
  injOn := xzCircle_injOn
  immersion := xzCircle_immersion

theorem unlink_disjoint :
    Disjoint (Set.range (xyCircle 0)) (Set.range (xyCircle 3)) := by
  rw [Set.disjoint_left]
  rintro p ⟨s, rfl⟩ ⟨t, hst⟩
  have hz := congrArg (fun q : R3 => q.ofLp 2) hst
  change (3 : ℝ) = 0 at hz
  norm_num at hz

theorem hopf_disjoint : Disjoint (Set.range (xyCircle 0)) (Set.range xzCircle) := by
  rw [Set.disjoint_left]
  rintro p ⟨s, rfl⟩ ⟨t, hst⟩
  have hx := congrArg (fun q : R3 => q.ofLp 0) hst
  have hy := congrArg (fun q : R3 => q.ofLp 1) hst
  have hz := congrArg (fun q : R3 => q.ofLp 2) hst
  simp [xyCircle, xzCircle, circleMap] at hx hy hz
  have hsunit := Real.sin_sq_add_cos_sq s
  have htunit := Real.sin_sq_add_cos_sq t
  have hcs : Real.cos s = 1 ∨ Real.cos s = -1 := by
    apply (sq_eq_one_iff).mp
    nlinarith
  have hct : Real.cos t = 1 ∨ Real.cos t = -1 := by
    apply (sq_eq_one_iff).mp
    nlinarith
  rcases hcs with hcs | hcs <;> rcases hct with hct | hct <;> nlinarith

noncomputable def unlink : TwoLink where
  K := horizontalKnot 0
  L := horizontalKnot 3
  disjoint := unlink_disjoint

noncomputable def hopfLink : TwoLink where
  K := horizontalKnot 0
  L := verticalKnot
  disjoint := hopf_disjoint

theorem detector_xyCircle (t : ℝ) : detector (xyCircle 0 t) = 0 := by
  apply Complex.ext
  · simp [detector, xyCircle, circleMap]
  · simp [detector, xyCircle]

theorem detector_xzCircle (t : ℝ) : detector (xzCircle t) = circleMap 1 2 t := by
  apply Complex.ext
  · simp [detector, xzCircle, circleMap]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · simp [detector, xzCircle, circleMap]

theorem detector_zero_mem_xyCircle {p : R3} (hp : detector p = 0) :
    p ∈ Set.range (xyCircle 0) := by
  have him : p.ofLp 2 = 0 := by
    have h := congrArg Complex.im hp
    simpa [detector] using h
  have hre : p.ofLp 0 ^ 2 + p.ofLp 1 ^ 2 = 1 := by
    have h := congrArg Complex.re hp
    simp [detector, him] at h
    linarith
  let z : ℂ := ⟨p.ofLp 0, p.ofLp 1⟩
  have hz : z ∈ Metric.sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_def]
    rw [show Complex.normSq z = 1 by
      simpa [Complex.normSq_apply, z, pow_two] using hre]
    norm_num
  have hrange : range (circleMap 0 1) = Metric.sphere 0 1 := by
    simpa only [abs_one] using range_circleMap 0 1
  rw [← hrange] at hz
  rcases hz with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext i
  fin_cases i
  · simpa [xyCircle, z] using congrArg Complex.re ht
  · simpa [xyCircle, z] using congrArg Complex.im ht
  · simp [xyCircle, him]

theorem detector_smooth : ContDiff ℝ (⊤ : ℕ∞) detector := by
  rw [← Complex.equivRealProdCLM.comp_contDiff_iff]
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : R3 =>
    (p.ofLp 0 ^ 2 + p.ofLp 1 ^ 2 + p.ofLp 2 ^ 2 - 1, 2 * p.ofLp 2))
  fun_prop

noncomputable def contractPoint (a u : ℝ) : R3 :=
  WithLp.toLp 2
    ![(circleMap 0 (1 - a) (2 * Real.pi * u)).re,
      (circleMap 0 (1 - a) (2 * Real.pi * u)).im, 3]

theorem contractPoint_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × ℝ => contractPoint p.1 p.2) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ =>
      Complex.ofRealCLM (1 - p.1) *
        Complex.exp (Complex.ofRealCLM (2 * Real.pi * p.2) * Complex.I)) := by
    fun_prop
  apply contDiff_piLp'
  intro i
  fin_cases i
  · simpa [contractPoint, circleMap, Function.comp_def] using
      Complex.reCLM.contDiff.comp hc
  · simpa [contractPoint, circleMap, Function.comp_def] using
      Complex.imCLM.contDiff.comp hc
  · simpa [contractPoint] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => (3 : ℝ)))

theorem contractPoint_zero (u : ℝ) : contractPoint 0 u = xyCircle 3 (2 * Real.pi * u) := by
  simp [contractPoint, xyCircle]

theorem contractPoint_one (u : ℝ) : contractPoint 1 u = contractPoint 1 0 := by
  simp [contractPoint, circleMap]

theorem contractPoint_loop (a : ℝ) : contractPoint a 1 = contractPoint a 0 := by
  simp [contractPoint, circleMap]

noncomputable def phase (r : CircleReparam) : ℝ → ℝ :=
  r.f ∘ HMul.hMul (2 * Real.pi)

noncomputable def phaseDeriv (r : CircleReparam) (t : ℝ) : ℝ :=
  2 * Real.pi * deriv r.f (2 * Real.pi * t)

theorem phase_hasDerivAt (r : CircleReparam) (t : ℝ) :
    HasDerivAt (phase r) (phaseDeriv r t) t := by
  have hinner : HasDerivAt (HMul.hMul (2 * Real.pi)) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  have houter : HasDerivAt r.f (deriv r.f (2 * Real.pi * t)) (2 * Real.pi * t) :=
    (r.smooth.differentiable (by simp) _).hasDerivAt
  unfold phase phaseDeriv
  simpa only [mul_comm] using houter.comp t hinner

theorem phaseDeriv_continuous (r : CircleReparam) : Continuous (phaseDeriv r) := by
  have hd : Continuous (deriv r.f) := r.smooth.continuous_deriv (by simp)
  unfold phaseDeriv
  fun_prop

noncomputable def linkingLoop (r : CircleReparam) :
    Path (circleMap 1 2 (r.f 0)) (circleMap 1 2 (r.f 0)) where
  toFun u := circleMap 1 2 (phase r (u : ℝ))
  continuous_toFun := by
    apply (continuous_circleMap 1 2).comp
    exact r.smooth.continuous.comp (by fun_prop)
  source' := by simp [phase]
  target' := by
    simp only [phase, Function.comp_apply]
    rw [show ((1 : I) : ℝ) = 1 by rfl, mul_one]
    change circleMap 1 2 (r.f (2 * Real.pi)) = circleMap 1 2 (r.f 0)
    rw [show 2 * Real.pi = 0 + 2 * Real.pi by ring, r.periodic,
      periodic_circleMap]

theorem linkingLoop_curveIntegral (r : CircleReparam) :
    curveIntegral invForm (linkingLoop r) = 2 * Real.pi * Complex.I := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  let g : ℝ → ℂ := fun t =>
    deriv (circleMap 1 2) t * (circleMap 1 2 t)⁻¹
  have heq :
      (∫ t in (0 : ℝ)..1,
        invForm ((linkingLoop r).extend t) (deriv (linkingLoop r).extend t)) =
      ∫ t in (0 : ℝ)..1, phaseDeriv r t • g (phase r t) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hext : Filter.EventuallyEq (nhds t) (linkingLoop r).extend
        (circleMap 1 2 ∘ phase r) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [Path.extend_apply _ ⟨hs.1.le, hs.2.le⟩]
      rfl
    have hd : HasDerivAt (circleMap 1 2 ∘ phase r)
        (phaseDeriv r t • deriv (circleMap 1 2) (phase r t)) t := by
      simpa only [deriv_circleMap] using
        (hasDerivAt_circleMap 1 2 (phase r t)).scomp t (phase_hasDerivAt r t)
    rw [Path.extend_apply _ htI, hext.deriv_eq, hd.deriv]
    simp [linkingLoop, invForm, g, mul_comm, mul_left_comm, mul_assoc]
  rw [heq]
  have hg : Continuous g := by
    apply Continuous.mul
    · have hderiv : deriv (circleMap 1 2) =
          fun t => circleMap 0 2 t * Complex.I := by
          funext t
          exact deriv_circleMap 1 2 t
      rw [hderiv]
      fun_prop
    · exact (continuous_circleMap 1 2).inv₀ (fun t => circleMap_ne_mem_ball
        (show (0 : ℂ) ∈ Metric.ball 1 2 by norm_num) t)
  have hsubst := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := 1) (f := phase r) (f' := phaseDeriv r) (g := g)
    (fun t _ => phase_hasDerivAt r t) (phaseDeriv_continuous r).continuousOn hg
  change (∫ t in (0 : ℝ)..1, phaseDeriv r t • g (phase r t)) =
    ∫ t in phase r 0..phase r 1, g t at hsubst
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro t
    simp only [g, deriv_circleMap]
    rw [periodic_circleMap 0 2 t, periodic_circleMap 1 2 t]
  have hrper := r.periodic 0
  simp only [zero_add] at hrper
  calc
    (∫ t in (0 : ℝ)..1, phaseDeriv r t • g (phase r t)) =
        ∫ t in phase r 0..phase r 1, g t := hsubst
    _ = ∫ t in r.f 0..r.f 0 + 2 * Real.pi, g t := by
      simp [phase, hrper]
    _ = ∫ t in (0 : ℝ)..0 + 2 * Real.pi, g t :=
      hgper.intervalIntegral_add_eq (r.f 0) 0
    _ = 2 * Real.pi * Complex.I := by
      rw [← circleIntegral.integral_sub_inv_of_mem_ball
        (show (0 : ℂ) ∈ Metric.ball 1 2 by norm_num)]
      simp only [zero_add, circleIntegral, sub_zero, smul_eq_mul, g]

noncomputable def contractMap (Phi : AmbientIsotopy) (p : ℝ × ℝ) : ℂ :=
  detector (Phi.H 1 (contractPoint p.1 p.2))

theorem contractMap_smooth (Phi : AmbientIsotopy) :
    ContDiff ℝ (⊤ : ℕ∞) (contractMap Phi) := by
  have hinput : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ((1 : ℝ), contractPoint p.1 p.2)) :=
    contDiff_const.prodMk contractPoint_smooth
  have hH := Phi.smooth.comp hinput
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × ℝ => detector (Phi.H 1 (contractPoint p.1 p.2)))
  exact detector_smooth.comp hH

theorem contractMap_ne_zero (Phi : AmbientIsotopy) (s : CircleReparam)
    (hK : ∀ t, Phi.H 1 (xyCircle 0 t) = xyCircle 0 (s.f t)) (p : ℝ × ℝ) :
    contractMap Phi p ≠ 0 := by
  intro hp
  rcases detector_zero_mem_xyCircle hp with ⟨t, ht⟩
  have hKt := hK (s.finv t)
  rw [s.right_inv] at hKt
  have hforward :
      Phi.H 1 (contractPoint p.1 p.2) = Phi.H 1 (xyCircle 0 (s.finv t)) := by
    calc
      Phi.H 1 (contractPoint p.1 p.2) = xyCircle 0 t := ht.symm
      _ = Phi.H 1 (xyCircle 0 (s.finv t)) := hKt.symm
  have hinjective := congrArg (Phi.Hinv 1) hforward
  simp only [Phi.inv_left] at hinjective
  have hz := congrArg (fun q : R3 => q.ofLp 2) hinjective
  change (3 : ℝ) = 0 at hz
  norm_num at hz

theorem linkingLoop_curveIntegral_zero_of_isotopy
    (Phi : AmbientIsotopy) (s r : CircleReparam)
    (hK : ∀ t, Phi.H 1 (xyCircle 0 t) = xyCircle 0 (s.f t))
    (hL : ∀ t, Phi.H 1 (xyCircle 3 t) = xzCircle (r.f t)) :
    curveIntegral invForm (linkingLoop r) = 0 := by
  let endpoint : ℂ := contractMap Phi (1, 0)
  let phi : ((linkingLoop r : Path _ _) : C(I, ℂ)).Homotopy (Path.refl endpoint) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : I × I => contractMap Phi ((p.1 : ℝ), (p.2 : ℝ)), by
        apply (contractMap_smooth Phi).continuous.comp
        fun_prop⟩
      (by
        intro u
        change contractMap Phi (0, (u : ℝ)) = circleMap 1 2 (phase r (u : ℝ))
        simp only [contractMap, contractPoint_zero, hL, detector_xzCircle, phase,
          Function.comp_apply])
      (by
        intro u
        change contractMap Phi (1, (u : ℝ)) = endpoint
        unfold endpoint contractMap
        exact congrArg (fun q => detector (Phi.H 1 q)) (contractPoint_one (u : ℝ)))
  have hne : ∀ p : I × I, phi p ≠ 0 := by
    intro p
    exact contractMap_ne_zero Phi s hK ((p.1 : ℝ), (p.2 : ℝ))
  have hloop : ∀ a : I, phi (a, 1) = phi (a, 0) := by
    intro a
    change contractMap Phi ((a : ℝ), 1) = contractMap Phi ((a : ℝ), 0)
    unfold contractMap
    exact congrArg (fun q => detector (Phi.H 1 q)) (contractPoint_loop (a : ℝ))
  have heq : Set.EqOn
      (fun x : ℝ × ℝ => Set.IccExtend zero_le_one (phi.extend x.1) x.2)
      (contractMap Phi) (Set.Icc 0 1) := by
    rw [Icc_prod_eq]
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    lift x to I using hx
    lift y to I using hy
    change Set.IccExtend zero_le_one (phi.extend (x : ℝ)) (y : ℝ) =
      contractMap Phi ((x : ℝ), (y : ℝ))
    rw [Set.IccExtend_of_mem _ _ y.property, phi.extend_apply_coe]
    change contractMap Phi ((x : ℝ), (y : ℝ)) =
      contractMap Phi ((x : ℝ), (y : ℝ))
    rfl
  have hcontdiff : ContDiffOn ℝ 2
      (fun x : ℝ × ℝ => Set.IccExtend zero_le_one (phi.extend x.1) x.2)
      (Set.Icc 0 1) :=
    ((contractMap_smooth Phi).of_le
      (WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))).contDiffOn.congr heq
  simpa using invForm_homotopy_invariant phi hne hloop hcontdiff

theorem unlink_not_isotopic_hopfLink : ¬ unlink.Isotopic hopfLink := by
  rintro ⟨Phi, s, r, hK, hL⟩
  change (∀ t, Phi.H 1 (xyCircle 0 t) = xyCircle 0 (s.f t)) at hK
  change (∀ t, Phi.H 1 (xyCircle 3 t) = xzCircle (r.f t)) at hL
  have hzero := linkingLoop_curveIntegral_zero_of_isotopy Phi s r hK hL
  rw [linkingLoop_curveIntegral r] at hzero
  have him := congrArg Complex.im hzero
  simp at him

theorem exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ :=
  ⟨unlink, hopfLink, unlink_not_isotopic_hopfLink⟩

end Submission
