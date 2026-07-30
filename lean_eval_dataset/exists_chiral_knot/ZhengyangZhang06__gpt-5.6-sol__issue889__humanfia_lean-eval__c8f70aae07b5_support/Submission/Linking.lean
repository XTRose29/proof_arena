import ChallengeDeps
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

open LeanEval.KnotTheory
open Complex MeasureTheory Set Topology
open scoped unitInterval Interval ComplexConjugate

namespace Submission.Linking

noncomputable section

def invForm (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) z⁻¹

def dInvForm (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) ∘L
    (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)).restrictScalars ℝ

theorem invForm_homotopy_invariant
    {a c : ℂ} {gammaOne : Path a a} {gammaTwo : Path c c}
    (phi : (gammaOne : C(I, ℂ)).Homotopy gammaTwo)
    (hne : ∀ p : I × I, phi p ≠ 0)
    (hloop : ∀ s : I, phi (s, 1) = phi (s, 0))
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (phi.extend xy.1) xy.2) (Icc 0 1)) :
    curveIntegral invForm gammaOne = curveIntegral invForm gammaTwo := by
  have hsides : curveIntegral invForm (phi.evalAt 1) =
      curveIntegral invForm (phi.evalAt 0) := by
    let e : Path (gammaOne 0) (gammaTwo 0) := (phi.evalAt 1).cast (by simp) (by simp)
    calc
      curveIntegral invForm (phi.evalAt 1) = curveIntegral invForm e := by
        symm
        exact curveIntegral_cast invForm (phi.evalAt 1) (by simp) (by simp)
      _ = curveIntegral invForm (phi.evalAt 0) := by
        congr 1
        ext s
        exact hloop s
  have hclosed : IsClosed (range phi) :=
    (isCompact_range (map_continuous phi)).isClosed
  have hmain := phi.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := range phi) (ω := invForm) (dω := dInvForm)
    (fun _ _ _ _ => mem_range_self _)
    (fun z hz => by
      rcases hz with ⟨p, rfl⟩
      exact ((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp (phi p)
        ((hasFDerivAt_inv (hne p)).restrictScalars ℝ)).hasFDerivWithinAt)
    (by
      rw [hclosed.closure_eq]
      rintro _ ⟨p, rfl⟩
      exact (((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp (phi p)
        ((hasFDerivAt_inv (hne p)).restrictScalars ℝ)).continuousAt.continuousWithinAt))
    (fun z _ u _ v _ => by simp [dInvForm, mul_left_comm, mul_comm])
    hcontdiff
  rw [hsides] at hmain
  exact add_right_cancel hmain

def periodicLoop (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t) :
    Path (curve 0) (curve 0) where
  toFun u := curve (2 * Real.pi * (u : ℝ))
  continuous_toFun := hcurve.continuous.comp (by fun_prop)
  source' := by simp
  target' := by
    simp only [show ((1 : I) : ℝ) = 1 by rfl, mul_one]
    simpa using hperiodic 0

def reparamLoop (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t) (sigma : CircleReparam) :
    Path (curve (sigma.f 0)) (curve (sigma.f 0)) where
  toFun u := curve (sigma.f (2 * Real.pi * (u : ℝ)))
  continuous_toFun := hcurve.continuous.comp
    (sigma.smooth.continuous.comp (by fun_prop))
  source' := by simp
  target' := by
    simp only [show ((1 : I) : ℝ) = 1 by rfl, mul_one]
    rw [show 2 * Real.pi = 0 + 2 * Real.pi by ring, sigma.periodic, hperiodic]

def linearLift (sigma : CircleReparam) (a u : ℝ) : ℝ :=
  (1 - a) * (2 * Real.pi * u) + a * sigma.f (2 * Real.pi * u)

def reparamHomotopy (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t) (sigma : CircleReparam) :
    ((periodicLoop curve hcurve hperiodic : Path _ _) : C(I, ℂ)).Homotopy
      (reparamLoop curve hcurve hperiodic sigma) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : I × I => curve (linearLift sigma (p.1 : ℝ) (p.2 : ℝ)), by
      apply hcurve.continuous.comp
      have hsigma : Continuous (fun p : I × I =>
          sigma.f (2 * Real.pi * (p.2 : ℝ))) :=
        sigma.smooth.continuous.comp (by fun_prop)
      unfold linearLift
      fun_prop⟩
    (by
      intro u
      simp [linearLift, periodicLoop])
    (by
      intro u
      simp [linearLift, reparamLoop])

theorem curveIntegral_reparam
    (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t)
    (hne : ∀ t, curve t ≠ 0) (sigma : CircleReparam) :
    curveIntegral invForm (periodicLoop curve hcurve hperiodic) =
      curveIntegral invForm (reparamLoop curve hcurve hperiodic sigma) := by
  let phi := reparamHomotopy curve hcurve hperiodic sigma
  have hphi_ne : ∀ p : I × I, phi p ≠ 0 := by
    intro p
    exact hne _
  have hphi_loop : ∀ a : I, phi (a, 1) = phi (a, 0) := by
    intro a
    change curve (linearLift sigma (a : ℝ) 1) =
      curve (linearLift sigma (a : ℝ) 0)
    have hsigma := sigma.periodic 0
    simp only [zero_add] at hsigma
    have hlift : linearLift sigma (a : ℝ) 1 =
        linearLift sigma (a : ℝ) 0 + 2 * Real.pi := by
      simp [linearLift, hsigma]
      ring
    rw [hlift, hperiodic]
  have heq : Set.EqOn
      (fun x : ℝ × ℝ => Set.IccExtend zero_le_one (phi.extend x.1) x.2)
      (fun x : ℝ × ℝ => curve (linearLift sigma x.1 x.2)) (Set.Icc 0 1) := by
    rw [Icc_prod_eq]
    rintro ⟨a, u⟩ ⟨ha, hu⟩
    lift a to I using ha
    lift u to I using hu
    change Set.IccExtend zero_le_one (phi.extend (a : ℝ)) (u : ℝ) =
      curve (linearLift sigma (a : ℝ) (u : ℝ))
    rw [Set.IccExtend_of_mem _ _ u.property, phi.extend_apply_coe]
    rfl
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ × ℝ => curve (linearLift sigma x.1 x.2)) := by
    have hsigma : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ × ℝ => sigma.f (2 * Real.pi * x.2)) :=
      sigma.smooth.comp (by fun_prop)
    unfold linearLift
    fun_prop
  have hcontdiff : ContDiffOn ℝ 2
      (fun x : ℝ × ℝ => Set.IccExtend zero_le_one (phi.extend x.1) x.2)
      (Set.Icc 0 1) :=
    (hsmooth.of_le (WithTop.coe_le_coe.2
      (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))).contDiffOn.congr heq
  exact invForm_homotopy_invariant phi hphi_ne hphi_loop hcontdiff

lemma deriv_map_conj {a b : ℂ} (g : Path a b) (t : ℝ) :
    deriv (g.map Complex.continuous_conj).extend t =
      conj (deriv g.extend t) := by
  change deriv (fun x => (g.map Complex.continuous_conj).extend x) t = _
  rw [show (fun x => (g.map Complex.continuous_conj).extend x) =
      Complex.conjCLE ∘ g.extend by funext x; rfl]
  have h := Complex.conjCLE.comp_fderiv (f := g.extend) (x := t)
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) h
  simpa [Complex.conjCLE_apply] using h1

theorem curveIntegral_map_conj {a b : ℂ} (g : Path a b) :
    curveIntegral invForm (g.map Complex.continuous_conj) =
      conj (curveIntegral invForm g) := by
  rw [curveIntegral_eq_intervalIntegral_deriv,
    curveIntegral_eq_intervalIntegral_deriv]
  calc
    (∫ t in 0..1, invForm ((g.map Complex.continuous_conj).extend t)
        (deriv (g.map Complex.continuous_conj).extend t)) =
        ∫ t in 0..1, conj (invForm (g.extend t) (deriv g.extend t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      change invForm ((g.map Complex.continuous_conj).extend t)
          (deriv (fun x => (g.map Complex.continuous_conj).extend x) t) = _
      rw [deriv_map_conj g t]
      rw [show (g.map Complex.continuous_conj).extend t =
        conj (g.extend t) by rfl]
      simp [invForm]
    _ = conj (∫ t in 0..1, invForm (g.extend t) (deriv g.extend t)) :=
      intervalIntegral.intervalIntegral_conj

def windingValue (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t) : ℝ :=
  (curveIntegral invForm (periodicLoop curve hcurve hperiodic)).im

theorem windingValue_congr
    {curve curve' : ℝ → ℂ} (h : curve = curve')
    (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t)
    (hcurve' : ContDiff ℝ (⊤ : ℕ∞) curve')
    (hperiodic' : ∀ t, curve' (t + 2 * Real.pi) = curve' t) :
    windingValue curve hcurve hperiodic =
      windingValue curve' hcurve' hperiodic' := by
  subst curve'
  rfl

theorem windingValue_reparam
    (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t)
    (hne : ∀ t, curve t ≠ 0) (sigma : CircleReparam) :
    windingValue curve hcurve hperiodic =
      (curveIntegral invForm (reparamLoop curve hcurve hperiodic sigma)).im := by
  exact congrArg Complex.im (curveIntegral_reparam curve hcurve hperiodic hne sigma)

theorem windingValue_eq_of_reparam
    (source target : ℝ → ℂ)
    (hsource : ContDiff ℝ (⊤ : ℕ∞) source)
    (htarget : ContDiff ℝ (⊤ : ℕ∞) target)
    (hsourcePeriodic : ∀ t, source (t + 2 * Real.pi) = source t)
    (htargetPeriodic : ∀ t, target (t + 2 * Real.pi) = target t)
    (htargetNe : ∀ t, target t ≠ 0) (sigma : CircleReparam)
    (hcomp : ∀ t, target (sigma.f t) = source t) :
    windingValue target htarget htargetPeriodic =
      windingValue source hsource hsourcePeriodic := by
  have hreparam := curveIntegral_reparam target htarget htargetPeriodic htargetNe sigma
  let sourcePath := periodicLoop source hsource hsourcePeriodic
  let targetPath := reparamLoop target htarget htargetPeriodic sigma
  have hzero : target (sigma.f 0) = source 0 := hcomp 0
  let sourcePath' : Path (target (sigma.f 0)) (target (sigma.f 0)) :=
    sourcePath.cast hzero hzero
  have hpaths : targetPath = sourcePath' := by
    ext u
    exact hcomp (2 * Real.pi * (u : ℝ))
  have hintegral : curveIntegral invForm targetPath = curveIntegral invForm sourcePath := by
    calc
      curveIntegral invForm targetPath = curveIntegral invForm sourcePath' := by rw [hpaths]
      _ = curveIntegral invForm sourcePath :=
        curveIntegral_cast invForm sourcePath hzero hzero
  unfold windingValue
  exact congrArg Complex.im (hreparam.trans hintegral)

theorem windingValue_conj
    (curve : ℝ → ℂ) (hcurve : ContDiff ℝ (⊤ : ℕ∞) curve)
    (hperiodic : ∀ t, curve (t + 2 * Real.pi) = curve t) :
    windingValue (fun t => conj (curve t))
      (Complex.conjCLE.contDiff.comp hcurve)
      (fun t => congrArg conj (hperiodic t)) =
      -windingValue curve hcurve hperiodic := by
  have hpath : periodicLoop (fun t => conj (curve t))
      (Complex.conjCLE.contDiff.comp hcurve)
      (fun t => congrArg conj (hperiodic t)) =
      (periodicLoop curve hcurve hperiodic).map Complex.continuous_conj := by
    ext u
    rfl
  unfold windingValue
  rw [hpath, curveIntegral_map_conj]
  simp

end


end Submission.Linking
