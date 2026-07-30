import Submission.CoreBoundaryHomotopy
import Submission.FiberAction
import Submission.PeripheralBridge
import Submission.PeripheralCollar

open scoped Topology unitInterval
open LeanEval.KnotTheory

namespace Submission.PeripheralBoundary

noncomputable section

set_option maxHeartbeats 2000000

open PeripheralTube

abbrev NegativeSymmetry := Symmetry.NegativeSymmetry AlgebraicTrefoil.knot

def bindingMap (S : NegativeSymmetry) : Binding ≃ₜ Binding :=
  (CompactifiedSymmetry.sphereHomeomorph S).subtype fun q =>
    (CompactifiedSymmetry.polynomial_zero_iff_image S q).symm

def bindingCircleMap (S : NegativeSymmetry) : Circle ≃ₜ Circle :=
  bindingHomeomorph.symm.trans (bindingMap S) |>.trans bindingHomeomorph

theorem bindingPoint_exp_eq_compactify_curve (t : ℝ) :
    (bindingPoint (Circle.exp t)).1 =
      (Milnor.compactify (AlgebraicTrefoil.curve t)).1 := by
  rw [Milnor.compactify_curve]
  apply Subtype.ext
  apply Prod.ext
  · change ((3 / 5 : ℝ) : ℂ) *
        Complex.exp (((t : ℝ) : ℂ) * Complex.I) ^ 3 =
      AlgebraicTrefoil.sphereCurveZ t
    rw [AlgebraicTrefoil.sphereCurveZ_eq_exp, ← Complex.exp_nat_mul]
    congr 1
    · norm_num
    · apply congrArg Complex.exp
      push_cast
      ring
  · change ((-4 / 5 : ℝ) : ℂ) *
        Complex.exp (((t : ℝ) : ℂ) * Complex.I) ^ 2 =
      AlgebraicTrefoil.sphereCurveW t
    rw [AlgebraicTrefoil.sphereCurveW_eq_exp, ← Complex.exp_nat_mul]
    congr 1
    · norm_num
    · apply congrArg Complex.exp
      push_cast
      ring

theorem bindingCircleMap_exp (S : NegativeSymmetry) (t : ℝ) :
    bindingCircleMap S (Circle.exp t) = Circle.exp (S.sigma.f t) := by
  apply bindingHomeomorph.symm.injective
  simp only [bindingCircleMap, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  change bindingMap S (bindingPoint (Circle.exp t)) =
    bindingPoint (Circle.exp (S.sigma.f t))
  apply Subtype.ext
  change CompactifiedSymmetry.sphereHomeomorph S
      (bindingPoint (Circle.exp t)).1 =
    (bindingPoint (Circle.exp (S.sigma.f t))).1
  rw [bindingPoint_exp_eq_compactify_curve,
    CompactifiedSymmetry.sphereHomeomorph_curve,
    ← bindingPoint_exp_eq_compactify_curve]

theorem circleReparam_add_int_period (sigma : CircleReparam) (n : ℤ) (t : ℝ) :
    sigma.f (t + n * (2 * Real.pi)) =
      sigma.f t + n * (2 * Real.pi) := by
  have hperiodic : Function.Periodic (fun x : ℝ => sigma.f x - x)
      (2 * Real.pi) := by
    intro x
    change sigma.f (x + 2 * Real.pi) - (x + 2 * Real.pi) =
      sigma.f x - x
    rw [sigma.periodic]
    ring
  have h := (hperiodic.int_mul n) t
  change sigma.f (t + n * (2 * Real.pi)) -
      (t + n * (2 * Real.pi)) = sigma.f t - t at h
  linarith

def loopRealLift {x : Circle} (gamma : Path x x) : C(unitInterval, ℝ) :=
  ⟨fun t => Complex.arg x.1 + CircleWinding.liftedLoop gamma t,
    continuous_const.add (CircleWinding.liftedLoop gamma).continuous⟩

theorem exp_loopRealLift {x : Circle} (gamma : Path x x)
    (t : unitInterval) : Circle.exp (loopRealLift gamma t) = gamma t := by
  change Circle.exp
      (Complex.arg x.1 + CircleWinding.liftedLoop gamma t) = gamma t
  rw [Circle.exp_add, Circle.exp_arg,
    CircleWinding.exp_liftedLoop]
  change x * (gamma t * x⁻¹) = gamma t
  calc
    x * (gamma t * x⁻¹) = gamma t * (x * x⁻¹) := by ac_rfl
    _ = gamma t := by simp

def bindingLoopHomotopy (S : NegativeSymmetry) {x : Circle}
    (gamma : Path x x) :
    (gamma : C(unitInterval, Circle)).Homotopy
      (gamma.map (bindingCircleMap S).continuous) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval =>
        Circle.exp
          ((1 - (p.1 : ℝ)) * loopRealLift gamma p.2 +
            (p.1 : ℝ) * S.sigma.f (loopRealLift gamma p.2)), by
      have hsigma : Continuous (fun p : unitInterval × unitInterval =>
          S.sigma.f (loopRealLift gamma p.2)) :=
        S.sigma.smooth.continuous.comp
          ((loopRealLift gamma).continuous.comp continuous_snd)
      exact Circle.exp.continuous.comp (by fun_prop)⟩
    (by
      intro t
      change Circle.exp
          ((1 - ((0 : unitInterval) : ℝ)) * loopRealLift gamma t +
            ((0 : unitInterval) : ℝ) *
              S.sigma.f (loopRealLift gamma t)) = gamma t
      simpa using exp_loopRealLift gamma t)
    (by
      intro t
      change Circle.exp
          ((1 - ((1 : unitInterval) : ℝ)) * loopRealLift gamma t +
            ((1 : unitInterval) : ℝ) *
              S.sigma.f (loopRealLift gamma t)) =
        bindingCircleMap S (gamma t)
      simp only [show ((1 : unitInterval) : ℝ) = 1 by rfl,
        sub_self, zero_mul, one_mul, zero_add]
      calc
        Circle.exp (S.sigma.f (loopRealLift gamma t)) =
            bindingCircleMap S (Circle.exp (loopRealLift gamma t)) :=
          (bindingCircleMap_exp S _).symm
        _ = bindingCircleMap S (gamma t) :=
          congrArg (bindingCircleMap S) (exp_loopRealLift gamma t))

theorem bindingLoopHomotopy_loop (S : NegativeSymmetry) {x : Circle}
    (gamma : Path x x) (s : unitInterval) :
    bindingLoopHomotopy S gamma (s, 1) =
      bindingLoopHomotopy S gamma (s, 0) := by
  obtain ⟨n, hn⟩ := CircleWinding.windingReal_eq_int_mul_two_pi gamma
  have hliftZero : loopRealLift gamma 0 = Complex.arg x.1 := by
    simp [loopRealLift]
  have hliftOne : loopRealLift gamma 1 =
      Complex.arg x.1 + n * (2 * Real.pi) := by
    rw [loopRealLift]
    change Complex.arg x.1 + CircleWinding.windingReal gamma = _
    rw [hn]
  have hsigma := circleReparam_add_int_period S.sigma n (Complex.arg x.1)
  change Circle.exp
      ((1 - (s : ℝ)) * loopRealLift gamma 1 +
        (s : ℝ) * S.sigma.f (loopRealLift gamma 1)) =
    Circle.exp
      ((1 - (s : ℝ)) * loopRealLift gamma 0 +
        (s : ℝ) * S.sigma.f (loopRealLift gamma 0))
  rw [hliftOne, hliftZero, hsigma]
  have harg :
      (1 - (s : ℝ)) * (Complex.arg x.1 + n * (2 * Real.pi)) +
          (s : ℝ) *
            (S.sigma.f (Complex.arg x.1) + n * (2 * Real.pi)) =
        ((1 - (s : ℝ)) * Complex.arg x.1 +
          (s : ℝ) * S.sigma.f (Complex.arg x.1)) +
            n * (2 * Real.pi) := by
    ring
  rw [harg]
  exact (Circle.periodic_exp.int_mul n) _

theorem windingReal_bindingCircleMap (S : NegativeSymmetry) {x : Circle}
    (gamma : Path x x) :
    CircleWinding.windingReal
        (gamma.map (bindingCircleMap S).continuous) =
      CircleWinding.windingReal gamma := by
  symm
  exact CircleWinding.windingReal_eq_of_freeHomotopy
    (bindingLoopHomotopy S gamma) (bindingLoopHomotopy_loop S gamma)

def circleLoopHomotopy {x y : Circle} (gamma : Path x x)
    (delta : Path y y) :
    (gamma : C(unitInterval, Circle)).Homotopy delta :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval =>
        Circle.exp
          ((1 - (p.1 : ℝ)) * loopRealLift gamma p.2 +
            (p.1 : ℝ) * loopRealLift delta p.2), by
      exact Circle.exp.continuous.comp (by fun_prop)⟩
    (by
      intro t
      change Circle.exp
          ((1 - ((0 : unitInterval) : ℝ)) * loopRealLift gamma t +
            ((0 : unitInterval) : ℝ) * loopRealLift delta t) = gamma t
      simpa using exp_loopRealLift gamma t)
    (by
      intro t
      change Circle.exp
          ((1 - ((1 : unitInterval) : ℝ)) * loopRealLift gamma t +
            ((1 : unitInterval) : ℝ) * loopRealLift delta t) = delta t
      simpa using exp_loopRealLift delta t)

theorem circleLoopHomotopy_loop {x y : Circle} (gamma : Path x x)
    (delta : Path y y)
    (hwind : CircleWinding.windingReal gamma =
      CircleWinding.windingReal delta) (s : unitInterval) :
    circleLoopHomotopy gamma delta (s, 1) =
      circleLoopHomotopy gamma delta (s, 0) := by
  have hgammaZero : loopRealLift gamma 0 = Complex.arg x.1 := by
    simp [loopRealLift]
  have hgammaOne : loopRealLift gamma 1 =
      Complex.arg x.1 + CircleWinding.windingReal gamma := by
    rfl
  have hdeltaZero : loopRealLift delta 0 = Complex.arg y.1 := by
    simp [loopRealLift]
  have hdeltaOne : loopRealLift delta 1 =
      Complex.arg y.1 + CircleWinding.windingReal gamma := by
    change Complex.arg y.1 + CircleWinding.windingReal delta = _
    rw [hwind]
  change Circle.exp
      ((1 - (s : ℝ)) * loopRealLift gamma 1 +
        (s : ℝ) * loopRealLift delta 1) =
    Circle.exp
      ((1 - (s : ℝ)) * loopRealLift gamma 0 +
        (s : ℝ) * loopRealLift delta 0)
  rw [hgammaOne, hdeltaOne, hgammaZero, hdeltaZero]
  have harg :
      (1 - (s : ℝ)) *
            (Complex.arg x.1 + CircleWinding.windingReal gamma) +
          (s : ℝ) *
            (Complex.arg y.1 + CircleWinding.windingReal gamma) =
        ((1 - (s : ℝ)) * Complex.arg x.1 +
          (s : ℝ) * Complex.arg y.1) +
            CircleWinding.windingReal gamma := by
    ring
  rw [harg, Circle.exp_add, CircleWinding.exp_windingReal, mul_one]

def collarRadiusMap : C(PeripheralCollar.CollarParameter, ℝ) :=
  ⟨fun x => x.1.1, by fun_prop⟩

def collarLongitudeMap : C(PeripheralCollar.CollarParameter, Circle) :=
  ⟨fun x => x.1.2, by fun_prop⟩

theorem convexCombination_pos {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (1 - s) * a + s * b := by
  by_cases hab : a ≤ b
  · have hmul : 0 ≤ s * (b - a) :=
      mul_nonneg hs0 (sub_nonneg.mpr hab)
    nlinarith
  · have hba : b ≤ a := le_of_not_ge hab
    have hmul : 0 ≤ (1 - s) * (a - b) :=
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hba)
    nlinarith

def collarLoopHomotopy
    {a b : PeripheralCollar.CollarParameter}
    (gamma : Path a a) (delta : Path b b) :
    (gamma : C(unitInterval, PeripheralCollar.CollarParameter)).Homotopy
      delta :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval =>
        ⟨(((1 - (p.1 : ℝ)) * (gamma p.2).1.1 +
              (p.1 : ℝ) * (delta p.2).1.1),
            circleLoopHomotopy
              (gamma.map collarLongitudeMap.continuous)
              (delta.map collarLongitudeMap.continuous) p), by
          constructor
          · have hs0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
            have hs1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
            have hgamma : 0 < (gamma p.2).1.1 := (gamma p.2).2.1
            have hdelta : 0 < (delta p.2).1.1 := (delta p.2).2.1
            change 0 < (1 - (p.1 : ℝ)) * (gamma p.2).1.1 +
              (p.1 : ℝ) * (delta p.2).1.1
            exact convexCombination_pos hgamma hdelta hs0 hs1
          · have hs0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
            have hs1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
            have hgamma : (gamma p.2).1.1 < PeripheralCollar.collarRadius :=
              (gamma p.2).2.2
            have hdelta : (delta p.2).1.1 < PeripheralCollar.collarRadius :=
              (delta p.2).2.2
            change (1 - (p.1 : ℝ)) * (gamma p.2).1.1 +
                (p.1 : ℝ) * (delta p.2).1.1 <
              PeripheralCollar.collarRadius
            have hcomplement := convexCombination_pos
              (show 0 < PeripheralCollar.collarRadius -
                (gamma p.2).1.1 by linarith)
              (show 0 < PeripheralCollar.collarRadius -
                (delta p.2).1.1 by linarith) hs0 hs1
            nlinarith⟩, by
      apply Continuous.subtype_mk
      have hgammaRadius : Continuous
          (fun p : unitInterval × unitInterval => (gamma p.2).1.1) :=
        (collarRadiusMap.continuous.comp gamma.continuous).comp continuous_snd
      have hdeltaRadius : Continuous
          (fun p : unitInterval × unitInterval => (delta p.2).1.1) :=
        (collarRadiusMap.continuous.comp delta.continuous).comp continuous_snd
      have hradius : Continuous (fun p : unitInterval × unitInterval =>
          (1 - (p.1 : ℝ)) * (gamma p.2).1.1 +
            (p.1 : ℝ) * (delta p.2).1.1) := by
        fun_prop
      exact hradius.prodMk
        (circleLoopHomotopy
          (gamma.map collarLongitudeMap.continuous)
          (delta.map collarLongitudeMap.continuous)).continuous⟩
    (by
      intro t
      apply Subtype.ext
      apply Prod.ext
      · norm_num
      · exact (circleLoopHomotopy
          (gamma.map collarLongitudeMap.continuous)
          (delta.map collarLongitudeMap.continuous)).apply_zero t)
    (by
      intro t
      apply Subtype.ext
      apply Prod.ext
      · norm_num
      · exact (circleLoopHomotopy
          (gamma.map collarLongitudeMap.continuous)
          (delta.map collarLongitudeMap.continuous)).apply_one t)

theorem collarLoopHomotopy_loop
    {a b : PeripheralCollar.CollarParameter}
    (gamma : Path a a) (delta : Path b b)
    (hwind : CircleWinding.windingReal
        (gamma.map collarLongitudeMap.continuous) =
      CircleWinding.windingReal
        (delta.map collarLongitudeMap.continuous))
    (s : unitInterval) :
    collarLoopHomotopy gamma delta (s, 1) =
      collarLoopHomotopy gamma delta (s, 0) := by
  apply Subtype.ext
  apply Prod.ext
  · change
      (1 - (s : ℝ)) * (gamma 1).1.1 + (s : ℝ) * (delta 1).1.1 =
        (1 - (s : ℝ)) * (gamma 0).1.1 +
          (s : ℝ) * (delta 0).1.1
    rw [gamma.target, gamma.source, delta.target, delta.source]
  · exact circleLoopHomotopy_loop
      (gamma.map collarLongitudeMap.continuous)
      (delta.map collarLongitudeMap.continuous) hwind s

def collarFiberMap :
    C(PeripheralCollar.CollarParameter, RadialMilnor.Fiber) :=
  ⟨PeripheralCollar.collarFiber, PeripheralCollar.collarFiber_continuous⟩

def collarCoreMap :
    C(PeripheralCollar.CollarParameter, RadialCore.Core) :=
  (FiberAction.fiberToCore).comp collarFiberMap

def collarCoreLoopHomotopy
    {a b : PeripheralCollar.CollarParameter}
    (gamma : Path a a) (delta : Path b b) :
    ((gamma.map collarCoreMap.continuous :
        Path (collarCoreMap a) (collarCoreMap a)) :
      C(unitInterval, RadialCore.Core)).Homotopy
        (delta.map collarCoreMap.continuous) :=
  ((ContinuousMap.Homotopy.refl collarCoreMap).comp
    (collarLoopHomotopy gamma delta)).cast (by rfl) (by rfl)

theorem collarCoreLoopHomotopy_loop
    {a b : PeripheralCollar.CollarParameter}
    (gamma : Path a a) (delta : Path b b)
    (hwind : CircleWinding.windingReal
        (gamma.map collarLongitudeMap.continuous) =
      CircleWinding.windingReal
        (delta.map collarLongitudeMap.continuous))
    (s : unitInterval) :
    collarCoreLoopHomotopy gamma delta (s, 1) =
      collarCoreLoopHomotopy gamma delta (s, 0) := by
  have h := congrArg collarCoreMap
    (collarLoopHomotopy_loop gamma delta hwind s)
  simpa [collarCoreLoopHomotopy] using h

theorem pathTransFamily_continuous
    {X : Type*} [TopologicalSpace X]
    {a b c : unitInterval → X}
    (P : ∀ s, Path (a s) (b s)) (Q : ∀ s, Path (b s) (c s))
    (hP : Continuous (fun x : unitInterval × unitInterval => P x.1 x.2))
    (hQ : Continuous (fun x : unitInterval × unitInterval => Q x.1 x.2)) :
    Continuous (fun x : unitInterval × unitInterval =>
      (P x.1).trans (Q x.1) x.2) := by
  change Continuous (fun x : unitInterval × unitInterval =>
    if (x.2 : ℝ) ≤ 1 / 2 then
      (P x.1).extend (2 * (x.2 : ℝ))
    else
      (Q x.1).extend (2 * (x.2 : ℝ) - 1))
  have hP' : Continuous (fun z :
      (unitInterval × unitInterval) × unitInterval => P z.1.1 z.2) :=
    hP.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hQ' : Continuous (fun z :
      (unitInterval × unitInterval) × unitInterval => Q z.1.1 z.2) :=
    hQ.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hleft : Continuous (fun x : unitInterval × unitInterval =>
      (P x.1).extend (2 * (x.2 : ℝ))) :=
    Continuous.IccExtend hP' (by fun_prop)
  have hright : Continuous (fun x : unitInterval × unitInterval =>
      (Q x.1).extend (2 * (x.2 : ℝ) - 1)) :=
    Continuous.IccExtend hQ' (by fun_prop)
  exact continuous_if_le (by fun_prop) continuous_const
    hleft.continuousOn hright.continuousOn (by
      intro x hx
      have ht : (x.2 : ℝ) = 1 / 2 := by simpa using hx
      rw [ht]
      norm_num)

theorem pathTrans_property
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (P : Path x y) (Q : Path y z) (property : X → Prop)
    (hP : ∀ t, property (P t)) (hQ : ∀ t, property (Q t))
    (t : unitInterval) : property (P.trans Q t) := by
  rw [Path.trans_apply]
  split_ifs
  · exact hP _
  · exact hQ _

def evenSpherePath (k : Fin 6) (s : unitInterval) :
    Path (PeripheralBridge.evenSphere k s 0)
      (PeripheralBridge.oddSphere k s 0) where
  toFun := PeripheralBridge.evenSphere k s
  continuous_toFun := by
    have hpair : Continuous (fun u : unitInterval => (s, u)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using
      (PeripheralBridge.evenSphere_continuous k).comp hpair
  source' := rfl
  target' := PeripheralBridge.evenSphere_one_eq_oddSphere_zero k s

def oddSpherePath (k : Fin 6) (s : unitInterval) :
    Path (PeripheralBridge.oddSphere k s 0)
      (PeripheralBridge.evenSphere (PeripheralBridge.nextCycle k) s 0) where
  toFun := PeripheralBridge.oddSphere k s
  continuous_toFun := by
    have hpair : Continuous (fun u : unitInterval => (s, u)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using
      (PeripheralBridge.oddSphere_continuous k).comp hpair
  source' := rfl
  target' := PeripheralBridge.oddSphere_one_eq_evenSphere_next_zero k s

theorem evenSpherePath_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval =>
      evenSpherePath k x.1 x.2) :=
  PeripheralBridge.evenSphere_continuous k

theorem oddSpherePath_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval =>
      oddSpherePath k x.1 x.2) :=
  PeripheralBridge.oddSphere_continuous k

def pairSpherePath (k : Fin 6) (s : unitInterval) :
    Path (PeripheralBridge.evenSphere k s 0)
      (PeripheralBridge.evenSphere (PeripheralBridge.nextCycle k) s 0) :=
  (evenSpherePath k s).trans ((oddSpherePath k s).cast rfl rfl)

theorem pairSpherePath_continuous (k : Fin 6) :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePath k x.1 x.2) :=
  pathTransFamily_continuous (evenSpherePath k)
    (fun s => (oddSpherePath k s).cast rfl rfl)
    (evenSpherePath_continuous k) (oddSpherePath_continuous k)

def pairSpherePathZero (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 0 s 0)
      (PeripheralBridge.evenSphere 1 s 0) :=
  (pairSpherePath 0 s).cast rfl (by rw [PeripheralBridge.nextCycle_zero])

def pairSpherePathOne (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 1 s 0)
      (PeripheralBridge.evenSphere 2 s 0) :=
  (pairSpherePath 1 s).cast rfl (by rw [PeripheralBridge.nextCycle_one])

def pairSpherePathTwo (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 2 s 0)
      (PeripheralBridge.evenSphere 3 s 0) :=
  (pairSpherePath 2 s).cast rfl (by rw [PeripheralBridge.nextCycle_two])

def pairSpherePathThree (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 3 s 0)
      (PeripheralBridge.evenSphere 4 s 0) :=
  (pairSpherePath 3 s).cast rfl (by rw [PeripheralBridge.nextCycle_three])

def pairSpherePathFour (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 4 s 0)
      (PeripheralBridge.evenSphere 5 s 0) :=
  (pairSpherePath 4 s).cast rfl (by rw [PeripheralBridge.nextCycle_four])

def pairSpherePathFive (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 5 s 0)
      (PeripheralBridge.evenSphere 0 s 0) :=
  (pairSpherePath 5 s).cast rfl (by rw [PeripheralBridge.nextCycle_five])

theorem pairSpherePathZero_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePathZero x.1 x.2) := pairSpherePath_continuous 0

theorem pairSpherePathOne_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePathOne x.1 x.2) := pairSpherePath_continuous 1

theorem pairSpherePathTwo_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePathTwo x.1 x.2) := pairSpherePath_continuous 2

theorem pairSpherePathThree_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePathThree x.1 x.2) := pairSpherePath_continuous 3

theorem pairSpherePathFour_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePathFour x.1 x.2) := pairSpherePath_continuous 4

theorem pairSpherePathFive_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      pairSpherePathFive x.1 x.2) := pairSpherePath_continuous 5

def boundarySpherePath (s : unitInterval) :
    Path (PeripheralBridge.evenSphere 0 s 0)
      (PeripheralBridge.evenSphere 0 s 0) :=
  (pairSpherePathZero s).trans
    ((pairSpherePathOne s).trans
      ((pairSpherePathTwo s).trans
        ((pairSpherePathThree s).trans
          ((pairSpherePathFour s).trans (pairSpherePathFive s)))))

theorem boundarySpherePath_continuous :
    Continuous (fun x : unitInterval × unitInterval =>
      boundarySpherePath x.1 x.2) := by
  have h45 := pathTransFamily_continuous pairSpherePathFour
    pairSpherePathFive pairSpherePathFour_continuous
    pairSpherePathFive_continuous
  have h345 := pathTransFamily_continuous pairSpherePathThree
    (fun s => (pairSpherePathFour s).trans (pairSpherePathFive s))
    pairSpherePathThree_continuous h45
  have h2345 := pathTransFamily_continuous pairSpherePathTwo
    (fun s => (pairSpherePathThree s).trans
      ((pairSpherePathFour s).trans (pairSpherePathFive s)))
    pairSpherePathTwo_continuous h345
  have h12345 := pathTransFamily_continuous pairSpherePathOne
    (fun s => (pairSpherePathTwo s).trans
      ((pairSpherePathThree s).trans
        ((pairSpherePathFour s).trans (pairSpherePathFive s))))
    pairSpherePathOne_continuous h2345
  exact pathTransFamily_continuous pairSpherePathZero
    (fun s => (pairSpherePathOne s).trans
      ((pairSpherePathTwo s).trans
        ((pairSpherePathThree s).trans
          ((pairSpherePathFour s).trans (pairSpherePathFive s)))))
    pairSpherePathZero_continuous h12345

theorem evenSpherePath_zero_polynomial (k : Fin 6) (t : unitInterval) :
    Milnor.polynomial (evenSpherePath k 0 t) = 0 := by
  have hradial :
      RadialMilnor.polynomial (PeripheralBridge.evenSphere k 0 t) = 0 := by
    rw [PeripheralBridge.polynomial_evenSphere]
    norm_num
  have hold : Milnor.polynomial (PeripheralBridge.evenSphere k 0 t) = 0 :=
    (Milnor.polynomial_zero_iff_range _).2
      ((RadialMilnor.polynomial_zero_iff_range _).1 hradial)
  have hvalue : evenSpherePath k 0 t =
      PeripheralBridge.evenSphere k 0 t := rfl
  rw [hvalue]
  exact hold

theorem oddSpherePath_zero_polynomial (k : Fin 6) (t : unitInterval) :
    Milnor.polynomial (oddSpherePath k 0 t) = 0 := by
  have hradial :
      RadialMilnor.polynomial (PeripheralBridge.oddSphere k 0 t) = 0 := by
    rw [PeripheralBridge.polynomial_oddSphere]
    norm_num
  have hold : Milnor.polynomial (PeripheralBridge.oddSphere k 0 t) = 0 :=
    (Milnor.polynomial_zero_iff_range _).2
      ((RadialMilnor.polynomial_zero_iff_range _).1 hradial)
  have hvalue : oddSpherePath k 0 t =
      PeripheralBridge.oddSphere k 0 t := rfl
  rw [hvalue]
  exact hold

theorem pairSpherePath_zero_polynomial (k : Fin 6) (t : unitInterval) :
    Milnor.polynomial (pairSpherePath k 0 t) = 0 := by
  exact pathTrans_property (evenSpherePath k 0)
    ((oddSpherePath k 0).cast rfl rfl)
    (fun q => Milnor.polynomial q = 0)
    (evenSpherePath_zero_polynomial k)
    (oddSpherePath_zero_polynomial k) t

theorem boundarySpherePath_zero_polynomial (t : unitInterval) :
    Milnor.polynomial (boundarySpherePath 0 t) = 0 := by
  let property : Milnor.CSphere → Prop := fun q => Milnor.polynomial q = 0
  have hpair : ∀ k : Fin 6, ∀ u : unitInterval,
      Milnor.polynomial (pairSpherePath k 0 u) = 0 :=
    pairSpherePath_zero_polynomial
  have h45 : ∀ u : unitInterval, property
      ((pairSpherePathFour 0).trans (pairSpherePathFive 0) u) :=
    fun u => pathTrans_property (pairSpherePathFour 0)
      (pairSpherePathFive 0) property (hpair 4) (hpair 5) u
  have h345 : ∀ u : unitInterval, property
      ((pairSpherePathThree 0).trans
        ((pairSpherePathFour 0).trans (pairSpherePathFive 0)) u) :=
    fun u => pathTrans_property (pairSpherePathThree 0)
      ((pairSpherePathFour 0).trans (pairSpherePathFive 0)) property
      (hpair 3) h45 u
  have h2345 : ∀ u : unitInterval, property
      ((pairSpherePathTwo 0).trans
        ((pairSpherePathThree 0).trans
          ((pairSpherePathFour 0).trans (pairSpherePathFive 0))) u) :=
    fun u => pathTrans_property (pairSpherePathTwo 0)
      ((pairSpherePathThree 0).trans
        ((pairSpherePathFour 0).trans (pairSpherePathFive 0))) property
      (hpair 2) h345 u
  have h12345 : ∀ u : unitInterval, property
      ((pairSpherePathOne 0).trans
        ((pairSpherePathTwo 0).trans
          ((pairSpherePathThree 0).trans
            ((pairSpherePathFour 0).trans (pairSpherePathFive 0)))) u) :=
    fun u => pathTrans_property (pairSpherePathOne 0)
      ((pairSpherePathTwo 0).trans
        ((pairSpherePathThree 0).trans
          ((pairSpherePathFour 0).trans (pairSpherePathFive 0)))) property
      (hpair 1) h2345 u
  exact pathTrans_property (pairSpherePathZero 0)
    ((pairSpherePathOne 0).trans
      ((pairSpherePathTwo 0).trans
        ((pairSpherePathThree 0).trans
          ((pairSpherePathFour 0).trans (pairSpherePathFive 0))))) property
    (hpair 0) h12345 t

theorem boundarySpherePath_zero_mem_localTube (t : unitInterval) :
    boundarySpherePath 0 t ∈ PeripheralCollar.LocalTubeSphere := by
  let q : Binding :=
    ⟨boundarySpherePath 0 t, boundarySpherePath_zero_polynomial t⟩
  have hmem := PeripheralCollar.bindingPoint_mem_localTubeSphere
    (bindingParameter q)
  rw [bindingPoint_bindingParameter] at hmem
  exact hmem

def PositiveLevel := {s : unitInterval // 0 < (s : ℝ)}

instance : TopologicalSpace PositiveLevel := by
  unfold PositiveLevel
  infer_instance

def onePositiveLevel : PositiveLevel := ⟨1, by norm_num⟩

theorem evenSpherePath_fiber_property (k : Fin 6) (s : PositiveLevel)
    (t : unitInterval) :
    0 < (RadialMilnor.polynomial (evenSpherePath k s.1 t)).re ∧
      (RadialMilnor.polynomial (evenSpherePath k s.1 t)).im = 0 := by
  have hvalue : evenSpherePath k s.1 t =
      PeripheralBridge.evenSphere k s.1 t := rfl
  rw [hvalue, PeripheralBridge.polynomial_evenSphere]
  constructor
  · change 0 < PeripheralBridge.unbalanceFactor
        (PeripheralBridge.evenBalancedSphere k s.1 t) ^ 2 * (s.1 : ℝ)
    exact mul_pos
      (sq_pos_of_pos (PeripheralBridge.unbalanceFactor_pos _)) s.2
  · norm_num [pow_two, Complex.mul_im]

theorem oddSpherePath_fiber_property (k : Fin 6) (s : PositiveLevel)
    (t : unitInterval) :
    0 < (RadialMilnor.polynomial (oddSpherePath k s.1 t)).re ∧
      (RadialMilnor.polynomial (oddSpherePath k s.1 t)).im = 0 := by
  have hvalue : oddSpherePath k s.1 t =
      PeripheralBridge.oddSphere k s.1 t := rfl
  rw [hvalue, PeripheralBridge.polynomial_oddSphere]
  constructor
  · change 0 < PeripheralBridge.unbalanceFactor
        (PeripheralBridge.oddBalancedSphere k s.1 t) ^ 2 * (s.1 : ℝ)
    exact mul_pos
      (sq_pos_of_pos (PeripheralBridge.unbalanceFactor_pos _)) s.2
  · norm_num [pow_two, Complex.mul_im]

theorem pairSpherePath_fiber_property (k : Fin 6) (s : PositiveLevel)
    (t : unitInterval) :
    0 < (RadialMilnor.polynomial (pairSpherePath k s.1 t)).re ∧
      (RadialMilnor.polynomial (pairSpherePath k s.1 t)).im = 0 := by
  exact pathTrans_property (evenSpherePath k s.1)
    ((oddSpherePath k s.1).cast rfl rfl)
    (fun q => 0 < (RadialMilnor.polynomial q).re ∧
      (RadialMilnor.polynomial q).im = 0)
    (evenSpherePath_fiber_property k s)
    (oddSpherePath_fiber_property k s) t

theorem boundarySpherePath_fiber_property (s : PositiveLevel)
    (t : unitInterval) :
    0 < (RadialMilnor.polynomial (boundarySpherePath s.1 t)).re ∧
      (RadialMilnor.polynomial (boundarySpherePath s.1 t)).im = 0 := by
  let property : Milnor.CSphere → Prop := fun q =>
    0 < (RadialMilnor.polynomial q).re ∧
      (RadialMilnor.polynomial q).im = 0
  have hpair : ∀ k : Fin 6, ∀ u : unitInterval,
      property (pairSpherePath k s.1 u) :=
    fun k u => pairSpherePath_fiber_property k s u
  have h45 : ∀ u : unitInterval, property
      ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1) u) :=
    fun u => pathTrans_property (pairSpherePathFour s.1)
      (pairSpherePathFive s.1) property (hpair 4) (hpair 5) u
  have h345 : ∀ u : unitInterval, property
      ((pairSpherePathThree s.1).trans
        ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1)) u) :=
    fun u => pathTrans_property (pairSpherePathThree s.1)
      ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1)) property
      (hpair 3) h45 u
  have h2345 : ∀ u : unitInterval, property
      ((pairSpherePathTwo s.1).trans
        ((pairSpherePathThree s.1).trans
          ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1))) u) :=
    fun u => pathTrans_property (pairSpherePathTwo s.1)
      ((pairSpherePathThree s.1).trans
        ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1))) property
      (hpair 2) h345 u
  have h12345 : ∀ u : unitInterval, property
      ((pairSpherePathOne s.1).trans
        ((pairSpherePathTwo s.1).trans
          ((pairSpherePathThree s.1).trans
            ((pairSpherePathFour s.1).trans
              (pairSpherePathFive s.1)))) u) :=
    fun u => pathTrans_property (pairSpherePathOne s.1)
      ((pairSpherePathTwo s.1).trans
        ((pairSpherePathThree s.1).trans
          ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1)))) property
      (hpair 1) h2345 u
  exact pathTrans_property (pairSpherePathZero s.1)
    ((pairSpherePathOne s.1).trans
      ((pairSpherePathTwo s.1).trans
        ((pairSpherePathThree s.1).trans
          ((pairSpherePathFour s.1).trans (pairSpherePathFive s.1))))) property
    (hpair 0) h12345 t

def boundaryFiberPoint (s : PositiveLevel) (t : unitInterval) :
    RadialMilnor.Fiber :=
  ⟨boundarySpherePath s.1 t, boundarySpherePath_fiber_property s t⟩

@[simp] theorem boundaryFiberPoint_val (s : PositiveLevel)
    (t : unitInterval) :
    (boundaryFiberPoint s t).1 = boundarySpherePath s.1 t :=
  rfl

theorem boundaryFiberPoint_continuous :
    Continuous (fun x : PositiveLevel × unitInterval =>
      boundaryFiberPoint x.1 x.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : PositiveLevel × unitInterval =>
    boundarySpherePath x.1.1 x.2)
  have hlevel : Continuous (fun s : PositiveLevel => s.1) :=
    continuous_subtype_val
  have hpair : Continuous (fun x : PositiveLevel × unitInterval =>
      (x.1.1, x.2)) :=
    (hlevel.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using
    boundarySpherePath_continuous.comp hpair

def boundaryFiberBase (s : PositiveLevel) : RadialMilnor.Fiber :=
  boundaryFiberPoint s 0

def boundaryFiberPath (s : PositiveLevel) :
    Path (boundaryFiberBase s) (boundaryFiberBase s) where
  toFun := boundaryFiberPoint s
  continuous_toFun := by
    have hpair : Continuous (fun t : unitInterval => (s, t)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using
      boundaryFiberPoint_continuous.comp hpair
  source' := rfl
  target' := by
    apply Subtype.ext
    change boundarySpherePath s.1 1 = boundarySpherePath s.1 0
    exact (boundarySpherePath s.1).target.trans
      (boundarySpherePath s.1).source.symm

theorem boundaryFiberPath_continuous :
    Continuous (fun x : PositiveLevel × unitInterval =>
      boundaryFiberPath x.1 x.2) := by
  change Continuous (fun x : PositiveLevel × unitInterval =>
    boundaryFiberPoint x.1 x.2)
  exact boundaryFiberPoint_continuous

def levelInterpolation (s : PositiveLevel) (a : unitInterval) :
    PositiveLevel := by
  let value : ℝ := (1 - (a : ℝ)) * (s.1 : ℝ) + (a : ℝ)
  have hpos : 0 < value := by
    dsimp [value]
    simpa only [mul_one] using
      (convexCombination_pos (a := (s.1 : ℝ)) (b := 1)
        (s := (a : ℝ)) s.2 (by norm_num) a.2.1 a.2.2)
  have hle : value ≤ 1 := by
    have hmul : (1 - (a : ℝ)) * (s.1 : ℝ) ≤
        (1 - (a : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left s.1.2.2 (sub_nonneg.mpr a.2.2)
    dsimp [value]
    nlinarith
  exact ⟨⟨value, hpos.le, hle⟩, hpos⟩

theorem levelInterpolation_continuous (s : PositiveLevel) :
    Continuous (levelInterpolation s) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem levelInterpolation_zero (s : PositiveLevel) :
    levelInterpolation s 0 = s := by
  apply Subtype.ext
  apply Subtype.ext
  simp [levelInterpolation]

@[simp] theorem levelInterpolation_one (s : PositiveLevel) :
    levelInterpolation s 1 = onePositiveLevel := by
  apply Subtype.ext
  apply Subtype.ext
  simp [levelInterpolation, onePositiveLevel]

def boundaryFiberLevelHomotopy (s : PositiveLevel) :
    (boundaryFiberPath s : C(unitInterval, RadialMilnor.Fiber)).Homotopy
      (boundaryFiberPath onePositiveLevel) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval =>
        boundaryFiberPoint (levelInterpolation s p.1) p.2, by
      have hpair : Continuous (fun p : unitInterval × unitInterval =>
          (levelInterpolation s p.1, p.2)) :=
        ((levelInterpolation_continuous s).comp continuous_fst).prodMk
          continuous_snd
      simpa only [Function.comp_def] using
        boundaryFiberPoint_continuous.comp hpair⟩
    (by
      intro t
      change boundaryFiberPoint (levelInterpolation s 0) t =
        boundaryFiberPoint s t
      rw [levelInterpolation_zero])
    (by
      intro t
      change boundaryFiberPoint (levelInterpolation s 1) t =
        boundaryFiberPoint onePositiveLevel t
      rw [levelInterpolation_one])

theorem boundaryFiberLevelHomotopy_loop (s : PositiveLevel)
    (a : unitInterval) :
    boundaryFiberLevelHomotopy s (a, 1) =
      boundaryFiberLevelHomotopy s (a, 0) := by
  change boundaryFiberPoint (levelInterpolation s a) 1 =
    boundaryFiberPoint (levelInterpolation s a) 0
  apply Subtype.ext
  exact (boundarySpherePath (levelInterpolation s a).1).target.trans
    (boundarySpherePath (levelInterpolation s a).1).source.symm

def boundaryCoreLevelHomotopy (s : PositiveLevel) :
    (((boundaryFiberPath s).map FiberAction.fiberToCore.continuous :
        Path (FiberAction.fiberToCore (boundaryFiberBase s))
          (FiberAction.fiberToCore (boundaryFiberBase s))) :
      C(unitInterval, RadialCore.Core)).Homotopy
        ((boundaryFiberPath onePositiveLevel).map
          FiberAction.fiberToCore.continuous) :=
  ((ContinuousMap.Homotopy.refl FiberAction.fiberToCore).comp
    (boundaryFiberLevelHomotopy s)).cast (by rfl) (by rfl)

theorem boundaryCoreLevelHomotopy_loop (s : PositiveLevel)
    (a : unitInterval) :
    boundaryCoreLevelHomotopy s (a, 1) =
      boundaryCoreLevelHomotopy s (a, 0) := by
  have h := congrArg FiberAction.fiberToCore
    (boundaryFiberLevelHomotopy_loop s a)
  simpa [boundaryCoreLevelHomotopy] using h

theorem eventually_forall_parameter_of_compact
    {X : Type*} [TopologicalSpace X]
    (F : unitInterval × unitInterval → X) (hF : Continuous F)
    (U : Set X) (hU : IsOpen U)
    (hzero : ∀ t : unitInterval, F (0, t) ∈ U) :
    ∀ᶠ s : unitInterval in 𝓝 0, ∀ t : unitInterval, F (s, t) ∈ U := by
  have hcompact : IsCompact (Set.univ : Set unitInterval) := isCompact_univ
  simpa only [Set.mem_univ, forall_const] using
    hcompact.eventually_forall_of_forall_eventually (x₀ := (0 : unitInterval))
      (K := Set.univ) (P := fun s t => F (s, t) ∈ U) (by
        intro t _
        exact hF.continuousAt (hU.mem_nhds (hzero t)))

theorem exists_positiveLevel_with_lower_interval
    {P : unitInterval → Prop}
    (hP : ∀ᶠ s : unitInterval in 𝓝 0, P s) :
    ∃ s : PositiveLevel, ∀ a : unitInterval,
      (a : ℝ) ≤ (s.1 : ℝ) → P a := by
  change {s : unitInterval | P s} ∈ 𝓝 0 at hP
  rw [Metric.mem_nhds_iff] at hP
  obtain ⟨ε, hε, hball⟩ := hP
  let r : ℝ := min (ε / 2) (1 / 2)
  have hr0 : 0 < r := lt_min (half_pos hε) (by norm_num)
  have hr1 : r ≤ 1 := by
    exact (min_le_right (ε / 2) (1 / 2)).trans (by norm_num)
  let sI : unitInterval := ⟨r, hr0.le, hr1⟩
  let s : PositiveLevel := ⟨sI, hr0⟩
  refine ⟨s, ?_⟩
  intro a ha
  apply hball
  have har0 : 0 ≤ (a : ℝ) := a.2.1
  have hrε : r < ε := by
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hadist : dist a (0 : unitInterval) < ε := by
    rw [Subtype.dist_eq]
    change dist (a : ℝ) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg har0]
    exact lt_of_le_of_lt ha hrε
  simpa [Metric.mem_ball] using hadist

theorem image_boundarySpherePath_zero_mem_localTube
    (S : NegativeSymmetry) (t : unitInterval) :
    CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath 0 t) ∈
      PeripheralCollar.LocalTubeSphere := by
  let q : Binding :=
    ⟨boundarySpherePath 0 t, boundarySpherePath_zero_polynomial t⟩
  let qimage : Binding := bindingMap S q
  have hmem := PeripheralCollar.bindingPoint_mem_localTubeSphere
    (bindingParameter qimage)
  rw [bindingPoint_bindingParameter] at hmem
  exact hmem

theorem exists_smallBoundaryLevel (S : NegativeSymmetry) :
    ∃ s : PositiveLevel,
      (∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
        ∀ t : unitInterval,
          boundarySpherePath a t ∈ PeripheralCollar.LocalTubeSphere) ∧
      (∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
        ∀ t : unitInterval,
          CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath a t) ∈
            PeripheralCollar.LocalTubeSphere) := by
  have hsource : ∀ᶠ a : unitInterval in 𝓝 0,
      ∀ t : unitInterval,
        boundarySpherePath a t ∈ PeripheralCollar.LocalTubeSphere :=
    eventually_forall_parameter_of_compact
      (fun p : unitInterval × unitInterval => boundarySpherePath p.1 p.2)
      boundarySpherePath_continuous PeripheralCollar.LocalTubeSphere
      PeripheralCollar.localTubeSphere_isOpen
      boundarySpherePath_zero_mem_localTube
  have himageContinuous : Continuous
      (fun p : unitInterval × unitInterval =>
        CompactifiedSymmetry.sphereHomeomorph S
          (boundarySpherePath p.1 p.2)) :=
    (CompactifiedSymmetry.sphereHomeomorph S).continuous.comp
      boundarySpherePath_continuous
  have himage : ∀ᶠ a : unitInterval in 𝓝 0,
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere :=
    eventually_forall_parameter_of_compact
      (fun p : unitInterval × unitInterval =>
        CompactifiedSymmetry.sphereHomeomorph S
          (boundarySpherePath p.1 p.2))
      himageContinuous PeripheralCollar.LocalTubeSphere
      PeripheralCollar.localTubeSphere_isOpen
      (image_boundarySpherePath_zero_mem_localTube S)
  obtain ⟨s, hs⟩ := exists_positiveLevel_with_lower_interval
    (hsource.and himage)
  exact ⟨s, fun a ha t => (hs a ha).1 t,
    fun a ha t => (hs a ha).2 t⟩

def torusRegionOfLocalSphere (q : Milnor.CSphere)
    (hq : q ∈ PeripheralCollar.LocalTubeSphere) : PeripheralTube.TorusRegion :=
  ⟨q, by
    rcases hq with ⟨x, _, hx⟩
    rw [← hx]
    exact x.2⟩

@[simp] theorem torusRegionOfLocalSphere_val (q : Milnor.CSphere)
    (hq : q ∈ PeripheralCollar.LocalTubeSphere) :
    (torusRegionOfLocalSphere q hq).1 = q :=
  rfl

theorem torusRegionOfLocalSphere_mem (q : Milnor.CSphere)
    (hq : q ∈ PeripheralCollar.LocalTubeSphere) :
    torusRegionOfLocalSphere q hq ∈ PeripheralCollar.LocalTubeSet := by
  rcases hq with ⟨x, hx, hval⟩
  have heq : torusRegionOfLocalSphere q ⟨x, hx, hval⟩ = x := by
    apply Subtype.ext
    exact hval.symm
  rw [heq]
  exact hx

theorem torusRegionOfLocalSphere_continuous
    {Y : Type*} [TopologicalSpace Y]
    (f : Y → Milnor.CSphere) (hf : Continuous f)
    (hlocal : ∀ y, f y ∈ PeripheralCollar.LocalTubeSphere) :
    Continuous (fun y => torusRegionOfLocalSphere (f y) (hlocal y)) := by
  apply Continuous.subtype_mk
  exact hf

theorem longitude_continuous : Continuous PeripheralTube.longitude :=
  PeripheralTube.zPhase_continuous.mul PeripheralTube.wPhase_continuous.inv

def localLongitudePath {q : Milnor.CSphere} (gamma : Path q q)
    (hlocal : ∀ t : unitInterval,
      gamma t ∈ PeripheralCollar.LocalTubeSphere) :
    Path
      (PeripheralTube.longitude
        (torusRegionOfLocalSphere (gamma 0) (hlocal 0)))
      (PeripheralTube.longitude
        (torusRegionOfLocalSphere (gamma 0) (hlocal 0))) where
  toFun t := PeripheralTube.longitude
    (torusRegionOfLocalSphere (gamma t) (hlocal t))
  continuous_toFun := by
    exact longitude_continuous.comp
      (torusRegionOfLocalSphere_continuous gamma gamma.continuous hlocal)
  source' := rfl
  target' := by
    apply congrArg PeripheralTube.longitude
    apply Subtype.ext
    exact gamma.target.trans gamma.source.symm

def sphereFamilyPath
    {X : Type*} [TopologicalSpace X]
    (F : unitInterval × unitInterval → X) (hF : Continuous F)
    (hloop : ∀ a : unitInterval, F (a, 1) = F (a, 0))
    (a : unitInterval) : Path (F (a, 0)) (F (a, 0)) where
  toFun t := F (a, t)
  continuous_toFun := by
    have hpair : Continuous (fun t : unitInterval => (a, t)) :=
      continuous_const.prodMk continuous_id
    exact hF.comp hpair
  source' := rfl
  target' := hloop a

def localLongitudeFamilyHomotopy
    (F : unitInterval × unitInterval → Milnor.CSphere)
    (hF : Continuous F)
    (hloop : ∀ a : unitInterval, F (a, 1) = F (a, 0))
    (hlocal : ∀ p, F p ∈ PeripheralCollar.LocalTubeSphere) :
    (localLongitudePath (sphereFamilyPath F hF hloop 0)
      (fun t => hlocal (0, t)) : C(unitInterval, Circle)).Homotopy
    (localLongitudePath (sphereFamilyPath F hF hloop 1)
      (fun t => hlocal (1, t))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval => PeripheralTube.longitude
        (torusRegionOfLocalSphere (F p) (hlocal p)), by
      exact longitude_continuous.comp
        (torusRegionOfLocalSphere_continuous F hF hlocal)⟩
    (by intro t; rfl)
    (by intro t; rfl)

theorem localLongitudeFamilyHomotopy_loop
    (F : unitInterval × unitInterval → Milnor.CSphere)
    (hF : Continuous F)
    (hloop : ∀ a : unitInterval, F (a, 1) = F (a, 0))
    (hlocal : ∀ p, F p ∈ PeripheralCollar.LocalTubeSphere)
    (a : unitInterval) :
    localLongitudeFamilyHomotopy F hF hloop hlocal (a, 1) =
      localLongitudeFamilyHomotopy F hF hloop hlocal (a, 0) := by
  apply congrArg PeripheralTube.longitude
  apply Subtype.ext
  exact hloop a

theorem windingReal_localLongitudeFamily
    (F : unitInterval × unitInterval → Milnor.CSphere)
    (hF : Continuous F)
    (hloop : ∀ a : unitInterval, F (a, 1) = F (a, 0))
    (hlocal : ∀ p, F p ∈ PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (localLongitudePath (sphereFamilyPath F hF hloop 0)
          (fun t => hlocal (0, t))) =
      CircleWinding.windingReal
        (localLongitudePath (sphereFamilyPath F hF hloop 1)
          (fun t => hlocal (1, t))) :=
  CircleWinding.windingReal_eq_of_freeHomotopy
    (localLongitudeFamilyHomotopy F hF hloop hlocal)
    (localLongitudeFamilyHomotopy_loop F hF hloop hlocal)

def lowerLevel (s : PositiveLevel) (a : unitInterval) : unitInterval :=
  ⟨(a : ℝ) * (s.1 : ℝ),
    mul_nonneg a.2.1 s.1.2.1, by
      have hmul := mul_le_mul a.2.2 s.1.2.2 s.1.2.1
        (by norm_num : (0 : ℝ) ≤ 1)
      norm_num at hmul ⊢
      exact hmul⟩

theorem lowerLevel_continuous (s : PositiveLevel) :
    Continuous (lowerLevel s) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem lowerLevel_zero (s : PositiveLevel) : lowerLevel s 0 = 0 := by
  apply Subtype.ext
  simp [lowerLevel]

@[simp] theorem lowerLevel_one (s : PositiveLevel) : lowerLevel s 1 = s.1 := by
  apply Subtype.ext
  simp [lowerLevel]

theorem lowerLevel_le (s : PositiveLevel) (a : unitInterval) :
    (lowerLevel s a : ℝ) ≤ (s.1 : ℝ) := by
  have hnonneg : 0 ≤ (1 - (a : ℝ)) * (s.1 : ℝ) :=
    mul_nonneg (sub_nonneg.mpr a.2.2) s.1.2.1
  change (a : ℝ) * (s.1 : ℝ) ≤ (s.1 : ℝ)
  nlinarith

def sourceBoundaryFamily (s : PositiveLevel) :
    unitInterval × unitInterval → Milnor.CSphere :=
  fun p => boundarySpherePath (lowerLevel s p.1) p.2

theorem sourceBoundaryFamily_continuous (s : PositiveLevel) :
    Continuous (sourceBoundaryFamily s) := by
  change Continuous (fun p : unitInterval × unitInterval =>
    boundarySpherePath (lowerLevel s p.1) p.2)
  have hpair : Continuous (fun p : unitInterval × unitInterval =>
      (lowerLevel s p.1, p.2)) :=
    ((lowerLevel_continuous s).comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using
    boundarySpherePath_continuous.comp hpair

theorem sourceBoundaryFamily_loop (s : PositiveLevel) (a : unitInterval) :
    sourceBoundaryFamily s (a, 1) = sourceBoundaryFamily s (a, 0) :=
  (boundarySpherePath (lowerLevel s a)).target.trans
    (boundarySpherePath (lowerLevel s a)).source.symm

def imageBoundaryFamily (S : NegativeSymmetry) (s : PositiveLevel) :
    unitInterval × unitInterval → Milnor.CSphere :=
  fun p => CompactifiedSymmetry.sphereHomeomorph S
    (sourceBoundaryFamily s p)

theorem imageBoundaryFamily_continuous (S : NegativeSymmetry)
    (s : PositiveLevel) : Continuous (imageBoundaryFamily S s) :=
  (CompactifiedSymmetry.sphereHomeomorph S).continuous.comp
    (sourceBoundaryFamily_continuous s)

theorem imageBoundaryFamily_loop (S : NegativeSymmetry)
    (s : PositiveLevel) (a : unitInterval) :
    imageBoundaryFamily S s (a, 1) = imageBoundaryFamily S s (a, 0) :=
  congrArg (CompactifiedSymmetry.sphereHomeomorph S)
    (sourceBoundaryFamily_loop s a)

theorem torusRegionOfLocalSphere_binding_eq (q : Binding)
    (hlocal : q.1 ∈ PeripheralCollar.LocalTubeSphere) :
    torusRegionOfLocalSphere q.1 hlocal =
      PeripheralCollar.BindingTorusPoint (bindingParameter q) := by
  apply Subtype.ext
  change q.1 = (bindingPoint (bindingParameter q)).1
  exact congrArg Subtype.val (bindingPoint_bindingParameter q).symm

theorem longitude_torusRegionOfLocalSphere_binding (q : Binding)
    (hlocal : q.1 ∈ PeripheralCollar.LocalTubeSphere) :
    PeripheralTube.longitude (torusRegionOfLocalSphere q.1 hlocal) =
      bindingParameter q := by
  rw [torusRegionOfLocalSphere_binding_eq q hlocal,
    PeripheralCollar.bindingTorusPoint_eq,
    PeripheralTube.longitude_torusPoint]
  rfl

def bindingPathOfZero {q : Milnor.CSphere} (gamma : Path q q)
    (hzero : ∀ t : unitInterval, Milnor.polynomial (gamma t) = 0) :
    Path (⟨gamma 0, hzero 0⟩ : Binding) ⟨gamma 0, hzero 0⟩ where
  toFun t := ⟨gamma t, hzero t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact gamma.continuous
  source' := rfl
  target' := by
    apply Subtype.ext
    exact gamma.target.trans gamma.source.symm

def bindingParameterPath {q : Milnor.CSphere} (gamma : Path q q)
    (hzero : ∀ t : unitInterval, Milnor.polynomial (gamma t) = 0) :
    Path
      (bindingParameter (⟨gamma 0, hzero 0⟩ : Binding))
      (bindingParameter (⟨gamma 0, hzero 0⟩ : Binding)) :=
  (bindingPathOfZero gamma hzero).map bindingParameter_continuous

theorem localLongitudePath_eq_bindingParameterPath
    {q : Milnor.CSphere} (gamma : Path q q)
    (hzero : ∀ t : unitInterval, Milnor.polynomial (gamma t) = 0)
    (hlocal : ∀ t : unitInterval,
      gamma t ∈ PeripheralCollar.LocalTubeSphere) :
    localLongitudePath gamma hlocal =
      (bindingParameterPath gamma hzero).cast
        (longitude_torusRegionOfLocalSphere_binding
          ⟨gamma 0, hzero 0⟩ (hlocal 0))
        (longitude_torusRegionOfLocalSphere_binding
          ⟨gamma 0, hzero 0⟩ (hlocal 0)) := by
  apply Path.ext
  funext t
  exact longitude_torusRegionOfLocalSphere_binding
    ⟨gamma t, hzero t⟩ (hlocal t)

theorem sourceBoundaryFamily_zero_polynomial (s : PositiveLevel)
    (t : unitInterval) :
    Milnor.polynomial (sourceBoundaryFamily s (0, t)) = 0 := by
  change Milnor.polynomial (boundarySpherePath (lowerLevel s 0) t) = 0
  rw [lowerLevel_zero]
  exact boundarySpherePath_zero_polynomial t

theorem imageBoundaryFamily_zero_polynomial (S : NegativeSymmetry)
    (s : PositiveLevel) (t : unitInterval) :
    Milnor.polynomial (imageBoundaryFamily S s (0, t)) = 0 := by
  apply (CompactifiedSymmetry.polynomial_zero_iff_image S _).2
  exact sourceBoundaryFamily_zero_polynomial s t

def sourceBindingParameterPath (s : PositiveLevel) : Path
    (bindingParameter
      (⟨sourceBoundaryFamily s (0, 0),
        sourceBoundaryFamily_zero_polynomial s 0⟩ : Binding))
    (bindingParameter
      (⟨sourceBoundaryFamily s (0, 0),
        sourceBoundaryFamily_zero_polynomial s 0⟩ : Binding)) :=
  bindingParameterPath
    (sphereFamilyPath (sourceBoundaryFamily s)
      (sourceBoundaryFamily_continuous s) (sourceBoundaryFamily_loop s) 0)
    (sourceBoundaryFamily_zero_polynomial s)

def imageBindingParameterPath (S : NegativeSymmetry) (s : PositiveLevel) : Path
    (bindingParameter
      (⟨imageBoundaryFamily S s (0, 0),
        imageBoundaryFamily_zero_polynomial S s 0⟩ : Binding))
    (bindingParameter
      (⟨imageBoundaryFamily S s (0, 0),
        imageBoundaryFamily_zero_polynomial S s 0⟩ : Binding)) :=
  bindingParameterPath
    (sphereFamilyPath (imageBoundaryFamily S s)
      (imageBoundaryFamily_continuous S s)
      (imageBoundaryFamily_loop S s) 0)
    (imageBoundaryFamily_zero_polynomial S s)

theorem bindingParameter_imageBoundaryFamily_zero
    (S : NegativeSymmetry) (s : PositiveLevel) (t : unitInterval) :
    bindingParameter
        (⟨imageBoundaryFamily S s (0, t),
          imageBoundaryFamily_zero_polynomial S s t⟩ : Binding) =
      bindingCircleMap S
        (bindingParameter
          (⟨sourceBoundaryFamily s (0, t),
            sourceBoundaryFamily_zero_polynomial s t⟩ : Binding)) := by
  let q : Binding :=
    ⟨sourceBoundaryFamily s (0, t),
      sourceBoundaryFamily_zero_polynomial s t⟩
  have himage :
      (⟨imageBoundaryFamily S s (0, t),
        imageBoundaryFamily_zero_polynomial S s t⟩ : Binding) =
        bindingMap S q := by
    apply Subtype.ext
    rfl
  rw [himage]
  simp only [bindingCircleMap, Homeomorph.trans_apply]
  change bindingParameter (bindingMap S q) =
    bindingParameter (bindingMap S (bindingPoint (bindingParameter q)))
  rw [bindingPoint_bindingParameter]

theorem imageBindingParameterPath_eq_mapped
    (S : NegativeSymmetry) (s : PositiveLevel) :
    imageBindingParameterPath S s =
      ((sourceBindingParameterPath s).map
        (bindingCircleMap S).continuous).cast
          (bindingParameter_imageBoundaryFamily_zero S s 0)
          (bindingParameter_imageBoundaryFamily_zero S s 0) := by
  apply Path.ext
  funext t
  exact bindingParameter_imageBoundaryFamily_zero S s t

def sourceLongitudeHomotopy (s : PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        boundarySpherePath a t ∈ PeripheralCollar.LocalTubeSphere) :=
  localLongitudeFamilyHomotopy (sourceBoundaryFamily s)
    (sourceBoundaryFamily_continuous s) (sourceBoundaryFamily_loop s)
    (fun p => hsource (lowerLevel s p.1) (lowerLevel_le s p.1) p.2)

def imageLongitudeHomotopy (S : NegativeSymmetry) (s : PositiveLevel)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :=
  localLongitudeFamilyHomotopy (imageBoundaryFamily S s)
    (imageBoundaryFamily_continuous S s) (imageBoundaryFamily_loop S s)
    (fun p => himage (lowerLevel s p.1) (lowerLevel_le s p.1) p.2)

theorem sourceLongitude_winding_zero_eq_one (s : PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        boundarySpherePath a t ∈ PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (sourceBoundaryFamily s)
            (sourceBoundaryFamily_continuous s)
            (sourceBoundaryFamily_loop s) 0)
          (fun t => hsource (lowerLevel s 0) (lowerLevel_le s 0) t)) =
      CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (sourceBoundaryFamily s)
            (sourceBoundaryFamily_continuous s)
            (sourceBoundaryFamily_loop s) 1)
          (fun t => hsource (lowerLevel s 1) (lowerLevel_le s 1) t)) :=
  windingReal_localLongitudeFamily (sourceBoundaryFamily s)
    (sourceBoundaryFamily_continuous s) (sourceBoundaryFamily_loop s)
    (fun p => hsource (lowerLevel s p.1) (lowerLevel_le s p.1) p.2)

theorem imageLongitude_winding_zero_eq_one
    (S : NegativeSymmetry) (s : PositiveLevel)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (imageBoundaryFamily S s)
            (imageBoundaryFamily_continuous S s)
            (imageBoundaryFamily_loop S s) 0)
          (fun t => himage (lowerLevel s 0) (lowerLevel_le s 0) t)) =
      CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (imageBoundaryFamily S s)
            (imageBoundaryFamily_continuous S s)
            (imageBoundaryFamily_loop S s) 1)
          (fun t => himage (lowerLevel s 1) (lowerLevel_le s 1) t)) :=
  windingReal_localLongitudeFamily (imageBoundaryFamily S s)
    (imageBoundaryFamily_continuous S s) (imageBoundaryFamily_loop S s)
    (fun p => himage (lowerLevel s p.1) (lowerLevel_le s p.1) p.2)

theorem sourceLongitude_zero_winding_eq_binding
    (s : PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        boundarySpherePath a t ∈ PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (sourceBoundaryFamily s)
            (sourceBoundaryFamily_continuous s)
            (sourceBoundaryFamily_loop s) 0)
          (fun t => hsource (lowerLevel s 0) (lowerLevel_le s 0) t)) =
      CircleWinding.windingReal (sourceBindingParameterPath s) := by
  let gamma := sphereFamilyPath (sourceBoundaryFamily s)
    (sourceBoundaryFamily_continuous s) (sourceBoundaryFamily_loop s) 0
  let hzero : ∀ t : unitInterval, Milnor.polynomial (gamma t) = 0 :=
    sourceBoundaryFamily_zero_polynomial s
  let hlocal : ∀ t : unitInterval,
      gamma t ∈ PeripheralCollar.LocalTubeSphere :=
    fun t => hsource (lowerLevel s 0) (lowerLevel_le s 0) t
  have heq := localLongitudePath_eq_bindingParameterPath gamma hzero hlocal
  rw [heq, CircleMapAlgebra.windingReal_cast]
  rfl

theorem imageLongitude_zero_winding_eq_binding
    (S : NegativeSymmetry) (s : PositiveLevel)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (imageBoundaryFamily S s)
            (imageBoundaryFamily_continuous S s)
            (imageBoundaryFamily_loop S s) 0)
          (fun t => himage (lowerLevel s 0) (lowerLevel_le s 0) t)) =
      CircleWinding.windingReal (imageBindingParameterPath S s) := by
  let gamma := sphereFamilyPath (imageBoundaryFamily S s)
    (imageBoundaryFamily_continuous S s) (imageBoundaryFamily_loop S s) 0
  let hzero : ∀ t : unitInterval, Milnor.polynomial (gamma t) = 0 :=
    imageBoundaryFamily_zero_polynomial S s
  let hlocal : ∀ t : unitInterval,
      gamma t ∈ PeripheralCollar.LocalTubeSphere :=
    fun t => himage (lowerLevel s 0) (lowerLevel_le s 0) t
  have heq := localLongitudePath_eq_bindingParameterPath gamma hzero hlocal
  rw [heq, CircleMapAlgebra.windingReal_cast]
  rfl

theorem imageBindingParameter_winding_eq_source
    (S : NegativeSymmetry) (s : PositiveLevel) :
    CircleWinding.windingReal (imageBindingParameterPath S s) =
      CircleWinding.windingReal (sourceBindingParameterPath s) := by
  rw [imageBindingParameterPath_eq_mapped,
    CircleMapAlgebra.windingReal_cast,
    windingReal_bindingCircleMap]

theorem ambientLongitude_winding_eq
    (S : NegativeSymmetry) (s : PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        boundarySpherePath a t ∈ PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S (boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (sourceBoundaryFamily s)
            (sourceBoundaryFamily_continuous s)
            (sourceBoundaryFamily_loop s) 1)
          (fun t => hsource (lowerLevel s 1) (lowerLevel_le s 1) t)) =
      CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (imageBoundaryFamily S s)
            (imageBoundaryFamily_continuous S s)
            (imageBoundaryFamily_loop S s) 1)
          (fun t => himage (lowerLevel s 1) (lowerLevel_le s 1) t)) := by
  calc
    _ = CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (sourceBoundaryFamily s)
            (sourceBoundaryFamily_continuous s)
            (sourceBoundaryFamily_loop s) 0)
          (fun t => hsource (lowerLevel s 0) (lowerLevel_le s 0) t)) :=
      (sourceLongitude_winding_zero_eq_one s hsource).symm
    _ = CircleWinding.windingReal (sourceBindingParameterPath s) :=
      sourceLongitude_zero_winding_eq_binding s hsource
    _ = CircleWinding.windingReal (imageBindingParameterPath S s) :=
      (imageBindingParameter_winding_eq_source S s).symm
    _ = CircleWinding.windingReal
        (localLongitudePath
          (sphereFamilyPath (imageBoundaryFamily S s)
            (imageBoundaryFamily_continuous S s)
            (imageBoundaryFamily_loop S s) 0)
          (fun t => himage (lowerLevel s 0) (lowerLevel_le s 0) t)) :=
      (imageLongitude_zero_winding_eq_binding S s himage).symm
    _ = _ := imageLongitude_winding_zero_eq_one S s himage

def rotateTorusCoordinates (s : ℝ) (x : PeripheralTube.TorusCoordinates) :
    PeripheralTube.TorusCoordinates :=
  (x.1, Circle.exp s * x.2.1, x.2.2)

theorem circleExp_pow (n : ℕ) (s : ℝ) :
    Circle.exp s ^ n = Circle.exp (n * s) := by
  apply Subtype.ext
  change Complex.exp (((s : ℝ) : ℂ) * Complex.I) ^ n =
    Complex.exp ((((n : ℝ) * s : ℝ) : ℂ) * Complex.I)
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem coordinateZPhase_rotateTorusCoordinates
    (s : ℝ) (x : PeripheralTube.TorusCoordinates) :
    PeripheralTube.coordinateZPhase (rotateTorusCoordinates s x) =
      Circle.exp (3 * s) * PeripheralTube.coordinateZPhase x := by
  unfold PeripheralTube.coordinateZPhase rotateTorusCoordinates
  rw [mul_pow, circleExp_pow]
  norm_num
  simp only [div_eq_mul_inv]
  group

theorem coordinateWPhase_rotateTorusCoordinates
    (s : ℝ) (x : PeripheralTube.TorusCoordinates) :
    PeripheralTube.coordinateWPhase (rotateTorusCoordinates s x) =
      Circle.exp (2 * s) * PeripheralTube.coordinateWPhase x := by
  unfold PeripheralTube.coordinateWPhase rotateTorusCoordinates
  rw [mul_pow, circleExp_pow]
  norm_num
  simp only [div_eq_mul_inv]
  group

theorem torusPoint_rotateTorusCoordinates
    (s : ℝ) (x : PeripheralTube.TorusCoordinates) :
    (PeripheralTube.torusPoint (rotateTorusCoordinates s x)).1 =
      Milnor.weightedRotate s (PeripheralTube.torusPoint x).1 := by
  apply Subtype.ext
  apply Prod.ext
  · change
      ((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) *
          PeripheralTube.coordinateZPhase (rotateTorusCoordinates s x) =
        Milnor.rotate 3 s
          (((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) *
            PeripheralTube.coordinateZPhase x)
    rw [coordinateZPhase_rotateTorusCoordinates]
    unfold Milnor.rotate
    change
      ((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) *
          (Complex.exp ((((3 * s : ℝ) : ℂ) * Complex.I)) *
            (PeripheralTube.coordinateZPhase x).1) =
        Complex.exp (((((3 : ℕ) : ℝ) * s : ℝ) : ℂ) * Complex.I) *
          (((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) *
            (PeripheralTube.coordinateZPhase x).1)
    norm_num
    ring
  · change
      -(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) *
          PeripheralTube.coordinateWPhase (rotateTorusCoordinates s x)) =
        Milnor.rotate 2 s
          (-(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) *
            PeripheralTube.coordinateWPhase x))
    rw [coordinateWPhase_rotateTorusCoordinates]
    unfold Milnor.rotate
    change
      -(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) *
          (Complex.exp ((((2 * s : ℝ) : ℂ) * Complex.I)) *
            (PeripheralTube.coordinateWPhase x).1)) =
        Complex.exp (((((2 : ℕ) : ℝ) * s : ℝ) : ℂ) * Complex.I) *
          -(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) *
            (PeripheralTube.coordinateWPhase x).1)
    norm_num
    ring

def weightedRotateTorus (s : ℝ) (q : PeripheralTube.TorusRegion) :
    PeripheralTube.TorusRegion :=
  PeripheralTube.torusPoint
    (rotateTorusCoordinates s (PeripheralTube.torusCoordinates q))

theorem weightedRotateTorus_val (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    (weightedRotateTorus s q).1 = Milnor.weightedRotate s q.1 := by
  calc
    (weightedRotateTorus s q).1 =
        (PeripheralTube.torusPoint
          (rotateTorusCoordinates s (PeripheralTube.torusCoordinates q))).1 := rfl
    _ = Milnor.weightedRotate s
        (PeripheralTube.torusPoint (PeripheralTube.torusCoordinates q)).1 :=
      torusPoint_rotateTorusCoordinates s _
    _ = Milnor.weightedRotate s q.1 := by
      rw [PeripheralTube.torusPoint_torusCoordinates]

theorem torusCoordinates_weightedRotateTorus (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    PeripheralTube.torusCoordinates (weightedRotateTorus s q) =
      rotateTorusCoordinates s (PeripheralTube.torusCoordinates q) := by
  simp [weightedRotateTorus]

theorem radial_weightedRotateTorus (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    PeripheralTube.radial (weightedRotateTorus s q) =
      PeripheralTube.radial q := by
  change (PeripheralTube.torusCoordinates (weightedRotateTorus s q)).1 =
    (PeripheralTube.torusCoordinates q).1
  rw [torusCoordinates_weightedRotateTorus]
  rfl

theorem longitude_weightedRotateTorus (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    PeripheralTube.longitude (weightedRotateTorus s q) =
      Circle.exp s * PeripheralTube.longitude q := by
  change (PeripheralTube.torusCoordinates (weightedRotateTorus s q)).2.1 =
    Circle.exp s * (PeripheralTube.torusCoordinates q).2.1
  rw [torusCoordinates_weightedRotateTorus]
  rfl

theorem normalPhase_weightedRotateTorus (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    PeripheralTube.normalPhase (weightedRotateTorus s q) =
      PeripheralTube.normalPhase q := by
  change (PeripheralTube.torusCoordinates (weightedRotateTorus s q)).2.2 =
    (PeripheralTube.torusCoordinates q).2.2
  rw [torusCoordinates_weightedRotateTorus]
  rfl

theorem normalFactor_weightedRotateTorus (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    PeripheralTube.normalFactor
        (PeripheralTube.torusCoordinates (weightedRotateTorus s q)) =
      PeripheralTube.normalFactor (PeripheralTube.torusCoordinates q) := by
  rw [torusCoordinates_weightedRotateTorus]
  rfl

theorem torusNormalCoordinates_weightedRotateTorus (s : ℝ)
    (q : PeripheralTube.TorusRegion) :
    PeripheralCollar.torusNormalCoordinates (weightedRotateTorus s q) =
      PeripheralCollar.torusNormalCoordinates q := by
  ext i
  fin_cases i
  · simp [PeripheralCollar.torusNormalCoordinates,
      radial_weightedRotateTorus]
  · simp [PeripheralCollar.torusNormalCoordinates,
      normalPhase_weightedRotateTorus]

theorem weightedRotateTorus_mem_localTubeSet (s : ℝ)
    {q : PeripheralTube.TorusRegion}
    (hq : q ∈ PeripheralCollar.LocalTubeSet) :
    weightedRotateTorus s q ∈ PeripheralCollar.LocalTubeSet := by
  rcases hq with ⟨hphase, hsource, hsmall⟩
  constructor
  · rw [normalPhase_weightedRotateTorus]
    exact hphase
  · constructor
    · rw [torusNormalCoordinates_weightedRotateTorus]
      exact hsource
    · rw [normalFactor_weightedRotateTorus]
      exact hsmall

end

end Submission.PeripheralBoundary
