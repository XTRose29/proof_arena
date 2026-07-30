import Submission.MeridianDegree

open Complex
open scoped unitInterval

namespace Submission.LocalWinding

noncomputable section

def complexDet (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

theorem complexDet_I_mul (a : ℂ) :
    complexDet a (Complex.I * a) = normSq a := by
  simp [complexDet, normSq_apply]

theorem complexDet_neg_I_mul (a : ℂ) :
    complexDet a (-(Complex.I * a)) = -normSq a := by
  rw [complexDet]
  simp [normSq_apply]
  ring

theorem complexDet_smul_add (a b c : ℂ) (r s : ℝ) :
    complexDet a (((r : ℝ) : ℂ) * b + ((s : ℝ) : ℂ) * c) =
      r * complexDet a b + s * complexDet a c := by
  simp [complexDet]
  ring

theorem linearCombination_ne_zero {a b : ℂ}
    (hdet : complexDet a b ≠ 0) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    (x : ℂ) * a + (y : ℂ) * b ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    add_im, mul_im, zero_re, zero_im] at hre him
  have hx : x * complexDet a b = 0 := by
    rw [complexDet]
    linear_combination b.im * hre - b.re * him
  have hy : y * complexDet a b = 0 := by
    rw [complexDet]
    linear_combination -a.im * hre + a.re * him
  have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_right hdet
  have hy0 : y = 0 := (mul_eq_zero.mp hy).resolve_right hdet
  rw [hx0, hy0] at hxy
  norm_num at hxy

def normalize (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / ‖z‖, by simp [Submonoid.unitSphere, norm_ne_zero_iff.mpr hz]⟩

@[simp] theorem normalize_coe (z : ℂ) (hz : z ≠ 0) :
    (normalize z hz : ℂ) = z / ‖z‖ :=
  rfl

def ellipseValue (a b : ℂ) (t : unitInterval) : ℂ :=
  (Real.cos (2 * Real.pi * (t : ℝ)) : ℂ) * a +
    (Real.sin (2 * Real.pi * (t : ℝ)) : ℂ) * b

theorem ellipseValue_ne_zero {a b : ℂ} (hdet : complexDet a b ≠ 0)
    (t : unitInterval) : ellipseValue a b t ≠ 0 := by
  apply linearCombination_ne_zero hdet
  exact Real.cos_sq_add_sin_sq (2 * Real.pi * (t : ℝ))

def ellipseLoop (a b : ℂ) (hdet : complexDet a b ≠ 0) :
    Path (normalize a (fun ha => hdet (by simp [ha, complexDet])))
      (normalize a (fun ha => hdet (by simp [ha, complexDet]))) where
  toFun t := normalize (ellipseValue a b t) (ellipseValue_ne_zero hdet t)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hvalue : Continuous (ellipseValue a b) := by
      unfold ellipseValue
      fun_prop
    exact hvalue.div (Complex.continuous_ofReal.comp hvalue.norm)
      (fun t => by
        exact_mod_cast norm_ne_zero_iff.mpr (ellipseValue_ne_zero hdet t))
  source' := by
    apply Subtype.ext
    simp [ellipseValue, normalize]
  target' := by
    apply Subtype.ext
    simp [ellipseValue, normalize, Real.cos_two_pi, Real.sin_two_pi]

def positiveBlend (a b : ℂ) (s : unitInterval) : ℂ :=
  ((1 - (s : ℝ) : ℝ) : ℂ) * b +
    ((s : ℝ) : ℂ) * (Complex.I * a)

theorem positiveBlend_det {a b : ℂ} (hdet : 0 < complexDet a b)
    (s : unitInterval) : 0 < complexDet a (positiveBlend a b s) := by
  rw [positiveBlend, complexDet_smul_add, complexDet_I_mul]
  have ha : 0 < normSq a := normSq_pos.mpr (fun ha => by
    subst a
    simp [complexDet] at hdet)
  by_cases hs : (s : ℝ) = 1
  · rw [hs]
    simp [ha]
  · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hslt) hdet)
      (mul_nonneg s.2.1 ha.le)

def negativeBlend (a b : ℂ) (s : unitInterval) : ℂ :=
  ((1 - (s : ℝ) : ℝ) : ℂ) * b +
    ((s : ℝ) : ℂ) * (-(Complex.I * a))

theorem negativeBlend_det {a b : ℂ} (hdet : complexDet a b < 0)
    (s : unitInterval) : complexDet a (negativeBlend a b s) < 0 := by
  rw [negativeBlend, complexDet_smul_add, complexDet_neg_I_mul]
  have ha : 0 < normSq a := normSq_pos.mpr (fun ha => by
    subst a
    simp [complexDet] at hdet)
  by_cases hs : (s : ℝ) = 1
  · rw [hs]
    simp [ha]
  · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs
    exact add_neg_of_neg_of_nonpos
      (mul_neg_of_pos_of_neg (sub_pos.mpr hslt) hdet)
      (mul_nonpos_of_nonneg_of_nonpos s.2.1 (neg_nonpos.mpr ha.le))

def standardLoopPos : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * (t : ℝ))
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

def standardLoopNeg : Path (1 : Circle) 1 where
  toFun t := Circle.exp (-(2 * Real.pi * (t : ℝ)))
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)
  source' := by simp
  target' := by
    rw [show -(2 * Real.pi * ((1 : unitInterval) : ℝ)) =
      0 - 2 * Real.pi by norm_num]
    rw [Circle.periodic_exp.sub_eq]
    simp

theorem windingReal_standardLoop_pos :
    CircleWinding.windingReal standardLoopPos = 2 * Real.pi := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => 2 * Real.pi * (t : ℝ), by fun_prop⟩
  have hlift : candidate = CircleWinding.liftedLoop standardLoopPos := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      apply Subtype.ext
      simp [candidate, CircleWinding.normalizeLoop, standardLoopPos]
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  simpa [candidate, CircleWinding.windingReal] using hend.symm

theorem windingReal_standardLoop_neg :
    CircleWinding.windingReal standardLoopNeg = -(2 * Real.pi) := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => -(2 * Real.pi * (t : ℝ)), by fun_prop⟩
  have hlift : candidate = CircleWinding.liftedLoop standardLoopNeg := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      apply Subtype.ext
      simp [candidate, CircleWinding.normalizeLoop, standardLoopNeg]
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  simpa [candidate, CircleWinding.windingReal] using hend.symm

def rotatedLoopPos (a : ℂ) (ha : a ≠ 0) :
    Path (normalize a ha) (normalize a ha) where
  toFun t := normalize a ha * standardLoopPos t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

def rotatedLoopNeg (a : ℂ) (ha : a ≠ 0) :
    Path (normalize a ha) (normalize a ha) where
  toFun t := normalize a ha * standardLoopNeg t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem windingReal_rotatedLoopPos (a : ℂ) (ha : a ≠ 0) :
    CircleWinding.windingReal (rotatedLoopPos a ha) = 2 * Real.pi := by
  have hnormalize :
      CircleWinding.normalizeLoop (rotatedLoopPos a ha) =
        CircleWinding.normalizeLoop standardLoopPos := by
    ext t
    simp [CircleWinding.normalizeLoop, rotatedLoopPos]
  have hlift : CircleWinding.liftedLoop (rotatedLoopPos a ha) =
      CircleWinding.liftedLoop standardLoopPos := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      simp only [Function.comp_apply]
      rw [CircleWinding.exp_liftedLoop]
      exact DFunLike.congr_fun (congrArg Path.toContinuousMap hnormalize) t
    · exact CircleWinding.liftedLoop_zero _
  rw [CircleWinding.windingReal, hlift]
  exact windingReal_standardLoop_pos

theorem windingReal_rotatedLoopNeg (a : ℂ) (ha : a ≠ 0) :
    CircleWinding.windingReal (rotatedLoopNeg a ha) = -(2 * Real.pi) := by
  have hnormalize :
      CircleWinding.normalizeLoop (rotatedLoopNeg a ha) =
        CircleWinding.normalizeLoop standardLoopNeg := by
    ext t
    simp [CircleWinding.normalizeLoop, rotatedLoopNeg]
  have hlift : CircleWinding.liftedLoop (rotatedLoopNeg a ha) =
      CircleWinding.liftedLoop standardLoopNeg := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      simp only [Function.comp_apply]
      rw [CircleWinding.exp_liftedLoop]
      exact DFunLike.congr_fun (congrArg Path.toContinuousMap hnormalize) t
    · exact CircleWinding.liftedLoop_zero _
  rw [CircleWinding.windingReal, hlift]
  exact windingReal_standardLoop_neg

theorem ellipseLoop_I_mul (a : ℂ) (ha : a ≠ 0) :
    ellipseLoop a (Complex.I * a) (by
      rw [complexDet_I_mul]
      exact ne_of_gt (normSq_pos.mpr ha)) = rotatedLoopPos a ha := by
  apply Path.ext
  funext t
  apply Subtype.ext
  let theta : ℝ := 2 * Real.pi * (t : ℝ)
  have hexp :
      (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I =
        Complex.exp ((theta : ℂ) * Complex.I) := by
    exact (Complex.exp_ofReal_mul_I theta).symm
  have hvalue : ellipseValue a (Complex.I * a) t =
      Complex.exp ((theta : ℂ) * Complex.I) * a := by
    rw [ellipseValue]
    change (Real.cos theta : ℂ) * a +
      (Real.sin theta : ℂ) * (Complex.I * a) = _
    rw [← hexp]
    ring
  change ellipseValue a (Complex.I * a) t /
      ‖ellipseValue a (Complex.I * a) t‖ =
    (a / ‖a‖) * Complex.exp ((theta : ℂ) * Complex.I)
  rw [hvalue, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  ring

theorem ellipseLoop_neg_I_mul (a : ℂ) (ha : a ≠ 0) :
    ellipseLoop a (-(Complex.I * a)) (by
      rw [complexDet_neg_I_mul]
      exact neg_ne_zero.mpr (ne_of_gt (normSq_pos.mpr ha))) =
      rotatedLoopNeg a ha := by
  apply Path.ext
  funext t
  apply Subtype.ext
  let theta : ℝ := 2 * Real.pi * (t : ℝ)
  have hexp :
      (Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I =
        Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have hvalue : ellipseValue a (-(Complex.I * a)) t =
      Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) * a := by
    rw [ellipseValue]
    change (Real.cos theta : ℂ) * a +
      (Real.sin theta : ℂ) * (-(Complex.I * a)) = _
    rw [← hexp]
    ring
  change ellipseValue a (-(Complex.I * a)) t /
      ‖ellipseValue a (-(Complex.I * a)) t‖ =
    (a / ‖a‖) * Complex.exp (((-theta : ℝ) : ℂ) * Complex.I)
  rw [hvalue, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  ring

def positiveEllipseHomotopy {a b : ℂ} (hdet : 0 < complexDet a b) :
    ((ellipseLoop a b hdet.ne' : Path _ _) : C(unitInterval, Circle)).Homotopy
      (ellipseLoop a (Complex.I * a) (by
        rw [complexDet_I_mul]
        exact ne_of_gt (normSq_pos.mpr (fun ha => by
          subst a
          simp [complexDet] at hdet)))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p => normalize (ellipseValue a (positiveBlend a b p.1) p.2)
        (ellipseValue_ne_zero (ne_of_gt (positiveBlend_det hdet p.1)) p.2), by
      apply Continuous.subtype_mk
      have hblend : Continuous
          (fun p : unitInterval × unitInterval => positiveBlend a b p.1) := by
        unfold positiveBlend
        fun_prop
      have hvalue : Continuous
          (fun p : unitInterval × unitInterval =>
            ellipseValue a (positiveBlend a b p.1) p.2) := by
        unfold ellipseValue
        fun_prop
      exact hvalue.div (Complex.continuous_ofReal.comp hvalue.norm)
        (fun p => by
          exact_mod_cast norm_ne_zero_iff.mpr
            (ellipseValue_ne_zero (ne_of_gt (positiveBlend_det hdet p.1)) p.2))⟩
    (by
      intro t
      apply Subtype.ext
      change ellipseValue a (positiveBlend a b 0) t /
          ‖ellipseValue a (positiveBlend a b 0) t‖ =
        ellipseValue a b t / ‖ellipseValue a b t‖
      simp [positiveBlend])
    (by
      intro t
      apply Subtype.ext
      change ellipseValue a (positiveBlend a b 1) t /
          ‖ellipseValue a (positiveBlend a b 1) t‖ =
        ellipseValue a (Complex.I * a) t /
          ‖ellipseValue a (Complex.I * a) t‖
      simp [positiveBlend])

def negativeEllipseHomotopy {a b : ℂ} (hdet : complexDet a b < 0) :
    ((ellipseLoop a b hdet.ne : Path _ _) : C(unitInterval, Circle)).Homotopy
      (ellipseLoop a (-(Complex.I * a)) (by
        rw [complexDet_neg_I_mul]
        exact neg_ne_zero.mpr (ne_of_gt (normSq_pos.mpr (fun ha => by
          subst a
          simp [complexDet] at hdet))))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p => normalize (ellipseValue a (negativeBlend a b p.1) p.2)
        (ellipseValue_ne_zero (ne_of_lt (negativeBlend_det hdet p.1)) p.2), by
      apply Continuous.subtype_mk
      have hblend : Continuous
          (fun p : unitInterval × unitInterval => negativeBlend a b p.1) := by
        unfold negativeBlend
        fun_prop
      have hvalue : Continuous
          (fun p : unitInterval × unitInterval =>
            ellipseValue a (negativeBlend a b p.1) p.2) := by
        unfold ellipseValue
        fun_prop
      exact hvalue.div (Complex.continuous_ofReal.comp hvalue.norm)
        (fun p => by
          exact_mod_cast norm_ne_zero_iff.mpr
            (ellipseValue_ne_zero (ne_of_lt (negativeBlend_det hdet p.1)) p.2))⟩
    (by
      intro t
      apply Subtype.ext
      change ellipseValue a (negativeBlend a b 0) t /
          ‖ellipseValue a (negativeBlend a b 0) t‖ =
        ellipseValue a b t / ‖ellipseValue a b t‖
      simp [negativeBlend])
    (by
      intro t
      apply Subtype.ext
      change ellipseValue a (negativeBlend a b 1) t /
          ‖ellipseValue a (negativeBlend a b 1) t‖ =
        ellipseValue a (-(Complex.I * a)) t /
          ‖ellipseValue a (-(Complex.I * a)) t‖
      simp [negativeBlend])

theorem windingReal_ellipse_of_pos {a b : ℂ} (hdet : 0 < complexDet a b) :
    CircleWinding.windingReal (ellipseLoop a b hdet.ne') = 2 * Real.pi := by
  have ha : a ≠ 0 := fun ha => by
    subst a
    simp [complexDet] at hdet
  calc
    CircleWinding.windingReal (ellipseLoop a b hdet.ne') =
        CircleWinding.windingReal
          (ellipseLoop a (Complex.I * a) (by
            rw [complexDet_I_mul]
            exact ne_of_gt (normSq_pos.mpr ha))) := by
      apply CircleWinding.windingReal_eq_of_freeHomotopy
        (positiveEllipseHomotopy hdet)
      intro s
      apply Subtype.ext
      change ellipseValue a (positiveBlend a b s) 1 /
          ‖ellipseValue a (positiveBlend a b s) 1‖ =
        ellipseValue a (positiveBlend a b s) 0 /
          ‖ellipseValue a (positiveBlend a b s) 0‖
      simp [ellipseValue]
    _ = CircleWinding.windingReal (rotatedLoopPos a ha) := by
      rw [ellipseLoop_I_mul a ha]
    _ = 2 * Real.pi := windingReal_rotatedLoopPos a ha

theorem windingReal_ellipse_of_neg {a b : ℂ} (hdet : complexDet a b < 0) :
    CircleWinding.windingReal (ellipseLoop a b hdet.ne) = -(2 * Real.pi) := by
  have ha : a ≠ 0 := fun ha => by
    subst a
    simp [complexDet] at hdet
  calc
    CircleWinding.windingReal (ellipseLoop a b hdet.ne) =
        CircleWinding.windingReal
          (ellipseLoop a (-(Complex.I * a)) (by
            rw [complexDet_neg_I_mul]
            exact neg_ne_zero.mpr (ne_of_gt (normSq_pos.mpr ha)))) := by
      apply CircleWinding.windingReal_eq_of_freeHomotopy
        (negativeEllipseHomotopy hdet)
      intro s
      apply Subtype.ext
      change ellipseValue a (negativeBlend a b s) 1 /
          ‖ellipseValue a (negativeBlend a b s) 1‖ =
        ellipseValue a (negativeBlend a b s) 0 /
          ‖ellipseValue a (negativeBlend a b s) 0‖
      simp [ellipseValue]
    _ = CircleWinding.windingReal (rotatedLoopNeg a ha) := by
      rw [ellipseLoop_neg_I_mul a ha]
    _ = -(2 * Real.pi) := windingReal_rotatedLoopNeg a ha

theorem closeValue_ne_zero {a b : ℂ} (_hdet : complexDet a b ≠ 0)
    {g : unitInterval → ℂ}
    (hclose : ∀ t, ‖g t - ellipseValue a b t‖ < ‖ellipseValue a b t‖)
    (t : unitInterval) : g t ≠ 0 := by
  intro hg
  have h := hclose t
  rw [hg, zero_sub, norm_neg] at h
  exact (lt_irrefl _) h

def normalizedLoopOf {g : unitInterval → ℂ} (hg : Continuous g)
    (hloop : g 1 = g 0) (hne : ∀ t, g t ≠ 0) :
    Path (normalize (g 0) (hne 0)) (normalize (g 0) (hne 0)) where
  toFun t := normalize (g t) (hne t)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact hg.div (Complex.continuous_ofReal.comp hg.norm) (fun t => by
      exact_mod_cast norm_ne_zero_iff.mpr (hne t))
  source' := rfl
  target' := by
    apply Subtype.ext
    rw [normalize_coe, normalize_coe, hloop]

def closeBlend (a b : ℂ) (g : unitInterval → ℂ)
    (s t : unitInterval) : ℂ :=
  ellipseValue a b t + ((s : ℝ) : ℂ) * (g t - ellipseValue a b t)

theorem closeBlend_ne_zero {a b : ℂ} (_hdet : complexDet a b ≠ 0)
    {g : unitInterval → ℂ}
    (hclose : ∀ t, ‖g t - ellipseValue a b t‖ < ‖ellipseValue a b t‖)
    (s t : unitInterval) : closeBlend a b g s t ≠ 0 := by
  intro hzero
  have heq : ellipseValue a b t =
      -(((s : ℝ) : ℂ) * (g t - ellipseValue a b t)) := by
    exact eq_neg_of_add_eq_zero_left hzero
  have hnorm := congrArg norm heq
  rw [norm_neg, norm_mul] at hnorm
  have hsNorm : ‖(((s : ℝ) : ℂ))‖ = (s : ℝ) := by
    simp [abs_of_nonneg s.2.1]
  rw [hsNorm] at hnorm
  have hle : (s : ℝ) * ‖g t - ellipseValue a b t‖ ≤
      ‖g t - ellipseValue a b t‖ := by
    exact mul_le_of_le_one_left (norm_nonneg _) s.2.2
  have hlt := hclose t
  rw [hnorm] at hlt
  exact (not_lt_of_ge hle) hlt

def closeHomotopy {a b : ℂ} (hdet : complexDet a b ≠ 0)
    {g : unitInterval → ℂ} (hg : Continuous g) (hloop : g 1 = g 0)
    (hclose : ∀ t, ‖g t - ellipseValue a b t‖ < ‖ellipseValue a b t‖) :
    ((ellipseLoop a b hdet : Path _ _) : C(unitInterval, Circle)).Homotopy
      (normalizedLoopOf hg hloop (closeValue_ne_zero hdet hclose)) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p => normalize (closeBlend a b g p.1 p.2)
        (closeBlend_ne_zero hdet hclose p.1 p.2), by
      apply Continuous.subtype_mk
      have hblend : Continuous
          (fun p : unitInterval × unitInterval => closeBlend a b g p.1 p.2) := by
        unfold closeBlend ellipseValue
        fun_prop
      exact hblend.div (Complex.continuous_ofReal.comp hblend.norm) (fun p => by
        exact_mod_cast norm_ne_zero_iff.mpr
          (closeBlend_ne_zero hdet hclose p.1 p.2))⟩
    (by
      intro t
      apply Subtype.ext
      change closeBlend a b g 0 t / ‖closeBlend a b g 0 t‖ =
        ellipseValue a b t / ‖ellipseValue a b t‖
      simp [closeBlend])
    (by
      intro t
      apply Subtype.ext
      change closeBlend a b g 1 t / ‖closeBlend a b g 1 t‖ =
        g t / ‖g t‖
      simp [closeBlend])

theorem windingReal_normalizedLoopOf_eq_ellipse {a b : ℂ}
    (hdet : complexDet a b ≠ 0) {g : unitInterval → ℂ}
    (hg : Continuous g) (hloop : g 1 = g 0)
    (hclose : ∀ t, ‖g t - ellipseValue a b t‖ < ‖ellipseValue a b t‖) :
    CircleWinding.windingReal
        (normalizedLoopOf hg hloop (closeValue_ne_zero hdet hclose)) =
      CircleWinding.windingReal (ellipseLoop a b hdet) := by
  symm
  apply CircleWinding.windingReal_eq_of_freeHomotopy
    (closeHomotopy hdet hg hloop hclose)
  intro s
  apply Subtype.ext
  change closeBlend a b g s 1 / ‖closeBlend a b g s 1‖ =
    closeBlend a b g s 0 / ‖closeBlend a b g s 0‖
  rw [closeBlend, closeBlend, hloop]
  simp [ellipseValue]

theorem windingReal_normalizedLoopOf_pos {a b : ℂ}
    (hdet : 0 < complexDet a b) {g : unitInterval → ℂ}
    (hg : Continuous g) (hloop : g 1 = g 0)
    (hclose : ∀ t, ‖g t - ellipseValue a b t‖ < ‖ellipseValue a b t‖) :
    CircleWinding.windingReal
        (normalizedLoopOf hg hloop (closeValue_ne_zero hdet.ne' hclose)) =
      2 * Real.pi := by
  rw [windingReal_normalizedLoopOf_eq_ellipse hdet.ne' hg hloop hclose,
    windingReal_ellipse_of_pos hdet]

theorem windingReal_normalizedLoopOf_neg {a b : ℂ}
    (hdet : complexDet a b < 0) {g : unitInterval → ℂ}
    (hg : Continuous g) (hloop : g 1 = g 0)
    (hclose : ∀ t, ‖g t - ellipseValue a b t‖ < ‖ellipseValue a b t‖) :
    CircleWinding.windingReal
        (normalizedLoopOf hg hloop (closeValue_ne_zero hdet.ne hclose)) =
      -(2 * Real.pi) := by
  rw [windingReal_normalizedLoopOf_eq_ellipse hdet.ne hg hloop hclose,
    windingReal_ellipse_of_neg hdet]

section DerivativeEstimate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def direction (u v : E) (t : unitInterval) : E :=
  Real.cos (2 * Real.pi * (t : ℝ)) • u +
    Real.sin (2 * Real.pi * (t : ℝ)) • v

theorem direction_continuous (u v : E) : Continuous (direction u v) := by
  unfold direction
  fun_prop

theorem direction_zero (u v : E) : direction u v 0 = u := by
  simp [direction]

theorem direction_one (u v : E) : direction u v 1 = u := by
  simp [direction, Real.cos_two_pi, Real.sin_two_pi]

theorem norm_direction_le (u v : E) (t : unitInterval) :
    ‖direction u v t‖ ≤ ‖u‖ + ‖v‖ := by
  calc
    ‖direction u v t‖ ≤
        ‖Real.cos (2 * Real.pi * (t : ℝ)) • u‖ +
          ‖Real.sin (2 * Real.pi * (t : ℝ)) • v‖ := norm_add_le _ _
    _ = |Real.cos (2 * Real.pi * (t : ℝ))| * ‖u‖ +
        |Real.sin (2 * Real.pi * (t : ℝ))| * ‖v‖ := by
      simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖u‖ + 1 * ‖v‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _))
    _ = ‖u‖ + ‖v‖ := by ring

theorem fderiv_direction (L : E →L[ℝ] ℂ) (u v : E) (t : unitInterval) :
    L (direction u v t) = ellipseValue (L u) (L v) t := by
  simp [direction, ellipseValue]

theorem ellipseValue_real_smul (r : ℝ) (a b : ℂ) (t : unitInterval) :
    ellipseValue ((r : ℂ) * a) ((r : ℂ) * b) t =
      (r : ℂ) * ellipseValue a b t := by
  simp [ellipseValue]
  ring

theorem complexDet_real_smul (r : ℝ) (a b : ℂ) :
    complexDet ((r : ℂ) * a) ((r : ℂ) * b) =
      r ^ 2 * complexDet a b := by
  simp [complexDet]
  ring

theorem exists_radius_bound_close_fderiv {f : E → ℂ} {L : E →L[ℝ] ℂ}
    {p u v : E} (hf : HasFDerivAt f L p)
    (hdet : complexDet (L u) (L v) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → ∀ t : unitInterval,
        ‖(f (p + r • direction u v t) - f p) -
            ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ <
          ‖ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ := by
  have hellipseCont : Continuous
      (fun t : unitInterval => ‖ellipseValue (L u) (L v) t‖) := by
    have hvalue : Continuous (ellipseValue (L u) (L v)) := by
      unfold ellipseValue
      fun_prop
    exact hvalue.norm
  obtain ⟨tmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    hellipseCont.continuousOn
  let m : ℝ := ‖ellipseValue (L u) (L v) tmin‖
  have hm_pos : 0 < m := by
    exact norm_pos_iff.mpr (ellipseValue_ne_zero hdet tmin)
  have hm_le (t : unitInterval) : m ≤ ‖ellipseValue (L u) (L v) t‖ :=
    hmin (Set.mem_univ t)
  let M : ℝ := ‖u‖ + ‖v‖
  have hM_nonneg : 0 ≤ M := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let c : ℝ := m / (2 * (M + 1))
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hcM_lt : c * M < m := by
    have hden : 0 < 2 * (M + 1) := by positivity
    have hratio : M / (2 * (M + 1)) < 1 := by
      rw [div_lt_one hden]
      linarith
    calc
      c * M = m * (M / (2 * (M + 1))) := by
        dsimp [c]
        field_simp
      _ < m * 1 := mul_lt_mul_of_pos_left hratio hm_pos
      _ = m := mul_one m
  have hevent := hf.isLittleO.bound hc_pos
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨ε, hε_pos, hbound⟩ := hevent
  let ρ : ℝ := ε / (M + 1)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  refine ⟨ρ, hρ_pos, ?_⟩
  intro r hr_pos hr_lt t
  let d := direction u v t
  have hd_norm : ‖d‖ ≤ M := norm_direction_le u v t
  have hrM_lt : r * M < ε := by
    have hden : 0 < M + 1 := by positivity
    have hr_large : r * (M + 1) < ε := by
      apply (lt_div_iff₀ hden).mp
      simpa [ρ] using hr_lt
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (by linarith : M ≤ M + 1) hr_pos.le)
      hr_large
  have hdist : dist (p + r • d) p < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr_pos]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd_norm hr_pos.le) hrM_lt
  have herr := hbound hdist
  have hlinear : L (r • d) =
      ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t := by
    rw [map_smul, fderiv_direction, ellipseValue_real_smul]
    rfl
  have hdisplacement : p + r • d - p = r • d := by abel
  rw [hdisplacement, hlinear] at herr
  have herror_le :
      ‖(f (p + r • d) - f p) -
          ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ ≤
        c * (r * M) := by
    calc
      _ ≤ c * ‖r • d‖ := herr
      _ = c * (r * ‖d‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr_pos]
      _ ≤ c * (r * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hd_norm hr_pos.le) hc_pos.le
  have herror_lt :
      ‖(f (p + r • d) - f p) -
          ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ <
        r * m := by
    calc
      _ ≤ c * (r * M) := herror_le
      _ = r * (c * M) := by ring
      _ < r * m := mul_lt_mul_of_pos_left hcM_lt hr_pos
  have hnorm_scaled :
      ‖ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ =
        r * ‖ellipseValue (L u) (L v) t‖ := by
    rw [ellipseValue_real_smul, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hr_pos, mul_comm]
  rw [hnorm_scaled]
  exact lt_of_lt_of_le herror_lt (mul_le_mul_of_nonneg_left (hm_le t) hr_pos.le)

theorem exists_radius_close_fderiv {f : E → ℂ} {L : E →L[ℝ] ℂ}
    {p u v : E} (hf : HasFDerivAt f L p)
    (hdet : complexDet (L u) (L v) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : unitInterval,
      ‖(f (p + r • direction u v t) - f p) -
          ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ <
        ‖ellipseValue ((r : ℂ) * L u) ((r : ℂ) * L v) t‖ := by
  obtain ⟨ε, hε, hbound⟩ := exists_radius_bound_close_fderiv hf hdet
  refine ⟨ε / 2, by positivity, hbound (ε / 2) (by positivity) (by linarith)⟩

end DerivativeEstimate

end

end Submission.LocalWinding
