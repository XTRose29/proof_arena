import Submission.CoreLift

open Complex
open scoped unitInterval

namespace Submission.CoreDeformation

noncomputable section

def prune (s : ℝ) (a : ℂ) : ℂ :=
  ((a.re + s * max (-a.re) 0 : ℝ) : ℂ) + (a.im : ℂ) * Complex.I

@[simp] theorem prune_re (s : ℝ) (a : ℂ) :
    (prune s a).re = a.re + s * max (-a.re) 0 := by
  simp [prune]

@[simp] theorem prune_im (s : ℝ) (a : ℂ) : (prune s a).im = a.im := by
  simp [prune]

@[simp] theorem prune_zero (s : ℝ) : prune s 0 = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem prune_zero_time (a : ℂ) : prune 0 a = a := by
  apply Complex.ext <;> simp

theorem prune_eq_of_re_nonneg (s : ℝ) {a : ℂ} (ha : 0 ≤ a.re) :
    prune s a = a := by
  apply Complex.ext
  · simp [max_eq_right (neg_nonpos.mpr ha)]
  · simp

theorem prune_one_re_nonneg (a : ℂ) : 0 ≤ (prune 1 a).re := by
  by_cases ha : 0 ≤ a.re
  · simp [ha]
  · have ha' : a.re < 0 := lt_of_not_ge ha
    rw [prune_re, max_eq_left (neg_nonneg.mpr ha'.le)]
    linarith

theorem prune_continuous : Continuous (fun x : ℝ × ℂ => prune x.1 x.2) := by
  unfold prune
  fun_prop

theorem norm_prune_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℂ) :
    ‖prune s a‖ ≤ ‖a‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp only [normSq_apply, prune_re, prune_im]
  by_cases ha : 0 ≤ a.re
  · rw [max_eq_right (neg_nonpos.mpr ha)]
    ring_nf
    exact le_rfl
  · have ha' : a.re < 0 := lt_of_not_ge ha
    rw [max_eq_left (neg_nonneg.mpr ha'.le)]
    have hfactor : (1 - s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg a.re)
    ring_nf at hmul ⊢
    nlinarith

def pruneRatio (s : ℝ) (a : ℂ) : ℂ :=
  if a = 0 then 0 else prune s a / a

@[simp] theorem pruneRatio_zero (s : ℝ) : pruneRatio s 0 = 0 := by
  simp [pruneRatio]

theorem pruneRatio_of_ne (s : ℝ) {a : ℂ} (ha : a ≠ 0) :
    pruneRatio s a = prune s a / a := by
  simp [pruneRatio, ha]

theorem pruneRatio_mul (s : ℝ) (a : ℂ) : pruneRatio s a * a = prune s a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [pruneRatio_of_ne s ha, div_mul_cancel₀ _ ha]

theorem pruneRatio_continuousAt_of_ne {x : ℝ × ℂ} (hx : x.2 ≠ 0) :
    ContinuousAt (fun y : ℝ × ℂ => pruneRatio y.1 y.2) x := by
  have hformula : ContinuousAt (fun y : ℝ × ℂ => prune y.1 y.2 / y.2) x := by
    exact prune_continuous.continuousAt.div continuous_snd.continuousAt hx
  apply hformula.congr_of_eventuallyEq
  filter_upwards [continuous_snd.tendsto x |>.eventually
    (compl_singleton_mem_nhds_iff.mpr hx)] with y hy
  exact pruneRatio_of_ne y.1 (by simpa using hy)

theorem pruneRatio_re_nonneg (s : ℝ) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℂ) :
    0 ≤ (pruneRatio s a).re := by
  by_cases ha0 : a = 0
  · simp [ha0]
  · rw [pruneRatio_of_ne s ha0, Complex.div_re]
    rw [prune_re, prune_im, ← add_div]
    apply div_nonneg
    · by_cases ha : 0 ≤ a.re
      · rw [max_eq_right (neg_nonpos.mpr ha)]
        nlinarith [sq_nonneg a.re, sq_nonneg a.im]
      · have ha' : a.re < 0 := lt_of_not_ge ha
        rw [max_eq_left (neg_nonneg.mpr ha'.le)]
        nlinarith [sq_nonneg a.re, sq_nonneg a.im]
    · exact (normSq_pos.mpr ha0).le

theorem norm_pruneRatio_le_one
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℂ) :
    ‖pruneRatio s a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [pruneRatio_of_ne s ha, norm_div]
    exact (div_le_one (norm_pos_iff.mpr ha)).2 (norm_prune_le s hs0 hs1 a)

def zRaw (s : ℝ) (z : ℂ) : ℂ :=
  pruneRatio s (RadialSpine.zTerm z) ^ ((2 : ℂ)⁻¹) * z

theorem zTerm_zRaw (s : ℝ) (z : ℂ) :
    RadialSpine.zTerm (zRaw s z) = prune s (RadialSpine.zTerm z) := by
  by_cases hz : z = 0
  · simp [hz, zRaw]
  · have hterm : RadialSpine.zTerm z ≠ 0 :=
      (RadialSpine.zTerm_eq_zero_iff z).not.mpr hz
    have hroot :
        (pruneRatio s (RadialSpine.zTerm z) ^ ((2 : ℂ)⁻¹)) ^ 2 =
          pruneRatio s (RadialSpine.zTerm z) :=
      Complex.cpow_nat_inv_pow _ (by norm_num)
    rw [zRaw, RadialSpine.zTerm, mul_pow, hroot]
    calc
      Complex.I * (16 * (pruneRatio s (RadialSpine.zTerm z) * z ^ 2)) =
          pruneRatio s (RadialSpine.zTerm z) * RadialSpine.zTerm z := by
            simp [RadialSpine.zTerm]
            ring
      _ = prune s (RadialSpine.zTerm z) := pruneRatio_mul s _

def wRaw (s : ℝ) (w : ℂ) : ℂ :=
  RadialMilnor.radialMultiplier (pruneRatio s (RadialSpine.wTerm w)) * w

theorem wTerm_wRaw (s : ℝ) (w : ℂ) :
    RadialSpine.wTerm (wRaw s w) = prune s (RadialSpine.wTerm w) := by
  rw [wRaw, RadialSpine.wTerm, RadialMilnor.radialCube_mul_radialMultiplier]
  change Complex.I * (9 * (pruneRatio s (RadialSpine.wTerm w) *
    RadialMilnor.radialCube w)) = _
  rw [show Complex.I * (9 * (pruneRatio s (RadialSpine.wTerm w) *
      RadialMilnor.radialCube w)) =
      pruneRatio s (RadialSpine.wTerm w) * RadialSpine.wTerm w by
    simp [RadialSpine.wTerm]
    ring]
  exact pruneRatio_mul s _

theorem norm_zRaw_le
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : ℂ) :
    ‖zRaw s z‖ ≤ ‖z‖ := by
  have hterm := congrArg norm (zTerm_zRaw s z)
  rw [RadialSpine.norm_zTerm] at hterm
  have hprune := norm_prune_le s hs0 hs1 (RadialSpine.zTerm z)
  rw [RadialSpine.norm_zTerm] at hprune
  nlinarith [norm_nonneg (zRaw s z), norm_nonneg z]

theorem norm_wRaw_le
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (w : ℂ) :
    ‖wRaw s w‖ ≤ ‖w‖ := by
  have hterm := congrArg norm (wTerm_wRaw s w)
  rw [RadialSpine.norm_wTerm] at hterm
  have hprune := norm_prune_le s hs0 hs1 (RadialSpine.wTerm w)
  rw [RadialSpine.norm_wTerm] at hprune
  nlinarith [norm_nonneg (wRaw s w), norm_nonneg w]

theorem zRaw_continuous :
    Continuous (fun x : unitInterval × ℂ => zRaw (x.1 : ℝ) x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, z⟩
  by_cases hz : z = 0
  · subst z
    rw [ContinuousAt, show zRaw (s : ℝ) 0 = 0 by simp [zRaw],
      tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun x => norm_nonneg (zRaw (x.1 : ℝ) x.2))
      (fun x => norm_zRaw_le (x.1 : ℝ) x.1.2.1 x.1.2.2 x.2) ?_
    have h : Filter.Tendsto (fun x : unitInterval × ℂ => ‖x.2‖)
        (nhds (s, 0)) (nhds ‖(s, (0 : ℂ)).2‖) :=
      (continuous_snd.norm : Continuous
        (fun x : unitInterval × ℂ => ‖x.2‖)).continuousAt
    simpa using h
  · have hterm : RadialSpine.zTerm z ≠ 0 :=
      (RadialSpine.zTerm_eq_zero_iff z).not.mpr hz
    have hpair : ContinuousAt
        (fun x : unitInterval × ℂ => ((x.1 : ℝ), RadialSpine.zTerm x.2))
        (s, z) := by
      exact (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
        (RadialSpine.zTerm_continuous.continuousAt.comp continuous_snd.continuousAt)
    have hratio : ContinuousAt
        (fun x : unitInterval × ℂ =>
          pruneRatio (x.1 : ℝ) (RadialSpine.zTerm x.2)) (s, z) :=
      (pruneRatio_continuousAt_of_ne hterm).comp hpair
    have hrootAt : ContinuousAt
        (fun a : ℂ => a ^ ((2 : ℂ)⁻¹))
        (pruneRatio (s : ℝ) (RadialSpine.zTerm z)) :=
      Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (pruneRatio_re_nonneg (s : ℝ) s.2.1 s.2.2 _)) (by norm_num)
    exact (Filter.Tendsto.comp hrootAt hratio).mul continuous_snd.continuousAt

theorem wRaw_continuous :
    Continuous (fun x : unitInterval × ℂ => wRaw (x.1 : ℝ) x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, w⟩
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show wRaw (s : ℝ) 0 = 0 by simp [wRaw],
      tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun x => norm_nonneg (wRaw (x.1 : ℝ) x.2))
      (fun x => norm_wRaw_le (x.1 : ℝ) x.1.2.1 x.1.2.2 x.2) ?_
    have h : Filter.Tendsto (fun x : unitInterval × ℂ => ‖x.2‖)
        (nhds (s, 0)) (nhds ‖(s, (0 : ℂ)).2‖) :=
      (continuous_snd.norm : Continuous
        (fun x : unitInterval × ℂ => ‖x.2‖)).continuousAt
    simpa using h
  · have hterm : RadialSpine.wTerm w ≠ 0 :=
      (RadialSpine.wTerm_eq_zero_iff w).not.mpr hw
    have hpair : ContinuousAt
        (fun x : unitInterval × ℂ => ((x.1 : ℝ), RadialSpine.wTerm x.2))
        (s, w) := by
      exact (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
        (RadialSpine.wTerm_continuous.continuousAt.comp continuous_snd.continuousAt)
    have hratio : ContinuousAt
        (fun x : unitInterval × ℂ =>
          pruneRatio (x.1 : ℝ) (RadialSpine.wTerm x.2)) (s, w) :=
      (pruneRatio_continuousAt_of_ne hterm).comp hpair
    have hmultAt : ContinuousAt RadialMilnor.radialMultiplier
        (pruneRatio (s : ℝ) (RadialSpine.wTerm w)) :=
      RadialMilnor.radialMultiplier_continuousAt_of_re_nonneg
        (pruneRatio_re_nonneg (s : ℝ) s.2.1 s.2.2 _)
    exact (Filter.Tendsto.comp hmultAt hratio).mul continuous_snd.continuousAt

def rawNormSq (s : ℝ) (q : RadialSpine.Spine) : ℝ :=
  normSq (zRaw s q.1.1.1.1) + normSq (wRaw s q.1.1.1.2)

theorem raw_terms_re_pos (s : ℝ) (hs : 0 ≤ s) (q : RadialSpine.Spine) :
    0 < (RadialSpine.zTerm (zRaw s q.1.1.1.1) +
      RadialSpine.wTerm (wRaw s q.1.1.1.2)).re := by
  rw [zTerm_zRaw, wTerm_wRaw]
  have hsum := RadialCore.spine_term_sum_pos q
  have hmax : 0 ≤ max (-(RadialSpine.zTerm q.1.1.1.1).re) 0 +
      max (-(RadialSpine.wTerm q.1.1.1.2).re) 0 :=
    add_nonneg (le_max_right _ _) (le_max_right _ _)
  simp only [add_re, prune_re]
  nlinarith [mul_nonneg hs hmax]

theorem raw_terms_im_zero (s : ℝ) (q : RadialSpine.Spine) :
    (RadialSpine.zTerm (zRaw s q.1.1.1.1) +
      RadialSpine.wTerm (wRaw s q.1.1.1.2)).im = 0 := by
  rw [zTerm_zRaw, wTerm_wRaw]
  simp [q.2.1, q.2.2]

theorem rawNormSq_pos (s : ℝ) (hs : 0 ≤ s) (q : RadialSpine.Spine) :
    0 < rawNormSq s q := by
  have hnonzero : zRaw s q.1.1.1.1 ≠ 0 ∨ wRaw s q.1.1.1.2 ≠ 0 := by
    by_contra h
    push Not at h
    have hre := raw_terms_re_pos s hs q
    simp [h.1, h.2] at hre
  rcases hnonzero with hz | hw
  · exact add_pos_of_pos_of_nonneg (normSq_pos.mpr hz) (normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (normSq_nonneg _) (normSq_pos.mpr hw)

def rawNorm (s : ℝ) (q : RadialSpine.Spine) : ℝ :=
  Real.sqrt (rawNormSq s q)

theorem rawNorm_pos (s : ℝ) (hs : 0 ≤ s) (q : RadialSpine.Spine) :
    0 < rawNorm s q := Real.sqrt_pos.2 (rawNormSq_pos s hs q)

theorem rawNorm_sq (s : ℝ) (hs : 0 ≤ s) (q : RadialSpine.Spine) :
    rawNorm s q ^ 2 = rawNormSq s q :=
  Real.sq_sqrt (rawNormSq_pos s hs q).le

def normalizingFactor (s : ℝ) (q : RadialSpine.Spine) : ℝ :=
  (rawNorm s q)⁻¹

theorem normalizingFactor_pos (s : ℝ) (hs : 0 ≤ s) (q : RadialSpine.Spine) :
    0 < normalizingFactor s q := inv_pos.mpr (rawNorm_pos s hs q)

def pruneSphere (s : unitInterval) (q : RadialSpine.Spine) : RadialMilnor.CSphere :=
  ⟨((normalizingFactor (s : ℝ) q : ℂ) * zRaw (s : ℝ) q.1.1.1.1,
      (normalizingFactor (s : ℝ) q : ℂ) * wRaw (s : ℝ) q.1.1.1.2), by
    have hnorm : rawNorm (s : ℝ) q ≠ 0 :=
      ne_of_gt (rawNorm_pos (s : ℝ) s.2.1 q)
    change normSq ((normalizingFactor (s : ℝ) q : ℂ) * zRaw (s : ℝ) q.1.1.1.1) +
        normSq ((normalizingFactor (s : ℝ) q : ℂ) * wRaw (s : ℝ) q.1.1.1.2) = 1
    rw [normSq_mul, normSq_mul, normSq_ofReal]
    rw [← mul_add, ← rawNormSq, normalizingFactor,
      ← rawNorm_sq (s : ℝ) s.2.1]
    field_simp⟩

theorem polynomial_pruneSphere (s : unitInterval) (q : RadialSpine.Spine) :
    RadialMilnor.polynomial (pruneSphere s q) =
      (normalizingFactor (s : ℝ) q : ℂ) ^ 2 *
        (RadialSpine.zTerm (zRaw (s : ℝ) q.1.1.1.1) +
          RadialSpine.wTerm (wRaw (s : ℝ) q.1.1.1.2)) := by
  rw [RadialSpine.polynomial_eq_terms]
  change RadialSpine.zTerm ((normalizingFactor (s : ℝ) q : ℂ) *
      zRaw (s : ℝ) q.1.1.1.1) +
      RadialSpine.wTerm ((normalizingFactor (s : ℝ) q : ℂ) *
        wRaw (s : ℝ) q.1.1.1.2) = _
  rw [RadialSpine.zTerm_smul_nonneg _
      (normalizingFactor_pos (s : ℝ) s.2.1 q).le,
    RadialSpine.wTerm_smul_nonneg _
      (normalizingFactor_pos (s : ℝ) s.2.1 q).le, ← mul_add]

def pruneFiber (s : unitInterval) (q : RadialSpine.Spine) : RadialMilnor.Fiber :=
  ⟨pruneSphere s q, by
    rw [polynomial_pruneSphere]
    have hfactorSq : 0 < normalizingFactor (s : ℝ) q ^ 2 :=
      sq_pos_of_pos (normalizingFactor_pos (s : ℝ) s.2.1 q)
    constructor
    · simpa [mul_re, pow_two] using
        mul_pos hfactorSq (raw_terms_re_pos (s : ℝ) s.2.1 q)
    · simp [mul_im, pow_two, raw_terms_im_zero (s : ℝ) q]⟩

def pruneSpine (s : unitInterval) (q : RadialSpine.Spine) : RadialSpine.Spine :=
  ⟨pruneFiber s q, by
    change (RadialSpine.zTerm ((normalizingFactor (s : ℝ) q : ℂ) *
        zRaw (s : ℝ) q.1.1.1.1)).im = 0 ∧
      (RadialSpine.wTerm ((normalizingFactor (s : ℝ) q : ℂ) *
        wRaw (s : ℝ) q.1.1.1.2)).im = 0
    rw [RadialSpine.zTerm_smul_nonneg _
        (normalizingFactor_pos (s : ℝ) s.2.1 q).le,
      RadialSpine.wTerm_smul_nonneg _
        (normalizingFactor_pos (s : ℝ) s.2.1 q).le,
      zTerm_zRaw, wTerm_wRaw]
    simp [mul_im, pow_two, q.2.1, q.2.2]⟩

def spineRetraction (q : RadialSpine.Spine) : RadialCore.Core :=
  ⟨pruneSpine 1 q, by
    change 0 ≤ (RadialSpine.zTerm ((normalizingFactor 1 q : ℂ) *
        zRaw 1 q.1.1.1.1)).re ∧
      0 ≤ (RadialSpine.wTerm ((normalizingFactor 1 q : ℂ) *
        wRaw 1 q.1.1.1.2)).re
    rw [RadialSpine.zTerm_smul_nonneg _
        (normalizingFactor_pos 1 (by norm_num) q).le,
      RadialSpine.wTerm_smul_nonneg _
        (normalizingFactor_pos 1 (by norm_num) q).le,
      zTerm_zRaw, wTerm_wRaw]
    constructor
    · simpa [mul_re, pow_two] using
        mul_nonneg (sq_nonneg (normalizingFactor 1 q))
          (prune_one_re_nonneg (RadialSpine.zTerm q.1.1.1.1))
    · simpa [mul_re, pow_two] using
        mul_nonneg (sq_nonneg (normalizingFactor 1 q))
          (prune_one_re_nonneg (RadialSpine.wTerm q.1.1.1.2))⟩

theorem pruneFiber_continuous :
    Continuous (fun x : unitInterval × RadialSpine.Spine =>
      pruneFiber x.1 x.2) := by
  have hzCoord : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      x.2.1.1.1.1) := by fun_prop
  have hwCoord : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      x.2.1.1.1.2) := by fun_prop
  have hzRawComp := zRaw_continuous.comp (continuous_fst.prodMk hzCoord)
  have hwRawComp := wRaw_continuous.comp (continuous_fst.prodMk hwCoord)
  have hzRawCont : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      zRaw (x.1 : ℝ) x.2.1.1.1.1) := by
    simpa only [Function.comp_def] using hzRawComp
  have hwRawCont : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      wRaw (x.1 : ℝ) x.2.1.1.1.2) := by
    simpa only [Function.comp_def] using hwRawComp
  have hrawSq : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      rawNormSq (x.1 : ℝ) x.2) := by
    unfold rawNormSq
    exact (Complex.continuous_normSq.comp hzRawCont).add
      (Complex.continuous_normSq.comp hwRawCont)
  have hrawNorm : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      rawNorm (x.1 : ℝ) x.2) := Real.continuous_sqrt.comp hrawSq
  have hfactor : Continuous (fun x : unitInterval × RadialSpine.Spine =>
      normalizingFactor (x.1 : ℝ) x.2) := by
    unfold normalizingFactor
    exact hrawNorm.inv₀ (fun x => ne_of_gt (rawNorm_pos (x.1 : ℝ) x.1.2.1 x.2))
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp hfactor).mul hzRawCont).prodMk
    ((Complex.continuous_ofReal.comp hfactor).mul hwRawCont)

theorem pruneSpine_continuous :
    Continuous (fun x : unitInterval × RadialSpine.Spine =>
      pruneSpine x.1 x.2) := by
  apply Continuous.subtype_mk
  exact pruneFiber_continuous

theorem pruneRatio_zero_time_of_ne {a : ℂ} (ha : a ≠ 0) :
    pruneRatio 0 a = 1 := by
  rw [pruneRatio_of_ne 0 ha, prune_zero_time, div_self ha]

@[simp] theorem zRaw_zero_time (z : ℂ) : zRaw 0 z = z := by
  by_cases hz : z = 0
  · simp [hz, zRaw]
  · have hterm : RadialSpine.zTerm z ≠ 0 :=
      (RadialSpine.zTerm_eq_zero_iff z).not.mpr hz
    rw [zRaw, pruneRatio_zero_time_of_ne hterm]
    simp

@[simp] theorem wRaw_zero_time (w : ℂ) : wRaw 0 w = w := by
  by_cases hw : w = 0
  · simp [hw, wRaw]
  · have hterm : RadialSpine.wTerm w ≠ 0 :=
      (RadialSpine.wTerm_eq_zero_iff w).not.mpr hw
    rw [wRaw, pruneRatio_zero_time_of_ne hterm,
      RadialSpine.radialMultiplier_one, one_mul]

@[simp] theorem rawNormSq_zero_time (q : RadialSpine.Spine) : rawNormSq 0 q = 1 := by
  rw [rawNormSq, zRaw_zero_time, wRaw_zero_time]
  exact q.1.1.2

@[simp] theorem normalizingFactor_zero_time (q : RadialSpine.Spine) :
    normalizingFactor 0 q = 1 := by
  rw [normalizingFactor, rawNorm, rawNormSq_zero_time]
  simp

@[simp] theorem pruneSpine_zero_time (q : RadialSpine.Spine) : pruneSpine 0 q = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change (normalizingFactor 0 q : ℂ) * zRaw 0 q.1.1.1.1 = q.1.1.1.1
    simp
  · change (normalizingFactor 0 q : ℂ) * wRaw 0 q.1.1.1.2 = q.1.1.1.2
    simp

theorem pruneRatio_eq_one_of_re_nonneg (s : ℝ) {a : ℂ}
    (ha0 : a ≠ 0) (ha : 0 ≤ a.re) : pruneRatio s a = 1 := by
  rw [pruneRatio_of_ne s ha0, prune_eq_of_re_nonneg s ha, div_self ha0]

theorem zRaw_eq_of_term_re_nonneg (s : ℝ) {z : ℂ}
    (hz : 0 ≤ (RadialSpine.zTerm z).re) : zRaw s z = z := by
  by_cases hz0 : z = 0
  · simp [hz0, zRaw]
  · have hterm : RadialSpine.zTerm z ≠ 0 :=
      (RadialSpine.zTerm_eq_zero_iff z).not.mpr hz0
    rw [zRaw, pruneRatio_eq_one_of_re_nonneg s hterm hz]
    simp

theorem wRaw_eq_of_term_re_nonneg (s : ℝ) {w : ℂ}
    (hw : 0 ≤ (RadialSpine.wTerm w).re) : wRaw s w = w := by
  by_cases hw0 : w = 0
  · simp [hw0, wRaw]
  · have hterm : RadialSpine.wTerm w ≠ 0 :=
      (RadialSpine.wTerm_eq_zero_iff w).not.mpr hw0
    rw [wRaw, pruneRatio_eq_one_of_re_nonneg s hterm hw,
      RadialSpine.radialMultiplier_one, one_mul]

theorem pruneSpine_core (s : unitInterval) (q : RadialCore.Core) :
    pruneSpine s q.1 = q.1 := by
  have hz := zRaw_eq_of_term_re_nonneg (s : ℝ) q.2.1
  have hw := wRaw_eq_of_term_re_nonneg (s : ℝ) q.2.2
  have hrawSq : rawNormSq (s : ℝ) q.1 = 1 := by
    rw [rawNormSq, hz, hw]
    exact q.1.1.1.2
  have hfactor : normalizingFactor (s : ℝ) q.1 = 1 := by
    rw [normalizingFactor, rawNorm, hrawSq]
    simp
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change (normalizingFactor (s : ℝ) q.1 : ℂ) *
      zRaw (s : ℝ) q.1.1.1.1.1 =
      q.1.1.1.1.1
    rw [hfactor, ofReal_one, one_mul, hz]
  · change (normalizingFactor (s : ℝ) q.1 : ℂ) *
      wRaw (s : ℝ) q.1.1.1.1.2 =
      q.1.1.1.1.2
    rw [hfactor, ofReal_one, one_mul, hw]

def coreInclusion : C(RadialCore.Core, RadialSpine.Spine) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def coreRetraction : C(RadialSpine.Spine, RadialCore.Core) :=
  ⟨spineRetraction, by
    apply Continuous.subtype_mk
    have hone : Continuous (fun _ : RadialSpine.Spine => (1 : unitInterval)) :=
      continuous_const
    have hcomp := pruneSpine_continuous.comp (hone.prodMk continuous_id)
    simpa only [Function.comp_def, id_eq, spineRetraction] using hcomp⟩

@[simp] theorem coreRetraction_inclusion (q : RadialCore.Core) :
    coreRetraction (coreInclusion q) = q := by
  apply Subtype.ext
  exact pruneSpine_core 1 q

def pruneHomotopy :
    (ContinuousMap.id RadialSpine.Spine).Homotopy
      (coreInclusion.comp coreRetraction) :=
  ContinuousMap.Homotopy.mk
    ⟨fun x : unitInterval × RadialSpine.Spine => pruneSpine x.1 x.2,
      pruneSpine_continuous⟩
    (by intro q; exact pruneSpine_zero_time q)
    (by intro q; rfl)

end

end Submission.CoreDeformation
