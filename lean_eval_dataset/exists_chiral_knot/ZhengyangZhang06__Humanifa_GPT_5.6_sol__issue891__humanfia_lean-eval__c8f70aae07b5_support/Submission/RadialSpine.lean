import Submission.RadialMilnor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Complex

namespace Submission.RadialSpine

noncomputable section

def zTerm (z : ℂ) : ℂ := I * (16 * z ^ 2)

def wTerm (w : ℂ) : ℂ := I * (9 * RadialMilnor.radialCube w)

theorem zTerm_continuous : Continuous zTerm := by
  unfold zTerm
  fun_prop

theorem wTerm_continuous : Continuous wTerm := by
  exact continuous_const.mul
    (continuous_const.mul RadialMilnor.radialCube_continuous)

theorem polynomial_eq_terms (q : RadialMilnor.CSphere) :
    RadialMilnor.polynomial q = zTerm q.1.1 + wTerm q.1.2 := by
  simp [RadialMilnor.polynomial, RadialMilnor.basePolynomial, zTerm, wTerm]
  ring

@[simp] theorem zTerm_zero : zTerm 0 = 0 := by simp [zTerm]

@[simp] theorem wTerm_zero : wTerm 0 = 0 := by simp [wTerm]

theorem norm_zTerm (z : ℂ) : ‖zTerm z‖ = 16 * ‖z‖ ^ 2 := by
  simp [zTerm, norm_pow]

theorem norm_wTerm (w : ℂ) : ‖wTerm w‖ = 9 * ‖w‖ ^ 2 := by
  simp [wTerm, RadialMilnor.norm_radialCube]

theorem zTerm_eq_zero_iff (z : ℂ) : zTerm z = 0 ↔ z = 0 := by
  rw [← norm_eq_zero, norm_zTerm]
  constructor
  · intro h
    have hs : ‖z‖ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hs' : ‖z‖ * ‖z‖ = 0 := by simpa [pow_two] using hs
    rcases mul_eq_zero.mp hs' with hz | hz <;> exact norm_eq_zero.mp hz
  · intro h
    rw [h]
    norm_num

theorem wTerm_eq_zero_iff (w : ℂ) : wTerm w = 0 ↔ w = 0 := by
  rw [← norm_eq_zero, norm_wTerm]
  constructor
  · intro h
    have hs : ‖w‖ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hs' : ‖w‖ * ‖w‖ = 0 := by simpa [pow_two] using hs
    rcases mul_eq_zero.mp hs' with hw | hw <;> exact norm_eq_zero.mp hw
  · intro h
    rw [h]
    norm_num

def flatten (s : ℝ) (a : ℂ) : ℂ :=
  (a.re : ℂ) + ((1 - s) * a.im : ℝ) * I

@[simp] theorem flatten_re (s : ℝ) (a : ℂ) : (flatten s a).re = a.re := by
  simp [flatten]

@[simp] theorem flatten_im (s : ℝ) (a : ℂ) :
    (flatten s a).im = (1 - s) * a.im := by
  simp [flatten]

@[simp] theorem flatten_zero (s : ℝ) : flatten s 0 = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem flatten_zero_time (a : ℂ) : flatten 0 a = a := by
  apply Complex.ext <;> simp

theorem flatten_add (s : ℝ) (a b : ℂ) :
    flatten s (a + b) = flatten s a + flatten s b := by
  apply Complex.ext <;> simp [flatten]
  ring

theorem flatten_continuous : Continuous (fun x : ℝ × ℂ => flatten x.1 x.2) := by
  unfold flatten
  fun_prop

theorem norm_flatten_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℂ) :
    ‖flatten s a‖ ≤ ‖a‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp [flatten, normSq_apply]
  have hfactor : (1 - s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  nlinarith [sq_nonneg a.im, mul_le_mul_of_nonneg_right hfactor (sq_nonneg a.im)]

def flattenRatio (s : ℝ) (a : ℂ) : ℂ :=
  if a = 0 then 0 else flatten s a / a

@[simp] theorem flattenRatio_zero (s : ℝ) : flattenRatio s 0 = 0 := by
  simp [flattenRatio]

theorem flattenRatio_of_ne (s : ℝ) {a : ℂ} (ha : a ≠ 0) :
    flattenRatio s a = flatten s a / a := by
  simp [flattenRatio, ha]

theorem flattenRatio_mul (s : ℝ) (a : ℂ) :
    flattenRatio s a * a = flatten s a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [flattenRatio_of_ne s ha, div_mul_cancel₀ _ ha]

theorem flattenRatio_continuousAt_of_ne {x : ℝ × ℂ} (hx : x.2 ≠ 0) :
    ContinuousAt (fun y : ℝ × ℂ => flattenRatio y.1 y.2) x := by
  have hformula : ContinuousAt (fun y : ℝ × ℂ => flatten y.1 y.2 / y.2) x := by
    exact flatten_continuous.continuousAt.div continuous_snd.continuousAt hx
  apply hformula.congr_of_eventuallyEq
  filter_upwards [continuous_snd.tendsto x |>.eventually (compl_singleton_mem_nhds_iff.mpr hx)]
    with y hy
  have hy0 : y.2 ≠ 0 := by simpa using hy
  exact flattenRatio_of_ne y.1 hy0

theorem flattenRatio_re_nonneg (s : ℝ) (hs1 : s ≤ 1) (a : ℂ) :
    0 ≤ (flattenRatio s a).re := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [flattenRatio_of_ne s ha, Complex.div_re]
    rw [flatten_re, flatten_im, ← add_div]
    apply div_nonneg
    · nlinarith [sq_nonneg a.re, sq_nonneg a.im]
    · exact (normSq_pos.mpr ha).le

theorem norm_flattenRatio_le_one
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℂ) :
    ‖flattenRatio s a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [flattenRatio_of_ne s ha, norm_div]
    exact (div_le_one (norm_pos_iff.mpr ha)).2 (norm_flatten_le s hs0 hs1 a)

def zRaw (s : ℝ) (z : ℂ) : ℂ :=
  flattenRatio s (zTerm z) ^ ((2 : ℂ)⁻¹) * z

theorem zTerm_zRaw (s : ℝ) (z : ℂ) :
    zTerm (zRaw s z) = flatten s (zTerm z) := by
  by_cases hz : z = 0
  · simp [hz, zRaw]
  · have hterm : zTerm z ≠ 0 := (zTerm_eq_zero_iff z).not.mpr hz
    have hroot :
        (flattenRatio s (zTerm z) ^ ((2 : ℂ)⁻¹)) ^ 2 =
          flattenRatio s (zTerm z) :=
      Complex.cpow_nat_inv_pow _ (by norm_num)
    rw [zRaw, zTerm, mul_pow, hroot]
    calc
      I * (16 * (flattenRatio s (zTerm z) * z ^ 2)) =
          flattenRatio s (zTerm z) * zTerm z := by simp [zTerm]; ring
      _ = flatten s (zTerm z) := flattenRatio_mul s (zTerm z)

def wRaw (s : ℝ) (w : ℂ) : ℂ :=
  RadialMilnor.radialMultiplier (flattenRatio s (wTerm w)) * w

theorem wTerm_wRaw (s : ℝ) (w : ℂ) :
    wTerm (wRaw s w) = flatten s (wTerm w) := by
  rw [wRaw, wTerm, RadialMilnor.radialCube_mul_radialMultiplier]
  change I * (9 * (flattenRatio s (wTerm w) * RadialMilnor.radialCube w)) = _
  rw [show I * (9 * (flattenRatio s (wTerm w) *
      RadialMilnor.radialCube w)) = flattenRatio s (wTerm w) * wTerm w by
    simp [wTerm]
    ring]
  exact flattenRatio_mul s (wTerm w)

theorem norm_zRaw_le
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : ℂ) :
    ‖zRaw s z‖ ≤ ‖z‖ := by
  have hterm := congrArg norm (zTerm_zRaw s z)
  rw [norm_zTerm] at hterm
  have hflat := norm_flatten_le s hs0 hs1 (zTerm z)
  rw [norm_zTerm] at hflat
  nlinarith [norm_nonneg (zRaw s z), norm_nonneg z]

theorem norm_wRaw_le
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (w : ℂ) :
    ‖wRaw s w‖ ≤ ‖w‖ := by
  have hterm := congrArg norm (wTerm_wRaw s w)
  rw [norm_wTerm] at hterm
  have hflat := norm_flatten_le s hs0 hs1 (wTerm w)
  rw [norm_wTerm] at hflat
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
      (continuous_snd.norm : Continuous (fun x : unitInterval × ℂ => ‖x.2‖)).continuousAt
    simpa using h
  · have hterm : zTerm z ≠ 0 := (zTerm_eq_zero_iff z).not.mpr hz
    have hpair : ContinuousAt
        (fun x : unitInterval × ℂ => ((x.1 : ℝ), zTerm x.2)) (s, z) := by
      exact (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
        (zTerm_continuous.continuousAt.comp continuous_snd.continuousAt)
    have hratio : ContinuousAt
        (fun x : unitInterval × ℂ => flattenRatio (x.1 : ℝ) (zTerm x.2)) (s, z) :=
      (flattenRatio_continuousAt_of_ne hterm).comp hpair
    have hrootAt : ContinuousAt
        (fun a : ℂ => a ^ ((2 : ℂ)⁻¹)) (flattenRatio (s : ℝ) (zTerm z)) :=
      Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (flattenRatio_re_nonneg (s : ℝ) s.2.2 (zTerm z))) (by norm_num)
    have hrootComp : ContinuousAt
        (fun x : unitInterval × ℂ =>
          flattenRatio (x.1 : ℝ) (zTerm x.2) ^ ((2 : ℂ)⁻¹)) (s, z) :=
      Filter.Tendsto.comp hrootAt hratio
    exact hrootComp.mul continuous_snd.continuousAt

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
      (continuous_snd.norm : Continuous (fun x : unitInterval × ℂ => ‖x.2‖)).continuousAt
    simpa using h
  · have hterm : wTerm w ≠ 0 := (wTerm_eq_zero_iff w).not.mpr hw
    have hpair : ContinuousAt
        (fun x : unitInterval × ℂ => ((x.1 : ℝ), wTerm x.2)) (s, w) := by
      exact (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
        (wTerm_continuous.continuousAt.comp continuous_snd.continuousAt)
    have hratio : ContinuousAt
        (fun x : unitInterval × ℂ => flattenRatio (x.1 : ℝ) (wTerm x.2)) (s, w) :=
      (flattenRatio_continuousAt_of_ne hterm).comp hpair
    have hmultAt : ContinuousAt RadialMilnor.radialMultiplier
        (flattenRatio (s : ℝ) (wTerm w)) :=
      RadialMilnor.radialMultiplier_continuousAt_of_re_nonneg
        (flattenRatio_re_nonneg (s : ℝ) s.2.2 (wTerm w))
    have hmultComp : ContinuousAt
        (fun x : unitInterval × ℂ =>
          RadialMilnor.radialMultiplier (flattenRatio (x.1 : ℝ) (wTerm x.2)))
        (s, w) := Filter.Tendsto.comp hmultAt hratio
    exact hmultComp.mul continuous_snd.continuousAt

theorem raw_terms_add (s : ℝ) (q : RadialMilnor.Fiber) :
    zTerm (zRaw s q.1.1.1) + wTerm (wRaw s q.1.1.2) =
      RadialMilnor.polynomial q.1 := by
  rw [zTerm_zRaw, wTerm_wRaw, ← flatten_add, ← polynomial_eq_terms]
  apply Complex.ext
  · simp
  · simp [q.2.2]

def rawNormSq (s : ℝ) (q : RadialMilnor.Fiber) : ℝ :=
  normSq (zRaw s q.1.1.1) + normSq (wRaw s q.1.1.2)

theorem rawNormSq_pos (s : ℝ) (q : RadialMilnor.Fiber) :
    0 < rawNormSq s q := by
  have hnonzero : zRaw s q.1.1.1 ≠ 0 ∨ wRaw s q.1.1.2 ≠ 0 := by
    by_contra h
    push Not at h
    have hpoly : RadialMilnor.polynomial q.1 = 0 := by
      rw [← raw_terms_add s q, h.1, h.2]
      simp
    have hre := congrArg Complex.re hpoly
    simp [q.2.1.ne'] at hre
  rcases hnonzero with hz | hw
  · exact add_pos_of_pos_of_nonneg (normSq_pos.mpr hz) (normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (normSq_nonneg _) (normSq_pos.mpr hw)

def rawNorm (s : ℝ) (q : RadialMilnor.Fiber) : ℝ :=
  Real.sqrt (rawNormSq s q)

theorem rawNorm_pos (s : ℝ) (q : RadialMilnor.Fiber) : 0 < rawNorm s q :=
  Real.sqrt_pos.2 (rawNormSq_pos s q)

theorem rawNorm_sq (s : ℝ) (q : RadialMilnor.Fiber) :
    rawNorm s q ^ 2 = rawNormSq s q :=
  Real.sq_sqrt (rawNormSq_pos s q).le

def normalizingFactor (s : ℝ) (q : RadialMilnor.Fiber) : ℝ :=
  (rawNorm s q)⁻¹

theorem normalizingFactor_pos (s : ℝ) (q : RadialMilnor.Fiber) :
    0 < normalizingFactor s q := by
  exact inv_pos.mpr (rawNorm_pos s q)

theorem zTerm_smul_nonneg (r : ℝ) (_hr : 0 ≤ r) (z : ℂ) :
    zTerm ((r : ℂ) * z) = (r : ℂ) ^ 2 * zTerm z := by
  simp [zTerm, mul_pow]
  ring

theorem wTerm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (w : ℂ) :
    wTerm ((r : ℂ) * w) = (r : ℂ) ^ 2 * wTerm w := by
  rw [wTerm, RadialMilnor.radialCube_smul_of_nonneg r hr]
  change I * (9 * ((r : ℂ) ^ 2 * RadialMilnor.radialCube w)) =
    (r : ℂ) ^ 2 * (I * (9 * RadialMilnor.radialCube w))
  ring

def flattenSphere (s : ℝ) (q : RadialMilnor.Fiber) : RadialMilnor.CSphere :=
  ⟨((normalizingFactor s q : ℂ) * zRaw s q.1.1.1,
      (normalizingFactor s q : ℂ) * wRaw s q.1.1.2), by
    have hnorm : rawNorm s q ≠ 0 := ne_of_gt (rawNorm_pos s q)
    change normSq ((normalizingFactor s q : ℂ) * zRaw s q.1.1.1) +
        normSq ((normalizingFactor s q : ℂ) * wRaw s q.1.1.2) = 1
    rw [normSq_mul, normSq_mul, normSq_ofReal]
    rw [← mul_add, ← rawNormSq, normalizingFactor]
    rw [← rawNorm_sq]
    field_simp⟩

theorem polynomial_flattenSphere (s : ℝ) (q : RadialMilnor.Fiber) :
    RadialMilnor.polynomial (flattenSphere s q) =
      (normalizingFactor s q : ℂ) ^ 2 * RadialMilnor.polynomial q.1 := by
  rw [polynomial_eq_terms]
  change zTerm ((normalizingFactor s q : ℂ) * zRaw s q.1.1.1) +
      wTerm ((normalizingFactor s q : ℂ) * wRaw s q.1.1.2) = _
  rw [zTerm_smul_nonneg _ (normalizingFactor_pos s q).le,
    wTerm_smul_nonneg _ (normalizingFactor_pos s q).le, ← mul_add, raw_terms_add]

def flattenFiber (s : ℝ) (q : RadialMilnor.Fiber) : RadialMilnor.Fiber :=
  ⟨flattenSphere s q, by
    rw [polynomial_flattenSphere]
    have hfactorSq : 0 < normalizingFactor s q ^ 2 :=
      sq_pos_of_pos (normalizingFactor_pos s q)
    constructor
    · simpa [mul_re, pow_two] using mul_pos hfactorSq q.2.1
    · simp [mul_im, pow_two, q.2.2]⟩

theorem flattenFiber_terms_real (q : RadialMilnor.Fiber) :
    (zTerm (flattenFiber 1 q).1.1.1).im = 0 ∧
      (wTerm (flattenFiber 1 q).1.1.2).im = 0 := by
  change (zTerm ((normalizingFactor 1 q : ℂ) * zRaw 1 q.1.1.1)).im = 0 ∧
    (wTerm ((normalizingFactor 1 q : ℂ) * wRaw 1 q.1.1.2)).im = 0
  rw [zTerm_smul_nonneg _ (normalizingFactor_pos 1 q).le,
    wTerm_smul_nonneg _ (normalizingFactor_pos 1 q).le,
    zTerm_zRaw, wTerm_wRaw]
  constructor <;> simp [mul_im, pow_two]

def Spine := {q : RadialMilnor.Fiber //
  (zTerm q.1.1.1).im = 0 ∧ (wTerm q.1.1.2).im = 0}

instance : TopologicalSpace Spine := by
  unfold Spine
  infer_instance

def retractToSpine (q : RadialMilnor.Fiber) : Spine :=
  ⟨flattenFiber 1 q, flattenFiber_terms_real q⟩

theorem flattenFiber_continuous :
    Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      flattenFiber (x.1 : ℝ) x.2) := by
  have hzCoord : Continuous (fun x : unitInterval × RadialMilnor.Fiber => x.2.1.1.1) := by
    fun_prop
  have hwCoord : Continuous (fun x : unitInterval × RadialMilnor.Fiber => x.2.1.1.2) := by
    fun_prop
  have hzPair : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      (x.1, x.2.1.1.1)) := continuous_fst.prodMk hzCoord
  have hwPair : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      (x.1, x.2.1.1.2)) := continuous_fst.prodMk hwCoord
  have hzRawComp := zRaw_continuous.comp hzPair
  have hwRawComp := wRaw_continuous.comp hwPair
  have hzRaw : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      zRaw (x.1 : ℝ) x.2.1.1.1) := by
    simpa only [Function.comp_def] using hzRawComp
  have hwRaw : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      wRaw (x.1 : ℝ) x.2.1.1.2) := by
    simpa only [Function.comp_def] using hwRawComp
  have hrawSq : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      rawNormSq (x.1 : ℝ) x.2) := by
    unfold rawNormSq
    exact (continuous_normSq.comp hzRaw).add (continuous_normSq.comp hwRaw)
  have hrawNorm : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      rawNorm (x.1 : ℝ) x.2) := by
    exact Real.continuous_sqrt.comp hrawSq
  have hfactor : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
      normalizingFactor (x.1 : ℝ) x.2) := by
    unfold normalizingFactor
    exact hrawNorm.inv₀ (fun x => ne_of_gt (rawNorm_pos (x.1 : ℝ) x.2))
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp hfactor).mul hzRaw).prodMk
    ((Complex.continuous_ofReal.comp hfactor).mul hwRaw)

theorem flattenRatio_zero_time_of_ne {a : ℂ} (ha : a ≠ 0) :
    flattenRatio 0 a = 1 := by
  rw [flattenRatio_of_ne 0 ha, flatten_zero_time, div_self ha]

theorem zRaw_zero_time (z : ℂ) : zRaw 0 z = z := by
  by_cases hz : z = 0
  · simp [hz, zRaw]
  · have hterm : zTerm z ≠ 0 := (zTerm_eq_zero_iff z).not.mpr hz
    rw [zRaw, flattenRatio_zero_time_of_ne hterm]
    simp

@[simp] theorem radialMultiplier_one : RadialMilnor.radialMultiplier 1 = 1 := by
  simp [RadialMilnor.radialMultiplier, RadialMilnor.cubeRoot]

theorem wRaw_zero_time (w : ℂ) : wRaw 0 w = w := by
  by_cases hw : w = 0
  · simp [hw, wRaw]
  · have hterm : wTerm w ≠ 0 := (wTerm_eq_zero_iff w).not.mpr hw
    rw [wRaw, flattenRatio_zero_time_of_ne hterm, radialMultiplier_one, one_mul]

theorem rawNormSq_zero_time (q : RadialMilnor.Fiber) : rawNormSq 0 q = 1 := by
  rw [rawNormSq, zRaw_zero_time, wRaw_zero_time]
  exact q.1.2

@[simp] theorem normalizingFactor_zero_time (q : RadialMilnor.Fiber) :
    normalizingFactor 0 q = 1 := by
  rw [normalizingFactor, rawNorm, rawNormSq_zero_time]
  simp

@[simp] theorem flattenFiber_zero_time (q : RadialMilnor.Fiber) :
    flattenFiber 0 q = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change (normalizingFactor 0 q : ℂ) * zRaw 0 q.1.1.1 = q.1.1.1
    rw [normalizingFactor_zero_time, ofReal_one, one_mul, zRaw_zero_time]
  · change (normalizingFactor 0 q : ℂ) * wRaw 0 q.1.1.2 = q.1.1.2
    rw [normalizingFactor_zero_time, ofReal_one, one_mul, wRaw_zero_time]

theorem flatten_eq_of_im_zero (s : ℝ) {a : ℂ} (ha : a.im = 0) :
    flatten s a = a := by
  apply Complex.ext
  · simp
  · simp [ha]

theorem flattenRatio_eq_one_of_im_zero (s : ℝ) {a : ℂ}
    (ha0 : a ≠ 0) (ha : a.im = 0) : flattenRatio s a = 1 := by
  rw [flattenRatio_of_ne s ha0, flatten_eq_of_im_zero s ha, div_self ha0]

theorem zRaw_eq_of_term_im_zero (s : ℝ) {z : ℂ} (hzIm : (zTerm z).im = 0) :
    zRaw s z = z := by
  by_cases hz : z = 0
  · simp [hz, zRaw]
  · have hterm : zTerm z ≠ 0 := (zTerm_eq_zero_iff z).not.mpr hz
    rw [zRaw, flattenRatio_eq_one_of_im_zero s hterm hzIm]
    simp

theorem wRaw_eq_of_term_im_zero (s : ℝ) {w : ℂ} (hwIm : (wTerm w).im = 0) :
    wRaw s w = w := by
  by_cases hw : w = 0
  · simp [hw, wRaw]
  · have hterm : wTerm w ≠ 0 := (wTerm_eq_zero_iff w).not.mpr hw
    rw [wRaw, flattenRatio_eq_one_of_im_zero s hterm hwIm,
      radialMultiplier_one, one_mul]

theorem flattenFiber_spine (s : ℝ) (q : Spine) : flattenFiber s q.1 = q.1 := by
  have hz := zRaw_eq_of_term_im_zero s q.2.1
  have hw := wRaw_eq_of_term_im_zero s q.2.2
  have hrawSq : rawNormSq s q.1 = 1 := by
    rw [rawNormSq, hz, hw]
    exact q.1.1.2
  have hfactor : normalizingFactor s q.1 = 1 := by
    rw [normalizingFactor, rawNorm, hrawSq]
    simp
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change (normalizingFactor s q.1 : ℂ) * zRaw s q.1.1.1.1 = q.1.1.1.1
    rw [hfactor, ofReal_one, one_mul, hz]
  · change (normalizingFactor s q.1 : ℂ) * wRaw s q.1.1.1.2 = q.1.1.1.2
    rw [hfactor, ofReal_one, one_mul, hw]

def spineInclusion : C(Spine, RadialMilnor.Fiber) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def spineRetraction : C(RadialMilnor.Fiber, Spine) :=
  ⟨retractToSpine, by
    have hone : Continuous (fun _ : RadialMilnor.Fiber => (1 : unitInterval)) :=
      continuous_const
    have hpair : Continuous (fun q : RadialMilnor.Fiber => ((1 : unitInterval), q)) :=
      hone.prodMk continuous_id
    have hcomp := flattenFiber_continuous.comp hpair
    have hline : Continuous (fun q : RadialMilnor.Fiber => flattenFiber 1 q) := by
      simpa [Function.comp_def] using hcomp
    apply Continuous.subtype_mk
    simpa only [retractToSpine] using hline⟩

@[simp] theorem spineRetraction_inclusion (q : Spine) :
    spineRetraction (spineInclusion q) = q := by
  apply Subtype.ext
  exact flattenFiber_spine 1 q

def flattenHomotopy :
    (ContinuousMap.id RadialMilnor.Fiber).Homotopy
      (spineInclusion.comp spineRetraction) :=
  ContinuousMap.Homotopy.mk
    ⟨fun x : unitInterval × RadialMilnor.Fiber => flattenFiber (x.1 : ℝ) x.2,
      flattenFiber_continuous⟩
    (by intro q; exact flattenFiber_zero_time q)
    (by intro q; rfl)

end

end Submission.RadialSpine
