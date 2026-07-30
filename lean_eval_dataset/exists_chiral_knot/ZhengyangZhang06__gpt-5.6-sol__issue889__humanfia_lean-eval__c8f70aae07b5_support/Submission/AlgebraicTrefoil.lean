import Submission.Detector

open LeanEval.KnotTheory
open Complex Set

namespace Submission.AlgebraicTrefoil

noncomputable section

def radiusSq (p : R3) : ℝ :=
  p.ofLp 0 ^ 2 + p.ofLp 1 ^ 2 + p.ofLp 2 ^ 2

def sphereDenom (p : R3) : ℝ := radiusSq p + 1

def inverseZ (p : R3) : ℂ :=
  ⟨2 * p.ofLp 0 / sphereDenom p, 2 * p.ofLp 1 / sphereDenom p⟩

def inverseW (p : R3) : ℂ :=
  ⟨2 * p.ofLp 2 / sphereDenom p, (radiusSq p - 1) / sphereDenom p⟩

def stereo (z w : ℂ) : R3 :=
  WithLp.toLp 2 ![z.re / (1 - w.im), z.im / (1 - w.im), w.re / (1 - w.im)]

def sphereCurveZ (t : ℝ) : ℂ :=
  ⟨(3 / 5) * Real.cos (3 * t), (3 / 5) * Real.sin (3 * t)⟩

def sphereCurveW (t : ℝ) : ℂ :=
  ⟨(-4 / 5) * Real.cos (2 * t), (-4 / 5) * Real.sin (2 * t)⟩

def curve (t : ℝ) : R3 := stereo (sphereCurveZ t) (sphereCurveW t)

def detectorMap (p : R3) : ℂ := 64 * inverseZ p ^ 2 + 45 * inverseW p ^ 3

theorem sphereDenom_pos (p : R3) : 0 < sphereDenom p := by
  dsimp [sphereDenom, radiusSq]
  positivity

theorem sphereDenom_ne (p : R3) : sphereDenom p ≠ 0 :=
  ne_of_gt (sphereDenom_pos p)

theorem sphereCurveW_im_lt_one (t : ℝ) : (sphereCurveW t).im < 1 := by
  simp [sphereCurveW]
  nlinarith [Real.neg_one_le_sin (2 * t), Real.sin_le_one (2 * t)]

theorem sphereCurveW_im_ne_one (t : ℝ) : (sphereCurveW t).im ≠ 1 :=
  ne_of_lt (sphereCurveW_im_lt_one t)

theorem sphereCurve_normSq (t : ℝ) :
    normSq (sphereCurveZ t) + normSq (sphereCurveW t) = 1 := by
  simp [sphereCurveZ, sphereCurveW, normSq_apply]
  nlinarith [Real.sin_sq_add_cos_sq (3 * t), Real.sin_sq_add_cos_sq (2 * t)]

theorem inverse_stereo {z w : ℂ}
    (hsphere : normSq z + normSq w = 1) (hne : w.im ≠ 1) :
    inverseZ (stereo z w) = z ∧ inverseW (stereo z w) = w := by
  have hk : 1 - w.im ≠ 0 := sub_ne_zero.mpr hne.symm
  simp [normSq_apply] at hsphere
  have hden :
      z.re ^ 2 + z.im ^ 2 + w.re ^ 2 + (1 - w.im) ^ 2 =
        2 * (1 - w.im) := by
    nlinarith
  constructor <;> apply Complex.ext
  · simp [inverseZ, stereo, sphereDenom, radiusSq]
    field_simp
    rw [hden]
    ring
  · simp [inverseZ, stereo, sphereDenom, radiusSq]
    field_simp
    rw [hden]
    ring
  · simp [inverseW, stereo, sphereDenom, radiusSq]
    field_simp
    rw [hden]
    ring
  · simp [inverseW, stereo, sphereDenom, radiusSq]
    field_simp
    nlinarith

theorem inverseZ_curve (t : ℝ) : inverseZ (curve t) = sphereCurveZ t :=
  (inverse_stereo (sphereCurve_normSq t) (sphereCurveW_im_ne_one t)).1

theorem inverseW_curve (t : ℝ) : inverseW (curve t) = sphereCurveW t :=
  (inverse_stereo (sphereCurve_normSq t) (sphereCurveW_im_ne_one t)).2

theorem sphereCurveZ_eq_exp (t : ℝ) :
    sphereCurveZ t = (3 / 5 : ℂ) * Complex.exp (((3 * t : ℝ) : ℂ) * I) := by
  have harg : (3 : ℂ) * (t : ℂ) * I = ((3 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  apply Complex.ext
  · simp [sphereCurveZ]
    rw [harg, Complex.exp_ofReal_mul_I_re]
  · simp [sphereCurveZ]
    rw [harg, Complex.exp_ofReal_mul_I_im]

theorem sphereCurveW_eq_exp (t : ℝ) :
    sphereCurveW t = (-4 / 5 : ℂ) * Complex.exp (((2 * t : ℝ) : ℂ) * I) := by
  have harg : (2 : ℂ) * (t : ℂ) * I = ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  apply Complex.ext
  · simp [sphereCurveW]
    rw [harg, Complex.exp_ofReal_mul_I_re]
  · simp [sphereCurveW]
    rw [harg, Complex.exp_ofReal_mul_I_im]

theorem detectorMap_curve (t : ℝ) : detectorMap (curve t) = 0 := by
  rw [detectorMap, inverseZ_curve, inverseW_curve, sphereCurveZ_eq_exp,
    sphereCurveW_eq_exp]
  have h2 : Complex.exp (((3 * t : ℝ) : ℂ) * I) ^ 2 =
      Complex.exp (((6 * t : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 : Complex.exp (((2 * t : ℝ) : ℂ) * I) ^ 3 =
      Complex.exp (((6 * t : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, h2, h3]
  ring

theorem inverse_normSq (p : R3) : normSq (inverseZ p) + normSq (inverseW p) = 1 := by
  simp [inverseZ, inverseW, normSq_apply, sphereDenom, radiusSq]
  field_simp [sphereDenom_ne]
  ring

theorem stereo_inverse (p : R3) : stereo (inverseZ p) (inverseW p) = p := by
  ext i
  fin_cases i <;>
    simp [stereo, inverseZ, inverseW, sphereDenom, radiusSq] <;>
    field_simp [sphereDenom_ne] <;>
    ring

theorem normSq_eq_of_polynomial_zero {z w : ℂ}
    (hsphere : normSq z + normSq w = 1)
    (hzero : 64 * z ^ 2 + 45 * w ^ 3 = 0) :
    normSq z = 9 / 25 ∧ normSq w = 16 / 25 := by
  have heq : (64 : ℂ) * z ^ 2 = -(45 : ℂ) * w ^ 3 := by
    simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hzero
  have hnorm := congrArg normSq heq
  simp only [map_mul, map_pow, normSq_ofNat, normSq_neg] at hnorm
  have hquad : 0 < 81 * normSq w ^ 2 - 112 * normSq w + 256 := by
    nlinarith [sq_nonneg (81 * normSq w - 56)]
  have hfactor :
      (25 * normSq w - 16) *
        (81 * normSq w ^ 2 - 112 * normSq w + 256) = 0 := by
    nlinarith
  have hw : normSq w = 16 / 25 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  exact ⟨by linarith, hw⟩

theorem exists_sphereCurve_of_polynomial_zero {z w : ℂ}
    (hsphere : normSq z + normSq w = 1)
    (hzero : 64 * z ^ 2 + 45 * w ^ 3 = 0) :
    ∃ t : ℝ, z = sphereCurveZ t ∧ w = sphereCurveW t := by
  obtain ⟨hz, hw⟩ := normSq_eq_of_polynomial_zero hsphere hzero
  let Z : ℂ := (5 / 3 : ℂ) * z
  let W : ℂ := (-5 / 4 : ℂ) * w
  have hZnormSq : normSq Z = 1 := by
    simp [Z, normSq_mul, hz]
    norm_num
  have hWnormSq : normSq W = 1 := by
    simp [W, normSq_mul, hw]
    norm_num
  have hWne : W ≠ 0 := by
    intro h
    rw [h, map_zero] at hWnormSq
    norm_num at hWnormSq
  have hz2 : z ^ 2 = -(45 / 64 : ℂ) * w ^ 3 := by
    have heq := eq_neg_of_add_eq_zero_left hzero
    apply (mul_left_cancel₀ (by norm_num : (64 : ℂ) ≠ 0))
    rw [heq]
    ring
  have hphase : Z ^ 2 = W ^ 3 := by
    dsimp [Z, W]
    rw [mul_pow, mul_pow, hz2]
    ring
  let u : ℂ := Z / W
  have hunormSq : normSq u = 1 := by
    dsimp [u]
    rw [normSq_div, hZnormSq, hWnormSq, div_one]
  have hunorm : ‖u‖ = 1 := by
    rw [Complex.norm_def, hunormSq, Real.sqrt_one]
  have hu2 : u ^ 2 = W := by
    dsimp [u]
    field_simp [hWne]
    simpa [pow_succ] using hphase
  have hu3 : u ^ 3 = Z := by
    calc
      u ^ 3 = u * u ^ 2 := by ring
      _ = u * W := by rw [hu2]
      _ = Z := by
        dsimp [u]
        field_simp [hWne]
  rcases (Complex.norm_eq_one_iff u).mp hunorm with ⟨t, ht⟩
  have hpow2 : Complex.exp (((2 * t : ℝ) : ℂ) * I) = u ^ 2 := by
    rw [show (((2 * t : ℝ) : ℂ) * I) = (2 : ℂ) * ((t : ℂ) * I) by
      push_cast
      ring]
    calc
      Complex.exp ((2 : ℂ) * ((t : ℂ) * I)) =
          Complex.exp ((t : ℂ) * I) ^ 2 := by
        simpa using Complex.exp_nat_mul ((t : ℂ) * I) 2
      _ = u ^ 2 := by rw [ht]
  have hpow3 : Complex.exp (((3 * t : ℝ) : ℂ) * I) = u ^ 3 := by
    rw [show (((3 * t : ℝ) : ℂ) * I) = (3 : ℂ) * ((t : ℂ) * I) by
      push_cast
      ring]
    calc
      Complex.exp ((3 : ℂ) * ((t : ℂ) * I)) =
          Complex.exp ((t : ℂ) * I) ^ 3 := by
        simpa using Complex.exp_nat_mul ((t : ℂ) * I) 3
      _ = u ^ 3 := by rw [ht]
  refine ⟨t, ?_, ?_⟩
  · rw [sphereCurveZ_eq_exp, hpow3, hu3]
    dsimp [Z]
    ring
  · rw [sphereCurveW_eq_exp, hpow2, hu2]
    dsimp [W]
    ring

theorem detectorMap_zero_iff (p : R3) :
    detectorMap p = 0 ↔ p ∈ Set.range curve := by
  constructor
  · intro hzero
    obtain ⟨t, hz, hw⟩ :=
      exists_sphereCurve_of_polynomial_zero (inverse_normSq p) hzero
    refine ⟨t, ?_⟩
    calc
      curve t = stereo (sphereCurveZ t) (sphereCurveW t) := rfl
      _ = stereo (inverseZ p) (inverseW p) := by rw [hz, hw]
      _ = p := stereo_inverse p
  · rintro ⟨t, rfl⟩
    exact detectorMap_curve t

theorem radiusSq_contDiff : ContDiff ℝ (⊤ : ℕ∞) radiusSq := by
  unfold radiusSq
  fun_prop

theorem sphereDenom_contDiff : ContDiff ℝ (⊤ : ℕ∞) sphereDenom := by
  exact radiusSq_contDiff.add contDiff_const

theorem inverseZ_contDiff : ContDiff ℝ (⊤ : ℕ∞) inverseZ := by
  rw [← Complex.equivRealProdCLM.comp_contDiff_iff]
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : R3 =>
    (2 * p.ofLp 0 / sphereDenom p, 2 * p.ofLp 1 / sphereDenom p))
  exact ((contDiff_const.mul (by fun_prop)).div sphereDenom_contDiff sphereDenom_ne).prodMk
    ((contDiff_const.mul (by fun_prop)).div sphereDenom_contDiff sphereDenom_ne)

theorem inverseW_contDiff : ContDiff ℝ (⊤ : ℕ∞) inverseW := by
  rw [← Complex.equivRealProdCLM.comp_contDiff_iff]
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : R3 =>
    (2 * p.ofLp 2 / sphereDenom p, (radiusSq p - 1) / sphereDenom p))
  exact ((contDiff_const.mul (by fun_prop)).div sphereDenom_contDiff sphereDenom_ne).prodMk
    ((radiusSq_contDiff.sub contDiff_const).div sphereDenom_contDiff sphereDenom_ne)

theorem detectorMap_contDiff : ContDiff ℝ (⊤ : ℕ∞) detectorMap := by
  unfold detectorMap
  exact (contDiff_const.mul (inverseZ_contDiff.pow 2)).add
    (contDiff_const.mul (inverseW_contDiff.pow 3))

theorem curve_contDiff : ContDiff ℝ (⊤ : ℕ∞) curve := by
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => 1 - (-4 / 5) * Real.sin (2 * t)) := by
    fun_prop
  have hden_ne : ∀ t : ℝ, 1 - (-4 / 5) * Real.sin (2 * t) ≠ 0 := by
    intro t
    change 1 - (sphereCurveW t).im ≠ 0
    exact sub_ne_zero.mpr (sphereCurveW_im_ne_one t).symm
  apply contDiff_piLp'
  intro i
  fin_cases i
  · simpa [curve, stereo, sphereCurveZ, sphereCurveW] using
      ((contDiff_const.mul (Real.contDiff_cos.comp
        (contDiff_const.mul contDiff_id))).div hden hden_ne)
  · simpa [curve, stereo, sphereCurveZ, sphereCurveW] using
      ((contDiff_const.mul (Real.contDiff_sin.comp
        (contDiff_const.mul contDiff_id))).div hden hden_ne)
  · simpa [curve, stereo, sphereCurveZ, sphereCurveW] using
      ((contDiff_const.mul (Real.contDiff_cos.comp
        (contDiff_const.mul contDiff_id))).div hden hden_ne)

theorem sphereCurveZ_periodic (t : ℝ) :
    sphereCurveZ (t + 2 * Real.pi) = sphereCurveZ t := by
  have h3 :
      3 * (t + 2 * Real.pi) = 3 * t + ((3 : ℕ) : ℝ) * (2 * Real.pi) := by
    norm_num
    ring
  have hcos := Real.cos_add_nat_mul_two_pi (3 * t) 3
  have hsin := Real.sin_add_nat_mul_two_pi (3 * t) 3
  norm_num at hcos hsin
  apply Complex.ext <;> simp [sphereCurveZ, h3, hcos, hsin]

theorem sphereCurveW_periodic (t : ℝ) :
    sphereCurveW (t + 2 * Real.pi) = sphereCurveW t := by
  have h2 :
      2 * (t + 2 * Real.pi) = 2 * t + ((2 : ℕ) : ℝ) * (2 * Real.pi) := by
    norm_num
    ring
  have hcos := Real.cos_add_nat_mul_two_pi (2 * t) 2
  have hsin := Real.sin_add_nat_mul_two_pi (2 * t) 2
  norm_num at hcos hsin
  apply Complex.ext <;> simp [sphereCurveW, h2, hcos, hsin]

theorem curve_periodic (t : ℝ) : curve (t + 2 * Real.pi) = curve t := by
  simp [curve, sphereCurveZ_periodic, sphereCurveW_periodic]

theorem curve_injOn : Set.InjOn curve (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht hst
  have hz := congrArg inverseZ hst
  have hw := congrArg inverseW hst
  rw [inverseZ_curve, inverseZ_curve] at hz
  rw [inverseW_curve, inverseW_curve] at hw
  have hcos3 : Real.cos (3 * s) = Real.cos (3 * t) := by
    have h := congrArg Complex.re hz
    simp [sphereCurveZ] at h
    linarith
  have hsin3 : Real.sin (3 * s) = Real.sin (3 * t) := by
    have h := congrArg Complex.im hz
    simp [sphereCurveZ] at h
    linarith
  have hcos2 : Real.cos (2 * s) = Real.cos (2 * t) := by
    have h := congrArg Complex.re hw
    simp [sphereCurveW] at h
    linarith
  have hsin2 : Real.sin (2 * s) = Real.sin (2 * t) := by
    have h := congrArg Complex.im hw
    simp [sphereCurveW] at h
    linarith
  have hangle2 : ((2 * s : ℝ) : Real.Angle) = (2 * t : ℝ) :=
    Real.Angle.cos_sin_inj hcos2 hsin2
  have hangle3 : ((3 * s : ℝ) : Real.Angle) = (3 * t : ℝ) :=
    Real.Angle.cos_sin_inj hcos3 hsin3
  obtain ⟨k2, hk2⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle2
  obtain ⟨k3, hk3⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle3
  let q : ℤ := k3 - k2
  have hd : s - t = 2 * Real.pi * (q : ℝ) := by
    dsimp [q]
    push_cast
    linarith
  have htwo_pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hd_lower : -(2 * Real.pi) < s - t := by linarith [hs.1, ht.2]
  have hd_upper : s - t < 2 * Real.pi := by linarith [ht.1, hs.2]
  have hq_lower : (-1 : ℝ) < (q : ℝ) := by
    apply lt_of_mul_lt_mul_left _ htwo_pi.le
    rw [← hd]
    simpa using hd_lower
  have hq_upper : (q : ℝ) < 1 := by
    apply lt_of_mul_lt_mul_left _ htwo_pi.le
    rw [← hd]
    simpa using hd_upper
  have hq_lower_int : (-1 : ℤ) < q := by exact_mod_cast hq_lower
  have hq_upper_int : q < (1 : ℤ) := by exact_mod_cast hq_upper
  have hq : q = 0 := by omega
  rw [hq, Int.cast_zero, mul_zero] at hd
  linarith

theorem sphereCurveZ_eq_circleMap (t : ℝ) :
    sphereCurveZ t = circleMap 0 (3 / 5) (3 * t) := by
  rw [sphereCurveZ_eq_exp]
  simp [circleMap]

theorem sphereCurveZ_hasDerivAt (t : ℝ) :
    HasDerivAt sphereCurveZ
      ((3 : ℝ) • (circleMap 0 (3 / 5) (3 * t) * I)) t := by
  have hinner : HasDerivAt (fun s : ℝ => 3 * s) 3 t := by
    simpa using (hasDerivAt_id t).const_mul 3
  have hcomp := (hasDerivAt_circleMap 0 (3 / 5) (3 * t)).scomp t hinner
  have hfun : (circleMap 0 (3 / 5) ∘ fun s : ℝ => 3 * s) = sphereCurveZ := by
    funext s
    exact (sphereCurveZ_eq_circleMap s).symm
  rw [hfun] at hcomp
  exact hcomp

theorem sphereCurveZ_deriv_ne_zero (t : ℝ) : deriv sphereCurveZ t ≠ 0 := by
  rw [(sphereCurveZ_hasDerivAt t).deriv]
  apply smul_ne_zero
  · norm_num
  · apply mul_ne_zero
    · intro hzero
      have hnorm := norm_circleMap_zero (3 / 5) (3 * t)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    · exact I_ne_zero

theorem curve_immersion (t : ℝ) : deriv curve t ≠ 0 := by
  intro hzero
  have hcurve : HasDerivAt curve (deriv curve t) t :=
    (curve_contDiff.differentiable (by simp) t).hasDerivAt
  have hinverse : HasFDerivAt inverseZ (fderiv ℝ inverseZ (curve t)) (curve t) :=
    (inverseZ_contDiff.differentiable (by simp) (curve t)).hasFDerivAt
  have hcomp := hinverse.comp_hasDerivAt t hcurve
  have hfun : inverseZ ∘ curve = sphereCurveZ := by
    funext s
    exact inverseZ_curve s
  rw [hfun, hzero, map_zero] at hcomp
  exact sphereCurveZ_deriv_ne_zero t hcomp.deriv

def knot : Knot where
  curve := curve
  smooth := curve_contDiff
  periodic := curve_periodic
  injOn := curve_injOn
  immersion := curve_immersion

def detector : Detector.KnotDetector knot where
  map := detectorMap
  smooth := detectorMap_contDiff
  zero_iff := detectorMap_zero_iff

end

end Submission.AlgebraicTrefoil
