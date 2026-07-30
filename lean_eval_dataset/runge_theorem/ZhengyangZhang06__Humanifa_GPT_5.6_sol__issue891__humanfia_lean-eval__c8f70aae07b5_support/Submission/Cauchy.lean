import Submission.Helpers

open Set MeasureTheory intervalIntegral Function Filter
open scoped Interval Real ContDiff Topology Polynomial

noncomputable section

namespace Submission.Helpers

def crDefect (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * fderiv ℝ g z 1 - fderiv ℝ g z Complex.I

lemma continuous_crDefect (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) :
    Continuous (crDefect g) := by
  have hD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  exact (continuous_const.mul (hD.clm_apply continuous_const)).sub
    (hD.clm_apply continuous_const)

lemma crDefect_hasCompactSupport (g : ℂ → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (crDefect g) := by
  apply hg.mono'
  intro z hz
  by_contra hzt
  have hD : fderiv ℝ g z = 0 := fderiv_of_notMem_tsupport ℝ hzt
  exact hz (by simp [crDefect, hD])

lemma exists_common_norm_bound (K : Set ℂ) (g : ℂ → ℂ)
    (hK : IsCompact K) (hg : HasCompactSupport g) :
    ∃ A : ℝ, 0 < A ∧
      (∀ z ∈ K, ‖z‖ < A) ∧ ∀ w ∈ tsupport g, ‖w‖ < A := by
  obtain ⟨A, hA, hbound⟩ :=
    (hK.union hg).isBounded.exists_pos_norm_lt
  exact ⟨A, hA, fun z hz => hbound z (Or.inl hz),
    fun w hw => hbound w (Or.inr hw)⟩

lemma real_im_bounds_of_norm_lt {A : ℝ} {z : ℂ} (hz : ‖z‖ < A) :
    -A < z.re ∧ z.re < A ∧ -A < z.im ∧ z.im < A := by
  have hre : |z.re| < A := (Complex.abs_re_le_norm z).trans_lt hz
  have him : |z.im| < A := (Complex.abs_im_le_norm z).trans_lt hz
  constructor
  · linarith [neg_le_abs z.re]
  constructor
  · linarith [le_abs_self z.re]
  constructor
  · linarith [neg_le_abs z.im]
  · linarith [le_abs_self z.im]

def dslopeFDeriv (g : ℂ → ℂ) (z w : ℂ) : ℂ →L[ℝ] ℂ :=
  if w = z then 0
  else fderiv ℝ (fun u => (u - z)⁻¹ * (g u - g z)) w

lemma hasFDerivAt_dslope_dslopeFDeriv (g : ℂ → ℂ)
    (hg : Differentiable ℝ g) {z w : ℂ} (hw : w ≠ z) :
    HasFDerivAt (dslope g z) (dslopeFDeriv g z w) w := by
  rw [dslopeFDeriv, if_neg hw]
  have hprod : DifferentiableAt ℝ (fun u => (u - z)⁻¹ * (g u - g z)) w := by
    exact ((differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr hw)).mul
      ((hg w).sub_const _)
  apply hprod.hasFDerivAt.congr_of_eventuallyEq
  have hslope := dslope_eventuallyEq_slope_of_ne g hw
  filter_upwards [hslope] with u hu
  simpa only [slope, vsub_eq_sub, smul_eq_mul] using hu

lemma dslopeFDeriv_crDefect (g : ℂ → ℂ) (hg : Differentiable ℝ g)
    {z w : ℂ} (hw : w ≠ z) :
    Complex.I * dslopeFDeriv g z w 1 -
        dslopeFDeriv g z w Complex.I =
      (w - z)⁻¹ * crDefect g w := by
  rw [dslopeFDeriv, if_neg hw]
  let a : ℂ → ℂ := fun u => (u - z)⁻¹
  let b : ℂ → ℂ := fun u => g u - g z
  have haC : DifferentiableAt ℂ a w := by
    dsimp [a]
    exact (differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr hw)
  have haR : DifferentiableAt ℝ a w := haC.restrictScalars ℝ
  have hbR : DifferentiableAt ℝ b w := (hg w).sub_const _
  have hDa : fderiv ℝ a w Complex.I = Complex.I * fderiv ℝ a w 1 := by
    rw [haC.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars']
    calc
      fderiv ℂ a w Complex.I =
          fderiv ℂ a w (Complex.I • (1 : ℂ)) := by
            rw [smul_eq_mul, mul_one]
      _ = Complex.I • fderiv ℂ a w 1 := by rw [map_smul]
      _ = Complex.I * fderiv ℂ a w 1 := by rw [smul_eq_mul]
  have hDb : fderiv ℝ b w = fderiv ℝ g w := by
    dsimp [b]
    exact fderiv_sub_const (𝕜 := ℝ) (f := g) (x := w) (g z)
  change Complex.I * fderiv ℝ (fun u => a u * b u) w 1 -
      fderiv ℝ (fun u => a u * b u) w Complex.I =
    a w * crDefect g w
  rw [fderiv_fun_mul haR hbR]
  simp only [add_apply, smul_apply, smul_eq_mul, hDa, hDb, crDefect]
  ring

lemma integral_boundary_square_inv_sub (z : ℂ) (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ in z.re - R..z.re + R,
        ((x : ℂ) + ((z.im - R : ℝ) : ℂ) * Complex.I - z)⁻¹) -
      (∫ x : ℝ in z.re - R..z.re + R,
        ((x : ℂ) + ((z.im + R : ℝ) : ℂ) * Complex.I - z)⁻¹) +
      Complex.I * (∫ y : ℝ in z.im - R..z.im + R,
        (((z.re + R : ℝ) : ℂ) + y * Complex.I - z)⁻¹) -
      Complex.I * (∫ y : ℝ in z.im - R..z.im + R,
        (((z.re - R : ℝ) : ℂ) + y * Complex.I - z)⁻¹) =
      2 * Real.pi * Complex.I := by
  have hbottom :
      (∫ x : ℝ in z.re - R..z.re + R,
          ((x : ℂ) + ((z.im - R : ℝ) : ℂ) * Complex.I - z)⁻¹) =
        ∫ x : ℝ in -R..R, ((x : ℂ) - R * Complex.I)⁻¹ := by
    have hshift := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ =>
        ((x : ℂ) + ((z.im - R : ℝ) : ℂ) * Complex.I - z)⁻¹)
      (a := -R) (b := R) z.re
    rw [show (fun x : ℝ =>
        ((((x + z.re : ℝ) : ℂ) +
          ((z.im - R : ℝ) : ℂ) * Complex.I - z)⁻¹)) =
        fun x : ℝ => ((x : ℂ) - R * Complex.I)⁻¹ by
      funext x
      congr 1
      apply Complex.ext <;> simp] at hshift
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift.symm
  have htop :
      (∫ x : ℝ in z.re - R..z.re + R,
          ((x : ℂ) + ((z.im + R : ℝ) : ℂ) * Complex.I - z)⁻¹) =
        ∫ x : ℝ in -R..R, ((x : ℂ) + R * Complex.I)⁻¹ := by
    have hshift := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ =>
        ((x : ℂ) + ((z.im + R : ℝ) : ℂ) * Complex.I - z)⁻¹)
      (a := -R) (b := R) z.re
    rw [show (fun x : ℝ =>
        ((((x + z.re : ℝ) : ℂ) +
          ((z.im + R : ℝ) : ℂ) * Complex.I - z)⁻¹)) =
        fun x : ℝ => ((x : ℂ) + R * Complex.I)⁻¹ by
      funext x
      congr 1
      apply Complex.ext <;> simp] at hshift
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift.symm
  have hright :
      (∫ y : ℝ in z.im - R..z.im + R,
          (((z.re + R : ℝ) : ℂ) + y * Complex.I - z)⁻¹) =
        ∫ y : ℝ in -R..R, ((R : ℂ) + y * Complex.I)⁻¹ := by
    have hshift := intervalIntegral.integral_comp_add_right
      (f := fun y : ℝ => (((z.re + R : ℝ) : ℂ) + y * Complex.I - z)⁻¹)
      (a := -R) (b := R) z.im
    rw [show (fun y : ℝ =>
        (((z.re + R : ℝ) : ℂ) +
          ((y + z.im : ℝ) : ℂ) * Complex.I - z)⁻¹) =
        fun y : ℝ => ((R : ℂ) + y * Complex.I)⁻¹ by
      funext y
      congr 1
      apply Complex.ext <;> simp] at hshift
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift.symm
  have hleft :
      (∫ y : ℝ in z.im - R..z.im + R,
          (((z.re - R : ℝ) : ℂ) + y * Complex.I - z)⁻¹) =
        ∫ y : ℝ in -R..R, ((-R : ℂ) + y * Complex.I)⁻¹ := by
    have hshift := intervalIntegral.integral_comp_add_right
      (f := fun y : ℝ => (((z.re - R : ℝ) : ℂ) + y * Complex.I - z)⁻¹)
      (a := -R) (b := R) z.im
    rw [show (fun y : ℝ =>
        (((z.re - R : ℝ) : ℂ) +
          ((y + z.im : ℝ) : ℂ) * Complex.I - z)⁻¹) =
        fun y : ℝ => ((-R : ℂ) + y * Complex.I)⁻¹ by
      funext y
      congr 1
      apply Complex.ext <;> simp] at hshift
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift.symm
  rw [hbottom, htop, hright, hleft]
  exact integral_boundary_square_inv R hR

lemma cauchyPompeiu_centered (K N : Set ℂ) (g : ℂ → ℂ)
    (hK : IsCompact K) (hN : IsOpen N) (hKN : K ⊆ N)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hhol : ∀ z ∈ K, DifferentiableAt ℂ g z)
    (hzero : ∀ w ∈ N, crDefect g w = 0) :
    ∀ z ∈ K,
      g z = -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∫ x : ℝ, ∫ y : ℝ,
          (x + y * Complex.I - z)⁻¹ * crDefect g (x + y * Complex.I) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨A, hA, hKb, hgb⟩ := exists_common_norm_bound K g hK hgc
  let R := 2 * A
  have hR : 0 < R := by positivity
  intro z hz
  have hzb := real_im_bounds_of_norm_lt (hKb z hz)
  let a : ℂ := ⟨z.re - R, z.im - R⟩
  let b : ℂ := ⟨z.re + R, z.im + R⟩
  let F : ℂ → ℂ := dslope g z
  let F' : ℂ → ℂ →L[ℝ] ℂ := dslopeFDeriv g z
  have hFc : ContinuousOn F ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    intro w hw
    by_cases hwz : w = z
    · subst w
      exact (continuousAt_dslope_same.2 (hhol z hz)).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne hwz).2
        hg.continuous.continuousAt).continuousWithinAt
  have hFd :
      ∀ w ∈ Ioo (min a.re b.re) (max a.re b.re) ×ℂ
          Ioo (min a.im b.im) (max a.im b.im) \ {z},
        HasFDerivAt F (F' w) w := by
    intro w hw
    exact hasFDerivAt_dslope_dslopeFDeriv g (hg.differentiable (by simp))
      (by simpa only [mem_singleton_iff] using hw.2)
  let hK0 : ∀ w ∈ K, crDefect g w = 0 := fun w hw => hzero w (hKN hw)
  have hCI : Continuous (cauchyIntegrand K (crDefect g) hK0) :=
    continuous_cauchyIntegrand K N (crDefect g) hK hN hKN
      (continuous_crDefect g hg) hzero
  have hscalar : Continuous fun w : ℂ =>
      (w - z)⁻¹ * crDefect g w := by
    have heval := (ContinuousMap.evalCLM ℝ ⟨z, hz⟩).continuous.comp hCI
    change Continuous (fun w =>
      (cauchyIntegrand K (crDefect g) hK0 w) ⟨z, hz⟩) at heval
    change Continuous (fun w => crDefect g w * (w - z)⁻¹) at heval
    simpa only [mul_comm] using heval
  have hFcr : ∀ w, Complex.I * F' w 1 - F' w Complex.I =
      (w - z)⁻¹ * crDefect g w := by
    intro w
    by_cases hw : w = z
    · subst w
      simp [F', dslopeFDeriv]
    · exact dslopeFDeriv_crDefect g (hg.differentiable (by simp)) hw
  have hFi : IntegrableOn
      (fun w => Complex.I • F' w 1 - F' w Complex.I)
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    have hcpt : IsCompact ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) :=
      isCompact_uIcc.reProdIm isCompact_uIcc
    apply ContinuousOn.integrableOn_compact hcpt
    intro w hw
    have hfun :
        (fun q => Complex.I • F' q 1 - F' q Complex.I) =
          fun q => (q - z)⁻¹ * crDefect g q := by
      funext q
      simpa only [smul_eq_mul] using hFcr q
    rw [hfun]
    exact hscalar.continuousAt.continuousWithinAt
  have H := Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable
    F F' a b {z} (countable_singleton z) hFc hFd hFi
  dsimp only [a, b] at H
  simp only [smul_eq_mul] at H
  have hboundary (w : ℂ) (hw : w ∉ tsupport g) (hwz : w ≠ z) :
      F w = -g z * (w - z)⁻¹ := by
    have hgw : g w = 0 := image_eq_zero_of_notMem_tsupport hw
    change dslope g z w = _
    rw [dslope_of_ne g hwz]
    simp [slope, vsub_eq_sub, smul_eq_mul, hgw]
    ring
  have hbottom :
      (fun x : ℝ => F ((x : ℂ) + ((z.im - R : ℝ) : ℂ) * Complex.I)) =
        fun x : ℝ => -g z *
          ((x : ℂ) + ((z.im - R : ℝ) : ℂ) * Complex.I - z)⁻¹ := by
    funext x
    apply hboundary
    · intro hw
      have hwb := real_im_bounds_of_norm_lt (hgb _ hw)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_add, mul_one] at hwb
      linarith
    · intro hwz
      have hi := congrArg Complex.im hwz
      simp at hi
      linarith
  have htop :
      (fun x : ℝ => F ((x : ℂ) + ((z.im + R : ℝ) : ℂ) * Complex.I)) =
        fun x : ℝ => -g z *
          ((x : ℂ) + ((z.im + R : ℝ) : ℂ) * Complex.I - z)⁻¹ := by
    funext x
    apply hboundary
    · intro hw
      have hwb := real_im_bounds_of_norm_lt (hgb _ hw)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_add, mul_one] at hwb
      linarith
    · intro hwz
      have hi := congrArg Complex.im hwz
      simp at hi
      linarith
  have hright : (fun y : ℝ => F ((z.re + R : ℝ) + y * Complex.I)) =
      fun y : ℝ => -g z *
        (((z.re + R : ℝ) : ℂ) + y * Complex.I - z)⁻¹ := by
    funext y
    apply hboundary
    · intro hw
      have hwb := real_im_bounds_of_norm_lt (hgb _ hw)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero] at hwb
      linarith
    · intro hwz
      have hr := congrArg Complex.re hwz
      simp at hr
      linarith
  have hleft : (fun y : ℝ => F ((z.re - R : ℝ) + y * Complex.I)) =
      fun y : ℝ => -g z *
        (((z.re - R : ℝ) : ℂ) + y * Complex.I - z)⁻¹ := by
    funext y
    apply hboundary
    · intro hw
      have hwb := real_im_bounds_of_norm_lt (hgb _ hw)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero] at hwb
      linarith
    · intro hwz
      have hr := congrArg Complex.re hwz
      simp at hr
      linarith
  have hbinv := integral_boundary_square_inv_sub z R hR
  have Hleft :
      (∫ x : ℝ in z.re - R..z.re + R,
          F ((x : ℂ) + ((z.im - R : ℝ) : ℂ) * Complex.I)) -
          (∫ x : ℝ in z.re - R..z.re + R,
            F ((x : ℂ) + ((z.im + R : ℝ) : ℂ) * Complex.I)) +
          Complex.I * (∫ y : ℝ in z.im - R..z.im + R,
            F ((z.re + R : ℝ) + y * Complex.I)) -
          Complex.I * (∫ y : ℝ in z.im - R..z.im + R,
            F ((z.re - R : ℝ) + y * Complex.I)) =
        -g z * (2 * Real.pi * Complex.I) := by
    rw [hbottom, htop, hright, hleft]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [← hbinv]
    ring
  rw [Hleft] at H
  simp_rw [hFcr] at H
  have hy (x : ℝ) :
      support (fun y : ℝ =>
        (x + y * Complex.I - z)⁻¹ * crDefect g (x + y * Complex.I)) ⊆
          Ioc (z.im - R) (z.im + R) := by
    intro y hy
    have hyD : crDefect g (x + y * Complex.I) ≠ 0 := by
      intro hy0
      exact hy (by simp [hy0])
    have hyt : x + y * Complex.I ∈ tsupport g := by
      by_contra hnot
      have hD : fderiv ℝ g (x + y * Complex.I) = 0 :=
        fderiv_of_notMem_tsupport ℝ hnot
      exact hyD (by simp [crDefect, hD])
    have hwb := real_im_bounds_of_norm_lt (hgb _ hyt)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_add, mul_one] at hwb
    constructor <;> linarith
  have hx :
      support (fun x : ℝ => ∫ y : ℝ,
        (x + y * Complex.I - z)⁻¹ * crDefect g (x + y * Complex.I)) ⊆
          Ioc (z.re - R) (z.re + R) := by
    intro x hx
    by_contra hxi
    apply hx
    apply integral_eq_zero_of_ae
    filter_upwards with y
    have hnot : x + y * Complex.I ∉ tsupport g := by
      intro hmem
      have hwb := real_im_bounds_of_norm_lt (hgb _ hmem)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero] at hwb
      have : x ≤ z.re - R ∨ z.re + R < x := by
        simpa only [mem_Ioc, not_and_or, not_lt, not_le] using hxi
      rcases this with hxl | hxr <;> linarith
    have hD : fderiv ℝ g (x + y * Complex.I) = 0 :=
      fderiv_of_notMem_tsupport ℝ hnot
    simp [crDefect, hD]
  have hyint (x : ℝ) :
      (∫ y : ℝ in z.im - R..z.im + R,
          (x + y * Complex.I - z)⁻¹ * crDefect g (x + y * Complex.I)) =
        ∫ y : ℝ,
          (x + y * Complex.I - z)⁻¹ * crDefect g (x + y * Complex.I) :=
    intervalIntegral.integral_eq_integral_of_support_subset (hy x)
  simp_rw [hyint] at H
  rw [intervalIntegral.integral_eq_integral_of_support_subset hx] at H
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc
    g z = -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (-g z * (2 * Real.pi * Complex.I)) := by field_simp
    _ = -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∫ x : ℝ, ∫ y : ℝ,
          (x + y * Complex.I - z)⁻¹ * crDefect g (x + y * Complex.I)) := by rw [H]

end Submission.Helpers
