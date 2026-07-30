import Mathlib

noncomputable section

open MeasureTheory Set

namespace Submission

def signedCross (u v : ℂ) : ℝ := (starRingEnd ℂ u * v).im

lemma signedCross_flux_algebra (a b c m : ℂ) :
    (1 / 2 : ℝ) * (starRingEnd ℂ c * m + b * starRingEnd ℂ a).im +
      -(1 / 2 : ℝ) * (starRingEnd ℂ c * m + a * starRingEnd ℂ b).im =
        signedCross a b := by
  unfold signedCross
  change (1 / 2 : ℝ) * (star c * m + b * star a).im +
      -(1 / 2 : ℝ) * (star c * m + a * star b).im =
        (star a * b).im
  rw [Complex.star_def]
  simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma flux_divergence_eq {phi : ℝ × ℝ → ℂ}
    {dphi : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ}
    {d2phi : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℂ}
    {p : ℝ × ℝ}
    (hphi : HasFDerivAt phi (dphi p) p)
    (hdphi : HasFDerivAt dphi (d2phi p) p)
    (hsymm : ∀ u v, d2phi p u v = d2phi p v u) :
    let radialFlux : ℝ × ℝ → ℝ := fun x =>
      (1 / 2 : ℝ) * signedCross (phi x) (dphi x (0, 1))
    let angularFlux : ℝ × ℝ → ℝ := fun x =>
      -(1 / 2 : ℝ) * signedCross (phi x) (dphi x (1, 0))
    fderiv ℝ radialFlux p (1, 0) + fderiv ℝ angularFlux p (0, 1) =
      signedCross (dphi p (1, 0)) (dphi p (0, 1)) := by
  dsimp only
  have hconj : HasFDerivAt (fun x => starRingEnd ℂ (phi x))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dphi p)) p :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp p hphi
  have heval (v : ℝ × ℝ) : HasFDerivAt (fun x => dphi x v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp (d2phi p)) p :=
    (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp p hdphi
  have hrad := (Complex.imCLM.hasFDerivAt.comp p
    (hconj.mul (heval (0, 1)))).const_mul (1 / 2 : ℝ)
  have hang := (Complex.imCLM.hasFDerivAt.comp p
    (hconj.mul (heval (1, 0)))).const_mul (-(1 / 2 : ℝ))
  change HasFDerivAt
    (fun x => (1 / 2 : ℝ) * signedCross (phi x) (dphi x (0, 1))) _ p at hrad
  change HasFDerivAt
    (fun x => -(1 / 2 : ℝ) * signedCross (phi x) (dphi x (1, 0))) _ p at hang
  rw [hrad.fderiv, hang.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [hsymm (1, 0) (0, 1)]
  exact signedCross_flux_algebra _ _ _ _

noncomputable def radialAreaFlux (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * signedCross (phi p) (fderiv ℝ phi p (0, 1))

noncomputable def angularAreaFlux (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  -(1 / 2 : ℝ) * signedCross (phi p) (fderiv ℝ phi p (1, 0))

noncomputable def polarJacobian (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  signedCross (fderiv ℝ phi p (1, 0)) (fderiv ℝ phi p (0, 1))

lemma polarJacobian_contDiffAt {phi : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hphi : ContDiffAt ℝ 2 phi p) : ContDiffAt ℝ 1 (polarJacobian phi) p := by
  have hdphi : ContDiffAt ℝ 1 (fderiv ℝ phi) p :=
    hphi.fderiv_right (m := 1) (by norm_num)
  have hrad : ContDiffAt ℝ 1 (fun x => fderiv ℝ phi x (1, 0)) p :=
    hdphi.clm_apply contDiffAt_const
  have hang : ContDiffAt ℝ 1 (fun x => fderiv ℝ phi x (0, 1)) p :=
    hdphi.clm_apply contDiffAt_const
  have hconj : ContDiffAt ℝ 1
      (fun x => starRingEnd ℂ (fderiv ℝ phi x (1, 0))) p :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp p hrad
  unfold polarJacobian signedCross
  exact Complex.imCLM.contDiff.contDiffAt.comp p (hconj.mul hang)

lemma radialAreaFlux_contDiffAt {phi : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hphi : ContDiffAt ℝ 2 phi p) : ContDiffAt ℝ 1 (radialAreaFlux phi) p := by
  have hdphi : ContDiffAt ℝ 1 (fderiv ℝ phi) p :=
    hphi.fderiv_right (m := 1) (by norm_num)
  have hconj : ContDiffAt ℝ 1 (fun x => starRingEnd ℂ (phi x)) p :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp p
      (hphi.of_le (by norm_num))
  have heval : ContDiffAt ℝ 1 (fun x => fderiv ℝ phi x (0, 1)) p :=
    hdphi.clm_apply contDiffAt_const
  have him : ContDiffAt ℝ 1
      (fun x => signedCross (phi x) (fderiv ℝ phi x (0, 1))) p := by
    unfold signedCross
    exact Complex.imCLM.contDiff.contDiffAt.comp p (hconj.mul heval)
  unfold radialAreaFlux
  exact contDiffAt_const.mul him

lemma angularAreaFlux_contDiffAt {phi : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hphi : ContDiffAt ℝ 2 phi p) : ContDiffAt ℝ 1 (angularAreaFlux phi) p := by
  have hdphi : ContDiffAt ℝ 1 (fderiv ℝ phi) p :=
    hphi.fderiv_right (m := 1) (by norm_num)
  have hconj : ContDiffAt ℝ 1 (fun x => starRingEnd ℂ (phi x)) p :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp p
      (hphi.of_le (by norm_num))
  have heval : ContDiffAt ℝ 1 (fun x => fderiv ℝ phi x (1, 0)) p :=
    hdphi.clm_apply contDiffAt_const
  have him : ContDiffAt ℝ 1
      (fun x => signedCross (phi x) (fderiv ℝ phi x (1, 0))) p := by
    unfold signedCross
    exact Complex.imCLM.contDiff.contDiffAt.comp p (hconj.mul heval)
  unfold angularAreaFlux
  exact contDiffAt_const.mul him

lemma areaFlux_divergence_eq {phi : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hphi : ContDiffAt ℝ 2 phi p) :
    fderiv ℝ (radialAreaFlux phi) p (1, 0) +
      fderiv ℝ (angularAreaFlux phi) p (0, 1) = polarJacobian phi p := by
  apply flux_divergence_eq
  · exact (hphi.differentiableAt (by norm_num)).hasFDerivAt
  · exact ((hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  · exact hphi.isSymmSndFDerivAt (by norm_num)

lemma integral_polarJacobian_eq_radialAreaFlux_sub {phi : ℝ × ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hphi : ∀ p ∈ Icc (a, -Real.pi) (b, Real.pi), ContDiffAt ℝ 2 phi p)
    (hangular : ∀ r ∈ Icc a b,
      angularAreaFlux phi (r, Real.pi) = angularAreaFlux phi (r, -Real.pi)) :
    (∫ p in Icc (a, -Real.pi) (b, Real.pi), polarJacobian phi p) =
      (∫ theta in -Real.pi..Real.pi, radialAreaFlux phi (b, theta)) -
        ∫ theta in -Real.pi..Real.pi, radialAreaFlux phi (a, theta) := by
  let rect : Set (ℝ × ℝ) := Icc (a, -Real.pi) (b, Real.pi)
  have hle : (a, -Real.pi) ≤ (b, Real.pi) :=
    ⟨hab, by linarith [Real.pi_pos]⟩
  have hradCont : ContinuousOn (radialAreaFlux phi) rect := by
    intro p hp
    exact (radialAreaFlux_contDiffAt (hphi p hp)).continuousAt.continuousWithinAt
  have hangCont : ContinuousOn (angularAreaFlux phi) rect := by
    intro p hp
    exact (angularAreaFlux_contDiffAt (hphi p hp)).continuousAt.continuousWithinAt
  have hdivCont : ContinuousOn
      (fun p => fderiv ℝ (radialAreaFlux phi) p (1, 0) +
        fderiv ℝ (angularAreaFlux phi) p (0, 1)) rect := by
    apply ContinuousOn.add
    · exact (fun p hp =>
        (radialAreaFlux_contDiffAt (hphi p hp)).continuousAt_fderiv (by norm_num)
          |>.clm_apply continuousAt_const |>.continuousWithinAt)
    · exact (fun p hp =>
        (angularAreaFlux_contDiffAt (hphi p hp)).continuousAt_fderiv (by norm_num)
          |>.clm_apply continuousAt_const |>.continuousWithinAt)
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (radialAreaFlux phi) (angularAreaFlux phi)
    (fderiv ℝ (radialAreaFlux phi)) (fderiv ℝ (angularAreaFlux phi))
    (a, -Real.pi) (b, Real.pi) hle hradCont hangCont
    (fun p hp => ((radialAreaFlux_contDiffAt (hphi p
      (by exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩))).differentiableAt
        (by norm_num)).hasFDerivAt)
    (fun p hp => ((angularAreaFlux_contDiffAt (hphi p
      (by exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩))).differentiableAt
        (by norm_num)).hasFDerivAt)
    hdivCont.integrableOn_Icc
  have hleft :
      (∫ p in rect, fderiv ℝ (radialAreaFlux phi) p (1, 0) +
          fderiv ℝ (angularAreaFlux phi) p (0, 1)) =
        ∫ p in rect, polarJacobian phi p := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro p hp
    exact areaFlux_divergence_eq (hphi p hp)
  rw [hleft] at hgreen
  have hangularIntegral :
      (∫ r in a..b, angularAreaFlux phi (r, Real.pi)) =
        ∫ r in a..b, angularAreaFlux phi (r, -Real.pi) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro r hr
    exact hangular r hr
  rw [hangularIntegral, sub_self, zero_add] at hgreen
  exact hgreen

/-- Green's identity in polar coordinates: nonnegative polar Jacobian gives nonnegative
signed area on the outer circle. -/
lemma radialAreaFlux_nonneg_of_polarJacobian {phi : ℝ × ℝ → ℂ} {A : ℝ}
    (hA : 0 < A)
    (hphi : ∀ p ∈ Icc ((0 : ℝ), -Real.pi) (A, Real.pi), ContDiffAt ℝ 2 phi p)
    (hangular : ∀ r ∈ Icc (0 : ℝ) A,
      angularAreaFlux phi (r, Real.pi) = angularAreaFlux phi (r, -Real.pi))
    (hzero : ∀ theta ∈ Icc (-Real.pi) Real.pi,
      radialAreaFlux phi (0, theta) = 0)
    (hjac : ∀ p ∈ Icc ((0 : ℝ), -Real.pi) (A, Real.pi),
      0 ≤ polarJacobian phi p) :
    0 ≤ ∫ theta in -Real.pi..Real.pi, radialAreaFlux phi (A, theta) := by
  let rect : Set (ℝ × ℝ) := Icc ((0 : ℝ), -Real.pi) (A, Real.pi)
  have hle : ((0 : ℝ), -Real.pi) ≤ (A, Real.pi) :=
    ⟨hA.le, by linarith [Real.pi_pos]⟩
  have hradCont : ContinuousOn (radialAreaFlux phi) rect := by
    intro p hp
    exact (radialAreaFlux_contDiffAt (hphi p hp)).continuousAt.continuousWithinAt
  have hangCont : ContinuousOn (angularAreaFlux phi) rect := by
    intro p hp
    exact (angularAreaFlux_contDiffAt (hphi p hp)).continuousAt.continuousWithinAt
  have hdivCont : ContinuousOn
      (fun p => fderiv ℝ (radialAreaFlux phi) p (1, 0) +
        fderiv ℝ (angularAreaFlux phi) p (0, 1)) rect := by
    apply ContinuousOn.add
    · exact (fun p hp =>
        (radialAreaFlux_contDiffAt (hphi p hp)).continuousAt_fderiv (by norm_num)
          |>.clm_apply continuousAt_const |>.continuousWithinAt)
    · exact (fun p hp =>
        (angularAreaFlux_contDiffAt (hphi p hp)).continuousAt_fderiv (by norm_num)
          |>.clm_apply continuousAt_const |>.continuousWithinAt)
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (radialAreaFlux phi) (angularAreaFlux phi)
    (fderiv ℝ (radialAreaFlux phi)) (fderiv ℝ (angularAreaFlux phi))
    ((0 : ℝ), -Real.pi) (A, Real.pi) hle hradCont hangCont
    (fun p hp => ((radialAreaFlux_contDiffAt (hphi p
      (by exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩))).differentiableAt
        (by norm_num)).hasFDerivAt)
    (fun p hp => ((angularAreaFlux_contDiffAt (hphi p
      (by exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩))).differentiableAt
        (by norm_num)).hasFDerivAt)
    hdivCont.integrableOn_Icc
  have hleft :
      (∫ p in rect, fderiv ℝ (radialAreaFlux phi) p (1, 0) +
          fderiv ℝ (angularAreaFlux phi) p (0, 1)) =
        ∫ p in rect, polarJacobian phi p := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro p hp
    exact areaFlux_divergence_eq (hphi p hp)
  rw [hleft] at hgreen
  have hangularIntegral :
      (∫ r in (0 : ℝ)..A, angularAreaFlux phi (r, Real.pi)) =
        ∫ r in (0 : ℝ)..A, angularAreaFlux phi (r, -Real.pi) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hA.le]
    intro r hr
    exact hangular r hr
  have hzeroIntegral :
      (∫ theta in -Real.pi..Real.pi, radialAreaFlux phi (0, theta)) = 0 := by
    calc
      (∫ theta in -Real.pi..Real.pi, radialAreaFlux phi (0, theta)) =
          ∫ _theta in -Real.pi..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        intro theta htheta
        exact hzero theta htheta
      _ = 0 := by simp
  rw [hangularIntegral, sub_self, zero_add, hzeroIntegral, sub_zero] at hgreen
  rw [← hgreen]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
  exact hjac p hp

end Submission
