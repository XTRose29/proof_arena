import Submission.Orientation

open LeanEval.Geometry.HopfUmlaufsatz

namespace Submission.AreaWinding

open Set Metric MeasureTheory ComplexConjugate
open Submission.Helpers
open Submission.Orientation

noncomputable section

/-- The planar Cauchy kernel is locally integrable. -/
theorem locallyIntegrable_inv :
    LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ)
    (C := 1) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_
    measurable_inv.aestronglyMeasurable
  filter_upwards with z
  simp [norm_inv, Real.rpow_neg_one]

private theorem integral_polarTarget_eq_iterated (g : ℝ × ℝ → ℂ)
    (hg : IntegrableOn g Complex.polarCoord.target) :
    (∫ p in Complex.polarCoord.target, g p) =
      ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, g (ρ, θ) := by
  rw [Complex.polarCoord_target] at hg ⊢
  rw [Measure.volume_eq_prod] at hg ⊢
  exact setIntegral_prod g hg

/-- The circle average of the Cauchy kernel jumps when the circle crosses
its pole. The equality-radius case is intentionally excluded. -/
private theorem circleAverage_c_sub_inv (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hne : ‖c‖ ≠ ρ) :
    Real.circleAverage (fun z : ℂ => (c - z)⁻¹) 0 ρ =
      if ‖c‖ < ρ then 0 else c⁻¹ := by
  rw [Real.circleAverage_eq_circleIntegral hρ.ne']
  by_cases hc : c = 0
  · subst c
    simp only [norm_zero, hρ, if_pos, zero_sub]
    have hzpow := circleIntegral.integral_sub_zpow_of_ne
      (n := (-2 : ℤ)) (by norm_num) 0 0 ρ
    have hcongr :
        (∮ z in C(0, ρ), (z - 0)⁻¹ • (-z)⁻¹) =
          ∮ z in C(0, ρ), -((z - 0) ^ (-2 : ℤ)) := by
      apply circleIntegral.integral_congr hρ.le
      intro z hz
      have hz0 : z ≠ 0 := by
        intro hzero
        subst z
        have hz' : (0 : ℝ) = ρ := by
          simpa [mem_sphere_iff_norm] using hz
        exact hρ.ne' hz'.symm
      simp only [smul_eq_mul, sub_zero, inv_neg]
      rw [show z ^ (-2 : ℤ) = z⁻¹ * z⁻¹ by
        rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg,
          zpow_ofNat, pow_two, mul_inv_rev]]
      ring
    rw [hcongr]
    have hneg : (∮ z in C(0, ρ), -((z - 0) ^ (-2 : ℤ))) =
        -(∮ z in C(0, ρ), (z - 0) ^ (-2 : ℤ)) := by
      calc
        (∮ z in C(0, ρ), -((z - 0) ^ (-2 : ℤ))) =
            ∮ z in C(0, ρ), (-1 : ℂ) * ((z - 0) ^ (-2 : ℤ)) := by
          apply circleIntegral.integral_congr hρ.le
          intro z _
          ring
        _ = (-1 : ℂ) * (∮ z in C(0, ρ), (z - 0) ^ (-2 : ℤ)) := by
          rw [circleIntegral.integral_const_mul]
        _ = -(∮ z in C(0, ρ), (z - 0) ^ (-2 : ℤ)) := by ring
    rw [hneg, hzpow]
    simp
  · have hzint : CircleIntegrable (fun z : ℂ => (z - 0)⁻¹) 0 ρ := by
      rw [circleIntegrable_sub_inv_iff]
      right
      intro hz
      have hz' : (0 : ℝ) = ρ := by
        simpa [abs_of_pos hρ, mem_sphere_iff_norm] using hz
      exact hρ.ne' hz'.symm
    have hcminusint : CircleIntegrable (fun z : ℂ => (c - z)⁻¹) 0 ρ := by
      apply ContinuousOn.circleIntegrable hρ.le
      apply (continuousOn_const.sub continuousOn_id).inv₀
      intro z hz hzero
      have hzc : c = z := sub_eq_zero.mp hzero
      subst z
      apply hne
      simpa [abs_of_pos hρ, mem_sphere_iff_norm] using hz
    have hdecomp :
        (∮ z in C(0, ρ), (z - 0)⁻¹ • (c - z)⁻¹) =
          c⁻¹ * ((∮ z in C(0, ρ), (z - 0)⁻¹) +
            ∮ z in C(0, ρ), (c - z)⁻¹) := by
      calc
        (∮ z in C(0, ρ), (z - 0)⁻¹ • (c - z)⁻¹) =
            ∮ z in C(0, ρ), c⁻¹ * ((z - 0)⁻¹ + (c - z)⁻¹) := by
          apply circleIntegral.integral_congr hρ.le
          intro z hz
          have hz0 : z ≠ 0 := by
            intro hzero
            subst z
            have hz' : (0 : ℝ) = ρ := by
              simpa [mem_sphere_iff_norm] using hz
            exact hρ.ne' hz'.symm
          have hzc : c - z ≠ 0 := by
            intro hzero
            have : c = z := sub_eq_zero.mp hzero
            subst z
            apply hne
            simpa [abs_of_pos hρ, mem_sphere_iff_norm] using hz
          simp only [smul_eq_mul, sub_zero]
          field_simp
          ring
        _ = c⁻¹ * (∮ z in C(0, ρ),
              (z - 0)⁻¹ + (c - z)⁻¹) := by
          rw [circleIntegral.integral_const_mul]
        _ = c⁻¹ * ((∮ z in C(0, ρ), (z - 0)⁻¹) +
              ∮ z in C(0, ρ), (c - z)⁻¹) := by
          rw [circleIntegral.integral_add hzint hcminusint]
    rw [hdecomp, circleIntegral.integral_sub_center_inv 0 hρ.ne']
    split_ifs with hinside
    · have hcball : c ∈ ball (0 : ℂ) ρ := by
        simpa [mem_ball_iff_norm] using hinside
      have hin := circleIntegral.integral_sub_inv_of_mem_ball hcball
      have hcminus : (∮ z in C(0, ρ), (c - z)⁻¹) =
          -(2 * Real.pi * Complex.I) := by
        calc
          (∮ z in C(0, ρ), (c - z)⁻¹) =
              ∮ z in C(0, ρ), (-1 : ℂ) * (z - c)⁻¹ := by
            apply circleIntegral.integral_congr hρ.le
            intro z _
            change (c - z)⁻¹ = (-1 : ℂ) * (z - c)⁻¹
            rw [show c - z = -(z - c) by ring, inv_neg]
            ring
          _ = (-1 : ℂ) * (∮ z in C(0, ρ), (z - c)⁻¹) := by
            rw [circleIntegral.integral_const_mul]
          _ = -(2 * Real.pi * Complex.I) := by rw [hin]; ring
      rw [hcminus]
      simp
    · have hout : ρ < ‖c‖ := lt_of_le_of_ne (le_of_not_gt hinside) (Ne.symm hne)
      have hdc : DiffContOnCl ℂ (fun z : ℂ => (c - z)⁻¹) (ball 0 ρ) := by
        apply (diffContOnCl_const.sub differentiable_id.diffContOnCl).inv
        intro z hz hzero
        rw [closure_ball _ hρ.ne'] at hz
        have hzc : c = z := sub_eq_zero.mp hzero
        subst z
        have := mem_closedBall_iff_norm.mp hz
        simp only [sub_zero] at this
        linarith
      rw [hdc.circleIntegral_eq_zero hρ.le]
      change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (c⁻¹ * (2 * (Real.pi : ℂ) * Complex.I + 0)) = c⁻¹
      rw [add_zero]
      have hA : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero
      calc
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (c⁻¹ * (2 * (Real.pi : ℂ) * Complex.I)) =
            c⁻¹ * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (2 * (Real.pi : ℂ) * Complex.I)) := by ring
        _ = c⁻¹ := by rw [inv_mul_cancel₀ hA, mul_one]

private noncomputable def diskKernel (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (ball (0 : ℂ) R).indicator (fun w => (c - w)⁻¹) z

private theorem diskKernel_measurable (c : ℂ) (R : ℝ) :
    Measurable (diskKernel c R) := by
  exact ((measurable_const.sub measurable_id).inv.indicator measurableSet_ball)

private theorem integrableOn_c_sub_inv_ball (c : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => (c - z)⁻¹) (ball 0 R) := by
  have hbase : IntegrableOn (fun z : ℂ => z⁻¹)
      (closedBall 0 (‖c‖ + R)) :=
    locallyIntegrable_inv.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) (‖c‖ + R))
  have hglobal : Integrable
      ((closedBall (0 : ℂ) (‖c‖ + R)).indicator (fun z => z⁻¹)) :=
    hbase.integrable_indicator measurableSet_closedBall
  have htranslated : Integrable (fun z : ℂ =>
      (closedBall (0 : ℂ) (‖c‖ + R)).indicator (fun w => w⁻¹) (c - z)) := by
    simpa using hglobal.comp_sub_left c
  apply IntegrableOn.congr_fun htranslated.integrableOn
  · intro z hz
    have hzmem : c - z ∈ closedBall (0 : ℂ) (‖c‖ + R) := by
      rw [mem_closedBall_iff_norm]
      simp only [sub_zero]
      calc
        ‖c - z‖ ≤ ‖c‖ + ‖z‖ := norm_sub_le c z
        _ ≤ ‖c‖ + R := by
          gcongr
          exact le_of_lt (by simpa [mem_ball_iff_norm] using hz)
    simp [hzmem]
  · exact measurableSet_ball

private theorem diskKernel_integrable (c : ℂ) (R : ℝ) :
    Integrable (diskKernel c R) := by
  exact (integrableOn_c_sub_inv_ball c R).integrable_indicator measurableSet_ball

private noncomputable def polarDiskKernel (c : ℂ) (R : ℝ)
    (p : ℝ × ℝ) : ℂ :=
  p.1 • diskKernel c R (Complex.polarCoord.symm p)

private theorem polarDiskKernel_measurable (c : ℂ) (R : ℝ) :
    Measurable (polarDiskKernel c R) := by
  have hp : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  exact measurable_fst.smul
    ((diskKernel_measurable c R).comp hp)

private theorem polarDiskKernel_integrableOn (c : ℂ) (R : ℝ) :
    IntegrableOn (polarDiskKernel c R) Complex.polarCoord.target := by
  have hf := diskKernel_integrable c R
  constructor
  · exact (polarDiskKernel_measurable c R).aestronglyMeasurable.restrict
  · rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ p, ‖polarDiskKernel c R p‖ₑ
          ∂volume.restrict Complex.polarCoord.target) =
          ∫⁻ p in Complex.polarCoord.target,
            ENNReal.ofReal p.1 *
              ‖diskKernel c R (Complex.polarCoord.symm p)‖ₑ := by
        apply setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
        intro p hp
        have hp0 : 0 ≤ p.1 := by
          rw [Complex.polarCoord_target] at hp
          exact hp.1.le
        have henorm : ‖(p.1 : ℂ)‖ₑ = ENNReal.ofReal p.1 := by
          rw [enorm_eq_nnnorm, Complex.nnnorm_real,
            Real.nnnorm_of_nonneg hp0]
          exact (ENNReal.ofReal_eq_coe_nnreal hp0).symm
        change ‖(p.1 : ℂ) •
          diskKernel c R (Complex.polarCoord.symm p)‖ₑ = _
        rw [enorm_smul, henorm]
      _ = ∫⁻ z : ℂ, ‖diskKernel c R z‖ₑ := by
        rw [show Complex.polarCoord.target = polarCoord.target by rfl]
        exact Complex.lintegral_comp_polarCoord_symm
          (fun z : ℂ => ‖diskKernel c R z‖ₑ)
      _ < ⊤ := hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral

private theorem polarCoord_symm_eq_circleMap (ρ θ : ℝ) :
    Complex.polarCoord.symm (ρ, θ) = circleMap 0 ρ θ := by
  rw [Complex.polarCoord_symm_apply, circleMap_zero,
    Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

private theorem integral_angle_polarDiskKernel (c : ℂ) (R ρ : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        polarDiskKernel c R (ρ, θ)) =
      (2 * Real.pi * ρ) • Real.circleAverage (diskKernel c R) 0 ρ := by
  let f : ℝ → ℂ := fun θ => diskKernel c R (circleMap 0 ρ θ)
  have hfper : Function.Periodic f (2 * Real.pi) := by
    exact (periodic_circleMap 0 ρ).comp (diskKernel c R)
  have hshift := hfper.intervalIntegral_add_eq (-Real.pi) 0
  have hshift' :
      (∫ θ in -Real.pi..Real.pi, f θ) =
        ∫ θ in 0..2 * Real.pi, f θ := by
    convert hshift using 1 <;> ring_nf
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hpi]
  simp_rw [polarDiskKernel, polarCoord_symm_eq_circleMap]
  rw [intervalIntegral.integral_smul, hshift', Real.circleAverage_def]
  simp only [smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero]

private theorem diskKernel_circleAverage (c : ℂ) (R : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (hne : ‖c‖ ≠ ρ) :
    Real.circleAverage (diskKernel c R) 0 ρ =
      if ρ < R then (if ‖c‖ < ρ then 0 else c⁻¹) else 0 := by
  by_cases hρR : ρ < R
  · rw [if_pos hρR]
    calc
      Real.circleAverage (diskKernel c R) 0 ρ =
          Real.circleAverage (fun z : ℂ => (c - z)⁻¹) 0 ρ := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hnorm : ‖z‖ = ρ := by
          simpa [mem_sphere_iff_norm, abs_of_pos hρ] using hz
        rw [diskKernel, indicator_of_mem]
        simpa [mem_ball_iff_norm, hnorm]
      _ = if ‖c‖ < ρ then 0 else c⁻¹ :=
        circleAverage_c_sub_inv c hρ hne
  · rw [if_neg hρR]
    calc
      Real.circleAverage (diskKernel c R) 0 ρ =
          Real.circleAverage (fun _ : ℂ => 0) 0 ρ := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hnorm : ‖z‖ = ρ := by
          simpa [mem_sphere_iff_norm, abs_of_pos hρ] using hz
        have hznot : z ∉ ball (0 : ℂ) R := by
          simpa [mem_ball_iff_norm, hnorm] using hρR
        rw [diskKernel, Set.indicator_of_notMem hznot]
      _ = 0 := by simp [Real.circleAverage_def]

private theorem integral_diskKernel_eq_radial (c : ℂ) (R : ℝ) :
    (∫ z : ℂ, diskKernel c R z) =
      ∫ ρ in Ioi (0 : ℝ),
        (2 * Real.pi * ρ) • Real.circleAverage (diskKernel c R) 0 ρ := by
  calc
    (∫ z : ℂ, diskKernel c R z) =
        ∫ p in Complex.polarCoord.target, polarDiskKernel c R p := by
      rw [show Complex.polarCoord.target = polarCoord.target by rfl]
      exact (Complex.integral_comp_polarCoord_symm (diskKernel c R)).symm
    _ = ∫ ρ in Ioi (0 : ℝ),
          ∫ θ in Ioo (-Real.pi) Real.pi,
            polarDiskKernel c R (ρ, θ) :=
      integral_polarTarget_eq_iterated _ (polarDiskKernel_integrableOn c R)
    _ = ∫ ρ in Ioi (0 : ℝ),
          (2 * Real.pi * ρ) •
            Real.circleAverage (diskKernel c R) 0 ρ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ρ _
      exact integral_angle_polarDiskKernel c R ρ

/-- The integral of the planar Cauchy kernel over a disk containing its pole. -/
theorem integral_c_sub_inv_ball {c : ℂ} {R : ℝ} (hcR : ‖c‖ < R) :
    (∫ z in ball (0 : ℂ) R, (c - z)⁻¹) =
      (Real.pi : ℂ) * conj c := by
  have hne_ae : ∀ᵐ ρ : ℝ, ρ ≠ ‖c‖ := by
    simp [ae_iff, measure_singleton]
  have hradial :
      (∫ ρ in Ioi (0 : ℝ),
          (2 * Real.pi * ρ) •
            Real.circleAverage (diskKernel c R) 0 ρ) =
        ∫ ρ in Ioo (0 : ℝ) ‖c‖, (2 * Real.pi * ρ) • c⁻¹ := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [hne_ae] with ρ hne
    by_cases hρ : 0 < ρ
    · rw [Set.indicator_of_mem
          (show ρ ∈ Ioi (0 : ℝ) from hρ),
        diskKernel_circleAverage c R hρ hne.symm]
      by_cases hρR : ρ < R
      · rw [if_pos hρR]
        by_cases hcρ : ‖c‖ < ρ
        · rw [if_pos hcρ]
          have hnot : ρ ∉ Ioo (0 : ℝ) ‖c‖ := by simp [hcρ.not_gt]
          rw [Set.indicator_of_notMem hnot]
          simp
        · rw [if_neg hcρ]
          have hρc : ρ < ‖c‖ :=
            lt_of_le_of_ne (le_of_not_gt hcρ) hne
          rw [Set.indicator_of_mem
            (show ρ ∈ Ioo (0 : ℝ) ‖c‖ from ⟨hρ, hρc⟩)]
      · rw [if_neg hρR]
        have hnot : ρ ∉ Ioo (0 : ℝ) ‖c‖ := by
          simp only [mem_Ioo, not_and_or]
          right
          linarith
        rw [Set.indicator_of_notMem hnot]
        simp
    · have hnotIoi : ρ ∉ Ioi (0 : ℝ) := by simpa using hρ
      have hnotIoo : ρ ∉ Ioo (0 : ℝ) ‖c‖ := by
        simpa only [mem_Ioo, not_and_or, not_lt] using Or.inl (le_of_not_gt hρ)
      rw [Set.indicator_of_notMem hnotIoi,
        Set.indicator_of_notMem hnotIoo]
  rw [← integral_indicator measurableSet_ball]
  change (∫ z : ℂ, diskKernel c R z) = _
  rw [integral_diskKernel_eq_radial, hradial]
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hc0,
    intervalIntegral.integral_smul_const,
    intervalIntegral.integral_const_mul,
    integral_id]
  have heval :
      (2 * Real.pi * ((‖c‖ ^ 2 - 0 ^ 2) / 2)) =
        Real.pi * ‖c‖ ^ 2 := by ring
  rw [heval]
  by_cases hc : c = 0
  · subst c
    simp
  · have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq]
    have hcoeff :
        (Real.pi * ‖c‖ ^ 2) * (‖c‖ ^ 2)⁻¹ = Real.pi := by
      field_simp [hnorm]
    have hcoeffC :
        ((Real.pi * ‖c‖ ^ 2 : ℝ) : ℂ) *
            (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) = (Real.pi : ℂ) := by
      rw [← Complex.ofReal_mul, hcoeff]
    rw [Complex.real_smul]
    calc
      ((Real.pi * ‖c‖ ^ 2 : ℝ) : ℂ) *
          (conj c * (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ)) =
          conj c * (((Real.pi * ‖c‖ ^ 2 : ℝ) : ℂ) *
            (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by ring
      _ = conj c * (Real.pi : ℂ) := by rw [hcoeffC]
      _ = (Real.pi : ℂ) * conj c := by ring

private noncomputable def normInvMajorant (R : ℝ) (z : ℂ) : ℝ :=
  (closedBall (0 : ℂ) R).indicator (fun w => ‖w⁻¹‖) z

private theorem normInvMajorant_integrable (R : ℝ) :
    Integrable (normInvMajorant R) := by
  have hbase : IntegrableOn (fun z : ℂ => z⁻¹) (closedBall 0 R) :=
    locallyIntegrable_inv.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) R)
  have hnorm : IntegrableOn (fun z : ℂ => ‖z⁻¹‖) (closedBall 0 R) := hbase.norm
  exact hnorm.integrable_indicator measurableSet_closedBall

private theorem norm_complexVelocity_le {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) (t : ℝ) :
    ‖complexVelocity r t‖ ≤ ‖planeToComplex.toContinuousLinearMap‖ := by
  calc
    ‖complexVelocity r t‖ = ‖planeToComplex (velocity r t)‖ := rfl
    _ ≤ ‖planeToComplex.toContinuousLinearMap‖ * ‖velocity r t‖ :=
      planeToComplex.toContinuousLinearMap.le_opNorm _
    _ = ‖planeToComplex.toContinuousLinearMap‖ := by rw [hr.unit_speed, mul_one]

private theorem windingKernel_norm_setIntegral_le {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) {R : ℝ}
    (hR : ∀ t ∈ Icc (0 : ℝ) period, ‖complexCurve r t‖ < R)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) period) :
    (∫ x in ball (0 : ℂ) R,
        ‖complexVelocity r t / (complexCurve r t - x)‖) ≤
      ‖planeToComplex.toContinuousLinearMap‖ *
        ∫ z : ℂ, normInvMajorant (2 * R) z := by
  let c := complexCurve r t
  let v := complexVelocity r t
  let m : ℂ → ℝ := normInvMajorant (2 * R)
  have hcR : ‖c‖ < R := hR t (Ioc_subset_Icc_self ht)
  have hkernel : IntegrableOn (fun x : ℂ => v / (c - x)) (ball 0 R) := by
    simpa only [IntegrableOn, div_eq_mul_inv] using
      (integrableOn_c_sub_inv_ball (c := c) (R := R)).const_mul v
  have hm : Integrable m := normInvMajorant_integrable (2 * R)
  have hmcomp : Integrable (fun x : ℂ => m (c - x)) := hm.comp_sub_left c
  have hscaled : Integrable (fun x : ℂ =>
      ‖planeToComplex.toContinuousLinearMap‖ * m (c - x)) := hmcomp.const_mul _
  have hpoint (x : ℂ) (hx : x ∈ ball (0 : ℂ) R) :
      ‖v / (c - x)‖ ≤ ‖planeToComplex.toContinuousLinearMap‖ * m (c - x) := by
    have hxR : ‖x‖ < R := by simpa [mem_ball_iff_norm] using hx
    have hmem : c - x ∈ closedBall (0 : ℂ) (2 * R) := by
      rw [mem_closedBall_iff_norm]
      simp only [sub_zero]
      calc
        ‖c - x‖ ≤ ‖c‖ + ‖x‖ := norm_sub_le c x
        _ ≤ 2 * R := by linarith
    change ‖v / (c - x)‖ ≤ ‖planeToComplex.toContinuousLinearMap‖ *
      normInvMajorant (2 * R) (c - x)
    rw [normInvMajorant, indicator_of_mem hmem, norm_div]
    rw [norm_inv]
    exact mul_le_mul_of_nonneg_right (norm_complexVelocity_le hr t)
      (inv_nonneg.mpr (norm_nonneg _))
  calc
    (∫ x in ball (0 : ℂ) R, ‖v / (c - x)‖) ≤
        ∫ x in ball (0 : ℂ) R,
          ‖planeToComplex.toContinuousLinearMap‖ * m (c - x) :=
      setIntegral_mono_on hkernel.norm hscaled.integrableOn measurableSet_ball hpoint
    _ ≤ ∫ x : ℂ, ‖planeToComplex.toContinuousLinearMap‖ * m (c - x) := by
      apply setIntegral_le_integral hscaled
      filter_upwards with x
      apply mul_nonneg (norm_nonneg _)
      by_cases hx : c - x ∈ closedBall (0 : ℂ) (2 * R)
      · simp only [m, normInvMajorant, indicator_of_mem hx]
        exact norm_nonneg _
      · simp only [m, normInvMajorant, indicator_of_notMem hx]
        exact le_rfl
    _ = ‖planeToComplex.toContinuousLinearMap‖ * ∫ x : ℂ, m (c - x) := by
      rw [integral_const_mul]
    _ = ‖planeToComplex.toContinuousLinearMap‖ *
        ∫ z : ℂ, normInvMajorant (2 * R) z := by
      rw [integral_sub_left_eq_self]

private theorem windingKernel_stronglyMeasurable {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    StronglyMeasurable (fun p : ℝ × ℂ =>
      complexVelocity r p.1 / (complexCurve r p.1 - p.2)) := by
  have hv : Measurable (fun p : ℝ × ℂ => complexVelocity r p.1) :=
    (planeToComplex.continuous.comp (velocity_continuous hr)).measurable.comp measurable_fst
  have hc : Measurable (fun p : ℝ × ℂ => complexCurve r p.1) :=
    (planeToComplex.continuous.comp hr.smooth.continuous).measurable.comp measurable_fst
  exact (hv.mul ((hc.sub measurable_snd).inv)).stronglyMeasurable

private theorem windingKernel_integrable {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) {R : ℝ}
    (hR : ∀ t ∈ Icc (0 : ℝ) period, ‖complexCurve r t‖ < R) :
    Integrable (Function.uncurry fun (t : ℝ) (x : ℂ) =>
      complexVelocity r t / (complexCurve r t - x))
      ((volume.restrict (uIoc (0 : ℝ) period)).prod
        (volume.restrict (ball (0 : ℂ) R))) := by
  rw [uIoc_of_le period_pos.le]
  let f : ℝ × ℂ → ℂ := fun p =>
    complexVelocity r p.1 / (complexCurve r p.1 - p.2)
  have hfsm : StronglyMeasurable f := windingKernel_stronglyMeasurable hr
  have hinner (t : ℝ) : Integrable (fun x : ℂ =>
      complexVelocity r t / (complexCurve r t - x))
      (volume.restrict (ball (0 : ℂ) R)) := by
    simpa only [div_eq_mul_inv] using
      (integrableOn_c_sub_inv_ball (c := complexCurve r t) (R := R)).const_mul
        (complexVelocity r t)
  have houterSm : StronglyMeasurable (fun t : ℝ =>
      ∫ x in ball (0 : ℂ) R,
        ‖complexVelocity r t / (complexCurve r t - x)‖) := by
    exact hfsm.norm.integral_prod_right'
  have houter : IntegrableOn (fun t : ℝ =>
      ∫ x in ball (0 : ℂ) R,
        ‖complexVelocity r t / (complexCurve r t - x)‖)
      (Ioc (0 : ℝ) period) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      houterSm.aestronglyMeasurable.restrict
      (‖planeToComplex.toContinuousLinearMap‖ *
        ∫ z : ℂ, normInvMajorant (2 * R) z) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t
    intro ht
    have hnonneg : 0 ≤ ∫ x in ball (0 : ℂ) R,
        ‖complexVelocity r t / (complexCurve r t - x)‖ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact windingKernel_norm_setIntegral_le hr hR ht
  refine (integrable_prod_iff hfsm.aestronglyMeasurable).2 ⟨?_, houter⟩
  exact Filter.Eventually.of_forall hinner

private theorem integral_windingKernel_ball {r : ℝ → Plane}
    {R : ℝ} (hR : ∀ t ∈ Icc (0 : ℝ) period, ‖complexCurve r t‖ < R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) period) :
    (∫ x in ball (0 : ℂ) R,
      (complexVelocity r t / (complexCurve r t - x)).im) =
        Real.pi * det2 (r t) (velocity r t) := by
  let c := complexCurve r t
  let v := complexVelocity r t
  have hkernel : IntegrableOn (fun x : ℂ => v / (c - x)) (ball 0 R) := by
    simpa only [IntegrableOn, div_eq_mul_inv] using
      (integrableOn_c_sub_inv_ball (c := c) (R := R)).const_mul v
  calc
    (∫ x in ball (0 : ℂ) R, (v / (c - x)).im) =
        (∫ x in ball (0 : ℂ) R, v / (c - x)).im := by
      change (∫ x in ball (0 : ℂ) R, Complex.imCLM (v / (c - x))) =
        Complex.imCLM (∫ x in ball (0 : ℂ) R, v / (c - x))
      rw [Complex.imCLM.integral_comp_comm hkernel]
    _ = (v * ((Real.pi : ℂ) * conj c)).im := by
      congr 1
      simp_rw [div_eq_mul_inv]
      rw [integral_const_mul, integral_c_sub_inv_ball (hR t ht)]
    _ = Real.pi * det2 (r t) (velocity r t) := by
      simp only [v, c, complexVelocity, complexCurve, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
        planeToComplex_re, planeToComplex_im, det2]
      ring

/-- On a disk containing the curve, the integral of its analytic winding is
the signed area. -/
theorem analyticWinding_integrableOn_ball_and_integral_eq_signedArea
    {r : ℝ → Plane} (hr : IsPositiveSimpleClosedUnitSpeedCurve r) {R : ℝ}
    (hR : ∀ t ∈ Icc (0 : ℝ) period, ‖complexCurve r t‖ < R) :
    IntegrableOn (analyticWinding r) (ball (0 : ℂ) R) ∧
      (∫ x in ball (0 : ℂ) R, analyticWinding r x) = signedArea r := by
  let k : ℝ → ℂ → ℝ := fun t x =>
    (complexVelocity r t / (complexCurve r t - x)).im
  have hcomplex := windingKernel_integrable hr hR
  have hreal : Integrable (Function.uncurry k)
      ((volume.restrict (uIoc (0 : ℝ) period)).prod
        (volume.restrict (ball (0 : ℂ) R))) := by
    have h := Complex.imCLM.integrable_comp hcomplex
    change Integrable (fun p : ℝ × ℂ =>
      (complexVelocity r p.1 / (complexCurve r p.1 - p.2)).im) _
    simpa only [Function.comp_apply, Function.uncurry, Complex.imCLM_apply] using h
  have hswap :
      (∫ t in (0 : ℝ)..period, ∫ x in ball (0 : ℂ) R, k t x) =
        ∫ x in ball (0 : ℂ) R, ∫ t in (0 : ℝ)..period, k t x :=
    intervalIntegral_integral_swap hreal
  have hleft :
      (∫ t in (0 : ℝ)..period, ∫ x in ball (0 : ℂ) R, k t x) =
        Real.pi * ∫ t in (0 : ℝ)..period, det2 (r t) (velocity r t) := by
    calc
      (∫ t in (0 : ℝ)..period, ∫ x in ball (0 : ℂ) R, k t x) =
          ∫ t in (0 : ℝ)..period,
            Real.pi * det2 (r t) (velocity r t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) period := by
          simpa only [uIcc_of_le period_pos.le] using ht
        exact integral_windingKernel_ball hR ht'
      _ = Real.pi * ∫ t in (0 : ℝ)..period,
          det2 (r t) (velocity r t) := by
        rw [intervalIntegral.integral_const_mul]
  have hraw : IntegrableOn (fun x : ℂ =>
      ∫ t in (0 : ℝ)..period, k t x) (ball (0 : ℂ) R) := by
    have h := hreal.integral_prod_right
    simpa only [IntegrableOn, intervalIntegral.integral_of_le period_pos.le,
      uIoc_of_le period_pos.le, Function.uncurry] using h
  have hwinding : IntegrableOn (analyticWinding r) (ball (0 : ℂ) R) := by
    have heq : analyticWinding r = fun x => period⁻¹ *
        (∫ t in (0 : ℝ)..period, k t x) := by
      funext x
      unfold analyticWinding
      change (∫ t in (0 : ℝ)..period, k t x) / period =
        period⁻¹ * (∫ t in (0 : ℝ)..period, k t x)
      rw [div_eq_mul_inv, mul_comm]
    have hscaled := hraw.const_mul period⁻¹
    rw [heq]
    exact hscaled
  refine ⟨hwinding, ?_⟩
  have houter :
      (∫ x in ball (0 : ℂ) R, ∫ t in (0 : ℝ)..period, k t x) =
        Real.pi * ∫ t in (0 : ℝ)..period, det2 (r t) (velocity r t) :=
    hswap.symm.trans hleft
  rw [show analyticWinding r = fun x => period⁻¹ *
      (∫ t in (0 : ℝ)..period, k t x) by
    funext x
    simp only [analyticWinding, k, div_eq_mul_inv, mul_comm],
    integral_const_mul, houter, signedArea]
  rw [period]
  field_simp [Real.pi_ne_zero]

/-- The image of the smooth closed curve has planar volume zero. -/
theorem curveCircle_range_volume_zero {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    volume (Set.range (curveCircle r hr)) = 0 := by
  have hrange :
      Set.range (curveCircle r hr) =
        complexCurve r '' Icc (0 : ℝ) period := by
    rw [range_curveCircle]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      letI : Fact (0 < period) := ⟨period_pos⟩
      let t₀ := AddCircle.equivIco period 0 (t : AddCircle period)
      have ht₀ : (t₀ : ℝ) ∈ Ico (0 : ℝ) period := by
        simpa [t₀] using t₀.2
      have hclass : ((t₀ : ℝ) : AddCircle period) =
          (t : AddCircle period) := by
        exact AddCircle.coe_equivIco
          (p := period) (a := 0) (y := (t : AddCircle period))
      have hrt : r t₀ = r t := by
        have h := congrArg hr.periodic.lift hclass
        simpa [t₀] using h
      exact ⟨t₀, Ico_subset_Icc_self ht₀, by simp [complexCurve, hrt]⟩
    · rintro ⟨t, _, rfl⟩
      exact ⟨t, rfl⟩
  have hcurve : ContDiff ℝ 1 (complexCurve r) := by
    unfold complexCurve
    exact planeToComplex.contDiff.comp hr.smooth
  obtain ⟨K, hK⟩ := hcurve.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0 : ℝ) period) isCompact_Icc
  have hfinite :
      μH[(1 : ℝ)] (complexCurve r '' Icc (0 : ℝ) period) < ⊤ := by
    have hle := hK.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num)
    rw [ENNReal.rpow_one, hausdorffMeasure_real] at hle
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top measure_Icc_lt_top)
  have hzero : μH[(2 : ℝ)] (Set.range (curveCircle r hr)) = 0 := by
    rw [hrange]
    exact (MeasureTheory.Measure.hausdorffMeasure_zero_or_top
      (by norm_num : (1 : ℝ) < 2) _).resolve_right
      hfinite.ne
  have hzero' :
      (MeasureTheory.Measure.euclideanHausdorffMeasure 2 : Measure ℂ)
          (Set.range (curveCircle r hr)) = 0 := by
    simp [MeasureTheory.Measure.euclideanHausdorffMeasure_def, hzero]
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  simpa [Complex.finrank_real_complex] using hzero'

private theorem exists_curve_norm_bound {r : ℝ → Plane}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r) :
    ∃ R : ℝ, ∀ t ∈ Icc (0 : ℝ) period, ‖complexCurve r t‖ < R := by
  have hc : Continuous (complexCurve r) :=
    planeToComplex.continuous.comp hr.smooth.continuous
  have hcompact : IsCompact (complexCurve r '' Icc (0 : ℝ) period) :=
    isCompact_Icc.image hc
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hcompact.isBounded
  refine ⟨R, fun t ht => ?_⟩
  have hmem := hR (show complexCurve r t ∈
      complexCurve r '' Icc (0 : ℝ) period from ⟨t, ht, rfl⟩)
  simpa [mem_ball_iff_norm] using hmem

/-- Positive signed area selects the positive branch of the orientation-free
turning theorem. -/
theorem angle_period_sub_eq_period {r : ℝ → Plane} {α : ℝ → ℝ}
    (hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (hα : IsTangentAngleLift r α) :
    α period - α 0 = period := by
  rcases angle_period_sub_eq_period_or_neg hr hα with hpos | hneg
  · exact hpos
  · exfalso
    obtain ⟨R, hR⟩ := exists_curve_norm_bound hr
    obtain ⟨_, harea⟩ :=
      analyticWinding_integrableOn_ball_and_integral_eq_signedArea hr hR
    have hcurve_ae : ∀ᵐ x : ℂ ∂volume,
        x ∉ Set.range (curveCircle r hr) := by
      rw [ae_iff]
      apply measure_mono_null ?_ (curveCircle_range_volume_zero hr)
      intro x hx
      simpa only [Set.mem_setOf_eq, not_not] using hx
    have hwinding_nonpos : ∀ᵐ x : ℂ ∂volume, analyticWinding r x ≤ 0 := by
      filter_upwards [hcurve_ae] with x hx
      rcases analyticWinding_eq_zero_or_neg_one hr hα hneg x hx with hzero | hminus
      · rw [hzero]
      · rw [hminus]
        norm_num
    have hintegral_nonpos :
        (∫ x in ball (0 : ℂ) R, analyticWinding r x) ≤ 0 :=
      setIntegral_nonpos_of_ae hwinding_nonpos
    rw [harea] at hintegral_nonpos
    exact (not_lt_of_ge hintegral_nonpos) hr.positive_orientation

end

end Submission.AreaWinding
