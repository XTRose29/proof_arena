import Submission.ExactArea

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Submission


lemma lintegral_closedAnnulus_eq_polar {g : ℂ → ℝ≥0∞} {a b : ℝ} (ha : 0 < a) :
    (∫⁻ z in closedAnnulus a b, g z) =
      ∫⁻ p in Icc a b ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) := by
  have hpolar := Complex.lintegral_comp_polarCoord_symm
    ((closedAnnulus a b).indicator g)
  rw [polarCoord_target] at hpolar
  rw [← lintegral_indicator (measurableSet_closedAnnulus a b)]
  rw [← hpolar]
  have hsubset : Icc a b ×ˢ Ioo (-Real.pi) Real.pi ⊆
      Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨ha.trans_le hr.1, hθ⟩
  rw [← inter_eq_left.mpr hsubset]
  rw [← setLIntegral_indicator
    (measurableSet_Icc.prod (measurableSet_Ioo : MeasurableSet (Ioo (-Real.pi) Real.pi)))
    (t := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)]
  apply setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ioo : MeasurableSet (Ioo (-Real.pi) Real.pi)))
  intro p hp
  change ENNReal.ofReal p.1 • (closedAnnulus a b).indicator g
      (Complex.polarCoord.symm p) = _
  have hp0 : 0 < p.1 := hp.1
  have hann : Complex.polarCoord.symm p ∈ closedAnnulus a b ↔ p.1 ∈ Icc a b := by
    rw [mem_closedAnnulus_iff]
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
    rfl
  by_cases hab : p.1 ∈ Icc a b
  · rw [Set.indicator_of_mem (hann.mpr hab),
      Set.indicator_of_mem (show p ∈ Icc a b ×ˢ Ioo (-Real.pi) Real.pi from ⟨hab, hp.2⟩)]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hab (hann.mp h)),
      Set.indicator_of_notMem
        (show p ∉ Icc a b ×ˢ Ioo (-Real.pi) Real.pi by intro h; exact hab h.1)]
    simp


lemma integral_polarAngle_eq_circleAverage (F : ℂ → ℝ) (r : ℝ) :
    (∫ θ in -Real.pi..Real.pi, F (Complex.polarCoord.symm (r, θ))) =
      2 * Real.pi * Real.circleAverage F 0 r := by
  have heq : (fun θ : ℝ => F (Complex.polarCoord.symm (r, θ))) =
      fun θ => F (circleMap 0 r θ) := by
    funext θ
    simp [circleMap, ← Complex.cos_add_sin_I]
  rw [heq]
  have hperiodic : Function.Periodic (fun θ => F (circleMap 0 r θ)) (2 * Real.pi) := by
    intro θ
    change F (circleMap 0 r (θ + 2 * Real.pi)) = F (circleMap 0 r θ)
    rw [periodic_circleMap]
  have hshift := hperiodic.intervalIntegral_add_eq (-Real.pi) 0
  have hends : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hends, zero_add] at hshift
  rw [hshift, Real.circleAverage_def]
  rw [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

lemma lintegral_polarAngle_ofReal_eq_circleAverage (F : ℂ → ℝ) (r : ℝ)
    (hcont : Continuous (fun θ => F (Complex.polarCoord.symm (r, θ))))
    (hFnonneg : ∀ z, 0 ≤ F z) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (F (Complex.polarCoord.symm (r, θ)))) =
        ENNReal.ofReal (2 * Real.pi * Real.circleAverage F 0 r) := by
  let h : ℝ → ℝ := fun θ => F (Complex.polarCoord.symm (r, θ))
  have hint : IntegrableOn h (Ioo (-Real.pi) Real.pi) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun θ => hFnonneg _)]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  exact integral_polarAngle_eq_circleAverage F r


lemma weightedExteriorIntegral_eq_radial {E : ℂ → ℂ} {R a b : ℝ}
    (hE : DifferentiableOn ℂ E (ball 0 R)) (ha : 0 < a)
    (hbR : b < R) :
    (∫⁻ w in closedAnnulus a b,
        ENNReal.ofReal (‖w‖⁻¹ ^ 4) * ENNReal.ofReal (‖E w‖ ^ 2)) =
      ∫⁻ r in Icc a b, ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 4) *
        ENNReal.ofReal
          (2 * Real.pi * Real.circleAverage (fun z => ‖E z‖ ^ 2) 0 r) := by
  let H : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal p.1 *
      (ENNReal.ofReal (‖Complex.polarCoord.symm p‖⁻¹ ^ 4) *
        ENNReal.ofReal (‖E (Complex.polarCoord.symm p)‖ ^ 2))
  rw [lintegral_closedAnnulus_eq_polar
    (g := fun w => ENNReal.ofReal (‖w‖⁻¹ ^ 4) * ENNReal.ofReal (‖E w‖ ^ 2)) ha]
  change (∫⁻ p in Icc a b ×ˢ Ioo (-Real.pi) Real.pi, H p) = _
  rw [Measure.volume_eq_prod]
  have hInvCont : ContinuousOn
      (fun p : ℝ × ℝ => ‖Complex.polarCoord.symm p‖⁻¹ ^ 4)
      (Icc a b ×ˢ Ioo (-Real.pi) Real.pi) := by
    intro p hp
    have hp0 : 0 < p.1 := ha.trans_le hp.1.1
    have hpolarAt : ContinuousAt (fun q : ℝ × ℝ => Complex.polarCoord.symm q) p := by
      have h : ContinuousAt (fun q : ℝ × ℝ =>
          (q.1 : ℂ) * ((Real.cos q.2 : ℂ) + (Real.sin q.2 : ℂ) * Complex.I)) p := by
        fun_prop
      simpa only [Complex.polarCoord_symm_apply] using h
    have hnorm0 : ‖Complex.polarCoord.symm p‖ ≠ 0 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
      exact ne_of_gt hp0
    exact (hpolarAt.norm.inv₀ hnorm0).pow 4 |>.continuousWithinAt
  have hEvalCont : ContinuousOn
      (fun p : ℝ × ℝ => ‖E (Complex.polarCoord.symm p)‖ ^ 2)
      (Icc a b ×ˢ Ioo (-Real.pi) Real.pi) := by
    intro p hp
    have hp0 : 0 < p.1 := ha.trans_le hp.1.1
    have hpR : p.1 < R := hp.1.2.trans_lt hbR
    have hzR : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp0]
      exact hpR
    have hEAt : ContinuousAt E (Complex.polarCoord.symm p) :=
      (hE.differentiableAt (isOpen_ball.mem_nhds hzR)).continuousAt
    have hpolarAt : ContinuousAt (fun q : ℝ × ℝ => Complex.polarCoord.symm q) p := by
      have h : ContinuousAt (fun q : ℝ × ℝ =>
          (q.1 : ℂ) * ((Real.cos q.2 : ℂ) + (Real.sin q.2 : ℂ) * Complex.I)) p := by
        fun_prop
      simpa only [Complex.polarCoord_symm_apply] using h
    have hEval : ContinuousAt (fun q : ℝ × ℝ => E (Complex.polarCoord.symm q)) p :=
      hEAt.comp hpolarAt
    exact (hEval.norm.pow 2).continuousWithinAt
  have hmeas : AEMeasurable H
      (volume.restrict (Icc a b ×ˢ Ioo (-Real.pi) Real.pi)) := by
    have hs : MeasurableSet (Icc a b ×ˢ Ioo (-Real.pi) Real.pi) :=
      measurableSet_Icc.prod
        (measurableSet_Ioo : MeasurableSet (Ioo (-Real.pi) Real.pi))
    dsimp only [H]
    exact (continuous_fst.measurable.aemeasurable.ennreal_ofReal).mul
      ((hInvCont.aemeasurable hs).ennreal_ofReal.mul
        (hEvalCont.aemeasurable hs).ennreal_ofReal)
  rw [MeasureTheory.setLIntegral_prod H
    (by simpa [Measure.volume_eq_prod] using hmeas)]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro r hr
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrR : r < R := hr.2.trans_lt hbR
  have hnorm (θ : ℝ) : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr0]
  have hangleCont : Continuous
      (fun θ => ‖E (Complex.polarCoord.symm (r, θ))‖ ^ 2) := by
    have hpolar : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) := by
      have h : Continuous (fun θ : ℝ =>
          (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) := by
        fun_prop
      simpa only [Complex.polarCoord_symm_apply] using h
    have hmaps : MapsTo (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) univ
        (ball (0 : ℂ) R) := by
      intro θ hθ
      rw [mem_ball_zero_iff, hnorm]
      exact hrR
    exact continuousOn_univ.mp
      ((hE.continuousOn.comp hpolar.continuousOn hmaps).norm.pow 2)
  change (∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r *
        (ENNReal.ofReal (‖Complex.polarCoord.symm (r, θ)‖⁻¹ ^ 4) *
          ENNReal.ofReal (‖E (Complex.polarCoord.symm (r, θ))‖ ^ 2))) = _
  simp_rw [hnorm]
  rw [MeasureTheory.lintegral_const_mul' _ _ (by simp),
    MeasureTheory.lintegral_const_mul' _ _ (by simp),
    lintegral_polarAngle_ofReal_eq_circleAverage
      (fun z => ‖E z‖ ^ 2) r hangleCont (fun z => sq_nonneg ‖E z‖)]
  exact (mul_assoc _ _ _).symm

lemma circleAverage_comp_mul (F : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage (fun z => F ((r : ℂ) * z)) 0 1 =
      Real.circleAverage F 0 r := by
  rw [Real.circleAverage_def, Real.circleAverage_def]
  congr 2 with θ
  simp [circleMap]

lemma weightedExteriorIntegral_lower_taylor {E : ℂ → ℂ} {R a b : ℝ}
    (hE : DifferentiableOn ℂ E (ball 0 R)) (ha : 0 < a) (hbR : b < R)
    (N : ℕ) :
    (∫⁻ r in Icc a b, ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 4) *
        ENNReal.ofReal (2 * Real.pi *
          (∑ n ∈ Finset.range (N + 1),
            ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n)))) ≤
      ∫⁻ w in closedAnnulus a b,
        ENNReal.ofReal (‖w‖⁻¹ ^ 4) * ENNReal.ofReal (‖E w‖ ^ 2) := by
  rw [weightedExteriorIntegral_eq_radial hE ha hbR]
  apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
  intro r hr
  have hr0 : 0 ≤ r := (ha.trans_le hr.1).le
  have hrR : r < R := hr.2.trans_lt hbR
  have havg := finite_taylorCoeff_sq_le_circleAverage hE hr0 hrR (N + 1)
  have hca : Real.circleAverage (fun z => ‖E ((r : ℂ) * z)‖ ^ 2) 0 1 =
      Real.circleAverage (fun z => ‖E z‖ ^ 2) 0 r := by
    exact circleAverage_comp_mul (fun z => ‖E z‖ ^ 2) r
  rw [hca] at havg
  gcongr

lemma sum_range_succ_eq_zero_add_sum_Icc (u : ℕ → ℝ) (hu1 : u 1 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), u n) = u 0 + ∑ n ∈ Finset.Icc 2 N, u n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hN : N = 0
      · subst N
        simp [hu1]
      · have htwo : 2 ≤ N + 1 := by omega
        have hnotmem : N + 1 ∉ Finset.Icc 2 N := by simp
        have hIcc : insert (N + 1) (Finset.Icc 2 N) = Finset.Icc 2 (N + 1) := by
          exact Finset.insert_Icc_right_eq_Icc_add_one htwo
        rw [← hIcc, Finset.sum_insert hnotmem]
        ring

lemma sum_taylorCoeff_sq_range_split {E : ℂ → ℂ}
    (hE0 : taylorCoeff E 0 = 1) (hE1 : taylorCoeff E 1 = 0)
    (N : ℕ) (r : ℝ) :
    (∑ n ∈ Finset.range (N + 1), ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n)) =
      1 + ∑ n ∈ Finset.Icc 2 N, ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n) := by
  rw [sum_range_succ_eq_zero_add_sum_Icc
    (fun n => ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n))]
  · simp [hE0]
  · simp [hE1]

lemma mul_inv_pow_mul_pow_eq_pow_sub {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    r * r⁻¹ ^ 4 * r ^ (2 * n) = r ^ (2 * n - 3) := by
  field_simp
  rw [← pow_add]
  congr 1
  omega

lemma mul_inv_pow_four_eq_inv_pow_three {r : ℝ} (hr : r ≠ 0) :
    r * r⁻¹ ^ 4 = r⁻¹ ^ 3 := by
  field_simp

lemma radialFiniteIntegrand_eq {E : ℂ → ℂ}
    (hE0 : taylorCoeff E 0 = 1) (hE1 : taylorCoeff E 1 = 0)
    (N : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r * r⁻¹ ^ 4 *
        (2 * Real.pi * (∑ n ∈ Finset.range (N + 1),
          ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n))) =
      2 * Real.pi * (r⁻¹ ^ 3 + ∑ n ∈ Finset.Icc 2 N,
        ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) := by
  rw [sum_taylorCoeff_sq_range_split hE0 hE1]
  calc
    r * r⁻¹ ^ 4 *
        (2 * Real.pi * (1 + ∑ n ∈ Finset.Icc 2 N,
          ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n))) =
        2 * Real.pi * (r * r⁻¹ ^ 4 +
          r * r⁻¹ ^ 4 * (∑ n ∈ Finset.Icc 2 N,
            ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n))) := by ring
    _ = 2 * Real.pi * (r⁻¹ ^ 3 +
          ∑ n ∈ Finset.Icc 2 N,
            r * r⁻¹ ^ 4 * (‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n))) := by
      rw [mul_inv_pow_four_eq_inv_pow_three hr, Finset.mul_sum]
    _ = 2 * Real.pi * (r⁻¹ ^ 3 + ∑ n ∈ Finset.Icc 2 N,
        ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) := by
      congr 2
      apply Finset.sum_congr rfl
      intro n hn
      rw [show r * r⁻¹ ^ 4 * (‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n)) =
          ‖taylorCoeff E n‖ ^ 2 * (r * r⁻¹ ^ 4 * r ^ (2 * n)) by ring,
        mul_inv_pow_mul_pow_eq_pow_sub hr (Finset.mem_Icc.mp hn).1]

lemma ennreal_radialFiniteIntegrand_eq {E : ℂ → ℂ}
    (hE0 : taylorCoeff E 0 = 1) (hE1 : taylorCoeff E 1 = 0)
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 4) *
        ENNReal.ofReal (2 * Real.pi * (∑ n ∈ Finset.range (N + 1),
          ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n))) =
      ENNReal.ofReal (2 * Real.pi * (r⁻¹ ^ 3 + ∑ n ∈ Finset.Icc 2 N,
        ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3))) := by
  rw [← ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_mul (mul_nonneg hr.le (by positivity))]
  rw [radialFiniteIntegrand_eq hE0 hE1 N hr.ne']

noncomputable def radialFiniteAreaIntegrand (E : ℂ → ℂ) (N : ℕ) (r : ℝ) : ℝ :=
  2 * Real.pi * (r⁻¹ ^ 3 + ∑ n ∈ Finset.Icc 2 N,
    ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3))

lemma radialFinite_lintegral_eq_ofReal_integral {E : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hE0 : taylorCoeff E 0 = 1) (hE1 : taylorCoeff E 1 = 0)
    (N : ℕ) :
    (∫⁻ r in Icc a b, ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 4) *
        ENNReal.ofReal (2 * Real.pi * (∑ n ∈ Finset.range (N + 1),
          ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n)))) =
      ENNReal.ofReal (∫ r in a..b, radialFiniteAreaIntegrand E N r) := by
  calc
    (∫⁻ r in Icc a b, ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 4) *
        ENNReal.ofReal (2 * Real.pi * (∑ n ∈ Finset.range (N + 1),
          ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n)))) =
        ∫⁻ r in Icc a b, ENNReal.ofReal (radialFiniteAreaIntegrand E N r) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro r hr
      exact ennreal_radialFiniteIntegrand_eq hE0 hE1 N (ha.trans_le hr.1)
    _ = ENNReal.ofReal (∫ r in a..b, radialFiniteAreaIntegrand E N r) := by
      have hcont : ContinuousOn (radialFiniteAreaIntegrand E N) (Icc a b) := by
        intro r hr
        have hr0 : 0 < r := ha.trans_le hr.1
        have hinv : ContinuousAt (fun x : ℝ => x⁻¹) r := continuousAt_id.inv₀ hr0.ne'
        unfold radialFiniteAreaIntegrand
        fun_prop
      have hint : IntegrableOn (radialFiniteAreaIntegrand E N) (Icc a b) :=
        hcont.integrableOn_Icc
      have hnonneg : ∀ r ∈ Icc a b, 0 ≤ radialFiniteAreaIntegrand E N r := by
        intro r hr
        have hr0 : 0 < r := ha.trans_le hr.1
        unfold radialFiniteAreaIntegrand
        positivity
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Icc).2
          (Filter.Eventually.of_forall fun r hr => hnonneg r hr))]
      congr 1
      rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]

lemma integral_inv_pow_three {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ r in a..1, r⁻¹ ^ 3) = (a⁻¹ ^ 2 - 1) / 2 := by
  let F : ℝ → ℝ := fun r => -(1 / 2) * (r⁻¹ ^ 2)
  have hFcont : ContinuousOn F (Icc a 1) := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (ha.trans_le hr.1)
    dsimp only [F]
    fun_prop
  have hderiv : ∀ r ∈ Ioo a 1, HasDerivAt F (r⁻¹ ^ 3) r := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (ha.trans hr.1)
    have h := ((hasDerivAt_inv hr0).pow 2).const_mul (-(1 / 2 : ℝ))
    have hval : -(1 / 2 : ℝ) *
        ((2 : ℝ) * r⁻¹ ^ (2 - 1) * -(r ^ 2)⁻¹) = r⁻¹ ^ 3 := by
      field_simp
      simpa [one_div] using mul_inv_cancel₀ hr0
    have hfun : (fun y : ℝ => -(1 / 2) * ((fun y : ℝ => y⁻¹) ^ 2) y) = F := by
      funext y
      rfl
    rw [hfun] at h
    exact h.congr_deriv hval
  have hint : IntervalIntegrable (fun r : ℝ => r⁻¹ ^ 3) volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha1]
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (ha.trans_le hr.1)
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha1 hFcont hderiv hint]
  dsimp only [F]
  field_simp
  ring

lemma integral_pow_two_mul_sub_three {a : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (∫ r in a..1, r ^ (2 * n - 3)) =
      (1 - a ^ (2 * n - 2)) / ((2 * n - 2 : ℕ) : ℝ) := by
  rw [integral_pow]
  have hexp : 2 * n - 3 + 1 = 2 * n - 2 := by omega
  rw [hexp, one_pow]
  congr 1
  exact_mod_cast hexp


noncomputable def finiteAreaCoefficientSum (E : ℂ → ℂ) (N : ℕ) (a : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ‖taylorCoeff E n‖ ^ 2 / ((n - 1 : ℕ) : ℝ) * (1 - a ^ (2 * n - 2))

noncomputable def areaCoefficientSum (E : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, ‖taylorCoeff E n‖ ^ 2 / ((n - 1 : ℕ) : ℝ)

@[simp]
lemma finiteAreaCoefficientSum_zero (E : ℂ → ℂ) (N : ℕ) :
    finiteAreaCoefficientSum E N 0 = areaCoefficientSum E N := by
  unfold finiteAreaCoefficientSum areaCoefficientSum
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 := (Finset.mem_Icc.mp hn).1
  have hpow : 2 * n - 2 ≠ 0 := by omega
  rw [zero_pow hpow]
  ring

lemma integral_radialFiniteAreaIntegrand {E : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    (∫ r in a..1, radialFiniteAreaIntegrand E N r) =
      Real.pi * (a⁻¹ ^ 2 - 1 + finiteAreaCoefficientSum E N a) := by
  have hinv : IntervalIntegrable (fun r : ℝ => r⁻¹ ^ 3) volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha1]
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (ha.trans_le hr.1)
    fun_prop
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      IntervalIntegrable
        (fun r : ℝ => ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) volume a 1 := by
    intro n hn
    exact (show Continuous (fun r : ℝ =>
      ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) by fun_prop).intervalIntegrable
        (μ := volume) a 1
  have hsum : IntervalIntegrable
      (fun r : ℝ => ∑ n ∈ Finset.Icc 2 N,
        ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) volume a 1 :=
    (show Continuous (fun r : ℝ => ∑ n ∈ Finset.Icc 2 N,
      ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) by fun_prop).intervalIntegrable
      (μ := volume) a 1
  unfold radialFiniteAreaIntegrand
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hinv hsum,
    integral_inv_pow_three ha ha1,
    intervalIntegral.integral_finsetSum hterm]
  have hmonomial (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      (∫ r in a..1, ‖taylorCoeff E n‖ ^ 2 * r ^ (2 * n - 3)) =
        ‖taylorCoeff E n‖ ^ 2 *
          ((1 - a ^ (2 * n - 2)) / ((2 * n - 2 : ℕ) : ℝ)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_pow_two_mul_sub_three (Finset.mem_Icc.mp hn).1]
  rw [Finset.sum_congr rfl hmonomial]
  unfold finiteAreaCoefficientSum
  have hden (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      (((2 * n - 2 : ℕ) : ℝ)) = 2 * ((n - 1 : ℕ) : ℝ) := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have heq : 2 * n - 2 = 2 * (n - 1) := by omega
    rw [heq]
    push_cast
    rfl
  have hsumEq :
      2 * (∑ n ∈ Finset.Icc 2 N,
        ‖taylorCoeff E n‖ ^ 2 *
          ((1 - a ^ (2 * n - 2)) / ((2 * n - 2 : ℕ) : ℝ))) =
        finiteAreaCoefficientSum E N a := by
    unfold finiteAreaCoefficientSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hden n hn]
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hpos : (0 : ℝ) < (n - 1 : ℕ) := by
      exact_mod_cast (show 0 < n - 1 by omega : 0 < n - 1)
    field_simp [hpos.ne']
  rw [show 2 * Real.pi *
      ((a⁻¹ ^ 2 - 1) / 2 + ∑ n ∈ Finset.Icc 2 N,
        ‖taylorCoeff E n‖ ^ 2 *
          ((1 - a ^ (2 * n - 2)) / ((2 * n - 2 : ℕ) : ℝ))) =
      Real.pi * (a⁻¹ ^ 2 - 1 +
        2 * (∑ n ∈ Finset.Icc 2 N,
          ‖taylorCoeff E n‖ ^ 2 *
            ((1 - a ^ (2 * n - 2)) / ((2 * n - 2 : ℕ) : ℝ)))) by ring,
    hsumEq]
  rfl

lemma finiteAreaCoefficientSum_le_one_of_exact_area
    {f L : ℂ → ℂ} {R A ρ : ℝ} {M : NNReal}
    (hR1 : 1 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hA : 0 < A) (h1A : 1 ≤ A) (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (N : ℕ) :
    finiteAreaCoefficientSum (exteriorDerivativeTransform L) N (1 / A) ≤ 1 := by
  have hR : 0 < R := lt_trans zero_lt_one hR1
  have hrecip : 1 / R < 1 := by
    simpa using one_div_lt_one_div_of_lt one_pos hR1
  have hE : DifferentiableOn ℂ (exteriorDerivativeTransform L) (ball 0 R) :=
    exteriorDerivativeTransform_differentiableOn hL
  have ha : 0 < 1 / A := one_div_pos.mpr hA
  have ha1 : 1 / A ≤ 1 := by
    simpa using one_div_le_one_div_of_le one_pos h1A
  have harea := exteriorTransform_area_le_exact hR hf hL hL0 hexp hrecip h1A hA
    hAρ hρR hP hK
  have hchange := exteriorTransform_area_eq_inner_integral hR hf hL hexp
    hrecip one_pos h1A
  rw [hchange] at harea
  have harea' :
      (∫⁻ w in closedAnnulus (1 / A) 1,
        ENNReal.ofReal (‖w‖⁻¹ ^ 4) *
          ENNReal.ofReal (‖exteriorDerivativeTransform L w‖ ^ 2)) ≤
        ENNReal.ofReal A ^ 2 * NNReal.pi := by
    simpa only [one_div_one] using harea
  have hlower := weightedExteriorIntegral_lower_taylor hE ha hR1 N
  rw [radialFinite_lintegral_eq_ofReal_integral ha ha1
      (taylorCoeff_exteriorDerivativeTransform_zero hL0)
      (taylorCoeff_exteriorDerivativeTransform_one hR hL hL0) N,
    integral_radialFiniteAreaIntegrand ha ha1 N] at hlower
  have hbound := hlower.trans harea'
  have hright : ENNReal.ofReal A ^ 2 * NNReal.pi =
      ENNReal.ofReal (A ^ 2 * Real.pi) := by
    rw [← ENNReal.ofReal_pow hA.le]
    rw [ENNReal.coe_nnreal_eq]
    rw [← ENNReal.ofReal_mul (sq_nonneg A)]
    rfl
  rw [hright, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hbound
  have hrecipSq : (1 / A)⁻¹ ^ 2 = A ^ 2 := by
    field_simp [hA.ne']
  rw [hrecipSq] at hbound
  nlinarith [Real.pi_pos]

lemma areaCoefficientSum_exteriorDerivativeTransform_le_one
    {f L : ℂ → ℂ} {R : ℝ}
    (hR1 : 1 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (N : ℕ) :
    areaCoefficientSum (exteriorDerivativeTransform L) N ≤ 1 := by
  have hR : 0 < R := lt_trans zero_lt_one hR1
  rcases exists_exteriorAnalyticSlope_lipschitzOn hR hL with
    ⟨ρ, hρ, hρR, M, hM⟩
  obtain ⟨C : ℕ, hC⟩ := exists_nat_gt
    (max (max 1 (1 / ρ)) (((M : NNReal) : ℝ) + 1))
  have hmaxC : max 1 (1 / ρ) < (C : ℝ) :=
    (le_max_left (max 1 (1 / ρ)) (((M : NNReal) : ℝ) + 1)).trans_lt hC
  have hC1 : 1 < (C : ℝ) := (le_max_left 1 (1 / ρ)).trans_lt hmaxC
  have hCρ : 1 / ρ < (C : ℝ) := (le_max_right 1 (1 / ρ)).trans_lt hmaxC
  have hCM : ((M : NNReal) : ℝ) + 1 < (C : ℝ) :=
    (le_max_right (max 1 (1 / ρ)) (((M : NNReal) : ℝ) + 1)).trans_lt hC
  have hbound (m : ℕ) :
      finiteAreaCoefficientSum (exteriorDerivativeTransform L) N
        (1 / (((m + C : ℕ) : ℝ))) ≤ 1 := by
    let A : ℝ := (m + C : ℕ)
    have hCA : (C : ℝ) ≤ A := by
      dsimp only [A]
      exact_mod_cast Nat.le_add_left C m
    have hA : 0 < A := lt_trans zero_lt_one (hC1.trans_le hCA)
    have h1A : 1 ≤ A := (le_of_lt hC1).trans hCA
    have hAρ : 1 / A < ρ := by
      have hrecipA : 1 / ρ < A := hCρ.trans_le hCA
      simpa [one_div_div] using
        one_div_lt_one_div_of_lt (one_div_pos.mpr hρ) hrecipA
    have hAsq : ((M : NNReal) : ℝ) < A ^ 2 := by
      have hMltA : ((M : NNReal) : ℝ) < A := by linarith
      nlinarith
    have hK : M * interiorReflectionLipschitzConstant A < 1 := by
      apply NNReal.coe_lt_coe.mp
      change (M : ℝ) *
        (((interiorReflectionLipschitzConstant A : NNReal) : ℝ)) < 1
      have hreflect : ((interiorReflectionLipschitzConstant A : NNReal) : ℝ) =
          1 / A ^ 2 := rfl
      rw [hreflect]
      simpa [div_eq_mul_inv] using (div_lt_one (sq_pos_of_pos hA)).2 hAsq
    exact finiteAreaCoefficientSum_le_one_of_exact_area hR1 hf hL hL0 hexp
      hA h1A hAρ hρR hM hK N
  have hAat : Tendsto (fun m : ℕ => (((m + C : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat C)
  have ha0 : Tendsto (fun m : ℕ => 1 / (((m + C : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hAat
  have hcont : Continuous (finiteAreaCoefficientSum
      (exteriorDerivativeTransform L) N) := by
    unfold finiteAreaCoefficientSum
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp ha0
  rw [← finiteAreaCoefficientSum_zero]
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall hbound

lemma taylorCoeff_id_mul_deriv {H : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hH : DifferentiableOn ℂ H (ball 0 R)) (n : ℕ) :
    taylorCoeff (id * deriv H) n = (n : ℕ) * taylorCoeff H n := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hid : ContDiffAt ℂ n (id : ℂ → ℂ) 0 := contDiff_id.contDiffAt
  have hHd : DifferentiableOn ℂ (deriv H) (ball 0 R) := hH.deriv isOpen_ball
  have hHdCont : ContDiffAt ℂ n (deriv H) 0 :=
    (hHd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  rw [taylorCoeff_mul hid hHdCont]
  cases n with
  | zero => simp [taylorCoeff, iteratedDeriv_id]
  | succ n =>
      rw [Finset.sum_eq_single 1]
      · rw [show taylorCoeff (id : ℂ → ℂ) 1 = 1 by
          simp [taylorCoeff, iteratedDeriv_id], one_mul, taylorCoeff_deriv]
        simp
      · intro b hb hb1
        simp [taylorCoeff, iteratedDeriv_id, hb1]
      · simp

lemma taylorCoeff_sub {F G : ℂ → ℂ} {n : ℕ}
    (hF : ContDiffAt ℂ n F 0) (hG : ContDiffAt ℂ n G 0) :
    taylorCoeff (F - G) n = taylorCoeff F n - taylorCoeff G n := by
  rw [taylorCoeff, taylorCoeff, taylorCoeff, iteratedDeriv_sub hF hG]
  ring

lemma deriv_exteriorAnalyticFactor_eq {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    Set.EqOn (deriv (exteriorAnalyticFactor L))
      (fun z => -exteriorAnalyticFactor L z * deriv L z) (ball 0 R) := by
  intro z hz
  have hLAt : DifferentiableAt ℂ L z :=
    hL.differentiableAt (isOpen_ball.mem_nhds hz)
  change deriv (fun w : ℂ => Complex.exp (-L w)) z =
    -Complex.exp (-L z) * deriv L z
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (-L w))
      (Complex.exp (-L z) * -deriv L z) z := by
    simpa only [Pi.neg_apply] using hLAt.hasDerivAt.neg.cexp
  rw [hd.deriv]
  ring

lemma exteriorDerivativeTransform_eq_factor_sub_deriv {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    Set.EqOn (exteriorDerivativeTransform L)
      (exteriorAnalyticFactor L - id * deriv (exteriorAnalyticFactor L)) (ball 0 R) := by
  intro z hz
  rw [Pi.sub_apply, Pi.mul_apply, id_eq,
    deriv_exteriorAnalyticFactor_eq hL hz]
  simp [exteriorDerivativeTransform, exteriorAnalyticFactor]
  ring

lemma taylorCoeff_exteriorDerivativeTransform {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (n : ℕ) :
    taylorCoeff (exteriorDerivativeTransform L) n =
      (1 - (n : ℂ)) * taylorCoeff (exteriorAnalyticFactor L) n := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hEq := exteriorDerivativeTransform_eq_factor_sub_deriv hL
  have hiter := hEq.iteratedDeriv_of_isOpen isOpen_ball n hzero
  have hcoef : taylorCoeff (exteriorDerivativeTransform L) n =
      taylorCoeff (exteriorAnalyticFactor L -
        id * deriv (exteriorAnalyticFactor L)) n := by
    simpa only [taylorCoeff] using congrArg (fun z : ℂ => z / n.factorial) hiter
  rw [hcoef]
  have hH := exteriorAnalyticFactor_differentiableOn hL
  have hHCont : ContDiffAt ℂ n (exteriorAnalyticFactor L) 0 :=
    (hH.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  have hprod : DifferentiableOn ℂ (id * deriv (exteriorAnalyticFactor L)) (ball 0 R) := by
    exact differentiableOn_id.mul (hH.deriv isOpen_ball)
  have hprodCont : ContDiffAt ℂ n (id * deriv (exteriorAnalyticFactor L)) 0 :=
    (hprod.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  rw [taylorCoeff_sub hHCont hprodCont,
    taylorCoeff_id_mul_deriv hR hH n]
  ring

noncomputable def exteriorFactorAreaSum (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ((n - 1 : ℕ) : ℝ) * ‖taylorCoeff (exteriorAnalyticFactor L) n‖ ^ 2

lemma areaCoefficientSum_exteriorDerivativeTransform_eq_factor
    {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (N : ℕ) :
    areaCoefficientSum (exteriorDerivativeTransform L) N =
      exteriorFactorAreaSum L N := by
  unfold areaCoefficientSum exteriorFactorAreaSum
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 := (Finset.mem_Icc.mp hn).1
  rw [taylorCoeff_exteriorDerivativeTransform hR hL]
  have hcast : (1 : ℂ) - (n : ℂ) = -((n - 1 : ℕ) : ℂ) := by
    have hnEq : n = 1 + (n - 1) := by omega
    have hcastn : (n : ℂ) = 1 + ((n - 1 : ℕ) : ℂ) := by
      calc
        (n : ℂ) = ((1 + (n - 1) : ℕ) : ℂ) := congrArg (fun k : ℕ => (k : ℂ)) hnEq
        _ = 1 + ((n - 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [hcastn]
    ring
  rw [hcast, norm_mul, norm_neg, norm_natCast]
  have hpos : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (show 0 < n - 1 by omega : 0 < n - 1)
  field_simp [hpos.ne']

lemma exteriorFactorAreaSum_le_one
    {f L : ℂ → ℂ} {R : ℝ}
    (hR1 : 1 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (N : ℕ) : exteriorFactorAreaSum L N ≤ 1 := by
  rw [← areaCoefficientSum_exteriorDerivativeTransform_eq_factor
    (lt_trans zero_lt_one hR1) hL]
  exact areaCoefficientSum_exteriorDerivativeTransform_le_one hR1 hf hL hL0 hexp N


end Submission
