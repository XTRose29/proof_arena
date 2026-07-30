import Submission.CanonicalStep

open Filter Function Metric Set

namespace Submission

lemma exists_normalizedLog_germ
    {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (hH1 : deriv H 0 = 1) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 0 ∧ L 0 = 0 ∧
      Complex.exp ∘ L =ᶠ[nhds 0] dslope H 0 := by
  have hq : AnalyticAt ℂ (dslope H 0) 0 :=
    hH.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
  have hq0 : dslope H 0 0 = 1 := by
    simp [dslope_same, hH1]
  have hslit : dslope H 0 0 ∈ Complex.slitPlane := by
    rw [hq0]
    exact Complex.one_mem_slitPlane
  have hmem : ∀ᶠ z in nhds (0 : ℂ), dslope H 0 z ∈ Complex.slitPlane :=
    hq.continuousAt (Complex.isOpen_slitPlane.mem_nhds hslit)
  let L : ℂ → ℂ := fun z ↦ Complex.log (dslope H 0 z)
  refine ⟨L, hq.clog hslit, ?_, ?_⟩
  · dsimp only [L]
    rw [hq0, Complex.log_one]
  filter_upwards [hmem] with z hz
  exact Complex.exp_log (Complex.slitPlane_ne_zero hz)

lemma formalLogarithmicCoeff_eq_logarithmicCoeff_of_germ
    {H L : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (hL : AnalyticAt ℂ L 0) (hH1 : deriv H 0 = 1) (hL0 : L 0 = 0)
    (hexp : Complex.exp ∘ L =ᶠ[nhds 0] dslope H 0) (n : ℕ) :
    formalLogarithmicCoeff (taylorCoeff H) n = logarithmicCoeff L n := by
  have hall : ∀ᶠ z in nhds (0 : ℂ),
      AnalyticAt ℂ H z ∧ AnalyticAt ℂ L z ∧
        Complex.exp (L z) = dslope H 0 z := by
    filter_upwards [hH.eventually_analyticAt, hL.eventually_analyticAt, hexp]
      with z hHz hLz heq
    exact ⟨hHz, hLz, heq⟩
  rcases Metric.mem_nhds_iff.mp hall with ⟨R, hR, hball⟩
  apply formalLogarithmicCoeff_eq_logarithmicCoeff hR
    (fun z hz ↦ (hball hz).1.differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hball hz).2.1.differentiableAt.differentiableWithinAt)
    hL0
  · simp [taylorCoeff, hH1]
  · intro z hz
    exact (hball hz).2.2

noncomputable def normalizedRotate (H : ℂ → ℂ) (eta z : ℂ) : ℂ :=
  H (eta * z) / eta

lemma normalizedRotate_zero
    {H : ℂ → ℂ} (hH0 : H 0 = 0) {eta : ℂ} :
    normalizedRotate H eta 0 = 0 := by
  simp [normalizedRotate, hH0]

lemma normalizedRotate_analyticAt
    {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) {eta : ℂ}
    (_heta : eta ≠ 0) :
    AnalyticAt ℂ (normalizedRotate H eta) 0 := by
  unfold normalizedRotate
  exact (hH.comp_of_eq (by fun_prop) (by simp)).div_const

lemma deriv_normalizedRotate
    {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) {eta : ℂ}
    (heta : eta ≠ 0) :
    deriv (normalizedRotate H eta) 0 = deriv H 0 := by
  have hinner : HasDerivAt (fun z : ℂ ↦ eta * z) eta 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul eta
  have hcomp : HasDerivAt (H ∘ fun z : ℂ ↦ eta * z)
      (deriv H 0 * eta) 0 :=
    hH.differentiableAt.hasDerivAt.comp_of_eq 0 hinner (by simp)
  rw [show normalizedRotate H eta =
      fun z ↦ (H ∘ fun w : ℂ ↦ eta * w) z / eta by rfl,
    (hcomp.div_const eta).deriv]
  field_simp [heta]

lemma dslope_normalizedRotate
    {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) {eta : ℂ} (heta : eta ≠ 0) (z : ℂ) :
    dslope (normalizedRotate H eta) 0 z = dslope H 0 (eta * z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [dslope_same, deriv_normalizedRotate hH heta]
  · have hetaz : eta * z ≠ 0 := mul_ne_zero heta hz
    rw [dslope_of_ne _ hz, dslope_of_ne _ hetaz]
    simp [slope, normalizedRotate, hH0, div_eq_mul_inv]
    field_simp [heta, hz]

lemma normalizedRotate_log_exp
    {H L : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) {eta : ℂ} (heta : eta ≠ 0)
    (hexp : Complex.exp ∘ L =ᶠ[nhds 0] dslope H 0) :
    Complex.exp ∘ (fun z ↦ L (eta * z)) =ᶠ[nhds 0]
      dslope (normalizedRotate H eta) 0 := by
  have htend : Tendsto (fun z : ℂ ↦ eta * z) (nhds 0) (nhds 0) := by
    have hc : Tendsto (fun _ : ℂ ↦ eta) (nhds 0) (nhds eta) :=
      tendsto_const_nhds
    have hi : Tendsto (fun z : ℂ ↦ z) (nhds 0) (nhds 0) := tendsto_id
    simpa only [mul_zero] using hc.mul hi
  filter_upwards [hexp.comp_tendsto htend] with z hz
  simpa only [comp_apply, dslope_normalizedRotate hH hH0 heta z] using hz

lemma NormalizedDiskEmbedding.OmittedPointStep.contraction_ne_zero
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : step.contraction ≠ 0 := by
  have hb : step.b ≠ 0 := by
    intro hb
    have ha : step.a = 0 := by
      have h := step.b_sq
      rw [hb] at h
      simpa using h.symm
    apply step.a_omitted
    exact ⟨0, mem_ball_self zero_lt_one, by simpa [ha] using E.map_base⟩
  unfold NormalizedDiskEmbedding.OmittedPointStep.contraction
  apply div_ne_zero (mul_ne_zero (by norm_num) hb)
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖step.b‖ ^ 2).ne'

noncomputable def NormalizedDiskEmbedding.OmittedPointStep.realRadius
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : ℝ :=
  ‖step.contraction‖

noncomputable def NormalizedDiskEmbedding.OmittedPointStep.canonicalOmega
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : ℂ :=
  starRingEnd ℂ step.contraction / (step.realRadius : ℂ)

lemma NormalizedDiskEmbedding.OmittedPointStep.realRadius_pos
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : 0 < step.realRadius := by
  exact norm_pos_iff.mpr step.contraction_ne_zero

lemma NormalizedDiskEmbedding.OmittedPointStep.realRadius_lt_one
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : step.realRadius < 1 :=
  step.norm_contraction_lt_one

lemma NormalizedDiskEmbedding.OmittedPointStep.norm_canonicalOmega
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : ‖step.canonicalOmega‖ = 1 := by
  have hr : step.realRadius ≠ 0 := step.realRadius_pos.ne'
  unfold NormalizedDiskEmbedding.OmittedPointStep.canonicalOmega
  change ‖star step.contraction / (step.realRadius : ℂ)‖ = 1
  rw [norm_div, norm_star]
  change step.realRadius / ‖(step.realRadius : ℂ)‖ = 1
  rw [Complex.norm_real, Real.norm_of_nonneg step.realRadius_pos.le, div_self hr]

lemma NormalizedDiskEmbedding.OmittedPointStep.canonicalOmega_ne_zero
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : step.canonicalOmega ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [step.norm_canonicalOmega]; norm_num)

lemma NormalizedDiskEmbedding.OmittedPointStep.canonicalOmega_unit
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) :
    starRingEnd ℂ step.canonicalOmega * step.canonicalOmega = 1 := by
  rw [Complex.conj_mul', step.norm_canonicalOmega]
  norm_num

lemma NormalizedDiskEmbedding.OmittedPointStep.contraction_eq_radius_phase
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) :
    step.contraction =
      (step.realRadius : ℂ) * starRingEnd ℂ step.canonicalOmega := by
  have hr : (step.realRadius : ℂ) ≠ 0 := by
    exact_mod_cast step.realRadius_pos.ne'
  unfold NormalizedDiskEmbedding.OmittedPointStep.canonicalOmega
  change step.contraction =
    (step.realRadius : ℂ) * star (star step.contraction / (step.realRadius : ℂ))
  rw [star_div₀, star_star]
  have hstar : star (step.realRadius : ℂ) = (step.realRadius : ℂ) :=
    Complex.conj_ofReal step.realRadius
  rw [hstar]
  field_simp [hr]

lemma NormalizedDiskEmbedding.OmittedPointStep.inverseMap_eq_canonicalTransition
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    step.inverseMap z =
      starRingEnd ℂ step.canonicalOmega *
        canonicalTransition (step.realRadius : ℂ) step.canonicalOmega z := by
  rw [step.inverseMap_eq_contraction hz, step.contraction_eq_radius_phase]
  simp only [map_mul, starRingEnd_self_apply]
  rw [show starRingEnd ℂ (step.realRadius : ℂ) = (step.realRadius : ℂ) by
    exact Complex.conj_ofReal step.realRadius]
  unfold canonicalTransition
  rw [show starRingEnd ℂ step.canonicalOmega *
      (z * ((step.realRadius : ℂ) + step.canonicalOmega * z) /
        (1 + (step.realRadius : ℂ) * step.canonicalOmega * z)) =
      (starRingEnd ℂ step.canonicalOmega *
        (z * ((step.realRadius : ℂ) + step.canonicalOmega * z))) /
          (1 + (step.realRadius : ℂ) * step.canonicalOmega * z) by ring]
  congr 1
  calc
    z * (z + (step.realRadius : ℂ) *
        starRingEnd ℂ step.canonicalOmega) =
      z * ((step.realRadius : ℂ) *
        starRingEnd ℂ step.canonicalOmega +
          (starRingEnd ℂ step.canonicalOmega * step.canonicalOmega) * z) := by
      rw [step.canonicalOmega_unit]
      ring
    _ = starRingEnd ℂ step.canonicalOmega *
        (z * ((step.realRadius : ℂ) + step.canonicalOmega * z)) := by
      ring

lemma NormalizedDiskEmbedding.OmittedPointStep.normalizedInverse_step_eq_canonical
    {E₀ E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (step : E.OmittedPointStep F)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse z =
      normalizedRotate reach.normalizedInverse
          (starRingEnd ℂ step.canonicalOmega)
          (canonicalTransition (step.realRadius : ℂ) step.canonicalOmega z) /
        (step.realRadius : ℂ) := by
  rw [step.normalizedInverse_step, step.inverseMap_eq_canonicalTransition hz,
    step.contraction_eq_radius_phase]
  unfold normalizedRotate
  have hr : (step.realRadius : ℂ) ≠ 0 := by
    exact_mod_cast step.realRadius_pos.ne'
  have homega : starRingEnd ℂ step.canonicalOmega ≠ 0 := by
    intro hzero
    have h := congrArg (starRingEnd ℂ) hzero
    simp only [map_zero, starRingEnd_self_apply] at h
    exact step.canonicalOmega_ne_zero h
  field_simp [hr, homega]

lemma NormalizedDiskEmbedding.OmittedPointStep.canonicalUpdatedLog_exp_step
    {E₀ E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (step : E.OmittedPointStep F)
    {L : ℂ → ℂ} (hL0 : L 0 = 0)
    (hLexp : Complex.exp ∘ L =ᶠ[nhds 0]
      dslope (normalizedRotate reach.normalizedInverse
        (starRingEnd ℂ step.canonicalOmega)) 0) :
    Complex.exp ∘
        canonicalUpdatedLog L (step.realRadius : ℂ) step.canonicalOmega =ᶠ[nhds 0]
      dslope (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse 0 := by
  let r : ℂ := step.realRadius
  let omega : ℂ := step.canonicalOmega
  let eta : ℂ := starRingEnd ℂ omega
  let chi : ℂ → ℂ := canonicalTransition r omega
  let Hrot : ℂ → ℂ := normalizedRotate reach.normalizedInverse eta
  let Hnew : ℂ → ℂ :=
    (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse
  have hr : r ≠ 0 := by
    dsimp only [r]
    exact_mod_cast step.realRadius_pos.ne'
  have heta : eta ≠ 0 := by
    dsimp only [eta, omega]
    intro hzero
    have h := congrArg (starRingEnd ℂ) hzero
    simp only [map_zero, starRingEnd_self_apply] at h
    exact step.canonicalOmega_ne_zero h
  have hHrot0 : Hrot 0 = 0 := by
    exact normalizedRotate_zero reach.normalizedInverse_zero
  have hHnew0 : Hnew 0 = 0 := by
    exact (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse_zero
  have hchi0 : chi 0 = 0 := canonicalTransition_zero r omega
  have hchiT : Tendsto chi (nhds 0) (nhds 0) := by
    have hc : ContinuousAt chi 0 := by
      simpa only [chi] using (canonicalTransition_analyticAt r omega).continuousAt
    have hcT : Tendsto chi (nhds 0) (nhds (chi 0)) := hc
    simpa only [hchi0] using hcT
  have hLchi : Complex.exp ∘ L ∘ chi =ᶠ[nhds 0]
      dslope Hrot 0 ∘ chi := by
    exact hLexp.comp_tendsto hchiT
  let p : ℂ → ℂ := fun z ↦ 1 + omega / r * z
  let q : ℂ → ℂ := fun z ↦ 1 + r * omega * z
  have hpT : Tendsto p (nhds 0) (nhds 1) := by
    have hp : ContinuousAt p 0 := by
      dsimp only [p]
      fun_prop
    have hp0 : p 0 = 1 := by simp [p]
    rw [← hp0]
    exact hp
  have hqT : Tendsto q (nhds 0) (nhds 1) := by
    have hq : ContinuousAt q 0 := by
      dsimp only [q]
      fun_prop
    have hq0 : q 0 = 1 := by simp [q]
    rw [← hq0]
    exact hq
  have hpSlit : ∀ᶠ z in nhds (0 : ℂ), p z ∈ Complex.slitPlane :=
    hpT (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hqSlit : ∀ᶠ z in nhds (0 : ℂ), q z ∈ Complex.slitPlane :=
    hqT (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hball : ∀ᶠ z in nhds (0 : ℂ), z ∈ ball (0 : ℂ) 1 :=
    isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)
  filter_upwards [hLchi, hpSlit, hqSlit, hball] with z hLz hpz hqz hz
  change Complex.exp (canonicalUpdatedLog L r omega z) = dslope Hnew 0 z
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [canonicalUpdatedLog, canonicalTransition_zero, hL0]
    simp [dslope_same, Hnew,
      NormalizedDiskEmbedding.ReachableFrom.deriv_normalizedInverse]
  · have hqne : q z ≠ 0 := Complex.slitPlane_ne_zero hqz
    have hstep : Hnew z = Hrot (chi z) / r := by
      simpa only [Hnew, Hrot, chi, r, omega, eta] using
        step.normalizedInverse_step_eq_canonical reach hz
    have hrotSlope : chi z * dslope Hrot 0 (chi z) = Hrot (chi z) := by
      simpa only [sub_zero, smul_eq_mul] using
        sub_smul_dslope_of_zero hHrot0 (chi z)
    have hnewSlope : z * dslope Hnew 0 z = Hnew z := by
      simpa only [sub_zero, smul_eq_mul] using
        sub_smul_dslope_of_zero hHnew0 z
    have hchi : chi z / r = z * (p z / q z) := by
      dsimp only [chi, p, q]
      unfold canonicalTransition
      field_simp [hr, hqne]
    have hslope : dslope Hrot 0 (chi z) * (p z / q z) =
        dslope Hnew 0 z := by
      apply (mul_left_cancel₀ hz0)
      calc
        z * (dslope Hrot 0 (chi z) * (p z / q z)) =
            (chi z / r) * dslope Hrot 0 (chi z) := by
          rw [hchi]
          ring
        _ = Hrot (chi z) / r := by rw [← hrotSlope]; ring
        _ = Hnew z := hstep.symm
        _ = z * dslope Hnew 0 z := hnewSlope.symm
    rw [canonicalUpdatedLog, Complex.exp_sub, Complex.exp_add,
      Complex.exp_log (Complex.slitPlane_ne_zero hpz),
      Complex.exp_log (Complex.slitPlane_ne_zero hqz)]
    change Complex.exp (L (chi z)) * p z / q z = _
    rw [show Complex.exp (L (chi z)) = dslope Hrot 0 (chi z) by
      simpa only [comp_apply] using hLz]
    simpa only [div_eq_mul_inv, mul_assoc] using hslope

lemma NormalizedDiskEmbedding.OmittedPointStep.formalLogarithmicCoeff_step
    {E₀ E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (step : E.OmittedPointStep F) (n : ℕ) :
    formalLogarithmicCoeff
        (taylorCoeff
          (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse) n =
      canonicalLoewnerCoeff
        (formalLogarithmicCoeff
          (taylorCoeff (normalizedRotate reach.normalizedInverse
            (starRingEnd ℂ step.canonicalOmega))))
        (step.realRadius : ℂ) step.canonicalOmega n := by
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have hHold : AnalyticAt ℂ reach.normalizedInverse 0 :=
    reach.normalizedInverse_differentiableOn.analyticAt
      (isOpen_ball.mem_nhds hzero)
  have heta : starRingEnd ℂ step.canonicalOmega ≠ 0 := by
    intro hzero'
    have h := congrArg (starRingEnd ℂ) hzero'
    simp only [map_zero, starRingEnd_self_apply] at h
    exact step.canonicalOmega_ne_zero h
  let Hrot : ℂ → ℂ := normalizedRotate reach.normalizedInverse
    (starRingEnd ℂ step.canonicalOmega)
  let Hnew : ℂ → ℂ :=
    (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse
  have hHrot : AnalyticAt ℂ Hrot 0 :=
    normalizedRotate_analyticAt hHold heta
  have hHrot1 : deriv Hrot 0 = 1 := by
    dsimp only [Hrot]
    rw [deriv_normalizedRotate hHold heta, reach.deriv_normalizedInverse]
  have hHnew : AnalyticAt ℂ Hnew 0 :=
    (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse_differentiableOn
      |>.analyticAt (isOpen_ball.mem_nhds hzero)
  have hHnew1 : deriv Hnew 0 = 1 :=
    (NormalizedDiskEmbedding.ReachableFrom.step reach step).deriv_normalizedInverse
  rcases exists_normalizedLog_germ hHrot hHrot1 with ⟨L, hL, hL0, hLexp⟩
  let M : ℂ → ℂ :=
    canonicalUpdatedLog L (step.realRadius : ℂ) step.canonicalOmega
  have hr : (step.realRadius : ℂ) ≠ 0 := by
    exact_mod_cast step.realRadius_pos.ne'
  have hM : AnalyticAt ℂ M 0 :=
    canonicalUpdatedLog_analyticAt hL hr
  have hM0 : M 0 = 0 := canonicalUpdatedLog_zero hL0
  have hMexp : Complex.exp ∘ M =ᶠ[nhds 0] dslope Hnew 0 := by
    simpa only [M, Hrot, Hnew] using
      step.canonicalUpdatedLog_exp_step reach hL0 hLexp
  have hold : formalLogarithmicCoeff (taylorCoeff Hrot) =
      logarithmicCoeff L := by
    funext k
    exact formalLogarithmicCoeff_eq_logarithmicCoeff_of_germ
      hHrot hL hHrot1 hL0 hLexp k
  have hnew := formalLogarithmicCoeff_eq_logarithmicCoeff_of_germ
    hHnew hM hHnew1 hM0 hMexp n
  change formalLogarithmicCoeff (taylorCoeff Hnew) n =
    canonicalLoewnerCoeff (formalLogarithmicCoeff (taylorCoeff Hrot))
      (step.realRadius : ℂ) step.canonicalOmega n
  rw [hnew]
  calc
    logarithmicCoeff M n =
        canonicalLoewnerCoeff (logarithmicCoeff L)
          (step.realRadius : ℂ) step.canonicalOmega n :=
      logarithmicCoeff_canonicalUpdatedLog hL n
    _ = canonicalLoewnerCoeff
        (formalLogarithmicCoeff (taylorCoeff Hrot))
          (step.realRadius : ℂ) step.canonicalOmega n := by
      rw [hold]

end Submission
