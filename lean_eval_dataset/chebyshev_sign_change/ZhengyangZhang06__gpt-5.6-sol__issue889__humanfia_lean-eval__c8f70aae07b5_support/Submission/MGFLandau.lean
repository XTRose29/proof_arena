import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.MGFAnalytic

open Complex Filter MeasureTheory Real Set Topology

namespace Submission.MGFLandau

lemma integrableExpSet_downward_closed_of_ae_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    (hXmeas : AEMeasurable X μ) (hXnonneg : 0 ≤ᵐ[μ] X)
    {u v : ℝ} (hu : u ∈ ProbabilityTheory.integrableExpSet X μ) (hvu : v ≤ u) :
    v ∈ ProbabilityTheory.integrableExpSet X μ := by
  apply hu.mono'
  · exact (Real.measurable_exp.comp_aemeasurable
      (hXmeas.const_mul v)).aestronglyMeasurable
  filter_upwards [hXnonneg] with ω hω
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hvu hω)

lemma lt_sSup_integrableExpSet_mem_interior
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    (hXmeas : AEMeasurable X μ) (hXnonneg : 0 ≤ᵐ[μ] X)
    (hne : (ProbabilityTheory.integrableExpSet X μ).Nonempty)
    (hb : BddAbove (ProbabilityTheory.integrableExpSet X μ))
    {u : ℝ} (hu : u < sSup (ProbabilityTheory.integrableExpSet X μ)) :
    u ∈ interior (ProbabilityTheory.integrableExpSet X μ) := by
  obtain ⟨v, hv, huv⟩ := (lt_csSup_iff hb hne).mp hu
  have hIio : Iio v ⊆ ProbabilityTheory.integrableExpSet X μ := by
    intro w hw
    exact integrableExpSet_downward_closed_of_ae_nonneg hXmeas hXnonneg hv (le_of_lt hw)
  exact (isOpen_Iio.subset_interior_iff.mpr hIio) huv

private noncomputable def mgfTaylorAtom
    {Ω : Type*} (X : Ω → ℝ) (c x : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  (m.factorial : ℝ)⁻¹ * (x - c) ^ m * X ω ^ m * Real.exp (c * X ω)

private lemma mgfTaylorAtom_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    (hXnonneg : 0 ≤ᵐ[μ] X) {c x : ℝ} (hcx : c ≤ x) (m : ℕ) :
    0 ≤ᵐ[μ] mgfTaylorAtom X c x m := by
  filter_upwards [hXnonneg] with ω hω
  unfold mgfTaylorAtom
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (pow_nonneg (sub_nonneg.mpr hcx) _))
      (pow_nonneg hω _))
    (Real.exp_pos _).le

private lemma mgfTaylorAtom_integrable
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    {c : ℝ} (hc : c ∈ interior (ProbabilityTheory.integrableExpSet X μ))
    (x : ℝ) (m : ℕ) :
    Integrable (mgfTaylorAtom X c x m) μ := by
  have hcore := ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    hc m
  have hmul := hcore.const_mul ((m.factorial : ℝ)⁻¹ * (x - c) ^ m)
  exact hmul.congr (ae_of_all _ fun ω => by
    unfold mgfTaylorAtom
    ring)

private lemma iteratedDeriv_complexMGF_re_eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    {c : ℝ} (hc : c ∈ interior (ProbabilityTheory.integrableExpSet X μ))
    (m : ℕ) :
    (iteratedDeriv m (ProbabilityTheory.complexMGF X μ) (c : ℂ)).re =
      ∫ ω, X ω ^ m * Real.exp (c * X ω) ∂μ := by
  rw [ProbabilityTheory.iteratedDeriv_complexMGF (by simpa using hc) m]
  rw [← RCLike.re_eq_complex_re, ← integral_re]
  · norm_cast
  · refine ProbabilityTheory.integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet ?_ m
    simpa using hc

private lemma integral_mgfTaylorAtom_eq
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    {c : ℝ} (hc : c ∈ interior (ProbabilityTheory.integrableExpSet X μ))
    (x : ℝ) (m : ℕ) :
    (∫ ω, mgfTaylorAtom X c x m ω ∂μ) =
      (((m.factorial : ℂ)⁻¹ * ((x : ℂ) - c) ^ m *
        iteratedDeriv m (ProbabilityTheory.complexMGF X μ) c)).re := by
  let q : ℝ := (m.factorial : ℝ)⁻¹ * (x - c) ^ m
  have hleft : (∫ ω, mgfTaylorAtom X c x m ω ∂μ) =
      q * ∫ ω, X ω ^ m * Real.exp (c * X ω) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by
      unfold mgfTaylorAtom
      dsimp [q]
      ring
  have hscalar :
      (m.factorial : ℂ)⁻¹ * ((x : ℂ) - c) ^ m = (q : ℂ) := by
    dsimp [q]
    push_cast
    rfl
  rw [hleft, hscalar, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, iteratedDeriv_complexMGF_re_eq_integral hc]

private lemma hasSum_mgfTaylorAtom
    {Ω : Type*} {X : Ω → ℝ} (c x : ℝ) (ω : Ω) :
    HasSum (fun m => mgfTaylorAtom X c x m ω) (Real.exp (x * X ω)) := by
  have hseries := (NormedSpace.expSeries_div_hasSum_exp ((x - c) * X ω : ℝ)).mul_left
    (Real.exp (c * X ω))
  rw [← Real.exp_eq_exp_ℝ] at hseries
  change HasSum
    (fun m : ℕ => Real.exp (c * X ω) * (((x - c) * X ω) ^ m / m.factorial))
    (Real.exp (c * X ω) * Real.exp ((x - c) * X ω)) at hseries
  have hseries' : HasSum (fun m => mgfTaylorAtom X c x m ω)
      (Real.exp (c * X ω) * Real.exp ((x - c) * X ω)) := by
    refine HasSum.congr_fun hseries (fun m => ?_)
    unfold mgfTaylorAtom
    rw [mul_pow]
    simp only [div_eq_mul_inv]
    ring
  have hvalue : Real.exp (c * X ω) * Real.exp ((x - c) * X ω) =
      Real.exp (x * X ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hvalue] at hseries'
  exact hseries'

theorem no_analyticContinuationAt_sSup_integrableExpSet
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω}
    (hXmeas : AEMeasurable X μ) (hXnonneg : 0 ≤ᵐ[μ] X)
    (hne : (ProbabilityTheory.integrableExpSet X μ).Nonempty)
    (hb : BddAbove (ProbabilityTheory.integrableExpSet X μ))
    {f : ℂ → ℂ} {beta r : ℝ}
    (hbeta : sSup (ProbabilityTheory.integrableExpSet X μ) = beta)
    (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball beta r))
    (heq : Set.EqOn f (ProbabilityTheory.complexMGF X μ)
      (Metric.ball beta r ∩ {z : ℂ | z.re < beta})) :
    False := by
  let d : ℝ := r / 8
  let c : ℝ := beta - d
  let x : ℝ := beta + d
  have hd : 0 < d := div_pos hr (by norm_num)
  have hcBeta : c < beta := by dsimp [c]; linarith
  have hxBeta : beta < x := by dsimp [x]; linarith
  have hcx : c < x := hcBeta.trans hxBeta
  have hcSup : c < sSup (ProbabilityTheory.integrableExpSet X μ) := by
    rw [hbeta]
    exact hcBeta
  have hcInt := lt_sSup_integrableExpSet_mem_interior hXmeas hXnonneg hne hb hcSup
  have hxNot : x ∉ ProbabilityTheory.integrableExpSet X μ := by
    intro hxMem
    have hxLe : x ≤ sSup (ProbabilityTheory.integrableExpSet X μ) := le_csSup hb hxMem
    rw [hbeta] at hxLe
    exact (not_le_of_gt hxBeta) hxLe
  have hcBall : (c : ℂ) ∈ Metric.ball (beta : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    dsimp [c, d]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hUOpen : IsOpen (Metric.ball (beta : ℂ) r ∩ {z : ℂ | z.re < beta}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_re continuous_const)
  have hcU : (c : ℂ) ∈ Metric.ball (beta : ℂ) r ∩ {z : ℂ | z.re < beta} :=
    ⟨hcBall, hcBeta⟩
  have hevent : f =ᶠ[𝓝 (c : ℂ)] ProbabilityTheory.complexMGF X μ :=
    eventually_of_mem (hUOpen.mem_nhds hcU) heq
  have hderiv (m : ℕ) : iteratedDeriv m f c =
      iteratedDeriv m (ProbabilityTheory.complexMGF X μ) c :=
    hevent.iteratedDeriv_eq m
  have hlocal : DifferentiableOn ℂ f (Metric.ball (c : ℂ) (r / 2)) := by
    apply hf.mono
    apply Metric.ball_subset_ball'
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    dsimp [c, d]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hxball : (x : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    dsimp [x, c, d]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htaylor := Complex.hasSum_taylorSeries_on_ball hlocal hxball
  have hcoeff : Summable (fun m => ∫ ω, mgfTaylorAtom X c x m ω ∂μ) := by
    refine (hasSum_re htaylor).summable.congr (fun m => ?_)
    rw [integral_mgfTaylorAtom_eq hcInt x m, hderiv]
    simp only [smul_eq_mul]
    rw [mul_assoc]
  have hatomInt (m : ℕ) : Integrable (mgfTaylorAtom X c x m) μ :=
    mgfTaylorAtom_integrable hcInt x m
  have hatomNonneg (m : ℕ) : 0 ≤ᵐ[μ] mgfTaylorAtom X c x m :=
    mgfTaylorAtom_nonneg hXnonneg hcx.le m
  have hpoint : ∀ᵐ ω ∂μ,
      (∑' m, ENNReal.ofReal (mgfTaylorAtom X c x m ω)) =
        ENNReal.ofReal (Real.exp (x * X ω)) := by
    filter_upwards [hXnonneg] with ω hω
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rw [(hasSum_mgfTaylorAtom c x ω).tsum_eq]
    · intro m
      unfold mgfTaylorAtom
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (pow_nonneg (sub_nonneg.mpr hcx.le) _))
          (pow_nonneg hω _))
        (Real.exp_pos _).le
    · exact (hasSum_mgfTaylorAtom c x ω).summable
  have hlintegral :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (x * X ω)) ∂μ) =
        ∑' m, (∫⁻ ω, ENNReal.ofReal (mgfTaylorAtom X c x m ω) ∂μ) := by
    calc
      _ = ∫⁻ ω, ∑' m, ENNReal.ofReal (mgfTaylorAtom X c x m ω) ∂μ :=
        lintegral_congr_ae (Filter.EventuallyEq.symm hpoint)
      _ = _ := lintegral_tsum fun m => (hatomInt m).aemeasurable.ennreal_ofReal
  have hsumFinite :
      (∑' m, (∫⁻ ω, ENNReal.ofReal (mgfTaylorAtom X c x m ω) ∂μ)) ≠
        (⊤ : ENNReal) := by
    have heqIntegral (m : ℕ) :
        (∫⁻ ω, ENNReal.ofReal (mgfTaylorAtom X c x m ω) ∂μ) =
          ENNReal.ofReal (∫ ω, mgfTaylorAtom X c x m ω ∂μ) := by
      exact (ofReal_integral_eq_lintegral_ofReal (hatomInt m) (hatomNonneg m)).symm
    simp_rw [heqIntegral]
    exact hcoeff.tsum_ofReal_ne_top
  have hexpMeas : AEStronglyMeasurable (fun ω => Real.exp (x * X ω)) μ :=
    (Real.measurable_exp.comp_aemeasurable (hXmeas.const_mul x)).aestronglyMeasurable
  have hexpNonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (x * X ω) :=
    Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hxInt : Integrable (fun ω => Real.exp (x * X ω)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hexpMeas hexpNonneg).mp
    rw [hlintegral]
    exact hsumFinite
  exact hxNot hxInt

end Submission.MGFLandau
