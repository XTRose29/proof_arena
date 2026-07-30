import Mathlib
import Submission.Helpers
import Submission.Logarithmic

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Submission

noncomputable def truncatedPowerPolynomial (a : ℕ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (a n)

lemma coeff_truncatedPowerPolynomial (a : ℕ → ℂ) (N n : ℕ) :
    (truncatedPowerPolynomial a N).coeff n = if n < N then a n else 0 := by
  simp [truncatedPowerPolynomial, Polynomial.coeff_monomial]

lemma support_truncatedPowerPolynomial_subset (a : ℕ → ℂ) (N : ℕ) :
    (truncatedPowerPolynomial a N).support ⊆ Finset.range N := by
  intro n hn
  by_contra hnN
  have hcoeff := Polynomial.mem_support_iff.mp hn
  rw [coeff_truncatedPowerPolynomial, if_neg] at hcoeff
  · exact hcoeff rfl
  · simpa only [Finset.mem_range, not_lt] using hnN

lemma truncatedPowerPolynomial_parseval (a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) =
      Real.circleAverage
        (fun z => ‖(truncatedPowerPolynomial a N).eval z‖ ^ 2) 0 1 := by
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  calc
    (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) =
        ∑ n ∈ Finset.range N, ‖(truncatedPowerPolynomial a N).coeff n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [coeff_truncatedPowerPolynomial, if_pos (Finset.mem_range.mp hn)]
    _ = ∑ n ∈ (truncatedPowerPolynomial a N).support,
        ‖(truncatedPowerPolynomial a N).coeff n‖ ^ 2 := by
      symm
      apply Finset.sum_subset (support_truncatedPowerPolynomial_subset a N)
      intro n hnRange hnSupport
      have hzero : (truncatedPowerPolynomial a N).coeff n = 0 := by
        exact not_ne_iff.mp fun hne => hnSupport (Polynomial.mem_support_iff.mpr hne)
      rw [hzero]
      simp

lemma eval_truncatedPowerPolynomial (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (truncatedPowerPolynomial a N).eval z =
      ∑ n ∈ Finset.range N, a n * z ^ n := by
  rw [truncatedPowerPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

lemma truncatedPowerSeries_parseval (a : ℕ → ℂ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)) =
      Real.circleAverage
        (fun z => ‖∑ n ∈ Finset.range N, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 := by
  let ar : ℕ → ℂ := fun n => a n * (r : ℂ) ^ n
  have hparseval := truncatedPowerPolynomial_parseval ar N
  calc
    (∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)) =
        ∑ n ∈ Finset.range N, ‖ar n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [ar]
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr]
      have hpow : r ^ (2 * n) = (r ^ n) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hpow]
      ring
    _ = Real.circleAverage
        (fun z => ‖(truncatedPowerPolynomial ar N).eval z‖ ^ 2) 0 1 := hparseval
    _ = Real.circleAverage
        (fun z => ‖∑ n ∈ Finset.range N, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 := by
      congr 1
      funext z
      rw [eval_truncatedPowerPolynomial]
      apply congrArg (fun w : ℂ => ‖w‖ ^ 2)
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [ar]
      rw [mul_pow]
      ring

lemma tendsto_circleAverage_norm_sq_of_tendstoUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ N, ContinuousOn (F N) (sphere (0 : ℂ) 1))
    (hf : ContinuousOn f (sphere (0 : ℂ) 1))
    (h : TendstoUniformlyOn F f atTop (sphere (0 : ℂ) 1)) :
    Tendsto (fun N => Real.circleAverage (fun z => ‖F N z‖ ^ 2) 0 1) atTop
      (nhds (Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 1)) := by
  rcases (isCompact_sphere (0 : ℂ) 1).bddAbove_image hf.norm with ⟨M, hM⟩
  have hfM : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ M := by
    intro z hz
    exact hM ⟨z, hz, rfl⟩
  have hnorm := uniformContinuous_norm.comp_tendstoUniformlyOn h
  have hFM : ∀ᶠ N in atTop, ∀ z ∈ sphere (0 : ℂ) 1, ‖F N z‖ ≤ M + 1 :=
    hnorm.eventually_forall_le (by linarith) hfM
  have hFMmem : ∀ᶠ N in atTop, ∀ z ∈ sphere (0 : ℂ) 1,
      F N z ∈ closedBall (0 : ℂ) (M + 1) := by
    filter_upwards [hFM] with N hN z hz
    simpa [mem_closedBall_zero_iff] using hN z hz
  have hfmem : ∀ z ∈ sphere (0 : ℂ) 1, f z ∈ closedBall (0 : ℂ) (M + 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    linarith [hfM z hz]
  have hsqUC : UniformContinuousOn (fun w : ℂ => ‖w‖ ^ 2)
      (closedBall (0 : ℂ) (M + 1)) :=
    (isCompact_closedBall (0 : ℂ) (M + 1)).uniformContinuousOn_of_continuous (by fun_prop)
  have hsq := hsqUC.comp_tendstoUniformlyOn_eventually hFMmem hfmem h
  have htheta := hsq.comp (circleMap (0 : ℂ) 1)
  change TendstoUniformlyOn
    (fun N θ => ‖F N (circleMap 0 1 θ)‖ ^ 2)
    (fun θ => ‖f (circleMap 0 1 θ)‖ ^ 2) atTop
    (circleMap 0 1 ⁻¹' sphere (0 : ℂ) 1) at htheta
  have htheta' : TendstoUniformlyOn
      (fun N θ => ‖F N (circleMap 0 1 θ)‖ ^ 2)
      (fun θ => ‖f (circleMap 0 1 θ)‖ ^ 2) atTop (Set.uIcc 0 (2 * Real.pi)) := by
    exact htheta.mono
      (fun θ hθ => circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ)
  have hint : Tendsto
      (fun N => ∫ θ : ℝ in 0..2 * Real.pi, ‖F N (circleMap 0 1 θ)‖ ^ 2)
      atTop
      (nhds (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 1 θ)‖ ^ 2)) :=
    htheta'.tendsto_intervalIntegral_of_continuousOn (μ := volume)
      (Eventually.of_forall fun N => (hF N).norm.pow 2 |>.comp
        (continuous_circleMap (0 : ℂ) 1).continuousOn
        (fun θ hθ => circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
  simpa only [Real.circleAverage_def] using tendsto_const_nhds.smul hint

lemma finite_powerSeries_sq_le_circleAverage {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hsummable : Summable (fun n => ‖a n‖ * r ^ n))
    (hsum : ∀ z ∈ sphere (0 : ℂ) 1,
      HasSum (fun n => a n * ((r : ℂ) * z) ^ n) (f z)) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)) ≤
      Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 1 := by
  let P : ℕ → ℂ → ℂ := fun K z =>
    ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n
  let fsum : ℂ → ℂ := fun z => ∑' n, a n * ((r : ℂ) * z) ^ n
  have huniformSum : TendstoUniformlyOn P fsum atTop (sphere (0 : ℂ) 1) := by
    apply tendstoUniformlyOn_tsum_nat hsummable
    intro n z hz
    have hznorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, hznorm]
    simp
  have hEq : Set.EqOn fsum f (sphere (0 : ℂ) 1) := by
    intro z hz
    exact (hsum z hz).tsum_eq
  have huniform : TendstoUniformlyOn P f atTop (sphere (0 : ℂ) 1) :=
    huniformSum.congr_right hEq
  have hPcont : ∀ K, ContinuousOn (P K) (sphere (0 : ℂ) 1) := by
    intro K
    apply Continuous.continuousOn
    dsimp only [P]
    fun_prop
  have hfcont : ContinuousOn f (sphere (0 : ℂ) 1) :=
    huniform.continuousOn (Frequently.of_forall hPcont)
  have havg := tendsto_circleAverage_norm_sq_of_tendstoUniformlyOn hPcont hfcont huniform
  apply ge_of_tendsto havg
  filter_upwards [eventually_ge_atTop N] with K hNK
  change (∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)) ≤
    Real.circleAverage (fun z => ‖P K z‖ ^ 2) 0 1
  rw [show Real.circleAverage (fun z => ‖P K z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 * r ^ (2 * n) by
    rw [truncatedPowerSeries_parseval a K hr]]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
  intro i hiK hiN
  positivity

lemma summable_norm_taylorCoeff_mul_pow {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 ≤ r) (hrR : r < R) :
    Summable (fun n => ‖taylorCoeff f n‖ * r ^ n) := by
  have hz : (r : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr]
    exact hrR
  have hsum : HasSum (fun n => taylorCoeff f n * (r : ℂ) ^ n) (f r) := by
    simpa only [taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using Complex.hasSum_taylorSeries_on_ball hf hz
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr] using
    hsum.summable.norm

lemma finite_taylorCoeff_sq_le_circleAverage {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 ≤ r) (hrR : r < R)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n)) ≤
      Real.circleAverage (fun z => ‖f ((r : ℂ) * z)‖ ^ 2) 0 1 := by
  apply finite_powerSeries_sq_le_circleAverage hr
    (summable_norm_taylorCoeff_mul_pow hf hr hrR)
  intro z hz
  have hznorm : ‖z‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, hznorm,
      mul_one]
    exact hrR
  simpa only [taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm,
    mul_left_comm, mul_assoc] using Complex.hasSum_taylorSeries_on_ball hf hrz

lemma det_complex_smul_one (d : ℂ) :
    (d • (1 : ℂ →L[ℝ] ℂ)).det = ‖d‖ ^ 2 := by
  rw [← Complex.restrictScalars_toSpanSingleton]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

lemma lintegral_norm_deriv_sq_eq_volume_image {g : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hg : ∀ z ∈ s, DifferentiableAt ℂ g z)
    (hinj : s.InjOn g) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv g z‖ ^ 2)) = volume (g '' s) := by
  have h := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    (μ := volume) hs
    (fun z hz => (hg z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt) hinj
  have hdet (z : ℂ) :
      |((deriv g z) • (1 : ℂ →L[ℝ] ℂ)).det| = ‖deriv g z‖ ^ 2 := by
    rw [det_complex_smul_one]
    exact abs_of_nonneg (sq_nonneg _)
  simpa only [hdet] using h

lemma lintegral_norm_deriv_sq_le_closedBall {g : ℂ → ℂ} {s : Set ℂ} {c : ℂ} {B : ℝ}
    (hs : MeasurableSet s) (hg : ∀ z ∈ s, DifferentiableAt ℂ g z)
    (hinj : s.InjOn g) (hB : g '' s ⊆ closedBall c B) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv g z‖ ^ 2)) ≤
      ENNReal.ofReal B ^ 2 * NNReal.pi := by
  rw [lintegral_norm_deriv_sq_eq_volume_image hs hg hinj]
  exact (measure_mono hB).trans_eq (Complex.volume_closedBall c B)

lemma lintegral_inv_image {s : Set ℂ} (hs : MeasurableSet s)
    (hs0 : ∀ z ∈ s, z ≠ 0) (g : ℂ → ℝ≥0∞) :
    (∫⁻ z in (fun w : ℂ => w⁻¹) '' s, g z) =
      ∫⁻ w in s, ENNReal.ofReal (‖w‖⁻¹ ^ 4) * g w⁻¹ := by
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) hs
    (fun z hz => (hasDerivAt_inv (hs0 z hz)).complexToReal_fderiv.hasFDerivWithinAt)
    inv_injective.injOn g
  have hdet (w : ℂ) :
      |((-(w ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)).det| = ‖w‖⁻¹ ^ 4 := by
    rw [det_complex_smul_one, abs_of_nonneg (sq_nonneg _), norm_neg, norm_inv, norm_pow]
    ring
  simpa only [hdet] using h

def exteriorDisk (R : ℝ) : Set ℂ :=
  {z | 1 / R < ‖z‖}

lemma isOpen_exteriorDisk (R : ℝ) : IsOpen (exteriorDisk R) :=
  isOpen_lt continuous_const continuous_norm

def closedAnnulus (r B : ℝ) : Set ℂ :=
  closedBall (0 : ℂ) B \ ball 0 r

lemma measurableSet_closedAnnulus (r B : ℝ) : MeasurableSet (closedAnnulus r B) :=
  measurableSet_closedBall.diff measurableSet_ball

lemma isCompact_closedAnnulus (r B : ℝ) : IsCompact (closedAnnulus r B) :=
  IsCompact.diff (isCompact_closedBall (0 : ℂ) B) isOpen_ball

lemma mem_closedAnnulus_iff {r B : ℝ} {z : ℂ} :
    z ∈ closedAnnulus r B ↔ r ≤ ‖z‖ ∧ ‖z‖ ≤ B := by
  simp [closedAnnulus, not_lt, and_comm]

lemma inv_image_closedAnnulus {r B : ℝ} (hr : 0 < r) (hrB : r ≤ B) :
    (fun z : ℂ => z⁻¹) '' closedAnnulus (1 / B) (1 / r) = closedAnnulus r B := by
  have hB : 0 < B := hr.trans_le hrB
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closedAnnulus_iff] at hw ⊢
    have hwpos : 0 < ‖w‖ := (one_div_pos.mpr hB).trans_le hw.1
    rw [norm_inv]
    exact ⟨by simpa only [one_div] using (le_one_div hr hwpos).2 hw.2,
      by simpa only [one_div] using (one_div_le hwpos hB).2 hw.1⟩
  · intro hz
    rw [mem_closedAnnulus_iff] at hz
    have hzpos : 0 < ‖z‖ := hr.trans_le hz.1
    refine ⟨z⁻¹, ?_, inv_inv z⟩
    rw [mem_closedAnnulus_iff, norm_inv]
    exact ⟨by simpa only [one_div] using one_div_le_one_div_of_le hzpos hz.2,
      by simpa only [one_div] using one_div_le_one_div_of_le hr hz.1⟩

lemma closedAnnulus_subset_exteriorDisk {R r B : ℝ} (hr : 1 / R < r) :
    closedAnnulus r B ⊆ exteriorDisk R := by
  intro z hz
  have hnorm : r ≤ ‖z‖ := by
    exact le_of_not_gt fun hzr => hz.2 (by simpa [mem_ball_zero_iff] using hzr)
  exact hr.trans_le hnorm

noncomputable def exteriorTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (f z⁻¹)⁻¹

noncomputable def exteriorDerivativeTransform (L : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.exp (-L w) * (1 + w * deriv L w)

lemma exteriorDerivativeTransform_differentiableOn {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    DifferentiableOn ℂ (exteriorDerivativeTransform L) (ball 0 R) := by
  intro z hz
  have hLAt : DifferentiableAt ℂ L z := hL.differentiableAt (isOpen_ball.mem_nhds hz)
  have hderivAt : DifferentiableAt ℂ (deriv L) z :=
    (hL.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ (fun w => Complex.exp (-L w) * (1 + w * deriv L w)) z
  exact (hLAt.hasDerivAt.neg.cexp.mul
    ((hasDerivAt_const (x := z) (c := (1 : ℂ))).add
      ((hasDerivAt_id z).mul hderivAt.hasDerivAt))).differentiableAt

@[simp]
lemma exteriorDerivativeTransform_zero {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    exteriorDerivativeTransform L 0 = 1 := by
  simp [exteriorDerivativeTransform, hL0]

lemma deriv_exteriorDerivativeTransform_zero {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) :
    deriv (exteriorDerivativeTransform L) 0 = 0 := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hLAt : DifferentiableAt ℂ L 0 := hL.differentiableAt (isOpen_ball.mem_nhds hzero)
  have hderivAt : DifferentiableAt ℂ (deriv L) 0 :=
    (hL.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hzero)
  have hleft := hLAt.hasDerivAt.neg.cexp
  have hright := (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
    ((hasDerivAt_id 0).mul hderivAt.hasDerivAt)
  have hprod := hleft.mul hright
  change deriv ((fun x => Complex.exp ((-L) x)) * ((fun _ => 1) + id * deriv L)) 0 = 0
  rw [hprod.deriv]
  simp [hL0]

@[simp]
lemma taylorCoeff_exteriorDerivativeTransform_zero {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    taylorCoeff (exteriorDerivativeTransform L) 0 = 1 := by
  simp [taylorCoeff, hL0]

lemma taylorCoeff_exteriorDerivativeTransform_one {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) :
    taylorCoeff (exteriorDerivativeTransform L) 1 = 0 := by
  simp [taylorCoeff, deriv_exteriorDerivativeTransform_zero hR hL hL0]

lemma inv_mem_ball_of_mem_exteriorDisk {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ exteriorDisk R) : z⁻¹ ∈ ball (0 : ℂ) R := by
  rw [mem_ball_zero_iff, norm_inv]
  change 1 / R < ‖z‖ at hz
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (by positivity : 0 ≤ 1 / R) hz
  simpa only [one_div] using (one_div_lt hz0 hR).2 hz

lemma ne_zero_of_mem_exteriorDisk {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ exteriorDisk R) : z ≠ 0 := by
  intro hz0
  subst z
  have hdiv : 0 < 1 / R := one_div_pos.mpr hR
  change 1 / R < ‖(0 : ℂ)‖ at hz
  have hnot : ¬1 / R < 0 := not_lt_of_ge hdiv.le
  exact hnot (by simpa using hz)

lemma exteriorTransform_differentiableAt {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) {z : ℂ} (hz : z ∈ exteriorDisk R) :
    DifferentiableAt ℂ (exteriorTransform f) z := by
  have hz0 := ne_zero_of_mem_exteriorDisk hR hz
  have hzinv := inv_mem_ball_of_mem_exteriorDisk hR hz
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hfz : f z⁻¹ ≠ 0 := by
    intro hfzero
    have heq : f z⁻¹ = f 0 := by simpa [hf.2.2.1] using hfzero
    exact hz0 (inv_eq_zero.mp (hf.2.1 hzinv hzero heq))
  have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := differentiableAt_inv hz0
  have hfAt : DifferentiableAt ℂ f z⁻¹ :=
    hf.1.differentiableAt (isOpen_ball.mem_nhds hzinv)
  change DifferentiableAt ℂ (fun w => (f w⁻¹)⁻¹) z
  simpa only [Function.comp_apply] using (hfAt.comp z hinv).fun_inv hfz

lemma exteriorTransform_injOn {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) :
    (exteriorDisk R).InjOn (exteriorTransform f) := by
  intro x hx y hy hxy
  have hx0 := ne_zero_of_mem_exteriorDisk hR hx
  have hy0 := ne_zero_of_mem_exteriorDisk hR hy
  have hxinv := inv_mem_ball_of_mem_exteriorDisk hR hx
  have hyinv := inv_mem_ball_of_mem_exteriorDisk hR hy
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hfx : f x⁻¹ ≠ 0 := by
    intro h
    have : f x⁻¹ = f 0 := by simpa [hf.2.2.1] using h
    exact hx0 (inv_eq_zero.mp (hf.2.1 hxinv hzero this))
  have hfy : f y⁻¹ ≠ 0 := by
    intro h
    have : f y⁻¹ = f 0 := by simpa [hf.2.2.1] using h
    exact hy0 (inv_eq_zero.mp (hf.2.1 hyinv hzero this))
  have hfxy : f x⁻¹ = f y⁻¹ := by
    apply inv_injective
    exact hxy
  have hinv : x⁻¹ = y⁻¹ := hf.2.1 hxinv hyinv hfxy
  exact inv_injective hinv

lemma exteriorTransform_eq_mul_exp_neg {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    {z : ℂ} (hz : z ∈ exteriorDisk R) :
    exteriorTransform f z = z * Complex.exp (-L z⁻¹) := by
  have hz0 := ne_zero_of_mem_exteriorDisk hR hz
  have hzinv := inv_mem_ball_of_mem_exteriorDisk hR hz
  have hEq := eqOn_mul_exp_of_normalized_log hf.2.2.1 hexp hzinv
  rw [exteriorTransform, hEq, Complex.exp_neg]
  field_simp [hz0, Complex.exp_ne_zero]

lemma deriv_exteriorTransform_eq {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    {z : ℂ} (hz : z ∈ exteriorDisk R) :
    deriv (exteriorTransform f) z = exteriorDerivativeTransform L z⁻¹ := by
  have hz0 := ne_zero_of_mem_exteriorDisk hR hz
  have hzinv := inv_mem_ball_of_mem_exteriorDisk hR hz
  have hLAt : DifferentiableAt ℂ L z⁻¹ :=
    hL.differentiableAt (isOpen_ball.mem_nhds hzinv)
  have heq : Set.EqOn (exteriorTransform f)
      (fun w => w * Complex.exp (-L w⁻¹)) (exteriorDisk R) := by
    intro w hw
    exact exteriorTransform_eq_mul_exp_neg hR hf hexp hw
  have hderiv := heq.deriv (isOpen_exteriorDisk R) hz
  have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz0
  have hcomp : HasDerivAt (fun w => L w⁻¹) (deriv L z⁻¹ * (-(z ^ 2)⁻¹)) z := by
    change HasDerivAt (L ∘ fun w : ℂ => w⁻¹) (deriv L z⁻¹ * (-(z ^ 2)⁻¹)) z
    exact hLAt.hasDerivAt.comp z hinv
  have hright := (hasDerivAt_id z).mul hcomp.neg.cexp
  have hright_deriv :
      deriv (fun w : ℂ => w * Complex.exp (-L w⁻¹)) z =
        1 * Complex.exp (-L z⁻¹) +
          z * (Complex.exp (-L z⁻¹) * -(deriv L z⁻¹ * (-(z ^ 2)⁻¹))) := by
    change deriv (id * fun x => Complex.exp (-L x⁻¹)) z = _
    exact hright.deriv
  rw [hderiv]
  rw [hright_deriv]
  unfold exteriorDerivativeTransform
  field_simp [hz0]

lemma exteriorTransform_area_eq_inner_integral {f L : ℂ → ℂ} {R r B : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (hr0 : 0 < r) (hrB : r ≤ B) :
    (∫⁻ z in closedAnnulus r B,
        ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2)) =
      ∫⁻ w in closedAnnulus (1 / B) (1 / r),
        ENNReal.ofReal (‖w‖⁻¹ ^ 4) *
          ENNReal.ofReal (‖exteriorDerivativeTransform L w‖ ^ 2) := by
  calc
    (∫⁻ z in closedAnnulus r B,
        ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2)) =
        ∫⁻ z in closedAnnulus r B,
          ENNReal.ofReal (‖exteriorDerivativeTransform L z⁻¹‖ ^ 2) := by
      apply setLIntegral_congr_fun (measurableSet_closedAnnulus r B)
      intro z hz
      change ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2) =
        ENNReal.ofReal (‖exteriorDerivativeTransform L z⁻¹‖ ^ 2)
      rw [deriv_exteriorTransform_eq hR hf hL hexp
        (closedAnnulus_subset_exteriorDisk hr hz)]
    _ = ∫⁻ w in closedAnnulus (1 / B) (1 / r),
          ENNReal.ofReal (‖w‖⁻¹ ^ 4) *
            ENNReal.ofReal (‖exteriorDerivativeTransform L w‖ ^ 2) := by
      rw [← inv_image_closedAnnulus hr0 hrB]
      have hB : 0 < B := hr0.trans_le hrB
      have hs0 : ∀ w ∈ closedAnnulus (1 / B) (1 / r), w ≠ 0 := by
        intro w hw hw0
        subst w
        have hpos : 0 < 1 / B := one_div_pos.mpr hB
        have := (mem_closedAnnulus_iff.mp hw).1
        simp at this
        linarith
      simpa only [inv_inv] using lintegral_inv_image
        (measurableSet_closedAnnulus (1 / B) (1 / r)) hs0
        (fun z => ENNReal.ofReal (‖exteriorDerivativeTransform L z⁻¹‖ ^ 2))

lemma exteriorTransform_sub_tendsto {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) :
    Tendsto (fun z => exteriorTransform f z - z) (Bornology.cobounded ℂ)
      (nhds (-deriv L 0)) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hLAt : DifferentiableAt ℂ L 0 := hL.differentiableAt (isOpen_ball.mem_nhds hzero)
  have hExp : HasDerivAt (fun w : ℂ => Complex.exp (-L w)) (-deriv L 0) 0 := by
    simpa [hL0] using hLAt.hasDerivAt.neg.cexp
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ)
      (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Filter.tendsto_inv₀_cobounded, ?_⟩
    filter_upwards [eventually_ne_of_tendsto_norm_atTop tendsto_norm_cobounded_atTop
      (0 : ℂ)] with z hz
    simpa using inv_ne_zero hz
  have hlim := hExp.tendsto_slope.comp hinv
  have hevent : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ∈ exteriorDisk R := by
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually
      (eventually_gt_atTop (1 / R))] with z hz
    exact hz
  apply hlim.congr'
  filter_upwards [hevent] with z hz
  rw [exteriorTransform_eq_mul_exp_neg hR hf hexp hz]
  simp [slope, hL0]
  ring

lemma exteriorTransform_asymptotic_bound {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, ∀ z : ℂ, A ≤ ‖z‖ →
      ‖exteriorTransform f z - (z - deriv L 0)‖ < ε := by
  have hlim := exteriorTransform_sub_tendsto hR hf hL hL0 hexp
  have hevent : ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      dist (exteriorTransform f z - z) (-deriv L 0) < ε :=
    hlim (Metric.ball_mem_nhds _ hε)
  rcases Filter.hasBasis_cobounded_norm.mem_iff.mp hevent with ⟨A, -, hA⟩
  refine ⟨A, fun z hz => ?_⟩
  have hdist := hA hz
  change dist (exteriorTransform f z - z) (-deriv L 0) < ε at hdist
  rw [dist_eq_norm] at hdist
  have heq : exteriorTransform f z - (z - deriv L 0) =
      (exteriorTransform f z - z) - -deriv L 0 := by ring
  rw [heq]
  exact hdist

lemma exists_exteriorTransform_inner_bound {f : ℂ → ℂ} {R r : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hr : 1 / R < r) (A : ℝ) (c : ℂ) :
    ∃ C : ℝ, ∀ z ∈ closedAnnulus r A, ‖exteriorTransform f z - c‖ ≤ C := by
  have hcont : ContinuousOn (fun z => ‖exteriorTransform f z - c‖)
      (closedAnnulus r A) := by
    intro z hz
    have hnorm : r ≤ ‖z‖ := by
      exact le_of_not_gt fun hzr => hz.2 (by simpa [mem_ball_zero_iff] using hzr)
    have hzext : z ∈ exteriorDisk R := hr.trans_le hnorm
    exact ((exteriorTransform_differentiableAt hR hf hzext).continuousAt.sub
      continuousAt_const).norm.continuousWithinAt
  rcases (isCompact_closedAnnulus r A).bddAbove_image hcont with ⟨C, hC⟩
  refine ⟨C, fun z hz => ?_⟩
  exact hC ⟨z, hz, rfl⟩

lemma eventually_exteriorTransform_closedAnnulus_subset {f L : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      exteriorTransform f '' closedAnnulus r B ⊆
        closedBall (-deriv L 0) (B + ε) := by
  rcases exteriorTransform_asymptotic_bound hR hf hL hL0 hexp hε with ⟨A, hA⟩
  let A₀ := max A r
  rcases exists_exteriorTransform_inner_bound hR hf hr A₀ (-deriv L 0) with ⟨C, hC⟩
  refine ⟨max A₀ C, fun B hB y hy => ?_⟩
  rcases hy with ⟨z, hz, rfl⟩
  have hz_upper : ‖z‖ ≤ B := by
    simpa [closedAnnulus, mem_closedBall_zero_iff] using hz.1
  have hz_lower : r ≤ ‖z‖ := by
    exact le_of_not_gt fun hzr => hz.2 (by simpa [mem_ball_zero_iff] using hzr)
  rw [mem_closedBall, dist_eq_norm]
  by_cases hz_large : A₀ ≤ ‖z‖
  · have hrem := hA z ((le_max_left A r).trans hz_large)
    have heq : exteriorTransform f z - -deriv L 0 =
        (exteriorTransform f z - (z - deriv L 0)) + z := by ring
    rw [heq]
    apply le_of_lt
    calc
      ‖exteriorTransform f z - (z - deriv L 0) + z‖ ≤
          ‖exteriorTransform f z - (z - deriv L 0)‖ + ‖z‖ := norm_add_le _ _
      _ < ε + ‖z‖ := by linarith
      _ ≤ ε + B := by linarith
      _ = B + ε := add_comm _ _
  · have hz_inner : z ∈ closedAnnulus r A₀ := by
      refine ⟨?_, hz.2⟩
      rw [mem_closedBall_zero_iff]
      exact le_of_not_ge hz_large
    exact (hC z hz_inner).trans ((le_max_right A₀ C).trans hB) |>.trans
      (le_add_of_nonneg_right hε.le)

lemma eventually_exteriorTransform_area_le {f L : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      (∫⁻ z in closedAnnulus r B,
        ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2)) ≤
          ENNReal.ofReal (B + ε) ^ 2 * NNReal.pi := by
  rcases eventually_exteriorTransform_closedAnnulus_subset hR hf hL hL0 hexp hr hε
    with ⟨B₀, hB₀⟩
  refine ⟨B₀, fun B hB => ?_⟩
  exact lintegral_norm_deriv_sq_le_closedBall
    (measurableSet_closedAnnulus r B)
    (fun z hz => exteriorTransform_differentiableAt hR hf
      (closedAnnulus_subset_exteriorDisk hr hz))
    ((exteriorTransform_injOn hR hf).mono (closedAnnulus_subset_exteriorDisk hr))
    (hB₀ B hB)

end Submission
