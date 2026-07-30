import ChallengeDeps

open LeanEval.Analysis
open MeasureTheory Submodule

namespace Submission.Helpers

noncomputable section

abbrev UnitCircle := AddCircle (1 : ℝ)

abbrev circleMeasure : Measure UnitCircle :=
  AddCircle.haarAddCircle

abbrev CircleL1 := Lp ℂ 1 circleMeasure

/-- Translation by `a` on `L^1` of the unit circle. -/
def rotate (a : UnitCircle) : CircleL1 →ₗᵢ[ℂ] CircleL1 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + a)
    (measurePreserving_add_right circleMeasure a)

def shiftMap (a : UnitCircle) : C(UnitCircle, UnitCircle) where
  toFun x := x + a
  continuous_toFun := continuous_id.add continuous_const

lemma continuous_shiftMap : Continuous shiftMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_snd.add continuous_fst

lemma continuous_rotate (f : CircleL1) : Continuous fun a => rotate a f := by
  change Continuous fun a =>
    Lp.compMeasurePreserving (shiftMap a) (measurePreserving_add_right circleMeasure a) f
  exact continuous_const.compMeasurePreservingLp continuous_shiftMap
    (fun a => measurePreserving_add_right circleMeasure a) (by norm_num)

lemma continuous_rotate_neg {f : UnitCircle → CircleL1} (hf : Continuous f) :
    Continuous fun a => rotate (-a) (f a) := by
  change Continuous fun a =>
    Lp.compMeasurePreserving (shiftMap (-a))
      (measurePreserving_add_right circleMeasure (-a)) (f a)
  exact hf.compMeasurePreservingLp (continuous_shiftMap.comp continuous_neg)
    (fun a => measurePreserving_add_right circleMeasure (-a)) (by norm_num)

lemma coeFn_rotate (a : UnitCircle) (f : CircleL1) :
    rotate a f =ᵐ[circleMeasure] fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right circleMeasure a)

abbrev mode (n : ℤ) : CircleL1 :=
  fourierLp 1 n

lemma coeFn_mode (n : ℤ) :
    mode n =ᵐ[circleMeasure] fourier n :=
  coeFn_fourierLp 1 n

lemma rotate_mode (a : UnitCircle) (n : ℤ) :
    rotate a (mode n) = fourier n a • mode n := by
  apply Lp.ext
  have hmode_shift :=
    (measurePreserving_add_right circleMeasure a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_mode n)
  filter_upwards [coeFn_rotate a (mode n), hmode_shift, coeFn_mode n,
    Lp.coeFn_smul (fourier n a) (mode n)] with x hrot hmode_shift hmode hsmul
  change mode n (x + a) = fourier n (x + a) at hmode_shift
  rw [hrot, hmode_shift, hsmul]
  change fourier n (x + a) = fourier n a * mode n x
  rw [hmode, fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, mul_comm]
  rfl

lemma fourier_add_arg (n : ℤ) (x y : UnitCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  rfl

lemma fourier_neg_arg (n : ℤ) (x : UnitCircle) :
    fourier n (-x) = fourier (-n) x := by
  simp only [fourier_apply, smul_neg, neg_smul]

lemma fourier_sub_arg (n : ℤ) (x y : UnitCircle) :
    fourier n (x - y) = fourier n x * fourier (-n) y := by
  rw [sub_eq_add_neg, fourier_add_arg, fourier_neg_arg]

/-- The bounded sawtooth on the unit circle, represented by `x` on `(0, 1]`. -/
def sawtooth : UnitCircle → ℂ :=
  AddCircle.liftIoc 1 0 (fun x : ℝ => (x : ℂ))

lemma norm_sawtooth_le_one (x : UnitCircle) : ‖sawtooth x‖ ≤ 1 := by
  rcases AddCircle.eq_coe_Ioc x with ⟨y, hy, rfl⟩
  have hy' : y ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa only [zero_add] using hy
  rw [sawtooth, AddCircle.liftIoc_coe_apply hy']
  simpa [Real.norm_eq_abs, abs_of_nonneg hy.1.le] using hy.2

lemma sawtooth_memLp : MemLp sawtooth (⊤ : ENNReal) circleMeasure := by
  apply MemLp.haarAddCircle
  apply MemLp.memLp_liftIoc
  refine MemLp.of_bound (p := (⊤ : ENNReal)) ?_ 1 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1.le] using hx.2

lemma sawtooth_integrable : Integrable sawtooth circleMeasure :=
  memLp_one_iff_integrable.mp <| sawtooth_memLp.mono_exponent (by simp)

/-- Pair an `L^1` function with the bounded sawtooth. -/
def sawFunctional : CircleL1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, sawtooth x * f x ∂circleMeasure
      map_add' := by
        intro f g
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards [Lp.coeFn_add f g] with x hx
          rw [hx]
          exact mul_add _ _ _
        · exact (L1.integrable_coeFn f).bdd_mul sawtooth_memLp.1
            (Filter.Eventually.of_forall norm_sawtooth_le_one)
        · exact (L1.integrable_coeFn g).bdd_mul sawtooth_memLp.1
            (Filter.Eventually.of_forall norm_sawtooth_le_one)
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at hx ⊢
        rw [hx]
        ring_nf }
    1 fun f => by
      calc
        ‖∫ x, sawtooth x * f x ∂circleMeasure‖
            ≤ ∫ x, ‖sawtooth x * f x‖ ∂circleMeasure :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖f x‖ ∂circleMeasure := by
          apply integral_mono
          · exact ((L1.integrable_coeFn f).bdd_mul sawtooth_memLp.1
              (Filter.Eventually.of_forall norm_sawtooth_le_one)).norm
          · exact (L1.integrable_coeFn f).norm
          · intro x
            change ‖sawtooth x * f x‖ ≤ ‖f x‖
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (norm_sawtooth_le_one x)
        _ = 1 * ‖f‖ := by rw [L1.norm_eq_integral_norm, one_mul]

lemma norm_sawFunctional_le (f : CircleL1) : ‖sawFunctional f‖ ≤ ‖f‖ := by
  change ‖∫ x, sawtooth x * f x ∂circleMeasure‖ ≤ ‖f‖
  calc
    ‖∫ x, sawtooth x * f x ∂circleMeasure‖
        ≤ ∫ x, ‖sawtooth x * f x‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ ∂circleMeasure := by
      apply integral_mono
      · exact ((L1.integrable_coeFn f).bdd_mul sawtooth_memLp.1
          (Filter.Eventually.of_forall norm_sawtooth_le_one)).norm
      · exact (L1.integrable_coeFn f).norm
      · intro x
        change ‖sawtooth x * f x‖ ≤ ‖f x‖
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_sawtooth_le_one x)
    _ = ‖f‖ := L1.norm_eq_integral_norm f |>.symm

lemma sawFunctional_rotate (a : UnitCircle) (f : CircleL1) :
    sawFunctional (rotate a f) = ∫ x, sawtooth x * f (x + a) ∂circleMeasure := by
  change (∫ x, sawtooth x * (rotate a f) x ∂circleMeasure) = _
  apply integral_congr_ae
  filter_upwards [coeFn_rotate a f] with x hx
  rw [hx]

lemma continuous_conjugated_apply (p : CircleL1 →L[ℂ] CircleL1) (f : CircleL1) :
    Continuous fun a => rotate (-a) (p (rotate a f)) :=
  continuous_rotate_neg (p.continuous.comp <| continuous_rotate f)

/-- Haar-average the scalar sawtooth pairing over all conjugates of an operator. -/
def averagedFunctional (p : CircleL1 →L[ℂ] CircleL1) : CircleL1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ a, sawFunctional (rotate (-a) (p (rotate a f))) ∂circleMeasure
      map_add' := by
        intro f g
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards with a
          simp
        · exact (sawFunctional.continuous.comp <| continuous_conjugated_apply p f)
            |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · exact (sawFunctional.continuous.comp <| continuous_conjugated_apply p g)
            |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with a
        simp }
    ‖p‖ fun f => by
      calc
        ‖∫ a, sawFunctional (rotate (-a) (p (rotate a f))) ∂circleMeasure‖
            ≤ (‖p‖ * ‖f‖) * circleMeasure.real Set.univ := by
          apply norm_integral_le_of_norm_le_const
          filter_upwards with a
          calc
            ‖sawFunctional (rotate (-a) (p (rotate a f)))‖
                ≤ ‖rotate (-a) (p (rotate a f))‖ := norm_sawFunctional_le _
            _ = ‖p (rotate a f)‖ := (rotate (-a)).norm_map _
            _ ≤ ‖p‖ * ‖rotate a f‖ := p.le_opNorm _
            _ = ‖p‖ * ‖f‖ := by rw [(rotate a).norm_map]
        _ = ‖p‖ * ‖f‖ := by simp

lemma average_pair_mode (f : CircleL1) (n : ℤ) :
    (∫ a, fourier n a * sawFunctional (rotate (-a) f) ∂circleMeasure) =
      fourierCoeff sawtooth (-n) * fourierCoeff f n := by
  let F : UnitCircle × UnitCircle → ℂ := fun z =>
    sawtooth z.2 * (fourier n z.1 * f (z.2 - z.1))
  have hf_base : Integrable (fun z : UnitCircle × UnitCircle => f z.2)
      (circleMeasure.prod circleMeasure) :=
    (L1.integrable_coeFn f).comp_snd circleMeasure
  have hf_shift : Integrable (fun z : UnitCircle × UnitCircle => f (z.2 - z.1))
      (circleMeasure.prod circleMeasure) := by
    have h := (measurePreserving_prod_sub circleMeasure circleMeasure).integrable_comp hf_base.1
    simpa only [Function.comp_def] using h.mpr hf_base
  have hfourier : AEStronglyMeasurable
      (fun z : UnitCircle × UnitCircle => fourier n z.1)
      (circleMeasure.prod circleMeasure) :=
    Continuous.aestronglyMeasurable (by fun_prop)
  have hfourier_bound : ∀ᵐ z : UnitCircle × UnitCircle ∂circleMeasure.prod circleMeasure,
      ‖fourier n z.1‖ ≤ 1 := by
    filter_upwards with z
    simp
  have hfourier_mul : Integrable
      (fun z : UnitCircle × UnitCircle => fourier n z.1 * f (z.2 - z.1))
      (circleMeasure.prod circleMeasure) :=
    hf_shift.bdd_mul hfourier hfourier_bound
  have hsaw_prod : Integrable (fun z : UnitCircle × UnitCircle => sawtooth z.2)
      (circleMeasure.prod circleMeasure) :=
    sawtooth_integrable.comp_snd circleMeasure
  have hF : Integrable F (circleMeasure.prod circleMeasure) :=
    hfourier_mul.bdd_mul hsaw_prod.1 <| by
      filter_upwards with z
      exact norm_sawtooth_le_one z.2
  simp_rw [sawFunctional_rotate, ← integral_const_mul]
  calc
    (∫ a, ∫ x, fourier n a * (sawtooth x * f (x + -a)) ∂circleMeasure
        ∂circleMeasure) =
        ∫ a, ∫ x, F (a, x) ∂circleMeasure ∂circleMeasure := by
      congr 1
      funext a
      apply integral_congr_ae
      filter_upwards with x
      simp only [F, sub_eq_add_neg]
      ring_nf
    _ = ∫ x, ∫ a, F (a, x) ∂circleMeasure ∂circleMeasure :=
      integral_integral_swap hF
    _ = ∫ x, sawtooth x * (fourier n x * fourierCoeff f n) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      have hchange :
          (∫ a, fourier n a * f (x - a) ∂circleMeasure) =
            ∫ u, fourier n (x - u) * f u ∂circleMeasure := by
        have hmp : MeasurePreserving (fun a : UnitCircle => x - a)
            circleMeasure circleMeasure := by
          have hraw := (measurePreserving_add_left circleMeasure x).comp
            (Measure.measurePreserving_neg circleMeasure)
          convert hraw using 1
          funext a
          simp [sub_eq_add_neg]
        have h := hmp.integral_comp
            (MeasurableEquiv.subLeft x).measurableEmbedding
            (fun u => fourier n (x - u) * f u)
        simpa [Function.comp_def] using h
      rw [show (∫ a, F (a, x) ∂circleMeasure) =
          sawtooth x * ∫ a, fourier n a * f (x - a) ∂circleMeasure by
        rw [← integral_const_mul]]
      rw [hchange]
      have heval : (∫ u, fourier n (x - u) * f u ∂circleMeasure) =
          fourier n x * fourierCoeff f n := by
        rw [show (fun u => fourier n (x - u) * f u) =
            fun u => fourier n x * (fourier (-n) u * f u) by
          funext u
          rw [fourier_sub_arg]
          ring_nf]
        rw [integral_const_mul]
        congr 1
      rw [heval]
    _ = fourierCoeff sawtooth (-n) * fourierCoeff f n := by
      rw [show (fun x => sawtooth x * (fourier n x * fourierCoeff f n)) =
          fun x => (sawtooth x * fourier n x) * fourierCoeff f n by
        funext x
        ring_nf]
      rw [integral_mul_const]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring_nf

lemma averagedFunctional_mode (p : CircleL1 →L[ℂ] CircleL1) (n : ℤ) :
    averagedFunctional p (mode n) =
      fourierCoeff sawtooth (-n) * fourierCoeff (p (mode n)) n := by
  change (∫ a, sawFunctional (rotate (-a) (p (rotate a (mode n)))) ∂circleMeasure) = _
  simp_rw [rotate_mode, map_smul]
  exact average_pair_mode (p (mode n)) n

lemma mode_mem_H1 {n : ℤ} (hn : 0 ≤ n) : mode n ∈ H1 := by
  intro k hk
  rw [fourierCoeff_congr_ae (coeFn_mode n), fourierCoeff_fourier]
  simp [Pi.single, ne_of_lt <| hk.trans_le hn]

lemma projected_mode_of_nonneg (P : CircleL1 →L[ℂ] H1)
    (hP : ∀ x : H1, P x = x) {n : ℤ} (hn : 0 ≤ n) :
    H1.subtypeL (P (mode n)) = mode n := by
  have h := hP ⟨mode n, mode_mem_H1 hn⟩
  exact congr_arg Subtype.val h

lemma projected_mode_coeff_of_neg (P : CircleL1 →L[ℂ] H1) {n : ℤ} (hn : n < 0) :
    fourierCoeff (H1.subtypeL (P (mode n))) n = 0 :=
  (P (mode n)).property n hn

def analyticSum (N : ℕ) : C(UnitCircle, ℂ) :=
  ∑ j ∈ Finset.range N, fourier (j : ℤ)

def fejerContinuous (N : ℕ) : C(UnitCircle, ℂ) where
  toFun x := (((N : ℝ)⁻¹ * ‖analyticSum N x‖ ^ 2 : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def fejerKernel (N : ℕ) : CircleL1 :=
  ContinuousMap.toLp 1 circleMeasure ℂ (fejerContinuous N)

lemma integral_fourier_mode (n : ℤ) :
    (∫ x : UnitCircle, fourier n x ∂circleMeasure) = if n = 0 then 1 else 0 := by
  calc
    (∫ x : UnitCircle, fourier n x ∂circleMeasure) =
        fourierCoeff (T := (1 : ℝ)) (fourier (T := (1 : ℝ)) n) 0 := by
      simp [fourierCoeff]
    _ = ((Pi.single n (1 : ℂ) : ℤ → ℂ) 0) :=
      congr_fun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
    _ = if n = 0 then 1 else 0 := by
      classical
      by_cases hn : n = 0
      · subst n
        simp
      · rw [if_neg hn]
        exact Pi.single_eq_of_ne (M := fun _ : ℤ => ℂ) (Ne.symm hn) (1 : ℂ)

lemma fejerContinuous_eq_sum (N : ℕ) :
    fejerContinuous N =
      (N : ℂ)⁻¹ • ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        fourier ((l : ℤ) - j) := by
  ext x
  simp only [fejerContinuous, analyticSum, ContinuousMap.coe_mk]
  push_cast
  rw [← Complex.conj_mul']
  have hsum : (∑ j ∈ Finset.range N, fourier (j : ℤ)) x =
      ∑ j ∈ Finset.range N, fourier (j : ℤ) x := by simp
  have hdouble :
      (∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, fourier ((l : ℤ) - j)) x =
        ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, fourier ((l : ℤ) - j) x := by
    simp
  rw [hsum]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hdouble]
  congr 1
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, ← fourier_neg, ← fourier_add]
  congr 2 with j
  congr 2 with l
  congr 2
  omega

lemma fejerKernel_eq_sum (N : ℕ) :
    fejerKernel N =
      (N : ℂ)⁻¹ • ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        mode ((l : ℤ) - j) := by
  rw [fejerKernel, fejerContinuous_eq_sum]
  simp only [map_smul, map_sum]

lemma integrable_fourier_mode (n : ℤ) :
    Integrable (fun x : UnitCircle => fourier n x) circleMeasure :=
  (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_fejerContinuous (N : ℕ) (hN : 0 < N) :
    (∫ x : UnitCircle, fejerContinuous N x ∂circleMeasure) = 1 := by
  rw [fejerContinuous_eq_sum]
  have hdouble (x : UnitCircle) :
      (∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, fourier ((l : ℤ) - j)) x =
        ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          fourier ((l : ℤ) - j) x := by
    simp
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [hdouble]
  rw [integral_const_mul]
  have hinner (j : ℕ) :
      (∫ x : UnitCircle, ∑ l ∈ Finset.range N, fourier ((l : ℤ) - j) x
          ∂circleMeasure) =
        ∑ l ∈ Finset.range N,
          ∫ x : UnitCircle, fourier ((l : ℤ) - j) x ∂circleMeasure := by
    apply integral_finsetSum
    intro l hl
    exact integrable_fourier_mode _
  rw [integral_finsetSum]
  · simp_rw [hinner, integral_fourier_mode]
    simp [sub_eq_zero]
    have hfilter : {x ∈ Finset.range N | x < N} = Finset.range N := by
      ext x
      simp
    rw [hfilter, Finset.card_range]
    simp [Nat.ne_of_gt hN]
  · intro j hj
    exact integrable_finsetSum _ fun l hl => integrable_fourier_mode _

lemma norm_fejerContinuous (N : ℕ) (x : UnitCircle) :
    ‖fejerContinuous N x‖ = (N : ℝ)⁻¹ * ‖analyticSum N x‖ ^ 2 := by
  simp only [fejerContinuous, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  positivity

lemma norm_fejerKernel (N : ℕ) (hN : 0 < N) : ‖fejerKernel N‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  have hre := congr_arg Complex.re (integral_fejerContinuous N hN)
  have hfi : Integrable (fun x : UnitCircle => fejerContinuous N x) circleMeasure :=
    (fejerContinuous N).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hre' :
      (∫ x : UnitCircle, Complex.re (fejerContinuous N x) ∂circleMeasure) = 1 := by
    calc
      (∫ x : UnitCircle, Complex.re (fejerContinuous N x) ∂circleMeasure) =
          Complex.re (∫ x : UnitCircle, fejerContinuous N x ∂circleMeasure) :=
        integral_re hfi
      _ = Complex.re 1 := hre
      _ = 1 := by simp
  have hreal :
      (∫ x : UnitCircle, (N : ℝ)⁻¹ * ‖analyticSum N x‖ ^ 2 ∂circleMeasure) = 1 := by
    simpa only [fejerContinuous, ContinuousMap.coe_mk, Complex.ofReal_re,
      Complex.one_re] using hre'
  calc
    (∫ x : UnitCircle, ‖fejerKernel N x‖ ∂circleMeasure) =
        ∫ x : UnitCircle, (N : ℝ)⁻¹ * ‖analyticSum N x‖ ^ 2 ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (𝕜 := ℂ) circleMeasure
        (fejerContinuous N)] with x hx
      change ‖(ContinuousMap.toLp 1 circleMeasure ℂ) (fejerContinuous N) x‖ =
        (N : ℝ)⁻¹ * ‖analyticSum N x‖ ^ 2
      rw [hx, norm_fejerContinuous]
    _ = 1 := hreal

lemma fourierCoeff_sawtooth (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff sawtooth n = 1 / (-2 * Real.pi * Complex.I * n) := by
  letI hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let h01 := lt_add_of_pos_right (0 : ℝ) hT.out
  have hconst : fourierCoeff (fun _ : UnitCircle => (1 : ℂ)) n = 0 := by
    have h := congr_fun (fourierCoeff_fourier (T := (1 : ℝ)) 0) n
    rw [show (fun _ : UnitCircle => (1 : ℂ)) = fourier 0 by funext x; simp]
    simpa [Pi.single, hn] using h
  have hconstOn :
      fourierCoeffOn h01 (fun _ : ℝ => (1 : ℂ)) n = 0 := by
    calc
      fourierCoeffOn h01 (fun _ : ℝ => (1 : ℂ)) n =
          fourierCoeff (AddCircle.liftIoc 1 0 (fun _ : ℝ => (1 : ℂ))) n := by
        symm
        convert fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := 0)
          (fun _ : ℝ => (1 : ℂ)) n using 1
      _ = fourierCoeff (fun _ : UnitCircle => (1 : ℂ)) n := by rfl
      _ = 0 := hconst
  rw [sawtooth]
  calc
    fourierCoeff (AddCircle.liftIoc 1 0 (fun x : ℝ => (x : ℂ))) n =
        fourierCoeffOn h01 (fun x : ℝ => (x : ℂ)) n := by
      convert fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := 0)
        (fun x : ℝ => (x : ℂ)) n using 1
    _ = 1 / (-2 * Real.pi * Complex.I * n) := by
      rw [fourierCoeffOn_of_hasDerivAt h01 hn]
      · rw [hconstOn]
        simp
      · intro x hx
        convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
      · exact intervalIntegrable_const

def ambientProjection (P : CircleL1 →L[ℂ] H1) : CircleL1 →L[ℂ] CircleL1 :=
  H1.subtypeL.comp P

lemma ambientProjection_mode_coeff_of_nonneg (P : CircleL1 →L[ℂ] H1)
    (hP : ∀ x : H1, P x = x) {n : ℤ} (hn : 0 ≤ n) :
    fourierCoeff (ambientProjection P (mode n)) n = 1 := by
  change fourierCoeff (H1.subtypeL (P (mode n))) n = 1
  rw [projected_mode_of_nonneg P hP hn]
  rw [fourierCoeff_congr_ae (coeFn_mode n), fourierCoeff_fourier]
  simp

lemma averagedProjection_mode_of_neg (P : CircleL1 →L[ℂ] H1) {n : ℤ} (hn : n < 0) :
    averagedFunctional (ambientProjection P) (mode n) = 0 := by
  rw [averagedFunctional_mode]
  change fourierCoeff sawtooth (-n) *
    fourierCoeff (H1.subtypeL (P (mode n))) n = 0
  rw [projected_mode_coeff_of_neg P hn, mul_zero]

lemma averagedProjection_mode_of_pos (P : CircleL1 →L[ℂ] H1)
    (hP : ∀ x : H1, P x = x) {n : ℤ} (hn : 0 < n) :
    averagedFunctional (ambientProjection P) (mode n) =
      1 / (2 * Real.pi * Complex.I * n) := by
  rw [averagedFunctional_mode, ambientProjection_mode_coeff_of_nonneg P hP hn.le, mul_one]
  rw [fourierCoeff_sawtooth (-n) (neg_ne_zero.mpr hn.ne')]
  congr 1
  push_cast
  ring

lemma norm_mode (n : ℤ) : ‖mode n‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ x : UnitCircle, ‖mode n x‖ ∂circleMeasure) =
        ∫ _ : UnitCircle, (1 : ℝ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [coeFn_mode n] with x hx
      rw [hx]
      exact Circle.norm_coe _
    _ = 1 := by simp

def testKernel (N : ℕ) : CircleL1 :=
  fejerKernel N - mode 0

lemma norm_testKernel_le_two (N : ℕ) (hN : 0 < N) : ‖testKernel N‖ ≤ 2 := by
  calc
    ‖testKernel N‖ ≤ ‖fejerKernel N‖ + ‖mode 0‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_fejerKernel N hN, norm_mode]; norm_num

def positiveSumC (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
    if j < l then 1 / (2 * Real.pi * Complex.I * (l - j : ℕ)) else 0

lemma averagedProjection_testKernel (P : CircleL1 →L[ℂ] H1)
    (hP : ∀ x : H1, P x = x) (N : ℕ) (hN : 0 < N) :
    averagedFunctional (ambientProjection P) (testKernel N) =
      (N : ℂ)⁻¹ * positiveSumC N := by
  let A := averagedFunctional (ambientProjection P)
  let a0 := A (mode 0)
  have hterm (j l : ℕ) :
      A (mode ((l : ℤ) - j)) =
        (if l = j then a0 else 0) +
          if j < l then 1 / (2 * Real.pi * Complex.I * (l - j : ℕ)) else 0 := by
    rcases lt_trichotomy l j with hlj | hlj | hlj
    · have hneg : (l : ℤ) - j < 0 := by omega
      rw [show A (mode ((l : ℤ) - j)) = 0 by
        exact averagedProjection_mode_of_neg P hneg]
      simp [ne_of_lt hlj, not_lt_of_ge hlj.le]
    · subst l
      simp [a0]
    · have hpos : 0 < (l : ℤ) - j := by omega
      rw [show A (mode ((l : ℤ) - j)) =
          1 / (2 * Real.pi * Complex.I * ((((l : ℤ) - j : ℤ)) : ℂ)) by
        simpa [A] using averagedProjection_mode_of_pos P hP hpos]
      have hdiff : (l : ℤ) - j = (l - j : ℕ) := by omega
      have hdiffC : ((((l : ℤ) - j : ℤ)) : ℂ) = ((l - j : ℕ) : ℂ) := by
        exact_mod_cast hdiff
      rw [hdiffC]
      rw [if_neg (ne_of_gt hlj), if_pos hlj, zero_add]
  have hsum :
      (∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, A (mode ((l : ℤ) - j))) =
        (N : ℂ) * a0 + positiveSumC N := by
    calc
      (∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, A (mode ((l : ℤ) - j))) =
          ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
            ((if l = j then a0 else 0) +
              if j < l then 1 / (2 * Real.pi * Complex.I * (l - j : ℕ)) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        exact hterm j l
      _ = ∑ j ∈ Finset.range N,
          (a0 + ∑ l ∈ Finset.range N,
            if j < l then 1 / (2 * Real.pi * Complex.I * (l - j : ℕ)) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_add_distrib]
        simp [hj]
      _ = (N : ℂ) * a0 + positiveSumC N := by
        rw [Finset.sum_add_distrib]
        simp [positiveSumC, Finset.card_range, mul_comm]
  change A (fejerKernel N - mode 0) = (N : ℂ)⁻¹ * positiveSumC N
  rw [map_sub, fejerKernel_eq_sum, map_smul]
  simp_rw [map_sum]
  rw [hsum]
  change (N : ℂ)⁻¹ * ((N : ℂ) * a0 + positiveSumC N) - a0 =
    (N : ℂ)⁻¹ * positiveSumC N
  field_simp [Nat.cast_ne_zero.mpr hN.ne']
  ring

def positiveSumR (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
    if j < l then ((l - j : ℕ) : ℝ)⁻¹ else 0

lemma positiveSumR_nonneg (N : ℕ) : 0 ≤ positiveSumR N := by
  unfold positiveSumR
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro l hl
  split_ifs
  · positivity
  · rfl

lemma positiveSumC_eq (N : ℕ) :
    positiveSumC N =
      (1 / (2 * Real.pi * Complex.I)) * (positiveSumR N : ℂ) := by
  rw [positiveSumC, positiveSumR]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hjl : j < l
  · rw [if_pos hjl, if_pos hjl]
    have hdiff : (l - j : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hjl)
    field_simp [hdiff]
    simp [hdiff]
  · simp [hjl]

lemma norm_averagedFunctional_le (p : CircleL1 →L[ℂ] CircleL1) (f : CircleL1) :
    ‖averagedFunctional p f‖ ≤ ‖p‖ * ‖f‖ := by
  change ‖∫ a, sawFunctional (rotate (-a) (p (rotate a f))) ∂circleMeasure‖ ≤
    ‖p‖ * ‖f‖
  calc
    ‖∫ a, sawFunctional (rotate (-a) (p (rotate a f))) ∂circleMeasure‖
        ≤ (‖p‖ * ‖f‖) * circleMeasure.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with a
      calc
        ‖sawFunctional (rotate (-a) (p (rotate a f)))‖
            ≤ ‖rotate (-a) (p (rotate a f))‖ := norm_sawFunctional_le _
        _ = ‖p (rotate a f)‖ := (rotate (-a)).norm_map _
        _ ≤ ‖p‖ * ‖rotate a f‖ := p.le_opNorm _
        _ = ‖p‖ * ‖f‖ := by rw [(rotate a).norm_map]
    _ = ‖p‖ * ‖f‖ := by simp

lemma real_harmonic_eq_sum (M : ℕ) :
    (harmonic M : ℝ) = ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ)⁻¹ := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma positiveSumR_two_mul_lower (M : ℕ) :
    (M : ℝ) * (harmonic M : ℝ) ≤ positiveSumR (2 * M) := by
  let source := Finset.range M ×ˢ Finset.range M
  let target := Finset.range (2 * M) ×ˢ Finset.range (2 * M)
  let φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2 + 1)
  let F : ℕ × ℕ → ℝ := fun p =>
    if p.1 < p.2 then ((p.2 - p.1 : ℕ) : ℝ)⁻¹ else 0
  have hφinj : Set.InjOn φ source := by
    intro p hp q hq hpq
    rcases p with ⟨j, k⟩
    rcases q with ⟨j', k'⟩
    simp only [φ, Prod.mk.injEq] at hpq ⊢
    omega
  have hφmem : ∀ p ∈ source, φ p ∈ target := by
    intro p hp
    simp only [source, target, Finset.mem_product, Finset.mem_range] at hp ⊢
    simp only [φ]
    constructor <;> omega
  have hFnonneg (p : ℕ × ℕ) : 0 ≤ F p := by
    simp only [F]
    split_ifs
    · positivity
    · rfl
  have hsum_source :
      ∑ p ∈ source, F (φ p) = (M : ℝ) * (harmonic M : ℝ) := by
    rw [Finset.sum_product]
    have hterm (j k : ℕ) : F (φ (j, k)) = ((k + 1 : ℕ) : ℝ)⁻¹ := by
      simp only [F, φ]
      rw [if_pos (by omega)]
      congr 2
      omega
    simp_rw [hterm, ← real_harmonic_eq_sum]
    simp
  have himage : source.image φ ⊆ target := by
    intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact hφmem p hp
  calc
    (M : ℝ) * (harmonic M : ℝ) = ∑ p ∈ source, F (φ p) := hsum_source.symm
    _ = ∑ q ∈ source.image φ, F q := (Finset.sum_image hφinj).symm
    _ ≤ ∑ q ∈ target, F q :=
      Finset.sum_le_sum_of_subset_of_nonneg himage fun q hqt hqs => hFnonneg q
    _ = positiveSumR (2 * M) := by
      rw [Finset.sum_product]
      rfl

lemma norm_positiveSumC (N : ℕ) :
    ‖positiveSumC N‖ = positiveSumR N / (2 * Real.pi) := by
  rw [positiveSumC_eq, norm_mul, norm_div, norm_one]
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  norm_num
  rw [abs_of_pos Real.pi_pos]
  rw [abs_of_nonneg (positiveSumR_nonneg N)]
  ring

lemma norm_averagedProjection_testKernel (P : CircleL1 →L[ℂ] H1)
    (hP : ∀ x : H1, P x = x) (N : ℕ) (hN : 0 < N) :
    ‖averagedFunctional (ambientProjection P) (testKernel N)‖ =
      positiveSumR N / ((N : ℝ) * (2 * Real.pi)) := by
  rw [averagedProjection_testKernel P hP N hN, norm_mul, norm_inv,
    norm_positiveSumC]
  simp only [norm_natCast]
  field_simp

lemma exists_harmonic_gt (C : ℝ) :
    ∃ M : ℕ, 0 < M ∧ C < (harmonic M : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp C)
  have hMpos : 0 < M := by
    exact_mod_cast (Real.exp_pos C).trans hM
  refine ⟨M, hMpos, ?_⟩
  have hlog : C < Real.log (M : ℝ) :=
    (Real.lt_log_iff_exp_lt (by positivity)).2 hM
  calc
    C < Real.log (M : ℝ) := hlog
    _ ≤ Real.log ((M + 1 : ℕ) : ℝ) := by gcongr; omega
    _ ≤ (harmonic M : ℝ) := log_add_one_le_harmonic M

theorem not_H1_closedComplemented : ¬ H1.ClosedComplemented := by
  rintro ⟨P, hP⟩
  let p := ambientProjection P
  obtain ⟨M, hMpos, hMlarge⟩ :=
    exists_harmonic_gt (8 * Real.pi * ‖p‖)
  have htwoM : 0 < 2 * M := by omega
  have hnorm := norm_averagedProjection_testKernel P hP (2 * M) htwoM
  have hlower :
      (harmonic M : ℝ) / (4 * Real.pi) ≤
        ‖averagedFunctional p (testKernel (2 * M))‖ := by
    rw [hnorm]
    calc
      (harmonic M : ℝ) / (4 * Real.pi) =
          ((M : ℝ) * (harmonic M : ℝ)) /
            (((2 * M : ℕ) : ℝ) * (2 * Real.pi)) := by
        push_cast
        field_simp [Nat.cast_ne_zero.mpr hMpos.ne']
        ring
      _ ≤ positiveSumR (2 * M) / (((2 * M : ℕ) : ℝ) * (2 * Real.pi)) := by
        apply div_le_div_of_nonneg_right (positiveSumR_two_mul_lower M)
        positivity
  have hupper :
      ‖averagedFunctional p (testKernel (2 * M))‖ ≤ 2 * ‖p‖ := by
    calc
      ‖averagedFunctional p (testKernel (2 * M))‖
          ≤ ‖p‖ * ‖testKernel (2 * M)‖ := norm_averagedFunctional_le _ _
      _ ≤ ‖p‖ * 2 :=
        mul_le_mul_of_nonneg_left (norm_testKernel_le_two (2 * M) htwoM) (norm_nonneg p)
      _ = 2 * ‖p‖ := mul_comm _ _
  have hgrowth :
      2 * ‖p‖ < (harmonic M : ℝ) / (4 * Real.pi) := by
    calc
      2 * ‖p‖ = (8 * Real.pi * ‖p‖) / (4 * Real.pi) := by
        field_simp [Real.pi_ne_zero]
        ring
      _ < (harmonic M : ℝ) / (4 * Real.pi) :=
        div_lt_div_of_pos_right hMlarge (by positivity)
  exact (lt_irrefl (2 * ‖p‖)) (hgrowth.trans_le (hlower.trans hupper))

end

end Submission.Helpers
