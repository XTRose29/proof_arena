import Submission.GrunskyArea

open Metric

namespace Submission

noncomputable def rootTransform (L : ℂ → ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  z * Complex.exp (L (z ^ q) / (q : ℂ))

noncomputable def rootTransformLog (L : ℂ → ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  L (z ^ q) / (q : ℂ)

noncomputable def rootTransformLogCoeff (L : ℂ → ℂ) (q n : ℕ) : ℂ :=
  if q ∣ n then taylorCoeff L (n / q) / (q : ℂ) else 0

noncomputable def rootTransformLogSeries (L : ℂ → ℂ) (q : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (rootTransformLogCoeff L q)

lemma rootTransformLogCoeff_mul {L : ℂ → ℂ} {q : ℕ} (hq : 0 < q) (n : ℕ) :
    rootTransformLogCoeff L q (q * n) = taylorCoeff L n / (q : ℂ) := by
  simp [rootTransformLogCoeff, hq.ne']

lemma rootTransformLogCoeff_add_lt {L : ℂ → ℂ} {q k r : ℕ}
    (hr0 : 0 < r) (hrq : r < q) :
    rootTransformLogCoeff L q (q * k + r) = 0 := by
  rw [rootTransformLogCoeff, if_neg]
  intro hdvd
  have hmod : (q * k + r) % q = r := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hrq]
  have hzero := Nat.mod_eq_zero_of_dvd hdvd
  rw [hmod] at hzero
  omega

lemma summable_rootTransformLogCoeff_norm_mul_pow
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) :
    Summable (fun n => ‖rootTransformLogCoeff L q n‖ * S ^ n) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hbase := summable_norm_taylorCoeff_mul_pow hL (pow_nonneg hS.le q) hSR
  have hbase' : Summable (fun k =>
      ‖taylorCoeff L k / (q : ℂ)‖ * S ^ (q * k)) := by
    refine (hbase.mul_left (1 / (q : ℝ))).congr ?_
    intro k
    rw [norm_div, Complex.norm_natCast, pow_mul]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hq0]
  rw [← (Nat.divModEquiv q).symm.summable_iff]
  apply (summable_prod_of_nonneg (fun _ =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hS.le _))).2
  constructor
  · intro k
    exact (hasSum_fintype _).summable
  · simpa only [Function.comp_apply] using hbase'.congr fun k => by
      rw [tsum_fintype]
      let r0 : Fin q := ⟨0, hq⟩
      rw [Finset.sum_eq_single r0]
      · simp [Nat.divModEquiv_symm_apply, r0, Nat.mul_comm,
          rootTransformLogCoeff_mul hq]
      · intro r hr hr0
        have hrpos : 0 < (r : ℕ) := by
          by_contra h
          apply hr0
          exact Fin.ext (Nat.eq_zero_of_not_pos h)
        rw [Nat.divModEquiv_symm_apply]
        rw [show k * q + (r : ℕ) = q * k + r by rw [Nat.mul_comm]]
        rw [rootTransformLogCoeff_add_lt hrpos r.isLt, norm_zero, zero_mul]
      · simp

lemma rootTransformLogSeries_radius
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) :
    ENNReal.ofReal S ≤ (rootTransformLogSeries L q).radius := by
  let s : NNReal := ⟨S, hS.le⟩
  have hsreal : (s : ℝ) = S := rfl
  have hs : (s : ENNReal) ≤ (rootTransformLogSeries L q).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    simpa [rootTransformLogSeries, FormalMultilinearSeries.ofScalars_norm, hsreal] using
      summable_rootTransformLogCoeff_norm_mul_pow hS hq hL hSR
  calc
    ENNReal.ofReal S = ENNReal.ofReal (s : ℝ) := congrArg ENNReal.ofReal hsreal.symm
    _ = (s : ENNReal) := ENNReal.ofReal_coe_nnreal
    _ ≤ (rootTransformLogSeries L q).radius := hs

set_option maxHeartbeats 800000 in
lemma hasSum_rootTransformLogCoeff_mul_pow
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R)) (hSR : S ^ q < R)
    {y : ℂ} (hy : y ∈ ball 0 S) :
    HasSum (fun n => rootTransformLogCoeff L q n * y ^ n)
      (rootTransformLog L q y) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hyR : y ^ q ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff] at hy ⊢
    rw [norm_pow]
    exact (pow_lt_pow_left₀ hy (norm_nonneg y) hq.ne').trans hSR
  have hbase : HasSum (fun k => taylorCoeff L k * (y ^ q) ^ k) (L (y ^ q)) := by
    simpa only [taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using Complex.hasSum_taylorSeries_on_ball hL hyR
  have hsparse : HasSum
      (fun k => rootTransformLogCoeff L q (q * k) * y ^ (q * k))
      (rootTransformLog L q y) := by
    simpa only [rootTransformLog, rootTransformLogCoeff_mul hq, pow_mul,
      div_mul_eq_mul_div] using hbase.div_const (q : ℂ)
  let e : ℕ × Fin q ≃ ℕ := (Nat.divModEquiv q).symm
  have hyNorm : ‖y‖ < S := by simpa [mem_ball_zero_iff] using hy
  have hS : 0 < S := (norm_nonneg y).trans_lt hyNorm
  have hfull : Summable
      (fun n => rootTransformLogCoeff L q n * y ^ n) := by
    apply Summable.of_norm_bounded
      (summable_rootTransformLogCoeff_norm_mul_pow hS hq hL hSR)
    intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg y) hyNorm.le n) (norm_nonneg _)
  have hprodSummable : Summable
      (fun p : ℕ × Fin q =>
        rootTransformLogCoeff L q (e p) * y ^ (e p)) := by
    exact e.summable_iff.mpr hfull
  have hfiber : ∀ k, HasSum
      (fun r : Fin q => rootTransformLogCoeff L q (e (k, r)) * y ^ (e (k, r)))
      (rootTransformLogCoeff L q (q * k) * y ^ (q * k)) := by
    intro k
    convert hasSum_fintype (fun r : Fin q =>
      rootTransformLogCoeff L q (e (k, r)) * y ^ (e (k, r))) using 1
    let r0 : Fin q := ⟨0, hq⟩
    rw [Finset.sum_eq_single r0]
    · simp [e, Nat.divModEquiv_symm_apply, r0, Nat.mul_comm,
        rootTransformLogCoeff_mul hq]
    · intro r hr hr0
      have hrpos : 0 < (r : ℕ) := by
        by_contra h
        apply hr0
        exact Fin.ext (Nat.eq_zero_of_not_pos h)
      rw [show e (k, r) = k * q + (r : ℕ) by
        simp [e, Nat.divModEquiv_symm_apply]]
      rw [show k * q + (r : ℕ) = q * k + r by rw [Nat.mul_comm]]
      rw [rootTransformLogCoeff_add_lt hrpos r.isLt, zero_mul]
    · simp
  have hprod : HasSum
      (fun p : ℕ × Fin q =>
        rootTransformLogCoeff L q (e p) * y ^ (e p))
      (rootTransformLog L q y) := by
    have hgrouped := hprodSummable.hasSum.prod_fiberwise hfiber
    have htotal := hgrouped.unique hsparse
    simpa only [htotal] using hprodSummable.hasSum
  exact e.hasSum_iff.mp hprod

lemma rootTransformLog_hasFPowerSeriesAt
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) :
    HasFPowerSeriesAt (rootTransformLog L q) (rootTransformLogSeries L q) 0 := by
  refine ⟨ENNReal.ofReal S, {
    r_le := rootTransformLogSeries_radius hS hq hL hSR
    r_pos := ENNReal.ofReal_pos.mpr hS
    hasSum := ?_ }⟩
  intro y hy
  rw [Metric.eball_ofReal] at hy
  simpa only [zero_add, rootTransformLogSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
    hasSum_rootTransformLogCoeff_mul_pow hq hL hSR hy

lemma taylorCoeff_rootTransformLog
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) (n : ℕ) :
    taylorCoeff (rootTransformLog L q) n = rootTransformLogCoeff L q n := by
  have hp := rootTransformLog_hasFPowerSeriesAt hS hq hL hSR
  have ha : AnalyticAt ℂ (rootTransformLog L q) 0 := ⟨rootTransformLogSeries L q, hp⟩
  have heq := hp.eq_formalMultilinearSeries ha.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simpa [rootTransformLogSeries, taylorCoeff] using hc.symm

lemma taylorCoeff_rootTransformLog_mul
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) (n : ℕ) :
    taylorCoeff (rootTransformLog L q) (q * n) = taylorCoeff L n / (q : ℂ) := by
  rw [taylorCoeff_rootTransformLog hS hq hL hSR,
    rootTransformLogCoeff_mul hq]

lemma taylorCoeff_rootTransformLog_add_lt
    {L : ℂ → ℂ} {R S : ℝ} {q k r : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) (hr0 : 0 < r) (hrq : r < q) :
    taylorCoeff (rootTransformLog L q) (q * k + r) = 0 := by
  rw [taylorCoeff_rootTransformLog hS hq hL hSR,
    rootTransformLogCoeff_add_lt hr0 hrq]

lemma logarithmicCoeff_rootTransformLog_mul
    {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hS : 0 < S) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ q < R) (n : ℕ) :
    logarithmicCoeff (rootTransformLog L q) (q * n) =
      logarithmicCoeff L n / (q : ℂ) := by
  rw [logarithmicCoeff, taylorCoeff_rootTransformLog_mul hS hq hL hSR,
    logarithmicCoeff]
  ring

lemma pow_mem_ball {R S : ℝ} {q : ℕ} (hq : 0 < q) (hSR : S ^ q < R) :
    Set.MapsTo (fun z : ℂ => z ^ q) (ball 0 S) (ball 0 R) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_pow]
  exact (pow_lt_pow_left₀ hz (norm_nonneg z) hq.ne').trans hSR

lemma rootTransformLog_differentiableOn {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R)) (hSR : S ^ q < R) :
    DifferentiableOn ℂ (rootTransformLog L q) (ball 0 S) := by
  intro z hz
  have hzR : z ^ q ∈ ball (0 : ℂ) R := pow_mem_ball hq hSR hz
  exact ((hL.differentiableAt (isOpen_ball.mem_nhds hzR)).comp z
    (differentiableAt_pow q)).div_const (q : ℂ) |>.differentiableWithinAt

lemma rootTransform_differentiableOn {L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R)) (hSR : S ^ q < R) :
    DifferentiableOn ℂ (rootTransform L q) (ball 0 S) := by
  intro z hz
  exact differentiableWithinAt_id.mul
    ((rootTransformLog_differentiableOn hq hL hSR z hz).cexp)

lemma rootTransform_pow_eq {f L : ℂ → ℂ} {R : ℝ} {q : ℕ}
    (hq : 0 < q) (h0 : f 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    {z : ℂ} (hz : z ^ q ∈ ball (0 : ℂ) R) :
    rootTransform L q z ^ q = f (z ^ q) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [rootTransform, mul_pow, ← Complex.exp_nat_mul]
  have hdiv : L (z ^ q) / (q : ℂ) * q = L (z ^ q) := by
    field_simp [hq0]
  rw [mul_comm (q : ℂ), hdiv, hexp (z ^ q) hz]
  calc
    z ^ q * dslope f 0 (z ^ q) = f (z ^ q) - f 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope f 0 (z ^ q)
    _ = f (z ^ q) := by rw [h0, sub_zero]

lemma rootTransform_injOn {f L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hq : 0 < q) (hinj : (ball (0 : ℂ) R).InjOn f) (h0 : f 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hSR : S ^ q < R) :
    (ball (0 : ℂ) S).InjOn (rootTransform L q) := by
  intro z hz w hw hzw
  have hzq := pow_mem_ball hq hSR hz
  have hwq := pow_mem_ball hq hSR hw
  have hpows : z ^ q = w ^ q := by
    apply hinj hzq hwq
    rw [← rootTransform_pow_eq hq h0 hexp hzq,
      ← rootTransform_pow_eq hq h0 hexp hwq, hzw]
  have hexpEq : Complex.exp (L (z ^ q) / (q : ℂ)) =
      Complex.exp (L (w ^ q) / (q : ℂ)) := by rw [hpows]
  have hcancel : Complex.exp (L (w ^ q) / (q : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hcancel
  calc
    z * Complex.exp (L (w ^ q) / (q : ℂ)) = rootTransform L q z := by
      rw [rootTransform, hexpEq]
    _ = rootTransform L q w := hzw
    _ = w * Complex.exp (L (w ^ q) / (q : ℂ)) := rfl

@[simp]
lemma rootTransform_zero (L : ℂ → ℂ) (q : ℕ) : rootTransform L q 0 = 0 := by
  simp [rootTransform]

lemma rootTransform_deriv_zero {L : ℂ → ℂ} {R : ℝ} {q : ℕ}
    (hR : 0 < R) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0) :
    deriv (rootTransform L q) 0 = 1 := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hLAt : DifferentiableAt ℂ L 0 :=
    hL.differentiableAt (isOpen_ball.mem_nhds hzero)
  have hLAt' : DifferentiableAt ℂ L ((0 : ℂ) ^ q) := by
    simpa [hq.ne'] using hLAt
  have hpow : DifferentiableAt ℂ (fun z : ℂ => z ^ q) 0 := differentiableAt_pow q
  have hinner : DifferentiableAt ℂ (fun z : ℂ => L (z ^ q)) 0 :=
    DifferentiableAt.fun_comp' (x := (0 : ℂ)) hLAt' hpow
  have hfactor : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (L (z ^ q) / (q : ℂ))) 0 :=
    (hinner.div_const (q : ℂ)).cexp
  have hprod := (hasDerivAt_id (0 : ℂ)).mul hfactor.hasDerivAt
  change deriv (id * fun z : ℂ => Complex.exp (L (z ^ q) / (q : ℂ))) 0 = 1
  simpa [hq.ne', hL0] using hprod.deriv

lemma rootTransformLog_zero {L : ℂ → ℂ} {q : ℕ} (hq : 0 < q) (hL0 : L 0 = 0) :
    rootTransformLog L q 0 = 0 := by
  simp [rootTransformLog, hq.ne', hL0]

lemma rootTransform_exp_log_eq_dslope {L : ℂ → ℂ} {R : ℝ} {q : ℕ}
    (hR : 0 < R) (hq : 0 < q) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0) (z : ℂ) :
    Complex.exp (rootTransformLog L q z) = dslope (rootTransform L q) 0 z := by
  by_cases hz : z = 0
  · subst z
    simp [rootTransformLog, hq.ne', hL0, dslope_same,
      rootTransform_deriv_zero hR hq hL hL0]
  · apply mul_left_cancel₀ hz
    simpa only [rootTransformLog, rootTransform, sub_zero, smul_eq_mul] using
      (sub_smul_dslope_of_zero (rootTransform_zero L q) z).symm

lemma normalizedUnivalentOn_rootTransform {f L : ℂ → ℂ} {R S : ℝ} {q : ℕ}
    (hR : 0 < R) (hq : 0 < q) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hSR : S ^ q < R) :
    NormalizedUnivalentOn (rootTransform L q) S := by
  refine ⟨rootTransform_differentiableOn hq hL hSR,
    rootTransform_injOn hq hf.2.1 hf.2.2.1 hexp hSR, rootTransform_zero L q, ?_⟩
  exact rootTransform_deriv_zero hR hq hL hL0

end Submission
