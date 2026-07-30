import Submission.Central
import Submission.ResidueCertificate
import Submission.Landau
import Submission.MGFLandau
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Probability.Moments.MGFAnalytic

open Complex Filter MeasureTheory Real Set Topology
open scoped LSeries.notation

namespace Submission.SignChange

open Submission.Analytic Submission.Helpers Submission.PrimeSeries

lemma abs_realCharacterPrimeSum_le (n : ℕ) :
    |realCharacterPrimeSum n| ≤ n + 1 := by
  calc
    |realCharacterPrimeSum n| = ‖(realCharacterPrimeSum n : ℂ)‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖complexCharacterPrimeSum n‖ := by
      rw [complexCharacterPrimeSum_eq_real]
    _ = ‖∑ p ∈ Finset.range (n + 1), primeCharacterCoeff p‖ := by
      rfl
    _ ≤
        ∑ p ∈ Finset.range (n + 1), ‖primeCharacterCoeff p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.range (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      unfold primeCharacterCoeff
      split_ifs with hp
      · rw [chiFour_apply_nat]
        generalize (p : ZMod 4) = z
        fin_cases z <;> norm_num [ZMod.χ₄]
      · simp
    _ = n + 1 := by simp

lemma exists_global_positive_shift_of_eventually_nonneg
    {a : ℕ → ℝ} (h : ∀ᶠ n in atTop, 0 ≤ a n) :
    ∃ C : ℝ, ∀ n, 1 ≤ a n + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, |a i|
  refine ⟨C, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have ha : 0 ≤ a n := hN n hn
    have hC : 1 ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    linarith
  · have hn' : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hterm : |a n| ≤ ∑ i ∈ Finset.range N, |a i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (a i)) hn'
    have halower : -|a n| ≤ a n := neg_abs_le (a n)
    dsimp [C]
    linarith

lemma exists_global_positive_shift_of_eventually_nonpos
    {a : ℕ → ℝ} (h : ∀ᶠ n in atTop, a n ≤ 0) :
    ∃ C : ℝ, ∀ n, 1 ≤ -a n + C := by
  have hneg : ∀ᶠ n in atTop, 0 ≤ -a n := h.mono fun _ hn => neg_nonneg.mpr hn
  simpa only [neg_neg] using
    (exists_global_positive_shift_of_eventually_nonneg (a := fun n => -a n) hneg)

noncomputable def adjustedPrimeCoeff (sign C : ℝ) (n : ℕ) : ℂ :=
  (sign : ℂ) * primeCharacterCoeff n + if n = 1 then (C : ℂ) else 0

noncomputable def adjustedPrimeSum (sign C : ℝ) (n : ℕ) : ℝ :=
  sign * realCharacterPrimeSum n + C

private lemma primeCharacterCoeff_zero : primeCharacterCoeff 0 = 0 := by
  simp [primeCharacterCoeff, Nat.not_prime_zero]

lemma sum_primeCharacterCoeff_Icc (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, primeCharacterCoeff k = complexCharacterPrimeSum n := by
  unfold complexCharacterPrimeSum
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hkRange hkIcc
    simp only [Finset.mem_range] at hkRange
    simp only [Finset.mem_Icc, not_and_or, not_le] at hkIcc
    have hkZero : k = 0 := by omega
    simpa [hkZero] using primeCharacterCoeff_zero

lemma sum_adjustedPrimeCoeff_Icc {sign C : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, adjustedPrimeCoeff sign C k =
      (adjustedPrimeSum sign C n : ℂ) := by
  simp_rw [adjustedPrimeCoeff]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_primeCharacterCoeff_Icc, complexCharacterPrimeSum_eq_real]
  have hone : ∑ k ∈ Finset.Icc 1 n, (if k = 1 then (C : ℂ) else 0) = C := by
    rw [Finset.sum_ite_eq' (a := 1)]
    simp [hn]
  rw [hone]
  simp [adjustedPrimeSum]

lemma abs_adjustedPrimeSum_le (sign C : ℝ) (n : ℕ) :
    |adjustedPrimeSum sign C n| ≤ |sign| * (n + 1) + |C| := by
  rw [adjustedPrimeSum]
  calc
    |sign * realCharacterPrimeSum n + C| ≤
        |sign * realCharacterPrimeSum n| + |C| := abs_add_le _ _
    _ = |sign| * |realCharacterPrimeSum n| + |C| := by rw [abs_mul]
    _ ≤ |sign| * (n + 1) + |C| := by
      gcongr
      exact abs_realCharacterPrimeSum_le n

lemma norm_adjustedPrimeCoeff_le (sign C : ℝ) (n : ℕ) :
    ‖adjustedPrimeCoeff sign C n‖ ≤ |sign| + |C| := by
  unfold adjustedPrimeCoeff
  calc
    ‖(sign : ℂ) * primeCharacterCoeff n +
        (if n = 1 then (C : ℂ) else 0)‖ ≤
        ‖(sign : ℂ) * primeCharacterCoeff n‖ +
          ‖if n = 1 then (C : ℂ) else 0‖ := norm_add_le _ _
    _ ≤ |sign| + |C| := by
      have hcoeff : ‖primeCharacterCoeff n‖ ≤ 1 := by
        unfold primeCharacterCoeff
        split_ifs
        · rw [chiFour_apply_nat]
          generalize (n : ZMod 4) = z
          fin_cases z <;> norm_num [ZMod.χ₄]
        · simp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      split_ifs
      · simpa [Complex.norm_real, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left hcoeff (abs_nonneg sign)
      · simp only [norm_zero, add_zero]
        calc
          |sign| * ‖primeCharacterCoeff n‖ ≤ |sign| := by
            simpa using mul_le_mul_of_nonneg_left hcoeff (abs_nonneg sign)
          _ ≤ |sign| + |C| := le_add_of_nonneg_right (abs_nonneg C)

lemma adjustedPrimeCoeff_LSeriesSummable {sign C : ℝ} {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (adjustedPrimeCoeff sign C) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re
    (m := |sign| + |C|) (fun n _hn => norm_adjustedPrimeCoeff_le sign C n) hs

noncomputable def mellinDensity (sign C : ℝ) (t : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator
    (fun x => adjustedPrimeSum sign C ⌊x⌋₊ * x ^ (-4 : ℝ)) t

lemma measurable_mellinDensity (sign C : ℝ) :
    Measurable (mellinDensity sign C) := by
  unfold mellinDensity
  have hrpow : Measurable (fun x : ℝ => x ^ (-4 : ℝ)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    exact (Real.continuousAt_rpow_const x (-4) (Or.inl hx)).continuousWithinAt
  apply Measurable.indicator
  · exact ((measurable_of_countable (adjustedPrimeSum sign C)).comp
      Nat.measurable_floor).mul hrpow
  · exact measurableSet_Ioi

lemma mellinDensity_nonneg {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) (t : ℝ) :
    0 ≤ mellinDensity sign C t := by
  unfold mellinDensity
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem ht]
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_nonneg (hpos _) (Real.rpow_nonneg ht0.le _)
  · rw [Set.indicator_of_notMem ht]

lemma integrable_mellinDensity {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) :
    Integrable (mellinDensity sign C) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-3 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  let D : ℝ := 2 * (|sign| + |C| + 1)
  have hD : 0 ≤ D := by positivity
  have hmajor : IntegrableOn (fun t : ℝ => D * t ^ (-3 : ℝ)) (Ioi 1) := by
    exact (hpow.const_mul D)
  have hcoreMeas : AEStronglyMeasurable
      (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (-4 : ℝ))
      (volume.restrict (Ioi 1)) := by
    have hrpow : Measurable (fun x : ℝ => x ^ (-4 : ℝ)) := by
      apply measurable_of_continuousOn_compl_singleton 0
      intro x hx
      exact (Real.continuousAt_rpow_const x (-4) (Or.inl hx)).continuousWithinAt
    exact (((measurable_of_countable (adjustedPrimeSum sign C)).comp
      Nat.measurable_floor).mul hrpow).aestronglyMeasurable
  have hcore : IntegrableOn
      (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (-4 : ℝ)) (Ioi 1) := by
    apply Integrable.mono' hmajor hcoreMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hpos _) (Real.rpow_nonneg ht0.le _))]
    calc
      adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (-4 : ℝ) ≤
          ((|sign| + |C| + 1) * (2 * t)) * t ^ (-4 : ℝ) := by
        have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
        have hsumAbs := abs_adjustedPrimeSum_le sign C ⌊t⌋₊
        have hsum : adjustedPrimeSum sign C ⌊t⌋₊ ≤
            (|sign| + |C| + 1) * (2 * t) := by
          have htOne : 1 < t := ht
          have hfloorOne : (⌊t⌋₊ : ℝ) + 1 ≤ 2 * t := by linarith
          calc
            adjustedPrimeSum sign C ⌊t⌋₊ ≤
                |adjustedPrimeSum sign C ⌊t⌋₊| := le_abs_self _
            _ ≤ |sign| * ((⌊t⌋₊ : ℝ) + 1) + |C| := by
              simpa using hsumAbs
            _ ≤ (|sign| + |C| + 1) * (2 * t) := by
              nlinarith [abs_nonneg sign, abs_nonneg C]
        gcongr
      _ = D * t ^ (-3 : ℝ) := by
        dsimp [D]
        rw [show (-3 : ℝ) = 1 + (-4 : ℝ) by norm_num, Real.rpow_add ht0,
          Real.rpow_one]
        ring
  unfold mellinDensity
  exact hcore.integrable_indicator measurableSet_Ioi

noncomputable def mellinMeasure (sign C : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (mellinDensity sign C t)

lemma mellinMeasure_finite {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) :
    IsFiniteMeasure (mellinMeasure sign C) := by
  unfold mellinMeasure
  exact isFiniteMeasure_withDensity_ofReal (integrable_mellinDensity hpos).hasFiniteIntegral

lemma adjustedPrimeCoeff_partialSums_isBigO (sign C : ℝ) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, adjustedPrimeCoeff sign C k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  let D : ℝ := 4 * (|sign| + |C| + 1)
  apply Asymptotics.IsBigO.of_bound D
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnormR : ‖(n : ℝ) ^ (1 : ℝ)‖ = (n : ℝ) := by
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [sum_adjustedPrimeCoeff_Icc hn, Complex.norm_real, Real.norm_eq_abs, hnormR]
  have hsum := abs_adjustedPrimeSum_le sign C n
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsign : 0 ≤ |sign| := abs_nonneg _
  have hC : 0 ≤ |C| := abs_nonneg _
  dsimp [D]
  nlinarith

noncomputable def adjustedPrimeMellin (sign C : ℝ) (s : ℂ) : ℂ :=
  ProbabilityTheory.complexMGF Real.log (mellinMeasure sign C) (3 - s)

private lemma mellinDensity_mul_exp {sign C : ℝ} {s : ℂ} {t : ℝ}
    (ht : t ∈ Ioi (1 : ℝ)) :
    ((mellinDensity sign C t : ℝ) : ℂ) *
        Complex.exp (((3 : ℂ) - s) * (Real.log t : ℂ)) =
      (adjustedPrimeSum sign C ⌊t⌋₊ : ℂ) *
        (t : ℂ) ^ (-(s + 1)) := by
  rw [mellinDensity, Set.indicator_of_mem ht]
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht0.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht0.ne')]
  rw [← Complex.ofReal_log ht0.le, mul_assoc, ← Complex.exp_add]
  congr 2
  norm_num
  ring

lemma adjustedPrimeMellin_eq_LSeries_div {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) {s : ℂ} (hs : 1 < s.re) :
    adjustedPrimeMellin sign C s =
      L (adjustedPrimeCoeff sign C) s / s := by
  letI : IsFiniteMeasure (mellinMeasure sign C) := mellinMeasure_finite hpos
  have hS := adjustedPrimeCoeff_LSeriesSummable (sign := sign) (C := C) hs
  have hAbel := LSeries_eq_mul_integral (adjustedPrimeCoeff sign C)
    (r := 1) zero_le_one hs hS (adjustedPrimeCoeff_partialSums_isBigO sign C)
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hIntegral :
      adjustedPrimeMellin sign C s =
        ∫ t in Ioi (1 : ℝ),
          (adjustedPrimeSum sign C ⌊t⌋₊ : ℂ) *
            (t : ℂ) ^ (-(s + 1)) := by
    unfold adjustedPrimeMellin ProbabilityTheory.complexMGF mellinMeasure
    rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_mellinDensity sign C).ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht, ENNReal.toReal_ofReal
          (mellinDensity_nonneg hpos t), Complex.real_smul]
      exact mellinDensity_mul_exp ht
    · rw [Set.indicator_of_notMem ht, mellinDensity, Set.indicator_of_notMem ht,
        ENNReal.ofReal_zero, ENNReal.toReal_zero, zero_smul]
  have hsumIntegral :
      (∫ t in Ioi (1 : ℝ),
          (adjustedPrimeSum sign C ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        ∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, adjustedPrimeCoeff sign C k) *
            (t : ℂ) ^ (-(s + 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (adjustedPrimeSum sign C ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, adjustedPrimeCoeff sign C k) *
        (t : ℂ) ^ (-(s + 1))
    have htOne : (1 : ℝ) ≤ t := le_of_lt ht
    have hfloor : 1 ≤ ⌊t⌋₊ := by
      apply Nat.le_floor
      simpa using htOne
    rw [sum_adjustedPrimeCoeff_Icc hfloor]
  calc
    adjustedPrimeMellin sign C s =
        ∫ t in Ioi (1 : ℝ),
          (adjustedPrimeSum sign C ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := hIntegral
    _ = ∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, adjustedPrimeCoeff sign C k) *
            (t : ℂ) ^ (-(s + 1)) := hsumIntegral
    _ = L (adjustedPrimeCoeff sign C) s / s := by
      rw [hAbel]
      field_simp

lemma ae_log_nonneg_mellinMeasure (sign C : ℝ) :
    ∀ᵐ t ∂mellinMeasure sign C, 0 ≤ Real.log t := by
  unfold mellinMeasure
  rw [ae_withDensity_iff
    ((measurable_mellinDensity sign C).ennreal_ofReal)]
  filter_upwards with t
  intro htDensity
  have htPos : 0 < mellinDensity sign C t :=
    ENNReal.ofReal_ne_zero_iff.mp htDensity
  have ht : t ∈ Ioi (1 : ℝ) := by
    by_contra ht
    have hdensityZero : mellinDensity sign C t = 0 := by
      simp [mellinDensity, ht]
    linarith
  exact Real.log_nonneg (le_of_lt ht)

lemma integrableExpSet_mellinMeasure_downward_closed (sign C : ℝ)
    {u v : ℝ}
    (hu : u ∈ ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C))
    (hvu : v ≤ u) :
    v ∈ ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) := by
  apply hu.mono'
  · exact (Real.measurable_exp.comp
      (measurable_const.mul Real.measurable_log)).aestronglyMeasurable
  filter_upwards [ae_log_nonneg_mellinMeasure sign C] with t ht
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hvu ht)

private lemma integrable_exp_mul_mellinDensity {sign C u : ℝ} (hu : u < 2) :
    Integrable
      (fun t : ℝ => Real.exp (u * Real.log t) * mellinDensity sign C t) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (u - 3)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  let D : ℝ := 2 * (|sign| + |C| + 1)
  have hmajor : IntegrableOn (fun t : ℝ => D * t ^ (u - 3)) (Ioi 1) :=
    hpow.const_mul D
  have hcoreMeas : AEStronglyMeasurable
      (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (u - 4))
      (volume.restrict (Ioi 1)) := by
    have hrpow : Measurable (fun x : ℝ => x ^ (u - 4)) := by
      apply measurable_of_continuousOn_compl_singleton 0
      intro x hx
      exact (Real.continuousAt_rpow_const x (u - 4) (Or.inl hx)).continuousWithinAt
    exact (((measurable_of_countable (adjustedPrimeSum sign C)).comp
      Nat.measurable_floor).mul hrpow).aestronglyMeasurable
  have hcore : IntegrableOn
      (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (u - 4)) (Ioi 1) := by
    apply Integrable.mono' hmajor hcoreMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      |adjustedPrimeSum sign C ⌊t⌋₊| * t ^ (u - 4) ≤
          ((|sign| + |C| + 1) * (2 * t)) * t ^ (u - 4) := by
        have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
        have hsumAbs := abs_adjustedPrimeSum_le sign C ⌊t⌋₊
        have hbound : |adjustedPrimeSum sign C ⌊t⌋₊| ≤
            (|sign| + |C| + 1) * (2 * t) := by
          have htOne : 1 < t := ht
          have hfloorOne : (⌊t⌋₊ : ℝ) + 1 ≤ 2 * t := by linarith
          calc
            |adjustedPrimeSum sign C ⌊t⌋₊| ≤
                |sign| * ((⌊t⌋₊ : ℝ) + 1) + |C| := by
              simpa using hsumAbs
            _ ≤ (|sign| + |C| + 1) * (2 * t) := by
              nlinarith [abs_nonneg sign, abs_nonneg C]
        gcongr
      _ = D * t ^ (u - 3) := by
        dsimp [D]
        rw [show u - 3 = 1 + (u - 4) by ring, Real.rpow_add ht0,
          Real.rpow_one]
        ring
  have hindicator : Integrable
      ((Ioi (1 : ℝ)).indicator
        (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (u - 4))) :=
    hcore.integrable_indicator measurableSet_Ioi
  apply hindicator.congr
  filter_upwards with t
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [mellinDensity, Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [show Real.exp (u * Real.log t) = t ^ u by
      rw [Real.rpow_def_of_pos ht0]
      congr 1
      ring]
    rw [show u - 4 = u + (-4) by ring, Real.rpow_add ht0]
    ring
  · rw [mellinDensity, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht,
      mul_zero]

lemma lt_two_mem_integrableExpSet_mellinMeasure {sign C u : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) (hu : u < 2) :
    u ∈ ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) := by
  unfold ProbabilityTheory.integrableExpSet mellinMeasure
  change Integrable (fun t : ℝ => Real.exp (u * Real.log t))
    (volume.withDensity fun t => ENNReal.ofReal (mellinDensity sign C t))
  rw [integrable_withDensity_iff
    ((measurable_mellinDensity sign C).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (mellinDensity_nonneg hpos _), mul_comm] using
    (integrable_exp_mul_mellinDensity (sign := sign) (C := C) hu)

lemma three_not_mem_integrableExpSet_mellinMeasure {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    (3 : ℝ) ∉ ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) := by
  intro hthree
  have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n := fun n => (hone n).trans' zero_le_one
  have hweighted : Integrable
      (fun t : ℝ => Real.exp (3 * Real.log t) * mellinDensity sign C t) := by
    unfold ProbabilityTheory.integrableExpSet mellinMeasure at hthree
    change Integrable (fun t : ℝ => Real.exp (3 * Real.log t))
      (volume.withDensity fun t => ENNReal.ofReal (mellinDensity sign C t)) at hthree
    rw [integrable_withDensity_iff
      ((measurable_mellinDensity sign C).ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hthree
    simpa only [ENNReal.toReal_ofReal (mellinDensity_nonneg hpos _), mul_comm] using hthree
  have htailIndicator : Integrable
      ((Ioi (1 : ℝ)).indicator
        (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (-1 : ℝ))) := by
    apply hweighted.congr
    filter_upwards with t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [mellinDensity, Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [show Real.exp (3 * Real.log t) = t ^ (3 : ℝ) by
        rw [Real.rpow_def_of_pos ht0]
        congr 1
        ring]
      rw [show (-1 : ℝ) = 3 + (-4) by norm_num, Real.rpow_add ht0]
      ring
    · rw [mellinDensity, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht,
        mul_zero]
  have htail : IntegrableOn
      (fun t : ℝ => adjustedPrimeSum sign C ⌊t⌋₊ * t ^ (-1 : ℝ)) (Ioi 1) :=
    (integrable_indicator_iff measurableSet_Ioi).mp htailIndicator
  have hinvMeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-1 : ℝ))
      (volume.restrict (Ioi 1)) := by
    have hrpow : Measurable (fun t : ℝ => t ^ (-1 : ℝ)) := by
      apply measurable_of_continuousOn_compl_singleton 0
      intro t ht
      exact (Real.continuousAt_rpow_const t (-1) (Or.inl ht)).continuousWithinAt
    exact hrpow.aestronglyMeasurable
  have hinv : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioi 1) := by
    apply Integrable.mono' htail hinvMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hpowNonneg : 0 ≤ t ^ (-1 : ℝ) := Real.rpow_nonneg ht0.le _
    have hsumOne : 1 ≤ adjustedPrimeSum sign C ⌊t⌋₊ := hone _
    simpa [Real.norm_eq_abs, abs_of_nonneg hpowNonneg,
      abs_of_nonneg (mul_nonneg (zero_le_one.trans hsumOne) hpowNonneg)] using
      (mul_le_mul_of_nonneg_right hsumOne hpowNonneg)
  have hnot : ¬ IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioi 1) := by
    rw [integrableOn_Ioi_rpow_iff zero_lt_one]
    norm_num
  exact hnot hinv

noncomputable def mellinMGFEndpoint (sign C : ℝ) : ℝ :=
  sSup (ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C))

noncomputable def mellinAbscissa (sign C : ℝ) : ℝ :=
  3 - mellinMGFEndpoint sign C

lemma integrableExpSet_mellinMeasure_nonempty {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) :
    (ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C)).Nonempty := by
  refine ⟨0, lt_two_mem_integrableExpSet_mellinMeasure hpos (by norm_num)⟩

lemma integrableExpSet_mellinMeasure_bddAbove {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    BddAbove (ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C)) := by
  refine ⟨3, fun u hu => ?_⟩
  by_contra hut
  have hthree : (3 : ℝ) ∈
      ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) :=
    integrableExpSet_mellinMeasure_downward_closed sign C hu
      (le_of_not_ge hut)
  exact three_not_mem_integrableExpSet_mellinMeasure hone hthree

lemma two_le_mellinMGFEndpoint {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    2 ≤ mellinMGFEndpoint sign C := by
  have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n := fun n => (hone n).trans' zero_le_one
  have hb := integrableExpSet_mellinMeasure_bddAbove hone
  by_contra hend
  let u : ℝ := (mellinMGFEndpoint sign C + 2) / 2
  have huEnd : mellinMGFEndpoint sign C < u := by
    dsimp [u]
    linarith
  have huTwo : u < 2 := by
    dsimp [u]
    linarith
  have huMem := lt_two_mem_integrableExpSet_mellinMeasure hpos huTwo
  have huLe : u ≤ mellinMGFEndpoint sign C := by
    unfold mellinMGFEndpoint
    exact le_csSup hb huMem
  exact (not_le_of_gt huEnd) huLe

lemma mellinMGFEndpoint_le_three {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    mellinMGFEndpoint sign C ≤ 3 := by
  have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n := fun n => (hone n).trans' zero_le_one
  unfold mellinMGFEndpoint
  apply csSup_le (integrableExpSet_mellinMeasure_nonempty hpos)
  intro u hu
  by_contra hut
  have hthree : (3 : ℝ) ∈
      ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) :=
    integrableExpSet_mellinMeasure_downward_closed sign C hu
      (le_of_not_ge hut)
  exact three_not_mem_integrableExpSet_mellinMeasure hone hthree

lemma mellinAbscissa_nonneg {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    0 ≤ mellinAbscissa sign C := by
  unfold mellinAbscissa
  linarith [mellinMGFEndpoint_le_three hone]

lemma mellinAbscissa_le_one {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    mellinAbscissa sign C ≤ 1 := by
  unfold mellinAbscissa
  linarith [two_le_mellinMGFEndpoint hone]

lemma lt_mellinMGFEndpoint_mem_interior {sign C u : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n)
    (hu : u < mellinMGFEndpoint sign C) :
    u ∈ interior
      (ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C)) := by
  have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n := fun n => (hone n).trans' zero_le_one
  have hb := integrableExpSet_mellinMeasure_bddAbove hone
  have hne := integrableExpSet_mellinMeasure_nonempty hpos
  unfold mellinMGFEndpoint at hu
  obtain ⟨v, hv, huv⟩ := (lt_csSup_iff hb hne).mp hu
  have hIio : Iio v ⊆
      ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) := by
    intro w hw
    exact integrableExpSet_mellinMeasure_downward_closed sign C hv (le_of_lt hw)
  exact (isOpen_Iio.subset_interior_iff.mpr hIio) huv

lemma mellinMGFEndpoint_lt_not_mem_integrableExpSet {sign C u : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n)
    (hu : mellinMGFEndpoint sign C < u) :
    u ∉ ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C) := by
  intro huMem
  have huLe : u ≤ mellinMGFEndpoint sign C := by
    unfold mellinMGFEndpoint
    exact le_csSup (integrableExpSet_mellinMeasure_bddAbove hone) huMem
  exact (not_le_of_gt hu) huLe

lemma three_sub_re_mem_interior_integrableExpSet {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) {s : ℂ}
    (hs : mellinAbscissa sign C < s.re) :
    (3 - s).re ∈ interior
      (ProbabilityTheory.integrableExpSet Real.log (mellinMeasure sign C)) := by
  apply lt_mellinMGFEndpoint_mem_interior hone
  change 3 - s.re < mellinMGFEndpoint sign C
  unfold mellinAbscissa at hs
  linarith

lemma analyticAt_adjustedPrimeMellin {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) {s : ℂ}
    (hs : mellinAbscissa sign C < s.re) :
    AnalyticAt ℂ (adjustedPrimeMellin sign C) s := by
  unfold adjustedPrimeMellin
  exact (ProbabilityTheory.analyticAt_complexMGF
    (three_sub_re_mem_interior_integrableExpSet hone hs)).comp (by fun_prop)

noncomputable def adjustedPrimeDirichlet (sign C : ℝ) (s : ℂ) : ℂ :=
  s * adjustedPrimeMellin sign C s

lemma adjustedPrimeCoeff_abscissaOfAbsConv_le (sign C : ℝ) :
    LSeries.abscissaOfAbsConv (adjustedPrimeCoeff sign C) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  exact ⟨|sign| + |C|, fun n _hn => norm_adjustedPrimeCoeff_le sign C n⟩

lemma logMul_adjustedPrimeCoeff (sign C : ℝ) (n : ℕ) :
    LSeries.logMul (adjustedPrimeCoeff sign C) n =
      (sign : ℂ) * twistedPrimeLogCoeff n := by
  rw [LSeries.logMul, adjustedPrimeCoeff, twistedPrimeLogCoeff_eq_log_mul]
  by_cases hn : n = 1
  · subst n
    simp
  · simp [hn]
    ring

lemma adjustedPrimeDirichlet_eq_LSeries {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) {s : ℂ} (hs : 1 < s.re) :
    adjustedPrimeDirichlet sign C s = L (adjustedPrimeCoeff sign C) s := by
  rw [adjustedPrimeDirichlet, adjustedPrimeMellin_eq_LSeries_div hpos hs]
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hs)
  field_simp

lemma deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation
    {sign C : ℝ} (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n)
    {s : ℂ} (hs : 1 < s.re) :
    deriv (adjustedPrimeDirichlet sign C) s =
      -(sign : ℂ) * twistedPrimeLogContinuation s := by
  have hOpen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const continuous_re
  have hevent : adjustedPrimeDirichlet sign C =ᶠ[𝓝 s]
      L (adjustedPrimeCoeff sign C) :=
    eventually_of_mem (hOpen.mem_nhds hs) fun _z hz =>
      adjustedPrimeDirichlet_eq_LSeries hpos hz
  rw [hevent.deriv_eq]
  have hab : LSeries.abscissaOfAbsConv (adjustedPrimeCoeff sign C) < (s.re : EReal) :=
    (adjustedPrimeCoeff_abscissaOfAbsConv_le sign C).trans_lt (by exact_mod_cast hs)
  rw [LSeries_deriv hab]
  have hcoeff : LSeries.logMul (adjustedPrimeCoeff sign C) =
      (sign : ℂ) • twistedPrimeLogCoeff := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    exact logMul_adjustedPrimeCoeff sign C n
  rw [hcoeff, LSeries_smul, ← twistedPrimeLogContinuation_eq_LSeries hs]
  ring

lemma squarePrimePowerContinuation_analyticAt_of_half_lt_re {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ squarePrimePowerContinuation s := by
  have htwoRe : 1 < (2 * s).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  have htwoOne : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.mul_re] at hre
    linarith
  have htwoHalf : (1 / 2 : ℝ) < (2 * s).re := by linarith
  have hodd := oddPrimeLogContinuation_analyticAt htwoOne
    (riemannZeta_ne_zero_of_one_le_re htwoRe.le) htwoHalf
  change AnalyticAt ℂ (fun z => oddPrimeLogContinuation (2 * z)) s
  exact hodd.comp (by fun_prop)

noncomputable def clearedAdjustedPrimeDerivative (sign C : ℝ) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction chiFour s * deriv (adjustedPrimeDirichlet sign C) s -
    (sign : ℂ) * deriv (DirichletCharacter.LFunction chiFour) s -
    (sign : ℂ) * DirichletCharacter.LFunction chiFour s *
      (squarePrimePowerContinuation s + L higherExponentPrimePowerCoeff s)

lemma clearedAdjustedPrimeDerivative_eq_zero_of_one_lt_re {sign C : ℝ}
    (hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n) {s : ℂ} (hs : 1 < s.re) :
    clearedAdjustedPrimeDerivative sign C s = 0 := by
  rw [clearedAdjustedPrimeDerivative,
    deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation hpos hs]
  rw [twistedPrimeLogContinuation, chiFourNegLogDerivative, logDeriv_apply]
  have hL : DirichletCharacter.LFunction chiFour s ≠ 0 :=
    chiFour_LFunction_ne_zero_of_one_le_re hs.le
  field_simp [hL]
  ring

lemma analyticAt_clearedAdjustedPrimeDerivative {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) {s : ℂ}
    (hs : max (mellinAbscissa sign C) (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ (clearedAdjustedPrimeDerivative sign C) s := by
  have hsAbscissa : mellinAbscissa sign C < s.re :=
    (le_max_left _ _).trans_lt hs
  have hsHalf : (1 / 2 : ℝ) < s.re := (le_max_right _ _).trans_lt hs
  have hM := analyticAt_adjustedPrimeMellin hone hsAbscissa
  have hA : AnalyticAt ℂ (adjustedPrimeDirichlet sign C) s := by
    unfold adjustedPrimeDirichlet
    exact analyticAt_id.mul hM
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) s :=
    differentiable_chiFour_LFunction.analyticAt s
  have hsquare := squarePrimePowerContinuation_analyticAt_of_half_lt_re hsHalf
  have hhigher : AnalyticAt ℂ (L higherExponentPrimePowerCoeff) s :=
    higherExponentPrimePowerCoeff_LSeries_analyticOnNhd s (by
      norm_num at hsHalf ⊢
      linarith)
  unfold clearedAdjustedPrimeDerivative
  exact (hL.mul hA.deriv).sub (analyticAt_const.mul hL.deriv) |>.sub
    ((analyticAt_const.mul hL).mul (hsquare.add hhigher))

lemma clearedAdjustedPrimeDerivative_eq_zero {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) {s : ℂ}
    (hs : max (mellinAbscissa sign C) (1 / 2 : ℝ) < s.re) :
    clearedAdjustedPrimeDerivative sign C s = 0 := by
  let U : Set ℂ := {z | max (mellinAbscissa sign C) (1 / 2 : ℝ) < z.re}
  have hAnalytic : AnalyticOnNhd ℂ (clearedAdjustedPrimeDerivative sign C) U :=
    fun z hz => analyticAt_clearedAdjustedPrimeDerivative hone hz
  have hzero : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) U := analyticOnNhd_const
  have hpre : IsPreconnected U :=
    (convex_halfSpace_re_gt
      (r := max (mellinAbscissa sign C) (1 / 2 : ℝ))).isPreconnected
  have htwoU : (2 : ℂ) ∈ U := by
    change max (mellinAbscissa sign C) (1 / 2 : ℝ) < 2
    rw [max_lt_iff]
    exact ⟨(mellinAbscissa_le_one hone).trans_lt (by norm_num), by norm_num⟩
  have hrightOpen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const continuous_re
  have htwoRight : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hevent : clearedAdjustedPrimeDerivative sign C =ᶠ[𝓝 (2 : ℂ)]
      (fun _ => (0 : ℂ)) :=
    eventually_of_mem (hrightOpen.mem_nhds htwoRight) fun z hz => by
      have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n :=
        fun n => (hone n).trans' zero_le_one
      exact clearedAdjustedPrimeDerivative_eq_zero_of_one_lt_re hpos hz
  exact hAnalytic.eqOn_of_preconnected_of_eventuallyEq hzero hpre htwoU hevent hs

lemma deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_ne_zero
    {sign C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) {s : ℂ}
    (hs : max (mellinAbscissa sign C) (1 / 2 : ℝ) < s.re)
    (hL : DirichletCharacter.LFunction chiFour s ≠ 0) :
    deriv (adjustedPrimeDirichlet sign C) s =
      -(sign : ℂ) * twistedPrimeLogContinuation s := by
  have hzero := clearedAdjustedPrimeDerivative_eq_zero hone hs
  rw [clearedAdjustedPrimeDerivative] at hzero
  rw [twistedPrimeLogContinuation, chiFourNegLogDerivative, logDeriv_apply]
  field_simp [hL]
  linear_combination hzero

lemma deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_real
    {sign C t : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n)
    (ht : max (mellinAbscissa sign C) (1 / 2 : ℝ) < t) :
    deriv (adjustedPrimeDirichlet sign C) (t : ℂ) =
      -(sign : ℂ) * twistedPrimeLogContinuation (t : ℂ) := by
  have hL : DirichletCharacter.LFunction chiFour (t : ℂ) ≠ 0 :=
    Submission.Central.chiFour_LFunction_real_ne_zero (by
      have hab := mellinAbscissa_nonneg hone
      have := (le_max_left (mellinAbscissa sign C) (1 / 2 : ℝ)).trans_lt ht
      linarith)
  exact deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_ne_zero
    hone (by simpa using ht) hL

lemma half_le_mellinAbscissa {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) (hsign : sign ≠ 0) :
    (1 / 2 : ℝ) ≤ mellinAbscissa sign C := by
  by_contra hhalf
  have hbeta : mellinAbscissa sign C < (1 / 2 : ℝ) := lt_of_not_ge hhalf
  have hM : AnalyticAt ℂ (adjustedPrimeMellin sign C) (1 / 2 : ℂ) :=
    analyticAt_adjustedPrimeMellin hone (by simpa using hbeta)
  have hA : AnalyticAt ℂ (adjustedPrimeDirichlet sign C) (1 / 2 : ℂ) := by
    unfold adjustedPrimeDirichlet
    exact analyticAt_id.mul hM
  have hcoeNhds : Filter.Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    convert continuous_ofReal.continuousAt.tendsto.mono_left
      (show 𝓝[>] (1 / 2 : ℝ) ≤ 𝓝 (1 / 2 : ℝ) from nhdsWithin_le_nhds) using 1
    · norm_num
  have hcoeNE : Filter.Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcoeNhds ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    change (1 / 2 : ℝ) < t at ht
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    exact (ne_of_gt ht) hre
  have hsub : Filter.Tendsto (fun t : ℝ => (t : ℂ) - 1 / 2)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    simpa using hcoeNhds.sub_const (1 / 2 : ℂ)
  have hderiv : Filter.Tendsto
      (fun t : ℝ => deriv (adjustedPrimeDirichlet sign C) (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (deriv (adjustedPrimeDirichlet sign C) (1 / 2 : ℂ))) :=
    hA.deriv.continuousAt.tendsto.comp hcoeNhds
  have hleft : Filter.Tendsto
      (fun t : ℝ => ((t : ℂ) - 1 / 2) *
        deriv (adjustedPrimeDirichlet sign C) (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    simpa using hsub.mul hderiv
  have hcentral := tendsto_twistedPrimeLogContinuation_central.comp hcoeNE
  rw [Submission.Central.chiFourCentralMultiplicity_eq_zero] at hcentral
  have hright : Filter.Tendsto
      (fun t : ℝ => -(sign : ℂ) *
        (((t : ℂ) - 1 / 2) * twistedPrimeLogContinuation (t : ℂ)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 ((sign : ℂ) / 2)) := by
    have h := (tendsto_const_nhds (x := -(sign : ℂ))).mul hcentral
    simpa [div_eq_mul_inv] using h
  have hevent :
      (fun t : ℝ => ((t : ℂ) - 1 / 2) *
        deriv (adjustedPrimeDirichlet sign C) (t : ℂ)) =ᶠ[𝓝[>] (1 / 2 : ℝ)]
      fun t : ℝ => -(sign : ℂ) *
        (((t : ℂ) - 1 / 2) * twistedPrimeLogContinuation (t : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmax : max (mellinAbscissa sign C) (1 / 2 : ℝ) < t := by
      rw [max_eq_right hbeta.le]
      exact ht
    rw [deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_real hone hmax]
    ring
  have hleft' : Filter.Tendsto
      (fun t : ℝ => ((t : ℂ) - 1 / 2) *
        deriv (adjustedPrimeDirichlet sign C) (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 ((sign : ℂ) / 2)) :=
    (tendsto_congr' hevent).2 hright
  have heq : (0 : ℂ) = (sign : ℂ) / 2 := tendsto_nhds_unique hleft hleft'
  have hsignC : (sign : ℂ) = 0 := by
    calc
      (sign : ℂ) = ((sign : ℂ) / 2) * 2 := by ring
      _ = 0 := by rw [← heq]; ring
  exact hsign (by exact_mod_cast hsignC)

lemma analyticAt_twistedPrimeLogContinuation_of_real {t : ℝ}
    (ht : (1 / 2 : ℝ) < t) :
    AnalyticAt ℂ twistedPrimeLogContinuation (t : ℂ) := by
  have hLAnalytic : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) (t : ℂ) :=
    differentiable_chiFour_LFunction.analyticAt _
  have hLne : DirichletCharacter.LFunction chiFour (t : ℂ) ≠ 0 :=
    Submission.Central.chiFour_LFunction_real_ne_zero (by linarith)
  have hlog : AnalyticAt ℂ chiFourNegLogDerivative (t : ℂ) := by
    change AnalyticAt ℂ
      (fun s => -(deriv (DirichletCharacter.LFunction chiFour) s /
        DirichletCharacter.LFunction chiFour s)) (t : ℂ)
    exact (hLAnalytic.deriv.div hLAnalytic hLne).neg
  have hsquare : AnalyticAt ℂ squarePrimePowerContinuation (t : ℂ) :=
    squarePrimePowerContinuation_analyticAt_of_half_lt_re (by simpa using ht)
  have hhigher : AnalyticAt ℂ (L higherExponentPrimePowerCoeff) (t : ℂ) :=
    higherExponentPrimePowerCoeff_LSeries_analyticOnNhd _ (by
      change (2 / 5 : ℝ) < t
      linarith)
  unfold twistedPrimeLogContinuation
  exact hlog.sub hsquare |>.sub hhigher

private theorem no_analyticContinuationAt_mellinAbscissa_aux {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball (mellinAbscissa sign C) r))
    (heq : Set.EqOn f (adjustedPrimeMellin sign C)
      (Metric.ball (mellinAbscissa sign C) r ∩
        {s : ℂ | mellinAbscissa sign C < s.re})) :
    False := by
  let g : ℂ → ℂ := fun z => f (3 - z)
  have hdist (z : ℂ) :
      dist (3 - z) (mellinAbscissa sign C : ℂ) =
        dist z (mellinMGFEndpoint sign C : ℂ) := by
    rw [show (mellinAbscissa sign C : ℂ) = 3 - mellinMGFEndpoint sign C by
      simp [mellinAbscissa]]
    rw [Complex.dist_eq, Complex.dist_eq,
      show (3 - z) - (3 - (mellinMGFEndpoint sign C : ℂ)) =
        -(z - mellinMGFEndpoint sign C) by ring, norm_neg]
  have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n := fun n => (hone n).trans' zero_le_one
  apply Submission.MGFLandau.no_analyticContinuationAt_sSup_integrableExpSet
    Real.measurable_log.aemeasurable (ae_log_nonneg_mellinMeasure sign C)
    (integrableExpSet_mellinMeasure_nonempty hpos)
    (integrableExpSet_mellinMeasure_bddAbove hone) rfl hr (f := g)
  · intro z hz
    have hsBall : (3 - z : ℂ) ∈ Metric.ball (mellinAbscissa sign C : ℂ) r := by
      rw [Metric.mem_ball, hdist]
      exact hz
    have hfAt := hf.differentiableAt (Metric.isOpen_ball.mem_nhds hsBall)
    exact ((hfAt.comp z (by fun_prop)).differentiableWithinAt :
      DifferentiableWithinAt ℂ g (Metric.ball (mellinMGFEndpoint sign C) r) z)
  · intro z hz
    dsimp [g]
    have hsBall : (3 - z : ℂ) ∈ Metric.ball (mellinAbscissa sign C : ℂ) r := by
      rw [Metric.mem_ball, hdist]
      exact hz.1
    have hzRe := hz.2
    change z.re < mellinMGFEndpoint sign C at hzRe
    have hsRe : mellinAbscissa sign C < (3 - z).re := by
      simpa [mellinAbscissa] using (sub_lt_sub_left hzRe (3 : ℝ))
    rw [heq ⟨hsBall, hsRe⟩]
    unfold adjustedPrimeMellin
    congr 1
    ring

lemma mellinAbscissa_le_half {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) :
    mellinAbscissa sign C ≤ (1 / 2 : ℝ) := by
  by_contra hhalf
  have hbeta : (1 / 2 : ℝ) < mellinAbscissa sign C := lt_of_not_ge hhalf
  let beta : ℝ := mellinAbscissa sign C
  have hFbeta : AnalyticAt ℂ twistedPrimeLogContinuation (beta : ℂ) :=
    analyticAt_twistedPrimeLogContinuation_of_real (by simpa [beta] using hbeta)
  have hLbetaAnalytic : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) (beta : ℂ) :=
    differentiable_chiFour_LFunction.analyticAt _
  have hLbeta : DirichletCharacter.LFunction chiFour (beta : ℂ) ≠ 0 :=
    Submission.Central.chiFour_LFunction_real_ne_zero (by
      dsimp [beta]
      linarith)
  have hbeta0 : (beta : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (show (0 : ℝ) < beta by dsimp [beta]; linarith)
  have hLneEvent : ∀ᶠ z in 𝓝 (beta : ℂ),
      DirichletCharacter.LFunction chiFour z ≠ 0 :=
    hLbetaAnalytic.continuousAt.preimage_mem_nhds
      (compl_singleton_mem_nhds_iff.mpr hLbeta)
  have hEvent : ∀ᶠ z in 𝓝 (beta : ℂ),
      AnalyticAt ℂ twistedPrimeLogContinuation z ∧
        DirichletCharacter.LFunction chiFour z ≠ 0 ∧ z ≠ 0 := by
    filter_upwards [hFbeta.eventually_analyticAt, hLneEvent,
      eventually_ne_nhds hbeta0] with z hF hL hz
    exact ⟨hF, hL, hz⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hEvent
  let D : ℂ → ℂ := fun z => -(sign : ℂ) * twistedPrimeLogContinuation z
  have hDdiff : DifferentiableOn ℂ D (Metric.ball (beta : ℂ) r) := by
    intro z hz
    exact ((hball z hz).1.differentiableAt.const_mul (-(sign : ℂ))).differentiableWithinAt
  let c : ℂ := beta + r / 2
  have hcBall : c ∈ Metric.ball (beta : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    dsimp [c]
    rw [show (beta : ℂ) + r / 2 - beta = (r / 2 : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hcRe : beta < c.re := by
    dsimp [c]
    simp
    linarith
  obtain ⟨P, hPc, hPderiv⟩ :=
    hDdiff.isExactOn_ball.with_val_at c (adjustedPrimeDirichlet sign C c)
  let U : Set ℂ := Metric.ball (beta : ℂ) r ∩ {z : ℂ | beta < z.re}
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hUpre : IsPreconnected U :=
    ((convex_ball (beta : ℂ) r).inter (convex_halfSpace_re_gt (r := beta))).isPreconnected
  have hcU : c ∈ U := ⟨hcBall, hcRe⟩
  have hPdiff : DifferentiableOn ℂ P U := by
    intro z hz
    exact (hPderiv z hz.1).differentiableAt.differentiableWithinAt
  have hAdiff : DifferentiableOn ℂ (adjustedPrimeDirichlet sign C) U := by
    intro z hz
    have hzAbscissa : mellinAbscissa sign C < z.re := by simpa [beta] using hz.2
    have hM := analyticAt_adjustedPrimeMellin hone hzAbscissa
    exact (analyticAt_id.mul hM).differentiableAt.differentiableWithinAt
  have hderivEq : U.EqOn (deriv P) (deriv (adjustedPrimeDirichlet sign C)) := by
    intro z hz
    rw [(hPderiv z hz.1).deriv]
    dsimp [D]
    symm
    apply deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_ne_zero hone
    · rw [max_eq_left hbeta.le]
      simpa [beta] using hz.2
    · exact (hball z hz.1).2.1
  have hPA : U.EqOn P (adjustedPrimeDirichlet sign C) :=
    hUopen.eqOn_of_deriv_eq hUpre hPdiff hAdiff hderivEq hcU hPc
  let f : ℂ → ℂ := fun z => P z / z
  have hfdiff : DifferentiableOn ℂ f (Metric.ball (beta : ℂ) r) := by
    intro z hz
    exact ((hPderiv z hz).differentiableAt.div (by fun_prop) (hball z hz).2.2).differentiableWithinAt
  have hfeq : Set.EqOn f (adjustedPrimeMellin sign C) U := by
    intro z hz
    dsimp [f]
    rw [hPA hz]
    unfold adjustedPrimeDirichlet
    field_simp [(hball z hz.1).2.2]
  exact no_analyticContinuationAt_mellinAbscissa_aux hone hr
    (by simpa [beta] using hfdiff) (by simpa [beta, U] using hfeq)

lemma mellinAbscissa_eq_half {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n) (hsign : sign ≠ 0) :
    mellinAbscissa sign C = (1 / 2 : ℝ) :=
  le_antisymm (mellinAbscissa_le_half hone) (half_le_mellinAbscissa hone hsign)

lemma adjustedPrimeDirichlet_re_nonneg {sign C t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (adjustedPrimeDirichlet sign C (t : ℂ)).re := by
  rw [adjustedPrimeDirichlet, adjustedPrimeMellin]
  have hreal : (3 : ℂ) - (t : ℂ) = ((3 - t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hreal, ProbabilityTheory.complexMGF_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  exact mul_nonneg ht ProbabilityTheory.mgf_nonneg

lemma tendsto_scaled_deriv_adjustedPrimeDirichlet_one_central {C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum 1 C n) :
    Filter.Tendsto
      (fun t : ℝ => (t - 1 / 2) *
        (deriv (adjustedPrimeDirichlet 1 C) (t : ℂ)).re)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hbeta : mellinAbscissa 1 C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone one_ne_zero
  have hcoeNhds : Filter.Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    convert continuous_ofReal.continuousAt.tendsto.mono_left
      (show 𝓝[>] (1 / 2 : ℝ) ≤ 𝓝 (1 / 2 : ℝ) from nhdsWithin_le_nhds) using 1
    norm_num
  have hcoeNE : Filter.Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcoeNhds ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    change (1 / 2 : ℝ) < t at ht
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    exact (ne_of_gt ht) hre
  have hcentral := tendsto_twistedPrimeLogContinuation_central.comp hcoeNE
  rw [Submission.Central.chiFourCentralMultiplicity_eq_zero] at hcentral
  have hright : Filter.Tendsto
      (fun t : ℝ => -(1 : ℂ) *
        (((t : ℂ) - 1 / 2) * twistedPrimeLogContinuation (t : ℂ)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    have h := (tendsto_const_nhds (x := -(1 : ℂ))).mul hcentral
    simpa [div_eq_mul_inv] using h
  have hevent :
      (fun t : ℝ => ((t : ℂ) - 1 / 2) *
        deriv (adjustedPrimeDirichlet 1 C) (t : ℂ)) =ᶠ[𝓝[>] (1 / 2 : ℝ)]
      fun t : ℝ => -(1 : ℂ) *
        (((t : ℂ) - 1 / 2) * twistedPrimeLogContinuation (t : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmax : max (mellinAbscissa 1 C) (1 / 2 : ℝ) < t := by
      rw [hbeta, max_self]
      exact ht
    rw [deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_real
      hone hmax]
    norm_num
  have hcomplex : Filter.Tendsto
      (fun t : ℝ => ((t : ℂ) - 1 / 2) *
        deriv (adjustedPrimeDirichlet 1 C) (t : ℂ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℂ)) :=
    (tendsto_congr' hevent).2 hright
  have hre := continuous_re.continuousAt.tendsto.comp hcomplex
  change Filter.Tendsto
    (fun t : ℝ => (((t : ℂ) - 1 / 2) *
      deriv (adjustedPrimeDirichlet 1 C) (t : ℂ)).re)
    (𝓝[>] (1 / 2 : ℝ)) (𝓝 ((1 / 2 : ℂ).re)) at hre
  norm_num at hre
  exact hre

lemma not_global_positive_adjustedPrimeSum_one (C : ℝ) :
    ¬ ∀ n, 1 ≤ adjustedPrimeSum 1 C n := by
  intro hone
  have hbeta : mellinAbscissa 1 C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone one_ne_zero
  let a : ℝ → ℝ := fun t => (adjustedPrimeDirichlet 1 C (t : ℂ)).re
  let g : ℝ → ℝ := a ∘ fun y => 1 / 2 + Real.exp y
  let q : ℝ → ℝ := g - fun y => y / 4
  have hparam : Filter.Tendsto (fun y : ℝ => 1 / 2 + Real.exp y)
      atBot (𝓝[>] (1 / 2 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_const_nhds.add Real.tendsto_exp_atBot)
    · filter_upwards with y
      show (1 / 2 : ℝ) < 1 / 2 + Real.exp y
      linarith [Real.exp_pos y]
  have hscaled :=
    (tendsto_scaled_deriv_adjustedPrimeDirichlet_one_central hone).comp hparam
  have hslopeEventually : ∀ᶠ y : ℝ in atBot,
      (1 / 4 : ℝ) < Real.exp y *
        (deriv (adjustedPrimeDirichlet 1 C)
          ((1 / 2 + Real.exp y : ℝ) : ℂ)).re := by
    simpa only [Function.comp_apply, add_sub_cancel_left] using
    hscaled.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨Y, hY⟩ := eventually_atBot.mp hslopeEventually
  have hqHasDeriv (y : ℝ) : HasDerivAt q
      (Real.exp y * (deriv (adjustedPrimeDirichlet 1 C)
        ((1 / 2 + Real.exp y : ℝ) : ℂ)).re - 1 / 4) y := by
    have ht : (1 / 2 : ℝ) < 1 / 2 + Real.exp y := by
      linarith [Real.exp_pos y]
    have hM : AnalyticAt ℂ (adjustedPrimeMellin 1 C)
        ((1 / 2 + Real.exp y : ℝ) : ℂ) :=
      analyticAt_adjustedPrimeMellin hone (by
        change mellinAbscissa 1 C < 1 / 2 + Real.exp y
        rw [hbeta]
        exact ht)
    have hA : AnalyticAt ℂ (adjustedPrimeDirichlet 1 C)
        ((1 / 2 + Real.exp y : ℝ) : ℂ) := by
      unfold adjustedPrimeDirichlet
      exact analyticAt_id.mul hM
    have ha : HasDerivAt a
        (deriv (adjustedPrimeDirichlet 1 C)
          ((1 / 2 + Real.exp y : ℝ) : ℂ)).re
        (1 / 2 + Real.exp y) := by
      simpa [a] using hA.differentiableAt.hasDerivAt.real_of_complex
    have htparam := (Real.hasDerivAt_exp y).const_add (1 / 2 : ℝ)
    have hg := ha.comp y htparam
    have hq := hg.sub ((hasDerivAt_id y).div_const 4)
    change HasDerivAt q
      ((deriv (adjustedPrimeDirichlet 1 C)
        ((1 / 2 + Real.exp y : ℝ) : ℂ)).re * Real.exp y - 1 / 4) y at hq
    simpa only [mul_comm] using hq
  have hqMono : MonotoneOn q (Iic Y) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic Y)
    · intro y _hy
      exact (hqHasDeriv y).continuousAt.continuousWithinAt
    · intro y _hy
      exact (hqHasDeriv y).hasDerivWithinAt
    · intro y hy
      have hyYlt : y < Y := by
        rw [interior_Iic] at hy
        exact hy
      have hyY : y ≤ Y := hyYlt.le
      exact sub_nonneg.mpr (le_of_lt (hY y hyY))
  have hgNonneg (y : ℝ) : 0 ≤ g y := by
    dsimp [g, a, Function.comp_def]
    apply adjustedPrimeDirichlet_re_nonneg
    positivity
  let x : ℝ := Y - 4 * (g Y + 1)
  have hxY : x ≤ Y := by
    dsimp [x]
    nlinarith [hgNonneg Y]
  have hqxy : q x ≤ q Y := hqMono hxY (by simp) hxY
  have hgx := hgNonneg x
  dsimp [q, x] at hqxy
  linarith

theorem no_analyticContinuationAt_mellinMGFEndpoint {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball (mellinMGFEndpoint sign C) r))
    (heq : Set.EqOn f (ProbabilityTheory.complexMGF Real.log (mellinMeasure sign C))
      (Metric.ball (mellinMGFEndpoint sign C) r ∩
        {z : ℂ | z.re < mellinMGFEndpoint sign C})) :
    False := by
  have hpos : ∀ n, 0 ≤ adjustedPrimeSum sign C n := fun n => (hone n).trans' zero_le_one
  exact Submission.MGFLandau.no_analyticContinuationAt_sSup_integrableExpSet
    Real.measurable_log.aemeasurable (ae_log_nonneg_mellinMeasure sign C)
    (integrableExpSet_mellinMeasure_nonempty hpos)
    (integrableExpSet_mellinMeasure_bddAbove hone) rfl hr hf heq

theorem no_analyticContinuationAt_mellinAbscissa {sign C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum sign C n)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball (mellinAbscissa sign C) r))
    (heq : Set.EqOn f (adjustedPrimeMellin sign C)
      (Metric.ball (mellinAbscissa sign C) r ∩
        {s : ℂ | mellinAbscissa sign C < s.re})) :
    False :=
  no_analyticContinuationAt_mellinAbscissa_aux hone hr hf heq



end Submission.SignChange
