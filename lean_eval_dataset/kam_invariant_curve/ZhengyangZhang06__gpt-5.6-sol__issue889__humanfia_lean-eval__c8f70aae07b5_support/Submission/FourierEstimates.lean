import Submission.Estimates

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

def intTail (n : ℤ) : ℝ := 1 / (n : ℝ) ^ 2

theorem intTail_nonneg (n : ℤ) : 0 ≤ intTail n := by
  unfold intTail
  positivity

theorem summable_intTail : Summable intTail := by
  exact Real.summable_one_div_int_pow.mpr (by norm_num)

def intTailSum : ℝ := ∑' n : ℤ, intTail n

theorem intTailSum_nonneg : 0 ≤ intTailSum :=
  tsum_nonneg intTail_nonneg

theorem norm_fourierCoeffOn_le_of_bound {g : ℝ → ℝ} (B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ B) (n : ℤ) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun x => Complex.ofReal (g x)) n‖ ≤ B := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, inv_one, one_smul]
  calc
    _ ≤ B * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul,
          Complex.norm_real]
        exact hbound x)
    _ = B := by norm_num

theorem realFourierCoeff_decay_of_majorized {s : ℕ} {A R : ℝ}
    {g : ℝ → ℝ} (hg : Majorized s A R g)
    (hgs : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1)
    (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖Cohomological.realFourierCoeff g n‖ ≤
      (1 / |(n : ℝ)|) ^ m * (A * weight s m * R ^ m) := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habspos : 0 < |(n : ℝ)| := abs_pos.mpr hnreal
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiv : ‖Helpers.fourierDerivativeDivisor n‖ ≤ 1 / |(n : ℝ)| := by
    rw [Helpers.norm_fourierDerivativeDivisor]
    apply one_div_le_one_div_of_le habspos
    nlinarith
  have hpow : ‖Helpers.fourierDerivativeDivisor n‖ ^ m ≤
      (1 / |(n : ℝ)|) ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) hdiv m
  have hderiv (x : ℝ) : ‖iteratedDeriv m g x‖ ≤
      A * weight s m * R ^ m := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hg m x
  have hcoeff := norm_fourierCoeffOn_le_of_bound
    (A * weight s m * R ^ m) hderiv n
  rw [Cohomological.realFourierCoeff,
    Helpers.fourierCoeffOn_iteratedDeriv_iterate hgs hper m n hn,
    norm_mul, norm_pow]
  exact mul_le_mul hpow hcoeff (norm_nonneg _)
    (pow_nonneg (by positivity) m)

theorem weight_add_four (s k : ℕ) :
    weight s (k + 4) =
      2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k := by
  unfold weight
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

/-- A single constant, depending only on the Diophantine rotation, controls
the four-derivative loss of Fourier division for every majorized forcing. -/
theorem exists_solve_majorant_constant {α : ℝ} (hα : IsDiophantine α) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {s : ℕ} {A R : ℝ} {g : ℝ → ℝ},
        Majorized s A R g → ContDiff ℝ ∞ g → Function.Periodic g 1 →
        0 ≤ A → 0 ≤ R →
        Majorized s
          (D * A * 2 ^ (16 * s) * R ^ 4)
          ((2 * Real.pi) * 2 ^ (8 * s) * R)
          (Cohomological.solve α g) := by
  obtain ⟨C, hC, hsymbol'⟩ := Helpers.isDiophantine_cos_symbol_bound hα
  have hsymbol : ∀ n : ℤ, n ≠ 0 →
      (C / |(n : ℝ)|) ^ 2 ≤ |Cohomological.laplacianSymbol α n| := by
    simpa only [Cohomological.laplacianSymbol] using hsymbol'
  let D : ℝ := 1 + 2 / C ^ 2 * intTailSum
  have hD : 0 < D := by
    dsimp only [D]
    have := intTailSum_nonneg
    positivity
  refine ⟨D, hD, ?_⟩
  intro s A R g hg hgs hper hA hR k t
  let Q : ℝ := 2 * (2 * Real.pi) ^ k / C ^ 2 *
    (A * weight s (k + 4) * R ^ (k + 4))
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (by positivity) k))
        (sq_nonneg C))
      (mul_nonneg (mul_nonneg hA (weight_nonneg s (k + 4)))
        (pow_nonneg hR (k + 4)))
  have hmode (n : ℤ) : Cohomological.modeDerivBound α g k n ≤
      Q * intTail n := by
    by_cases hn : n = 0
    · subst n
      simp [Cohomological.modeDerivBound,
        Cohomological.inverseFourierCoeff, intTail]
    · have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have habspos : 0 < |(n : ℝ)| := abs_pos.mpr hnreal
      have hcoeff := realFourierCoeff_decay_of_majorized hg hgs hper
        (k + 4) n hn
      calc
        Cohomological.modeDerivBound α g k n ≤
            2 * |2 * Real.pi * (n : ℝ)| ^ k *
              ((|(n : ℝ)| / C) ^ 2 *
                ‖Cohomological.realFourierCoeff g n‖) :=
          mul_le_mul_of_nonneg_left
            (Cohomological.norm_inverseFourierCoeff_le
              g C hC hsymbol n hn)
            (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))
        _ ≤ 2 * |2 * Real.pi * (n : ℝ)| ^ k *
              ((|(n : ℝ)| / C) ^ 2 *
                ((1 / |(n : ℝ)|) ^ (k + 4) *
                  (A * weight s (k + 4) * R ^ (k + 4)))) := by
          gcongr
        _ = Q * intTail n := by
          simp only [intTail]
          rw [← sq_abs (n : ℝ)]
          simp only [Q, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_pos Real.pi_pos, mul_pow, one_div, inv_pow, pow_add]
          field_simp [hC.ne', abs_ne_zero.mpr hnreal]
  have hQsum : Summable (fun n : ℤ => Q * intTail n) :=
    summable_intTail.mul_left Q
  have heq := iteratedFDeriv_tsum
    (N := (⊤ : ℕ∞))
    (f := fun n : ℤ => Cohomological.mode
      (Cohomological.inverseFourierCoeff α g n) n)
    (v := fun j n => Cohomological.modeDerivBound α g j n)
    (fun n => Cohomological.mode_contDiff _ n)
    (fun j _ => Cohomological.summable_modeDerivBound hα hgs hper j)
    (fun j n x _ => Cohomological.norm_iteratedFDeriv_mode_le _ n j x)
    (show (k : ℕ∞) ≤ ⊤ from le_top)
  have heqAt := congrFun heq t
  change iteratedFDeriv ℝ k (Cohomological.solve α g) t =
      ∑' n : ℤ, iteratedFDeriv ℝ k
        (Cohomological.mode (Cohomological.inverseFourierCoeff α g n) n) t
    at heqAt
  rw [heqAt]
  have hterm (n : ℤ) :
      ‖iteratedFDeriv ℝ k
        (Cohomological.mode (Cohomological.inverseFourierCoeff α g n) n) t‖ ≤
        Q * intTail n :=
    (Cohomological.norm_iteratedFDeriv_mode_le _ n k t).trans (hmode n)
  have hnormsum : Summable (fun n : ℤ =>
      ‖iteratedFDeriv ℝ k
        (Cohomological.mode (Cohomological.inverseFourierCoeff α g n) n) t‖) :=
    hQsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc
    ‖∑' n : ℤ, iteratedFDeriv ℝ k
        (Cohomological.mode (Cohomological.inverseFourierCoeff α g n) n) t‖ ≤
      ∑' n : ℤ, ‖iteratedFDeriv ℝ k
        (Cohomological.mode (Cohomological.inverseFourierCoeff α g n) n) t‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℤ, Q * intTail n :=
      hnormsum.tsum_le_tsum hterm hQsum
    _ = Q * intTailSum := by rw [tsum_mul_left]; rfl
    _ ≤ D * A * 2 ^ (16 * s) * R ^ 4 * weight s k *
        ((2 * Real.pi) * 2 ^ (8 * s) * R) ^ k := by
      have hcoef : 2 / C ^ 2 * intTailSum ≤ D := by
        dsimp only [D]
        linarith
      rw [show Q * intTailSum =
          (2 / C ^ 2 * intTailSum) *
            (A * weight s (k + 4) * R ^ (k + 4)) *
            (2 * Real.pi) ^ k by
        dsimp only [Q]
        ring]
      rw [weight_add_four, pow_add]
      have hnon : 0 ≤
          (A * (2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k) *
            (R ^ k * R ^ 4)) * (2 * Real.pi) ^ k := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg hA
              (mul_nonneg
                (mul_nonneg (pow_nonneg (by positivity) (16 * s))
                  (pow_nonneg (by positivity) k))
                (weight_nonneg s k)))
            (mul_nonneg (pow_nonneg hR k) (pow_nonneg hR 4)))
          (pow_nonneg (by positivity) k)
      calc
        (2 / C ^ 2 * intTailSum) *
            (A * (2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k) *
              (R ^ k * R ^ 4)) * (2 * Real.pi) ^ k ≤
          D *
            ((A * (2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k) *
              (R ^ k * R ^ 4)) * (2 * Real.pi) ^ k) :=
          by
            calc
              (2 / C ^ 2 * intTailSum) *
                    (A * (2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k) *
                      (R ^ k * R ^ 4)) * (2 * Real.pi) ^ k =
                (2 / C ^ 2 * intTailSum) *
                  ((A * (2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k) *
                    (R ^ k * R ^ 4)) * (2 * Real.pi) ^ k) := by ring
              _ ≤ D *
                  ((A * (2 ^ (16 * s) * (2 ^ (8 * s)) ^ k * weight s k) *
                    (R ^ k * R ^ 4)) * (2 * Real.pi) ^ k) :=
                mul_le_mul_of_nonneg_right hcoef hnon
        _ = D * A * 2 ^ (16 * s) * R ^ 4 * weight s k *
            ((2 * Real.pi) * 2 ^ (8 * s) * R) ^ k := by
          rw [mul_pow]
          ring

end

end Submission.Majorant
