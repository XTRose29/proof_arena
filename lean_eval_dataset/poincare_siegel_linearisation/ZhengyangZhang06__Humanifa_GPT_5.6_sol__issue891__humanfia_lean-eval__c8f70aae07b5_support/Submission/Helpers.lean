import ChallengeDeps

open LeanEval.ComplexAnalysis

namespace Submission.Helpers

theorem irrational_of_isDiophantine {α : ℝ} (hα : IsDiophantine α) :
    Irrational α := by
  rw [irrational_iff_ne_rational]
  rintro p q hq hαpq
  obtain ⟨C, τ, hC, hbound⟩ := hα
  have hq_real : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq
  have hdenom : 0 < |(q : ℝ)| ^ τ :=
    Real.rpow_pos_of_pos (abs_pos.mpr hq_real) _
  have hpositive : 0 < C / |(q : ℝ)| ^ τ := div_pos hC hdenom
  have hle := hbound p q hq
  rw [hαpq, sub_self, abs_zero] at hle
  exact (not_le_of_gt hpositive) hle

theorem pow_ne_one_of_isDiophantine {α : ℝ} (hα : IsDiophantine α)
    {lam : ℂ}
    (hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))
    {n : ℕ} (hn : n ≠ 0) :
    lam ^ n ≠ 1 := by
  intro hpow
  rw [hlam, ← Complex.exp_nat_mul] at hpow
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hpow
  have hperiod : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    Complex.two_pi_I_ne_zero
  have hna_complex : (n : ℂ) * (α : ℂ) = (k : ℂ) := by
    apply mul_right_cancel₀ hperiod
    calc
      ((n : ℂ) * (α : ℂ)) * (2 * Real.pi * Complex.I) =
          (n : ℂ) * (2 * Real.pi * Complex.I * (α : ℂ)) := by ring
      _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
  have hna_real : (n : ℝ) * α = (k : ℝ) := by
    exact_mod_cast congrArg Complex.re hna_complex
  have hn_real : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  have hα_rat : α = (k : ℝ) / (n : ℝ) := by
    apply (eq_div_iff hn_real).2
    nlinarith
  exact (irrational_of_isDiophantine hα).ne_rational k (n : ℤ) (by simpa using hα_rat)

theorem pow_ne_self_of_isDiophantine {α : ℝ} (hα : IsDiophantine α)
    {lam : ℂ}
    (hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))
    {n : ℕ} (hn : 2 ≤ n) :
    lam ^ n ≠ lam := by
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact Complex.exp_ne_zero _
  intro hpow
  apply pow_ne_one_of_isDiophantine hα hlam (n := n - 1) (by omega)
  apply mul_right_cancel₀ hlam0
  calc
    lam ^ (n - 1) * lam = lam ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    _ = lam := hpow
    _ = 1 * lam := (one_mul lam).symm

/-- The Diophantine inequality gives a polynomial lower bound for all
small divisors of the associated rotation. -/
theorem exists_norm_pow_sub_one_lower_bound
    {α : ℝ} (hα : IsDiophantine α)
    {lam : ℂ}
    (hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))) :
    ∃ c τ : ℝ, 0 < c ∧ ∀ n : ℕ, n ≠ 0 →
      c / (n : ℝ) ^ τ ≤ ‖lam ^ n - 1‖ := by
  obtain ⟨C, τ, hC, hbound⟩ := hα
  refine ⟨4 * C, τ, by positivity, ?_⟩
  intro n hn
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hn_real : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  let k : ℤ := round ((n : ℝ) * α)
  let t : ℝ := (n : ℝ) * α - (k : ℝ)
  have happrox :
      C / (n : ℝ) ^ τ ≤ |α - (k : ℝ) / (n : ℝ)| := by
    simpa [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
      hbound k (n : ℤ) (by exact_mod_cast hn)
  have ht_formula :
      t = (n : ℝ) * (α - (k : ℝ) / (n : ℝ)) := by
    dsimp [t]
    field_simp
  have habs_formula :
      |t| = (n : ℝ) * |α - (k : ℝ) / (n : ℝ)| := by
    rw [ht_formula, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have hdist : C / (n : ℝ) ^ τ ≤ |t| := by
    rw [habs_formula]
    calc
      C / (n : ℝ) ^ τ
          ≤ 1 * |α - (k : ℝ) / (n : ℝ)| := by simpa using happrox
      _ ≤ (n : ℝ) * |α - (k : ℝ) / (n : ℝ)| := by
        gcongr
        exact_mod_cast hn_pos
  have ht_half : |t| ≤ 1 / 2 := by
    simpa [t, k] using abs_sub_round ((n : ℝ) * α)
  have hpi_t : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left ht_half Real.pi_pos.le]
  have hsin : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have hjordan := Real.mul_abs_le_abs_sin hpi_t
    calc
      2 * |t| = 2 / Real.pi * |Real.pi * t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * t)| := hjordan
  have hlam_pow :
      lam ^ n = Complex.exp (Complex.I * (2 * Real.pi * t : ℝ)) := by
    calc
      lam ^ n =
          Complex.exp ((n : ℕ) *
            (2 * Real.pi * Complex.I * (α : ℂ))) := by
              rw [hlam, Complex.exp_nat_mul]
      _ = Complex.exp
          (Complex.I * (2 * Real.pi * t : ℝ) +
            (k : ℂ) * (2 * Real.pi * Complex.I)) := by
              congr 1
              dsimp [t]
              push_cast
              ring_nf
      _ = Complex.exp (Complex.I * (2 * Real.pi * t : ℝ)) := by
        rw [Complex.exp_add,
          (Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩), mul_one]
  have hnorm :
      ‖lam ^ n - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    rw [hlam_pow, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring_nf
  rw [hnorm]
  calc
    4 * C / (n : ℝ) ^ τ = 4 * (C / (n : ℝ) ^ τ) := by ring
    _ ≤ 4 * |t| := mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ ≤ 2 * |Real.sin (Real.pi * t)| := by nlinarith [hsin]

/-- A version of the small-divisor estimate with a positive natural
exponent. This is convenient for dyadic counting arguments. -/
theorem exists_norm_pow_sub_one_lower_bound_nat
    {α : ℝ} (hα : IsDiophantine α)
    {lam : ℂ}
    (hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))) :
    ∃ c : ℝ, ∃ T : ℕ, 0 < c ∧ T ≠ 0 ∧ ∀ n : ℕ, n ≠ 0 →
      c / (n : ℝ) ^ T ≤ ‖lam ^ n - 1‖ := by
  obtain ⟨c, τ, hc, hbound⟩ :=
    exists_norm_pow_sub_one_lower_bound hα hlam
  let T : ℕ := ⌈max τ 0⌉₊ + 1
  refine ⟨c, T, hc, by simp [T], ?_⟩
  intro n hn
  have hn_one : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hτT : τ ≤ (T : ℝ) := by
    calc
      τ ≤ max τ 0 := le_max_left _ _
      _ ≤ (⌈max τ 0⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ (T : ℝ) := by
        dsimp [T]
        norm_num
  have hpow : (n : ℝ) ^ τ ≤ (n : ℝ) ^ T := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn_one hτT
  calc
    c / (n : ℝ) ^ T ≤ c / (n : ℝ) ^ τ :=
      div_le_div_of_nonneg_left hc.le
        (Real.rpow_pos_of_pos (by positivity) _) hpow
    _ ≤ ‖lam ^ n - 1‖ := hbound n hn

end Submission.Helpers
