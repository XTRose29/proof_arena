import Mathlib

open NumberField Polynomial Complex Real Finset

namespace Submission.Analysis

/-- Key analytic lemma: if z is real with |z| ≤ 2, roots of t²-zt+1=0 have norm 1 -/
lemma norm_root_eq_one {z : ℂ} (hz_im : z.im = 0) (hz_norm : ‖z‖ ≤ 2) {w : ℂ}
    (hw : w ^ 2 - z * w + 1 = 0) (hw0 : w ≠ 0) : ‖w‖ = 1 := by
  have hz_real : z = z.re := by simpa [Complex.ext_iff, hz_im]
  rw [hz_real] at hw; norm_num [Complex.ext_iff, sq] at *
  by_cases h : w.im = 0 <;> simp_all +decide [Complex.normSq, Complex.norm_def]
  · rw [Real.sqrt_le_left] at hz_norm <;> nlinarith [sq_nonneg (w.re - z.re / 2)]
  · grind

/-- For all k coprime to d (d ≥ 3, odd), |cos(2πk/d)| ≤ cos(π/d) -/
lemma abs_cos_le_cos_pi_div_of_odd {d : ℕ} (hd : 3 ≤ d) (hd_odd : d % 2 = 1)
    {k : ℤ} (hk : Int.gcd k d = 1) :
    |Real.cos (2 * Real.pi * k / d)| ≤ Real.cos (Real.pi / d) := by
  have h_coprime : Int.gcd (2 * k) d = 1 := by
    simp_all +decide [Int.gcd_eq_natAbs, Int.natAbs_mul]
    exact Nat.Coprime.mul_left (Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by
      have := Nat.mod_eq_zero_of_dvd h; aesop) hk
  obtain ⟨m, hm⟩ : ∃ m : ℤ, |(2 * k : ℝ) - m * d| ≤ d / 2 ∧ 1 ≤ |(2 * k : ℝ) - m * d| := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, |(2 * k : ℝ) - m * d| ≤ d / 2 := by
      use Int.floor ((2 * k : ℝ) / d + 1 / 2)
      rw [abs_le]; constructor <;>
        nlinarith [Int.floor_le ((2 * k : ℝ) / d + 1 / 2),
          Int.lt_floor_add_one ((2 * k : ℝ) / d + 1 / 2),
          show (d : ℝ) ≥ 3 by norm_cast,
          mul_div_cancel₀ (2 * k : ℝ) (by positivity : (d : ℝ) ≠ 0)]
    refine ⟨m, hm, ?_⟩
    contrapose! hm; norm_cast at *; simp_all +decide [Int.gcd_eq_right]
    exact absurd (h_coprime ▸ Int.dvd_coe_gcd
      (show (d : ℤ) ∣ 2 * k from ⟨m, by linarith⟩) (dvd_refl _))
      (by norm_cast; aesop)
  have h_cos_eq : |Real.cos (2 * Real.pi * k / d)| =
      |Real.cos (Real.pi * |(2 * k : ℝ) - m * d| / d)| := by
    cases abs_cases (2 * k - m * d : ℝ) <;> simp +decide [*] <;> ring_nf at * <;>
      norm_num at *
    · norm_num [show d ≠ 0 by positivity, mul_assoc, mul_comm Real.pi _, Real.cos_sub]
    · norm_num [show d ≠ 0 by positivity, mul_assoc, mul_comm Real.pi _, Real.cos_add]
  rw [h_cos_eq, abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)]
  · refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_ <;>
      nlinarith [Real.pi_pos, show (d : ℝ) ≥ 3 by norm_cast,
        mul_div_cancel₀ (Real.pi * |(2 * k : ℝ) - m * d|) (by positivity : (d : ℝ) ≠ 0),
        mul_div_cancel₀ Real.pi (by positivity : (d : ℝ) ≠ 0)]
  · exact le_trans (by linarith [Real.pi_pos])
      (div_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg _)) (Nat.cast_nonneg _))
  · rw [div_le_iff₀] <;> nlinarith [Real.pi_pos, show (d : ℝ) ≥ 3 by norm_cast]

/-- For all k coprime to d (d ≥ 4, even), |cos(2πk/d)| ≤ cos(2π/d) -/
lemma abs_cos_le_cos_two_pi_div_of_even {d : ℕ} (hd : 4 ≤ d) (hd_even : d % 2 = 0)
    {k : ℤ} (hk : Int.gcd k d = 1) :
    |Real.cos (2 * Real.pi * k / d)| ≤ Real.cos (2 * Real.pi / d) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, |(2 * k : ℝ) - m * d| ≤ d / 2 ∧ |(2 * k : ℝ) - m * d| ≥ 2 := by
    refine ⟨⌊(2 * k : ℝ) / d + 1 / 2⌋, ?_, ?_⟩ <;> norm_num [abs_le]
    · constructor <;>
        nlinarith [Int.floor_le ((2 * k : ℝ) / d + 1 / 2),
          Int.lt_floor_add_one ((2 * k : ℝ) / d + 1 / 2),
          show (d : ℝ) ≥ 4 by norm_cast,
          mul_div_cancel₀ (2 * k : ℝ) (by positivity : (d : ℝ) ≠ 0)]
    · have h_even : (2 * k - ⌊(2 * k : ℝ) / d + 1 / 2⌋ * d) % 2 = 0 := by
        norm_num [Int.sub_emod, Int.mul_emod, show (d : ℤ) % 2 = 0 from mod_cast hd_even]
      have h_nonzero : (2 * k - ⌊(2 * k : ℝ) / d + 1 / 2⌋ * d) ≠ 0 := by
        by_contra h_contra
        have h_div : (d : ℤ) ∣ 2 * k := ⟨⌊(2 * k : ℝ) / d + 1 / 2⌋, by linarith⟩
        have h_gcd : (d : ℤ) ∣ 2 :=
          Int.dvd_of_dvd_mul_left_of_gcd_one h_div (by simpa [Int.gcd_comm] using hk)
        have : d ≤ 2 := Nat.le_of_dvd (by decide) (Int.natCast_dvd_natCast.mp h_gcd)
        linarith [hd]
      norm_cast at *; grind
  have h_cos_dist : |Real.cos (2 * Real.pi * k / d)| =
      Real.cos (Real.pi * |(2 * k : ℝ) - m * d| / d) := by
    have h_cos_dist' : |Real.cos (2 * Real.pi * k / d)| =
        |Real.cos (Real.pi * |(2 * k : ℝ) - m * d| / d)| := by
      cases abs_cases (2 * k - m * d : ℝ) <;> simp +decide [*] <;> ring_nf <;>
        norm_num [show d ≠ 0 by positivity]
      · norm_num [mul_comm Real.pi, Real.cos_sub]
      · norm_num [mul_comm Real.pi, Real.cos_add]
    rw [h_cos_dist', abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, show (d : ℝ) ≥ 4 by norm_cast, abs_nonneg (2 * k - m * d : ℝ)],
    by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, show (d : ℝ) ≥ 4 by norm_cast,
        abs_nonneg (2 * k - m * d : ℝ)]⟩)]
  rw [h_cos_dist]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_ <;>
    nlinarith [Real.pi_pos, show (d : ℝ) ≥ 4 by norm_cast,
      mul_div_cancel₀ (2 * Real.pi) (by positivity : (d : ℝ) ≠ 0),
      mul_div_cancel₀ (Real.pi * |(2 * (k : ℝ)) - m * d|) (by positivity : (d : ℝ) ≠ 0)]

end Submission.Analysis
