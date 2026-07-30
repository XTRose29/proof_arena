import Mathlib
import Submission.Helpers

open scoped Real

namespace Submission

lemma pell_gcd_one (d x y : ℤ) (hsol : x ^ 2 - d * y ^ 2 = 1) : x.gcd y = 1 := by
  have h_coprime : IsCoprime x y := by
    refine ⟨x, -d * y, ?_⟩
    nlinarith
  rcases h_coprime with ⟨a, b, h⟩
  have h_dvd : (x.gcd y : ℤ) ∣ (1 : ℤ) := by
    have hx : (x.gcd y : ℤ) ∣ x := Int.gcd_dvd_left _ _
    have hy : (x.gcd y : ℤ) ∣ y := Int.gcd_dvd_right _ _
    have h_comb : (x.gcd y : ℤ) ∣ a * x + b * y := dvd_add (hx.mul_left a) (hy.mul_left b)
    rw [h] at h_comb
    exact h_comb
  have hpos : x.gcd y > 0 := by
    by_cases hx0 : x = 0
    · have hy0 : y ≠ 0 := by
        intro hy0'
        have : x ^ 2 - d * y ^ 2 = 0 := by simp [hx0, hy0']
        nlinarith
      have h_abs_pos : 0 < |y| := abs_pos.mpr hy0
      have h_natAbs_pos : y.natAbs > 0 := by simpa using h_abs_pos
      exact Nat.gcd_pos_of_pos_right x.natAbs h_natAbs_pos
    · have h_abs_pos : 0 < |x| := abs_pos.mpr hx0
      have h_natAbs_pos : x.natAbs > 0 := by simpa using h_abs_pos
      exact Nat.gcd_pos_of_pos_left y.natAbs h_natAbs_pos
  apply Nat.eq_one_of_dvd_one
  exact_mod_cast h_dvd

lemma pell_approx_bound (d x y : ℤ) (hd0 : 0 < d) (hx : 0 < x) (hy : 0 < y) (hsol : x ^ 2 - d * y ^ 2 = 1) :
    |(x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ)| < 1 / (2 * ((y : ℝ) ^ 2)) := by
  have hypos : (y : ℝ) > 0 := by exact_mod_cast hy
  have hy_ne : (y : ℝ) ≠ 0 := by linarith
  have hsol' : (x : ℝ)^2 - (d : ℝ) * (y : ℝ)^2 = 1 := by exact_mod_cast hsol
  have hsqrt_sq : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd0.le)
  have hd0_real : (1 : ℝ) ≤ (d : ℝ) := by
    have : (1 : ℤ) ≤ d := by omega
    exact_mod_cast this
  have hx_gt_y : (x : ℝ) > (y : ℝ) := by
    have hxpos : (x : ℝ) > 0 := by exact_mod_cast hx
    have hsq : (x : ℝ)^2 > (y : ℝ)^2 := by
      nlinarith
    have h_factor : (x : ℝ) - (y : ℝ) > 0 := by
      by_contra! H
      have h_nonpos : (x : ℝ) - (y : ℝ) ≤ 0 := H
      have h_nonneg_sum : (x : ℝ) + (y : ℝ) > 0 := by nlinarith
      have : (x : ℝ)^2 - (y : ℝ)^2 ≤ 0 := by nlinarith
      nlinarith
    nlinarith
  have h_div_gt_one : (x : ℝ) / (y : ℝ) > 1 := (one_lt_div hypos).mpr hx_gt_y
  have hsqrt_ge_one : Real.sqrt (d : ℝ) ≥ 1 := by
    refine calc
      Real.sqrt (d : ℝ) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hd0)
      _ = 1 := by norm_num
  have h_sum_gt_two : (x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ) > 2 := by
    linarith
  have h_sq_diff : ((x : ℝ) / (y : ℝ)) ^ 2 - (d : ℝ) = 1 / ((y : ℝ) ^ 2) := by
    field_simp [hy_ne]
    nlinarith
  have h_prod : ((x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ)) * ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) = 1 / ((y : ℝ) ^ 2) := by
    nlinarith
  have h_sum_pos : 0 < (x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ) := by
    linarith
  have h_diff_formula : (x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ) = 1 / (((y : ℝ) ^ 2) * ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ))) := by
    field_simp [hy_ne, show (x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ) ≠ 0 from by linarith]
    nlinarith
  rw [h_diff_formula]
  have h_denom_pos : 0 < ((y : ℝ) ^ 2) * ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) := by
    positivity
  have h_expr_pos : 0 < 1 / (((y : ℝ) ^ 2) * ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ))) :=
    div_pos (by norm_num) h_denom_pos
  rw [abs_of_pos h_expr_pos]
  have h_denom_gt : ((y : ℝ)^2) * ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) > 2 * (y : ℝ)^2 := by
    calc
      ((y : ℝ)^2) * ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) > ((y : ℝ)^2) * 2 :=
        mul_lt_mul_of_pos_left h_sum_gt_two (by positivity)
      _ = 2 * (y : ℝ)^2 := by ring
  have h_two_y_sq_pos : 0 < 2 * (y : ℝ) ^ 2 := by positivity
  apply (one_div_lt_one_div h_denom_pos h_two_y_sq_pos).mpr
  exact h_denom_gt

theorem pell_solution_is_convergent (d : ℤ) (_hd : Squarefree d) (_hd0 : 0 < d)
    (x y : ℤ) (_hx : 0 < x) (_hy : 0 < y)
    (_hsol : x ^ 2 - d * y ^ 2 = 1) :
    ∃ n : ℕ, (GenContFract.of (Real.sqrt (d : ℝ))).convs n = (x : ℝ) / (y : ℝ) := by
  have hgcd : x.gcd y = 1 := pell_gcd_one d x y _hsol
  have h_coprime : Nat.Coprime x.natAbs y.natAbs := by
    have h_gcd_nat : (x.natAbs).gcd (y.natAbs) = 1 := by
      simpa using hgcd
    exact (Nat.coprime_iff_gcd_eq_one.mpr h_gcd_nat)
  have hypos_int : (0 : ℤ) < y := _hy
  have hy_nonneg : (0 : ℤ) ≤ y := by omega
  have h_den_eq : ((x : ℚ) / (y : ℚ)).den = y.natAbs := by
    have h_temp := Rat.den_div_eq_of_coprime hypos_int h_coprime
    have h_y_natAbs_eq : (y.natAbs : ℤ) = y := by
      simp [hy_nonneg]
    have h_eq_int : (((x : ℚ) / (y : ℚ)).den : ℤ) = (y.natAbs : ℤ) := by
      calc
        (((x : ℚ) / (y : ℚ)).den : ℤ) = y := h_temp
        _ = (y.natAbs : ℤ) := by rw [h_y_natAbs_eq]
    exact_mod_cast h_eq_int
  set q := (x : ℚ) / (y : ℚ) with hq_def
  have h_q_real : (q : ℝ) = (x : ℝ) / (y : ℝ) := by
    simp [hq_def]
  have h_abs_bound : |Real.sqrt (d : ℝ) - (q : ℝ)| < 1 / (2 * ((q.den : ℝ) ^ 2)) := by
    rw [h_q_real]
    have h_bound := pell_approx_bound d x y _hd0 _hx _hy _hsol
    have h_den_eq_real : (q.den : ℝ) = (y : ℝ) := by
      calc
        (q.den : ℝ) = (y.natAbs : ℝ) := by exact_mod_cast h_den_eq
        _ = (y : ℝ) := by simp [hy_nonneg]
    rw [h_den_eq_real]
    rw [abs_sub_comm]
    exact h_bound
  have h_result := Real.exists_convs_eq_rat (ξ := Real.sqrt (d : ℝ)) (q := q) h_abs_bound
  rcases h_result with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [h_q_real] at hn
  exact hn

end Submission