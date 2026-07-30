import Mathlib
import Submission.Helpers

open scoped Real

namespace Submission

theorem pell_solution_is_convergent (d : ℤ) (_hd : Squarefree d) (_hd0 : 0 < d)
    (x y : ℤ) (_hx : 0 < x) (_hy : 0 < y)
    (_hsol : x ^ 2 - d * y ^ 2 = 1) :
    ∃ n : ℕ, (GenContFract.of (Real.sqrt (d : ℝ))).convs n = (x : ℝ) / (y : ℝ) := by
  have hd1 : 1 ≤ d := by omega
  have hcoprime : Nat.Coprime x.natAbs y.natAbs := by
    rw [← Int.isCoprime_iff_nat_coprime]
    exact ⟨x, -d * y, by nlinarith [_hsol]⟩
  let q : ℚ := (x : ℚ) / (y : ℚ)
  have hdenR : (q.den : ℝ) = (y : ℝ) := by
    dsimp [q]
    exact_mod_cast Rat.den_div_eq_of_coprime _hy hcoprime

  have hysq_lt_xsq : y ^ 2 < x ^ 2 := by
    have hdy : y ^ 2 ≤ d * y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg y)]
    nlinarith [_hsol]
  have hxy : y < x :=
    (sq_lt_sq₀ _hy.le _hx.le).mp hysq_lt_xsq

  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast _hd0.le
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast _hy
  have hsqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt hdR
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  have hratio_one : (1 : ℝ) < (x : ℝ) / (y : ℝ) :=
    (one_lt_div hyR).2 (by exact_mod_cast hxy)
  have hratio_nonneg : (0 : ℝ) ≤ (x : ℝ) / (y : ℝ) :=
    zero_le_one.trans hratio_one.le
  have hy_sq_pos : (0 : ℝ) < (y : ℝ) ^ 2 :=
    sq_pos_of_pos hyR
  have hsolR : (x : ℝ) ^ 2 - (d : ℝ) * (y : ℝ) ^ 2 = 1 := by
    exact_mod_cast _hsol
  have hsqrt_lt_ratio : Real.sqrt (d : ℝ) < (x : ℝ) / (y : ℝ) := by
    apply (sq_lt_sq₀ hsqrt_nonneg hratio_nonneg).mp
    rw [hsqrt_sq, div_pow, lt_div_iff₀ hy_sq_pos]
    nlinarith [hsolR]
  have hsum : 2 < Real.sqrt (d : ℝ) + (x : ℝ) / (y : ℝ) := by
    linarith
  have hsum_pos : 0 < Real.sqrt (d : ℝ) + (x : ℝ) / (y : ℝ) :=
    zero_lt_two.trans hsum
  have hdiff :
      (x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ) =
        1 / ((y : ℝ) ^ 2 *
          (Real.sqrt (d : ℝ) + (x : ℝ) / (y : ℝ))) := by
    field_simp [hyR.ne', hsum_pos.ne']
    nlinarith [hsolR, hsqrt_sq]
  have hdenom :
      2 * (y : ℝ) ^ 2 <
        (y : ℝ) ^ 2 * (Real.sqrt (d : ℝ) + (x : ℝ) / (y : ℝ)) := by
    calc
      2 * (y : ℝ) ^ 2 = (y : ℝ) ^ 2 * 2 := by ring
      _ < (y : ℝ) ^ 2 * (Real.sqrt (d : ℝ) + (x : ℝ) / (y : ℝ)) :=
        mul_lt_mul_of_pos_left hsum hy_sq_pos
  have happrox :
      |Real.sqrt (d : ℝ) - (x : ℝ) / (y : ℝ)| <
        1 / (2 * (y : ℝ) ^ 2) := by
    rw [abs_of_neg (sub_neg.mpr hsqrt_lt_ratio), neg_sub, hdiff]
    exact one_div_lt_one_div_of_lt (mul_pos zero_lt_two hy_sq_pos) hdenom
  have hlegendre :
      |Real.sqrt (d : ℝ) - (q : ℝ)| <
        1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hdenR]
    simpa [q] using happrox
  obtain ⟨n, hn⟩ :=
    Real.exists_convs_eq_rat (ξ := Real.sqrt (d : ℝ)) (q := q) hlegendre
  refine ⟨n, ?_⟩
  simpa [q] using hn

end Submission
