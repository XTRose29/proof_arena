import Mathlib
import Submission.Helpers

open scoped Real

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem pell_solution_is_convergent (d : ℤ) (_hd : Squarefree d) (_hd0 : 0 < d)
    (x y : ℤ) (_hx : 0 < x) (_hy : 0 < y)
    (_hsol : x ^ 2 - d * y ^ 2 = 1) :
    ∃ n : ℕ, (GenContFract.of (Real.sqrt (d : ℝ))).convs n = (x : ℝ) / (y : ℝ) := by
  -- Work in the reals first.  We will use Legendre's criterion for
  -- continued fractions, applied to the rational number `x/y`.
  have hyR : 0 < (y : ℝ) := by exact_mod_cast _hy
  have hxR : 0 < (x : ℝ) := by exact_mod_cast _hx
  have hdR : 0 < (d : ℝ) := by exact_mod_cast _hd0
  have hy_ne : (y : ℝ) ≠ 0 := ne_of_gt hyR
  have hsolR : (x : ℝ) ^ 2 - (d : ℝ) * (y : ℝ) ^ 2 = 1 := by
    exact_mod_cast _hsol
  -- The elementary identity coming from the Pell equation.
  have hsq : ((x : ℝ) / (y : ℝ)) ^ 2 - (d : ℝ) = 1 / (y : ℝ) ^ 2 := by
    field_simp [hy_ne]
    nlinarith [hsolR]
  have hratio_pos : 0 < (x : ℝ) / (y : ℝ) := div_pos hxR hyR
  have hsqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (le_of_lt hdR)
  have hsquares_lt : (Real.sqrt (d : ℝ)) ^ 2 < ((x : ℝ) / (y : ℝ)) ^ 2 := by
    rw [hsqrt_sq]
    have hpos : 0 < 1 / (y : ℝ) ^ 2 := by positivity
    linarith [hsq]
  have hsqrt_lt : Real.sqrt (d : ℝ) < (x : ℝ) / (y : ℝ) := by
    have hnon : 0 ≤ (x : ℝ) / (y : ℝ) := le_of_lt hratio_pos
    exact (sq_lt_sq₀ hsqrt_nonneg hnon).1 hsquares_lt
  -- Since d is a positive integer, sqrt d is at least one.  This is the
  -- harmless extra factor of two in Legendre's estimate.
  have hd_one_int : (1 : ℤ) ≤ d := by omega
  have hd_one_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_one_int
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    (Real.one_le_sqrt).2 hd_one_real
  have hsum_gt : (2 : ℝ) < (x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ) := by
    linarith
  have hsum_pos : 0 < (x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ) := by
    linarith
  -- Isolate the small difference from the difference of two squares.
  have hdiff_mul :
      ((x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ)) *
          ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) = 1 / (y : ℝ) ^ 2 := by
    calc
      ((x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ)) *
          ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) =
          ((x : ℝ) / (y : ℝ)) ^ 2 - (Real.sqrt (d : ℝ)) ^ 2 := by ring
      _ = ((x : ℝ) / (y : ℝ)) ^ 2 - (d : ℝ) := by rw [hsqrt_sq]
      _ = 1 / (y : ℝ) ^ 2 := hsq
  have hdiff :
      (x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ) =
        (1 / (y : ℝ) ^ 2) / ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) := by
    apply (eq_div_iff (ne_of_gt hsum_pos)).2
    exact hdiff_mul
  have hsmall0 :
      (x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ) < 1 / (2 * (y : ℝ) ^ 2) := by
    rw [hdiff]
    have hA : 0 < (1 / (y : ℝ) ^ 2 : ℝ) := by positivity
    have hlt :
        (1 / (y : ℝ) ^ 2) / ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ)) <
          (1 / (y : ℝ) ^ 2) / (2:ℝ) :=
      div_lt_div_of_pos_left hA (by norm_num) hsum_gt
    calc
      (1 / (y : ℝ) ^ 2) / ((x : ℝ) / (y : ℝ) + Real.sqrt (d : ℝ))
          < (1 / (y : ℝ) ^ 2) / (2:ℝ) := hlt
      _ = 1 / (2 * (y : ℝ) ^ 2) := by ring
  have habs_small :
      |Real.sqrt (d : ℝ) - (x : ℝ) / (y : ℝ)| < 1 / (2 * (y : ℝ) ^ 2) := by
    rw [abs_of_neg (sub_neg.mpr hsqrt_lt)]
    have hneg : -(Real.sqrt (d : ℝ) - (x : ℝ) / (y : ℝ)) =
        (x : ℝ) / (y : ℝ) - Real.sqrt (d : ℝ) := by ring
    rw [hneg]
    exact hsmall0
  let q : ℚ := (x : ℚ) / (y : ℚ)
  have hqcast : (q : ℝ) = (x : ℝ) / (y : ℝ) := by
    dsimp [q]
    norm_cast
  -- The reduced denominator of this rational divides `y`, so replacing
  -- `y` by that denominator can only make the permitted error bigger.
  have hden_dvd : (q.den : ℤ) ∣ y := by
    dsimp [q]
    simpa [Rat.intCast_div_eq_divInt] using (Rat.den_dvd x y)
  have hden_le_int : (q.den : ℤ) ≤ y :=
    Int.le_of_dvd _hy hden_dvd
  have hden_le : (q.den : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hden_le_int
  have hden_pos : (0 : ℝ) < (q.den : ℝ) := by
    exact_mod_cast (Rat.den_pos q)
  have hbound_le :
      1 / (2 * (y : ℝ) ^ 2) ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by
    have hsqp : (q.den : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by
      exact (sq_le_sq₀ (le_of_lt hden_pos) (le_of_lt hyR)).2 hden_le
    have hmul : (2:ℝ) * (q.den : ℝ) ^ 2 ≤ (2:ℝ) * (y : ℝ) ^ 2 := by
      nlinarith
    have hpos : 0 < (2:ℝ) * (q.den : ℝ) ^ 2 := by positivity
    exact one_div_le_one_div_of_le hpos hmul
  have hleg : |Real.sqrt (d : ℝ) - (q : ℝ)| <
      1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hqcast]
    exact lt_of_lt_of_le habs_small hbound_le
  obtain ⟨n, hn⟩ := (Real.exists_convs_eq_rat (ξ := Real.sqrt (d : ℝ)) (q := q) hleg)
  refine ⟨n, ?_⟩
  simpa [hqcast] using hn


end Submission
