import Mathlib
import Submission.Helpers

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]
      exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  letI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) :=
    by simp [coeff_X, coeff_X_pow]; exact invertibleOne
  let Q := substInv ((X : ℚ⟦X⟧) - X ^ 2)
  have hP : constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, LinearMap.map_sub (coeff (0 : ℕ)) (X : ℚ⟦X⟧) (X ^ 2),
      coeff_zero_X, coeff_X_pow, if_neg (by decide : 0 ≠ 2)]
    simp
  have hQ : Q - Q ^ 2 = X := by
    rw [← subst_substInv_right ((X : ℚ⟦X⟧) - X ^ 2) hP,
      subst_sub (HasSubst.substInv ((X : ℚ⟦X⟧) - X ^ 2)) X (X ^ 2),
      subst_X (HasSubst.substInv ((X : ℚ⟦X⟧) - X ^ 2)),
      subst_pow (HasSubst.substInv ((X : ℚ⟦X⟧) - X ^ 2)) X 2,
      subst_X (HasSubst.substInv ((X : ℚ⟦X⟧) - X ^ 2))]
  have hQ0 : coeff 0 Q = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_substInv ((X : ℚ⟦X⟧) - X ^ 2)
  have hQ1 : coeff 1 Q = 1 := by
    have hQ' : Q = X + Q ^ 2 := by rw [← hQ]; ring
    rw [hQ', LinearMap.map_add (coeff 1) X (Q ^ 2), coeff_one_X, pow_two, coeff_mul 1 Q Q,
      Finset.Nat.antidiagonal_succ 0, Finset.sum_cons, Finset.sum_map, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton]
    rw [Function.Embedding.coe_prodMap, Prod.map, Function.Embedding.refl_apply]
    rw [hQ0]
    ring
  have hmain : coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) = (catalan n : ℚ) := by
    induction' n using Nat.strong_induction_on with n ih
    by_cases h : n = 0
    · subst h
      rw [hQ1, catalan_zero]
      rfl
    · have hpos : n ≥ 1 := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr h)
      have hn : n + 1 = (n - 1) + 2 := by omega
      have hQ' : Q = X + Q ^ 2 := by rw [← hQ]; ring
      show coeff (n + 1) Q = (catalan n : ℚ)
      rw [hQ', LinearMap.map_add (coeff (n + 1)) X (Q ^ 2), coeff_X,
        if_neg (by omega : n + 1 ≠ 1), zero_add, pow_two, coeff_mul (n + 1) Q Q,
        hn, @Finset.Nat.antidiagonal_succ_succ' (n - 1),
        Finset.sum_cons, Finset.sum_cons, hQ0, mul_zero, zero_mul, zero_add, zero_add]
      rw [Finset.sum_map]
      rw [← Nat.sub_add_cancel hpos]
      rw [catalan_succ' (n - 1)]
      push_cast
      rw [Finset.sum_congr rfl]
      intro p hp
      rw [Function.Embedding.coe_prodMap]
      simp only [Prod.map, Function.Embedding.coeFn_mk, Nat.succ_eq_add_one]
      rw [ih p.1 (Nat.lt_of_le_of_lt (Finset.antidiagonal.fst_le hp) (Nat.sub_one_lt h)),
        ih p.2 (Nat.lt_of_le_of_lt (Finset.antidiagonal.snd_le hp) (Nat.sub_one_lt h))]
  rw [hmain, catalan_eq_centralBinom_div n, Nat.cast_div_charZero (Nat.succ_dvd_centralBinom n),
    Nat.cast_succ, Nat.centralBinom_eq_two_mul_choose n]

end Submission
