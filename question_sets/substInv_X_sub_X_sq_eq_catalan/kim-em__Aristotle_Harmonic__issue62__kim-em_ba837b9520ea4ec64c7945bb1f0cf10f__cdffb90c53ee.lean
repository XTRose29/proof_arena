import Mathlib

open PowerSeries

namespace Submission

private noncomputable def C_rat : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

private lemma C_rat_eq : C_rat ^ 2 * X + 1 = C_rat := by
  have := congr_arg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, map_X] at this
  exact this

private lemma C_rat_coeff (n : ℕ) : coeff n C_rat = (catalan n : ℚ) := by
  simp [C_rat, coeff_map, catalanSeries_coeff]

private lemma hasSubst_X_mul_C_rat : HasSubst (X * C_rat : ℚ⟦X⟧) := by
  simp [HasSubst, ← constantCoeff.eq_def, map_mul, C_rat]

private lemma subst_X_sub_X_sq_eq :
    ((X : ℚ⟦X⟧) - X ^ 2).subst (X * C_rat) = X := by
  rw [subst_sub hasSubst_X_mul_C_rat, subst_X hasSubst_X_mul_C_rat,
      subst_pow hasSubst_X_mul_C_rat, subst_X hasSubst_X_mul_C_rat]
  have key : C_rat - X * C_rat ^ 2 = 1 := by linear_combination -C_rat_eq
  calc X * C_rat - (X * C_rat) ^ 2
      = X * (C_rat - X * C_rat ^ 2) := by ring
    _ = X * 1 := by rw [key]
    _ = X := mul_one X

private noncomputable instance : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
  simp [coeff_X, coeff_X_pow]; exact invertibleOne

private lemma substInv_eq : substInv ((X : ℚ⟦X⟧) - X ^ 2) = X * C_rat := by
  have P_const : constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = 0 := by
    simp [map_sub, map_pow]
  have hP : HasSubst ((X : ℚ⟦X⟧) - X ^ 2) := by
    simp [HasSubst, ← constantCoeff.eq_def, map_sub, map_pow]
  have hg : HasSubst (X * C_rat : ℚ⟦X⟧) := hasSubst_X_mul_C_rat
  have h1 := subst_substInv_left ((X : ℚ⟦X⟧) - X ^ 2) P_const
  have h2 := subst_comp_subst_apply hP hg (substInv ((X : ℚ⟦X⟧) - X ^ 2))
  rw [h1, subst_X hg, subst_X_sub_X_sq_eq, X_subst] at h2
  exact h2.symm

private lemma catalan_eq_choose_div (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom] at h
  have hn : (↑n + 1 : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff hn]
  have : (↑(catalan n) : ℚ) * (↑n + 1) = ↑((n + 1) * catalan n) := by push_cast; ring
  rw [this, h]

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  rw [substInv_eq, coeff_succ_X_mul, C_rat_coeff, catalan_eq_choose_div]

end Submission
