import Mathlib

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  letI hInv : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]
    exact invertibleOne
  change
    coeff (n + 1) (@substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) hInv) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1)
  have hQ :
      @substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) hInv =
        (PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries) * X := by
    let P : ℚ⟦X⟧ := (X : ℚ⟦X⟧) - X ^ 2
    let Q : ℚ⟦X⟧ := @substInv ℚ _ P hInv
    let C : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries
    let Y : ℚ⟦X⟧ := C * X
    have hYS : HasSubst Y := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      simp [Y]
    have hP0 : constantCoeff P = 0 := by simp [P]
    have hPS : HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero' hP0
    have hPY : PowerSeries.subst Y P = X := by
      have hY : Y - Y ^ 2 = X := by
        subst Y
        have hC : C ^ 2 * X + 1 = C := by
          subst C
          simpa using
            congrArg (PowerSeries.map (Nat.castRingHom ℚ))
              PowerSeries.catalanSeries_sq_mul_X_add_one
        calc
          C * X - (C * X) ^ 2 = (C ^ 2 * X + 1) * X - (C * X) ^ 2 := by rw [hC]
          _ = X := by ring
      subst P
      rw [PowerSeries.subst_sub hYS, PowerSeries.subst_pow hYS]
      simpa [PowerSeries.subst_X hYS] using hY
    have hQsubP : PowerSeries.subst P Q = X := by
      subst Q
      exact PowerSeries.subst_substInv_left P hP0
    have hcomp := PowerSeries.subst_comp_subst_apply (ha := hPS) (hb := hYS) Q
    calc
      Q = PowerSeries.subst X Q := by rw [PowerSeries.X_subst]
      _ = PowerSeries.subst (PowerSeries.subst Y P) Q := by rw [hPY]
      _ = PowerSeries.subst Y (PowerSeries.subst P Q) := by rw [← hcomp]
      _ = PowerSeries.subst Y X := by rw [hQsubP]
      _ = Y := by rw [PowerSeries.subst_X hYS]
      _ = (PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries) * X := rfl
  rw [hQ, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_map,
    PowerSeries.catalanSeries_coeff]
  have hcat : (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
    have hmul : ((n + 1 : ℕ) * catalan n : ℚ) = (Nat.centralBinom n : ℚ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom n
    have hden : (n : ℚ) + 1 ≠ 0 := by positivity
    rw [Nat.centralBinom_eq_two_mul_choose] at hmul
    field_simp [hden]
    simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hcat

end Submission
