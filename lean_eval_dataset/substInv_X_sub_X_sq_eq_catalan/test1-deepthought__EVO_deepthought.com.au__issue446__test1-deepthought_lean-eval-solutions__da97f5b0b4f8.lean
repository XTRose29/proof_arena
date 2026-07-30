import Mathlib
open PowerSeries

namespace Submission

set_option maxHeartbeats 400000

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  -- Make the Invertible instance available
  letI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]; exact invertibleOne
  -- Let S := substInv (X - X^2) over ℚ
  set S := substInv ((X : ℚ⟦X⟧) - X ^ 2) with hS
  -- Let C := catalanSeries over ℚ
  set C := catalanSeries.map (algebraMap ℕ ℚ) with hC
  -- HasSubst instance for S (since constantCoeff S = 0)
  have hS_has : HasSubst S := by
    dsimp [HasSubst, S]
    have h0 : constantCoeff (substInv ((X : ℚ⟦X⟧) - X ^ 2)) = 0 := constantCoeff_substInv _
    refine ⟨1, ?_⟩
    simpa [h0]
  -- Key identity 1: S - S^2 = X (from subst_substInv_right)
  have hS_eq : S - S ^ 2 = X := by
    have h := subst_substInv_right ((X : ℚ⟦X⟧) - X ^ 2) (by simp)
    have h_expand : subst S ((X : ℚ⟦X⟧) - X ^ 2) = S - S ^ 2 := by
      calc
        subst S ((X : ℚ⟦X⟧) - X ^ 2) = subst S (X : ℚ⟦X⟧) - subst S (X ^ 2 : ℚ⟦X⟧) := by
          rw [subst_sub hS_has]
        _ = S - subst S (X ^ 2 : ℚ⟦X⟧) := by rw [subst_X hS_has]
        _ = S - (subst S (X : ℚ⟦X⟧)) ^ 2 := by rw [subst_pow hS_has]
        _ = S - S ^ 2 := by rw [subst_X hS_has]
    calc
      S - S ^ 2 = subst S ((X : ℚ⟦X⟧) - X ^ 2) := by rw [h_expand]
      _ = X := h
  -- Key identity 2: C^2 * X + 1 = C (Catalan identity over ℚ)
  have hC_eq : C ^ 2 * X + 1 = C := by
    have h := catalanSeries_sq_mul_X_add_one
    have hmap := congrArg (fun s : ℕ⟦X⟧ => s.map (algebraMap ℕ ℚ)) h
    simpa [map_add, map_mul, map_pow, map_X, map_one, C] using hmap
  -- From this, C - X*C^2 = 1
  have hC_eq2 : C - X * C ^ 2 = 1 := by
    calc
      C - X * C ^ 2 = (C ^ 2 * X + 1) - X * C ^ 2 := by rw [hC_eq]
      _ = (C ^ 2 * X - X * C ^ 2) + 1 := by ring
      _ = 0 + 1 := by ring
      _ = 1 := by simp
  -- Then (X*C) - (X*C)^2 = X
  have hXC_eq : (X * C) - (X * C) ^ 2 = X := by
    calc
      (X * C) - (X * C) ^ 2 = X * C - X ^ 2 * C ^ 2 := by ring
      _ = X * (C - X * C ^ 2) := by ring
      _ = X * 1 := by rw [hC_eq2]
      _ = X := by simp
  -- Now we have S - S^2 = X and (X*C) - (X*C)^2 = X
  -- So (S - X*C) * (1 - (S + X*C)) = 0
  have h_factor : (S - X * C) * (1 - (S + X * C)) = 0 := by
    calc
      (S - X * C) * (1 - (S + X * C)) = (S - X * C) - (S - X * C) * (S + X * C) := by ring
      _ = (S - X * C) - (S ^ 2 - (X * C) ^ 2) := by ring
      _ = (S - S ^ 2) - ((X * C) - (X * C) ^ 2) := by ring
      _ = X - X := by rw [hS_eq, hXC_eq]
      _ = 0 := by ring
  -- Since constantCoeff (1 - (S + X*C)) = 1, it's a unit
  have h_unit : IsUnit (1 - (S + X * C)) := by
    apply ((PowerSeries.isUnit_iff_constantCoeff (R := ℚ)).mpr ?_)
    have h0_S : constantCoeff S = 0 := constantCoeff_substInv _
    have h0_XC : constantCoeff (X * C) = 0 := by simp
    simp [h0_S, h0_XC]
  -- Therefore S - X*C = 0, i.e., S = X*C
  have h_eq : S = X * C := by
    have hzero : (S - X * C) * (1 - (S + X * C)) = 0 := h_factor
    have hzero' : (0 : ℚ⟦X⟧) * (1 - (S + X * C)) = 0 := by simp
    have : S - X * C = 0 := h_unit.mul_right_cancel (by
      calc
        (S - X * C) * (1 - (S + X * C)) = 0 := hzero
        _ = (0 : ℚ⟦X⟧) * (1 - (S + X * C)) := by simp)
    calc
      S = (S - X * C) + X * C := by ring
      _ = 0 + X * C := by rw [this]
      _ = X * C := by simp
  -- Now compute the coefficient
  calc
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) = coeff (n + 1) S := rfl
    _ = coeff (n + 1) (X * C) := by rw [h_eq]
    _ = coeff n C := by
      simpa [mul_comm, add_comm] using coeff_mul_X_pow C 1 n
    _ = (catalan n : ℚ) := by
      simp [C, catalanSeries_coeff]
    _ = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
      have h_cat := catalan_eq_centralBinom_div n
      have h_div : (n + 1 : ℕ) ∣ n.centralBinom := Nat.succ_dvd_centralBinom n
      have h0 : (n : ℚ) + 1 ≠ 0 := by
        intro hzero
        have : (n : ℕ) + 1 = 0 := by exact_mod_cast hzero
        omega
      have h0' : (↑(n + 1) : ℚ) ≠ 0 := by
        have : (↑(n + 1) : ℚ) = (n : ℚ) + 1 := by simp
        rw [this]
        exact h0
      calc
        (catalan n : ℚ) = ((n.centralBinom / (n + 1) : ℕ) : ℚ) := by
          push_cast
          rw [h_cat]
        _ = (n.centralBinom : ℚ) / ((n + 1 : ℕ) : ℚ) := by
          rw [Nat.cast_div h_div h0']
        _ = (n.centralBinom : ℚ) / (↑n + 1) := by simp
        _ = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
          simp [Nat.centralBinom]

end Submission