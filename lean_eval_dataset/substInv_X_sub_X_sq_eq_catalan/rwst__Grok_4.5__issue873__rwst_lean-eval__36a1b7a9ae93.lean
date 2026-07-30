import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  -- Instance for `substInv` lemmas (the one in the type is only for elaboration)
  haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]; exact invertibleOne
  -- Catalan ogf over ℚ: C = 1 + X C²
  set C : ℚ⟦X⟧ := map (Nat.castRingHom ℚ) catalanSeries
  have hC : C = 1 + X * C ^ 2 := by
    have h := congr_arg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
    simp only [map_add, map_mul, map_pow, map_X, map_one] at h
    calc
      C = C ^ 2 * X + 1 := h.symm
      _ = 1 + X * C ^ 2 := by rw [mul_comm (C ^ 2), add_comm]
  set Q : ℚ⟦X⟧ := X * C
  have hQ : HasSubst Q := HasSubst.of_constantCoeff_zero' (by simp [Q])
  have hP0 : constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = 0 := by simp
  have hPhs : HasSubst ((X : ℚ⟦X⟧) - X ^ 2) := HasSubst.of_constantCoeff_zero' hP0
  -- (X - X²)(Q) = Q - Q² = X
  have hPQ : subst Q ((X : ℚ⟦X⟧) - X ^ 2) = X := by
    rw [subst_sub hQ, subst_X hQ, subst_pow hQ, subst_X hQ]
    have hCQ : C - X * C ^ 2 = 1 := sub_eq_iff_eq_add.mpr hC
    calc
      Q - Q ^ 2 = X * C - X ^ 2 * C ^ 2 := by simp only [Q]; ring
      _ = X * (C - X * C ^ 2) := by ring
      _ = X := by rw [hCQ, mul_one]
  -- Uniqueness of compositional inverse
  have huniq : substInv ((X : ℚ⟦X⟧) - X ^ 2) = Q := by
    calc
      substInv (X - X ^ 2) = subst X (substInv (X - X ^ 2)) :=
        (X_subst _).symm
      _ = subst (subst Q (X - X ^ 2)) (substInv (X - X ^ 2)) := by rw [hPQ]
      _ = subst Q (subst (X - X ^ 2) (substInv (X - X ^ 2))) :=
        (subst_comp_subst_apply hPhs hQ _).symm
      _ = subst Q X := by rw [subst_substInv_left _ hP0]
      _ = Q := subst_X hQ
  -- Coefficients of Q are Catalan numbers
  have hcoeff : coeff (n + 1) Q = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
    simp only [Q, coeff_succ_X_mul]
    have hc : coeff n C = (catalan n : ℚ) := by
      simp [C, coeff_map, catalanSeries_coeff]
    rw [hc, eq_div_iff (by exact_mod_cast n.succ_ne_zero)]
    have hcat := congr_arg (Nat.cast (R := ℚ)) (succ_mul_catalan_eq_centralBinom n)
    push_cast at hcat
    rw [mul_comm, hcat, Nat.centralBinom]
  -- Identify the goal's `substInv` (other Invertible instance) with Q
  convert hcoeff
  refine (congrArg (fun i : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) =>
    @substInv ℚ _ (X - X ^ 2) i) (Subsingleton.elim _ _)).trans huniq

end Submission
