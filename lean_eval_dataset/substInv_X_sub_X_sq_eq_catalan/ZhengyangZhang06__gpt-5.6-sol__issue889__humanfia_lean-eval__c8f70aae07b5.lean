import Mathlib
import Submission.Helpers

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  letI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]
    exact invertibleOne
  let Cq : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries
  let Q : ℚ⟦X⟧ := X * Cq
  have hCq : Cq ^ 2 * X + 1 = Cq := by
    simpa [Cq] using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      catalanSeries_sq_mul_X_add_one
  have hCq' : Cq - Cq ^ 2 * X = 1 := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm] using hCq.symm
  have hQ : Q - Q ^ 2 = X := by
    dsimp [Q]
    calc
      X * Cq - (X * Cq) ^ 2 = X * (Cq - Cq ^ 2 * X) := by ring
      _ = X := by rw [hCq']; ring
  have hP0 : constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = 0 := by
    simp
  have hPSubst : HasSubst ((X : ℚ⟦X⟧) - X ^ 2) :=
    HasSubst.of_constantCoeff_zero' hP0
  have hQSubst : HasSubst Q :=
    HasSubst.of_constantCoeff_zero' (by simp [Q])
  have hQ' : subst Q ((X : ℚ⟦X⟧) - X ^ 2) = X := by
    simpa only [subst_sub hQSubst, subst_X hQSubst, subst_pow hQSubst] using hQ
  have hQeq : Q = substInv ((X : ℚ⟦X⟧) - X ^ 2) := by
    calc
      Q = subst Q X := (subst_X hQSubst).symm
      _ = subst Q (subst ((X : ℚ⟦X⟧) - X ^ 2)
          (substInv ((X : ℚ⟦X⟧) - X ^ 2))) := by
        rw [subst_substInv_left _ hP0]
      _ = subst (subst Q ((X : ℚ⟦X⟧) - X ^ 2))
          (substInv ((X : ℚ⟦X⟧) - X ^ 2)) :=
        subst_comp_subst_apply hPSubst hQSubst _
      _ = subst X (substInv ((X : ℚ⟦X⟧) - X ^ 2)) := by rw [hQ']
      _ = substInv ((X : ℚ⟦X⟧) - X ^ 2) := X_subst _
  rw [← hQeq]
  simp only [Q, coeff_succ_X_mul]
  simp only [Cq, coeff_map, catalanSeries_coeff]
  change (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (↑n + 1)
  apply (eq_div_iff (by positivity : (n : ℚ) + 1 ≠ 0)).2
  have hCatalan := congrArg (fun k : ℕ ↦ (k : ℚ))
    (succ_mul_catalan_eq_centralBinom n)
  simpa [Nat.centralBinom, mul_comm] using hCatalan

end Submission
