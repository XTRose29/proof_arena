import Mathlib
import Submission.Helpers

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]; exact invertibleOne
  let Q := substInv ((X : ℚ⟦X⟧) - X ^ 2)
  have hF : ((X : ℚ⟦X⟧) - X ^ 2).constantCoeff = 0 := by simp
  have hQ_hsubst : HasSubst Q := HasSubst.substInv ((X : ℚ⟦X⟧) - X ^ 2)
  have hP_subst_Q_eq_X : ((X : ℚ⟦X⟧) - X ^ 2).subst Q = X :=
    subst_substInv_right ((X : ℚ⟦X⟧) - X ^ 2) hF
  have hQ_subst_P_eq_X : subst Q ((X : ℚ⟦X⟧) - X ^ 2) = X :=
    subst_substInv_right ((X : ℚ⟦X⟧) - X ^ 2) hF
  have hsubstQX : subst (Q : ℚ⟦X⟧) (X : ℚ⟦X⟧) = Q := by
    have := subst_X (R := ℚ) (S := ℚ) (τ := Unit) hQ_hsubst
    simpa using this
  have hsubstQX2 : subst (Q : ℚ⟦X⟧) ((X : ℚ⟦X⟧) ^ 2) = Q ^ 2 := by
    calc
      subst (Q : ℚ⟦X⟧) ((X : ℚ⟦X⟧) ^ 2) = (subst (Q : ℚ⟦X⟧) (X : ℚ⟦X⟧)) ^ 2 :=
        subst_pow (R := ℚ) (S := ℚ) (τ := Unit) hQ_hsubst (X : ℚ⟦X⟧) 2
      _ = Q ^ 2 := by rw [hsubstQX]
  have hQ_minus_sq_eq_X : Q - Q ^ 2 = X := by
    calc
      Q - Q ^ 2 = subst Q X - subst Q (X ^ 2) := by rw [hsubstQX, hsubstQX2]
      _ = subst Q (X - X ^ 2) := by rw [subst_sub hQ_hsubst]
      _ = X := hQ_subst_P_eq_X
  have hQ_eq_X_add_sq : Q = X + Q ^ 2 := by
    calc
      Q = (Q - Q ^ 2) + Q ^ 2 := by rw [sub_add_cancel]
      _ = X + Q ^ 2 := by rw [hQ_minus_sq_eq_X]
  have hcoeff0 : coeff 0 Q = 0 := by
    have h := constantCoeff_substInv ((X : ℚ⟦X⟧) - X ^ 2)
    simpa [Q] using h
  have hcoeff1 : coeff 1 Q = 1 := by
    calc
      coeff 1 Q = ⅟ (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := coeff_one_substInv ((X : ℚ⟦X⟧) - X ^ 2)
      _ = 1 := by simp [coeff_X, coeff_X_pow]
  have hcoeff_eq_catalan (k : ℕ) : coeff (k + 1) Q = (catalan k : ℚ) := by
    induction' k using Nat.strong_induction_on with n ih
    rcases n with (rfl | n)
    · simpa using hcoeff1
    · have hcoeff_X : coeff (n + 2) (X : ℚ⟦X⟧) = 0 := by
        simpa using coeff_X (R := ℚ) (n := n+2)
      rw [hQ_eq_X_add_sq, map_add (coeff (n+2)), hcoeff_X, zero_add, pow_two, coeff_mul]
      have hzero0 : coeff 0 Q = 0 := hcoeff0
      rw [Finset.Nat.antidiagonal_succ_succ' (n := n), Finset.sum_cons, Finset.sum_cons, Finset.sum_map]
      simp [hzero0]
      have hsum : ∑ p ∈ Finset.antidiagonal n, coeff (p.1 + 1) Q * coeff (p.2 + 1) Q =
        ∑ p ∈ Finset.antidiagonal n, (catalan p.1 : ℚ) * (catalan p.2 : ℚ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp1_lt_np1 : p.1 < n + 1 := by
          have := Finset.mem_antidiagonal.mp hp
          omega
        have hp2_lt_np1 : p.2 < n + 1 := by
          have := Finset.mem_antidiagonal.mp hp
          omega
        have h1 : coeff (p.1 + 1) Q = (catalan p.1 : ℚ) := ih p.1 (by omega)
        have h2 : coeff (p.2 + 1) Q = (catalan p.2 : ℚ) := ih p.2 (by omega)
        simp [h1, h2]
      rw [hsum]
      have hsum_catalan : ∑ p ∈ Finset.antidiagonal n, (catalan p.1 : ℚ) * (catalan p.2 : ℚ) = (catalan (n + 1) : ℚ) := by
        simpa [catalan_succ' n] using congrArg (fun x : ℕ => (x : ℚ)) (catalan_succ' n)
      rw [hsum_catalan]
  have main : coeff (n + 1) Q = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
    calc
      coeff (n + 1) Q = (catalan n : ℚ) := hcoeff_eq_catalan n
      _ = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
        have h_dvd : n + 1 ∣ Nat.centralBinom n := Nat.succ_dvd_centralBinom n
        calc
          (catalan n : ℚ) = ((Nat.centralBinom n / (n + 1) : ℕ) : ℚ) :=
            mod_cast (catalan_eq_centralBinom_div n)
          _ = (Nat.centralBinom n : ℚ) / (↑n + 1) := by
            have h_nonzero : ((n+1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
            simpa [Nat.cast_succ] using Nat.cast_div h_dvd h_nonzero
          _ = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by simp [Nat.centralBinom]
  convert main
  · apply Subsingleton.elim

end Submission
