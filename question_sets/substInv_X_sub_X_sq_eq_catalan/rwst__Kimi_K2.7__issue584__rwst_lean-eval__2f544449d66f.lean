import Mathlib
import Submission.Helpers

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  let inst : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]; exact invertibleOne
  let P := (X : ℚ⟦X⟧) - X ^ 2
  have hP0 : constantCoeff P = 0 := by simp [P]
  have hQ0 : constantCoeff (@substInv ℚ _ P inst) = 0 :=
    @PowerSeries.constantCoeff_substInv ℚ _ P inst
  have hQ_eq : @substInv ℚ _ P inst = X + (@substInv ℚ _ P inst) ^ 2 := by
    have h : subst (@substInv ℚ _ P inst) P = X :=
      @PowerSeries.subst_substInv_right ℚ _ P hP0 inst
    simp only [P] at h
    rw [subst_sub (@PowerSeries.HasSubst.substInv ℚ _ P inst),
      subst_X (@PowerSeries.HasSubst.substInv ℚ _ P inst),
      subst_pow (@PowerSeries.HasSubst.substInv ℚ _ P inst) X 2,
      subst_X (@PowerSeries.HasSubst.substInv ℚ _ P inst)] at h
    linear_combination h
  have h1 : coeff 1 (@substInv ℚ _ P inst) = 1 := by
    have h : coeff 1 (@substInv ℚ _ P inst) =
        coeff 1 X + coeff 1 ((@substInv ℚ _ P inst) ^ 2) := by
      conv_lhs => rw [hQ_eq]
      rw [map_add]
    rw [h]
    have h2 : coeff 1 ((@substInv ℚ _ P inst) ^ 2) = 0 := by
      simp only [pow_two, coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun p => coeff p.1 (@substInv ℚ _ P inst) * coeff p.2 (@substInv ℚ _ P inst))]
      simp [Finset.sum_range_succ, coeff_zero_eq_constantCoeff, hQ0]
    simp [coeff_X, h2]
  have hrec (m : ℕ) : coeff (m + 1) (@substInv ℚ _ P inst) = (catalan m : ℚ) := by
    induction' m using Nat.strongRecOn with m ih
    cases m with
    | zero =>
      rw [h1]
      simp [catalan_zero]
    | succ m =>
      have h : coeff (m + 2) (@substInv ℚ _ P inst) =
          coeff (m + 2) X + coeff (m + 2) ((@substInv ℚ _ P inst) ^ 2) := by
        conv_lhs => rw [hQ_eq]
        rw [map_add]
      rw [h]
      have h2 : coeff (m + 2) ((@substInv ℚ _ P inst) ^ 2) = (catalan (m + 1) : ℚ) := by
        simp only [pow_two, coeff_mul]
        rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
        have h0 : coeff 0 (@substInv ℚ _ P inst) = 0 := by
          rw [coeff_zero_eq_constantCoeff, hQ0]
        simp [h0]
        rw [catalan_succ', Nat.cast_sum]
        simp only [Nat.cast_mul]
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Finset.mem_antidiagonal] at hp
        rw [ih (p.1) (by omega), ih (p.2) (by omega)]
      have hX : coeff (m + 2) (X : ℚ⟦X⟧) = 0 := by
        rw [coeff_X]
        split_ifs with h
        · omega
        · rfl
      simp only [h2, hX]
      all_goals norm_num
  rw [hrec n]
  have hcat : (n + 1 : ℚ) * (catalan n : ℚ) = ((2 * n).choose n : ℚ) := by
    have h : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    norm_cast at h ⊢
  have hdiv : (catalan n : ℚ) = ((2 * n).choose n : ℚ) / (↑n + 1) := by
    field_simp [(show (↑n + 1 : ℚ) ≠ 0 by positivity)]
    linarith
  exact hdiv

end Submission
