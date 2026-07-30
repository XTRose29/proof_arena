import Mathlib
import Submission.Helpers

open Polynomial

namespace Submission

theorem abel_ruffini (n : ℕ) (_hn : 1 ≤ n) :
    (∀ p : ℚ[X], p.natDegree = n → ∀ x : ℂ, aeval x p = 0 →
        x ∈ solvableByRad ℚ ℂ) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra hn4
    have hn5 : 5 ≤ n := by omega
    let q : ℚ[X] := AbelRuffini.Φ ℚ 4 2 * X ^ (n - 5)
    have hqdeg : q.natDegree = n := by
      dsimp [q]
      rw [natDegree_mul (AbelRuffini.monic_Phi 4 2).ne_zero
        (pow_ne_zero _ X_ne_zero), AbelRuffini.natDegree_Phi, natDegree_X_pow]
      omega
    obtain ⟨x, hx⟩ :=
      (IsAlgClosed.splits (AbelRuffini.Φ ℂ 4 2)).exists_eval_eq_zero (by
        rw [AbelRuffini.degree_Phi]
        norm_num)
    have hxΦ : aeval x (AbelRuffini.Φ ℚ 4 2) = 0 := by
      rw [← AbelRuffini.map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
      exact hx
    have hxq : aeval x q = 0 := by
      simp [q, hxΦ]
    exact AbelRuffini.not_solvable_by_rad' x hxΦ (h q hqdeg x hxq)
  · intro hn4 p hp x hx
    have hcoeff (i : ℕ) : (p.coeff i : ℂ) ∈ solvableByRad ℚ ℂ :=
      (solvableByRad ℚ ℂ).algebraMap_mem (p.coeff i)
    have hleading (k : ℕ) (hk : k ≠ 0) (hdeg : p.natDegree = k) :
        (p.coeff k : ℂ) ≠ 0 := by
      have hp0 : p ≠ 0 := by
        intro hpzero
        have : 0 = k := by simpa [hpzero] using hdeg
        exact hk this.symm
      have hc : p.coeff k ≠ 0 := by
        rw [← hdeg, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hp0
      exact_mod_cast hc
    interval_cases n
    · have hx1 : (p.coeff 1 : ℂ) * x + (p.coeff 0 : ℂ) = 0 := by
        rw [Polynomial.aeval_eq_sum_range' (show p.natDegree < 2 by rw [hp]; norm_num) x] at hx
        simp [Finset.sum_range_succ, Algebra.smul_def] at hx
        linear_combination hx
      exact Helpers.linear_root_mem (hcoeff 1) (hcoeff 0)
        (hleading 1 (by norm_num) hp) hx1
    · have hx2 :
          (p.coeff 2 : ℂ) * x ^ 2 + (p.coeff 1 : ℂ) * x + (p.coeff 0 : ℂ) = 0 := by
        rw [Polynomial.aeval_eq_sum_range' (show p.natDegree < 3 by rw [hp]; norm_num) x] at hx
        simp [Finset.sum_range_succ, Algebra.smul_def] at hx
        linear_combination hx
      exact Helpers.quadratic_root_mem (hcoeff 2) (hcoeff 1) (hcoeff 0)
        (hleading 2 (by norm_num) hp) hx2
    · have hx3 :
          (p.coeff 3 : ℂ) * x ^ 3 + (p.coeff 2 : ℂ) * x ^ 2 +
            (p.coeff 1 : ℂ) * x + (p.coeff 0 : ℂ) = 0 := by
        rw [Polynomial.aeval_eq_sum_range' (show p.natDegree < 4 by rw [hp]; norm_num) x] at hx
        simp [Finset.sum_range_succ, Algebra.smul_def] at hx
        linear_combination hx
      exact Helpers.cubic_root_mem (hcoeff 3) (hcoeff 2) (hcoeff 1) (hcoeff 0)
        (hleading 3 (by norm_num) hp) hx3
    · have hx4 :
          (p.coeff 4 : ℂ) * x ^ 4 + (p.coeff 3 : ℂ) * x ^ 3 +
            (p.coeff 2 : ℂ) * x ^ 2 + (p.coeff 1 : ℂ) * x + (p.coeff 0 : ℂ) = 0 := by
        rw [Polynomial.aeval_eq_sum_range' (show p.natDegree < 5 by rw [hp]; norm_num) x] at hx
        simp [Finset.sum_range_succ, Algebra.smul_def] at hx
        linear_combination hx
      exact Helpers.quartic_root_mem (hcoeff 4) (hcoeff 3) (hcoeff 2) (hcoeff 1)
        (hcoeff 0) (hleading 4 (by norm_num) hp) hx4

end Submission
