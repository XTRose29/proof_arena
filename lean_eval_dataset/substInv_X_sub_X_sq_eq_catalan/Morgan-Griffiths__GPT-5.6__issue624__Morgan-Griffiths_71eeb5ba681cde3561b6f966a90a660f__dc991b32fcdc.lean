import Mathlib
import Submission.Helpers

open PowerSeries

namespace Submission

/-ResultProofDefinitionsBegin-/

lemma ps_catalan_solution_unique {A B : ℚ⟦X⟧}
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hA : A - A ^ 2 = (X : ℚ⟦X⟧))
    (hB : B - B ^ 2 = (X : ℚ⟦X⟧)) : A = B := by
  have hprod : (A - B) * (1 - (A + B)) = 0 := by
    calc
      _ = (A - A ^ 2) - (B - B ^ 2) := by ring
      _ = 0 := by rw [hA, hB, sub_self]
  have hnz : (1 - (A + B)) ≠ 0 := by
    intro hz
    -- apply constant coefficient
    have hz' := congrArg (fun T : ℚ⟦X⟧ => PowerSeries.constantCoeff T) hz
    -- simplify
    -- should yield 1 = 0
    simp [hA0, hB0] at hz'
  have hzero : A - B = 0 := by
    rcases (mul_eq_zero.mp hprod) with h | h
    · exact h
    · exact (hnz h).elim
  exact sub_eq_zero.mp hzero

/-ResultProofDefinitionsEnd-/


theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  letI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]; exact invertibleOne
  -- bring the definitional instance into scope
  -- main series of Catalan numbers over Q
  let S : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries
  let B : ℚ⟦X⟧ := (X : ℚ⟦X⟧) * S
  let P : ℚ⟦X⟧ := (X : ℚ⟦X⟧) - X ^ 2
  let A : ℚ⟦X⟧ := substInv P
  have hP0 : PowerSeries.constantCoeff P = 0 := by
    -- simp
    simp [P]
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    dsimp [A]
    -- need rewrite P
    simpa using (PowerSeries.constantCoeff_substInv (P := P))
  have hAeq : A - A ^ 2 = (X : ℚ⟦X⟧) := by
    have h := PowerSeries.subst_substInv_right P hP0
    -- h : subst (substInv P) P = X
    -- unfold P
    -- simp substitution
    have hs : PowerSeries.HasSubst (substInv P) :=
      PowerSeries.hasSubst_substInv P
    -- expand the polynomial P under substitution
    change (PowerSeries.subst (substInv P) ((X : ℚ⟦X⟧) - X ^ 2)) = (X : ℚ⟦X⟧) at h
    rw [PowerSeries.subst_sub hs, PowerSeries.subst_X hs,
        PowerSeries.subst_pow hs, PowerSeries.subst_X hs] at h
    simpa [A] using h
  have hS : S ^ 2 * (X : ℚ⟦X⟧) + 1 = S := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      (PowerSeries.catalanSeries_sq_mul_X_add_one)
    -- the coefficientwise map is a ring homomorphism
    simpa [S] using h
  have hB0 : PowerSeries.constantCoeff B = 0 := by
    simp [B]
  have hBeq : B - B ^ 2 = (X : ℚ⟦X⟧) := by
    -- the Catalan functional equation gives this after multiplying by X
    dsimp [B]
    -- prove algebraically from hS
    have hSX : S = S ^ 2 * (X : ℚ⟦X⟧) + 1 := hS.symm
    have hSd : S - S ^ 2 * (X : ℚ⟦X⟧) = 1 := by
      linear_combination hSX
    -- commutative power series ring
    calc
      (X : ℚ⟦X⟧) * S - (X * S) ^ 2 = X * (S - S ^ 2 * X) := by ring
      _ = X := by rw [hSd]; ring
  have hAB : A = B := ps_catalan_solution_unique hA0 hB0 hAeq hBeq
  -- now read the coefficients of X times the Catalan series
  have hcoeffB : coeff (n + 1) B = (catalan n : ℚ) := by
    -- move X to the right and use coeff_succ_mul_X
    change coeff (n + 1) ((X : ℚ⟦X⟧) * S) = _
    rw [mul_comm, PowerSeries.coeff_succ_mul_X]
    -- coefficient of the mapped Catalan series
    simp [S]
  have hnat : (n + 1) * catalan n = n.centralBinom :=
    succ_mul_catalan_eq_centralBinom n
  have hrat : (n + 1 : ℚ) * (catalan n : ℚ) = (n.centralBinom : ℚ) := by
    exact_mod_cast hnat
  have hform : (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
    -- divide the integral identity by n+1
    -- central binomial coefficient is (2*n choose n)
    rw [Nat.centralBinom] at hrat
    -- use field equation
    have hden : ( (n:ℚ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    -- hrat has (n+1:ℚ) form
    apply (eq_div_iff hden).2
    -- need rearrange product
    -- eq_div_iff gives ? = ? ; result c*n ?
    simpa [add_comm, add_left_comm, add_assoc, mul_comm] using hrat
  -- identify A with B
  change coeff (n + 1) A = _
  rw [hAB, hcoeffB]
  exact hform


end Submission
