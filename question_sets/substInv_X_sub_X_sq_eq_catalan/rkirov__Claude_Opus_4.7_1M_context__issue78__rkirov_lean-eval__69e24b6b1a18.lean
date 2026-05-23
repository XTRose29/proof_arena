import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Submission.Helpers

open PowerSeries

namespace Submission

/-- The Catalan generating function over `ℚ`, obtained from `PowerSeries.catalanSeries`
by mapping `ℕ → ℚ`. -/
noncomputable def catQ : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

@[simp]
lemma coeff_catQ (k : ℕ) : coeff k catQ = (catalan k : ℚ) := by
  simp [catQ, coeff_map]

/-- The Catalan series identity over `ℚ`: `catQ ^ 2 * X + 1 = catQ`. -/
lemma catQ_sq_mul_X_add_one : catQ ^ 2 * X + 1 = catQ := by
  unfold catQ
  rw [show (X : ℚ⟦X⟧) = PowerSeries.map (Nat.castRingHom ℚ) X from (PowerSeries.map_X _).symm,
      show (1 : ℚ⟦X⟧) = PowerSeries.map (Nat.castRingHom ℚ) 1 from (RingHom.map_one _).symm,
      ← RingHom.map_pow, ← RingHom.map_mul, ← RingHom.map_add, catalanSeries_sq_mul_X_add_one]

lemma constantCoeff_X_mul_catQ : constantCoeff (R := ℚ) (X * catQ) = 0 := by
  rw [map_mul, constantCoeff_X, zero_mul]

/-- `X * catQ` satisfies `Y - Y² = X` where `Y = X * catQ`. -/
lemma X_mul_catQ_sub_sq : (X * catQ) - (X * catQ) ^ 2 = (X : ℚ⟦X⟧) := by
  have h := catQ_sq_mul_X_add_one
  have h' : catQ - X * catQ ^ 2 = 1 := by linear_combination -h
  have heq : (X * catQ) - (X * catQ) ^ 2 = X * (catQ - X * catQ ^ 2) := by ring
  rw [heq, h', mul_one]

/-- The key lemma, with the `Invertible` instance taken explicitly so it doesn't
have to be re-synthesized when applied. -/
private lemma substInv_X_sub_X_sq_eq_X_mul_catQ
    (inst : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2))) :
    @substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) inst = X * catQ := by
  have hP_const : constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = 0 := by
    rw [map_sub, map_pow, constantCoeff_X, zero_pow two_ne_zero, sub_zero]
  have hP_hasSubst : HasSubst ((X : ℚ⟦X⟧) - X ^ 2) :=
    HasSubst.of_constantCoeff_zero hP_const
  have hQ_hasSubst : HasSubst (X * catQ : ℚ⟦X⟧) :=
    HasSubst.of_constantCoeff_zero constantCoeff_X_mul_catQ
  have hPQ : ((X : ℚ⟦X⟧) - X ^ 2).subst (X * catQ : ℚ⟦X⟧) = X := by
    rw [subst_sub hQ_hasSubst, subst_X hQ_hasSubst, subst_pow hQ_hasSubst,
        subst_X hQ_hasSubst, X_mul_catQ_sub_sq]
  -- Use uniqueness via subst_substInv_left.
  have h1 : PowerSeries.subst (X : ℚ⟦X⟧)
                (@substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) inst) =
            @substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) inst := X_subst _
  have h2 : PowerSeries.subst (X * catQ : ℚ⟦X⟧) (PowerSeries.subst ((X : ℚ⟦X⟧) - X ^ 2)
                (@substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) inst)) =
            PowerSeries.subst (X * catQ : ℚ⟦X⟧) (X : ℚ⟦X⟧) := by
    rw [@subst_substInv_left ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) hP_const inst]
  have h3 := subst_comp_subst_apply hP_hasSubst hQ_hasSubst
                (@substInv ℚ _ ((X : ℚ⟦X⟧) - X ^ 2) inst)
  rw [h2, subst_X hQ_hasSubst, hPQ] at h3
  exact h1.symm.trans h3.symm

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  rw [substInv_X_sub_X_sq_eq_X_mul_catQ]
  -- Coefficient computation: (n+1)-th coefficient of X * catQ is catalan n.
  have hQ_coeff : coeff (n + 1) ((X : ℚ⟦X⟧) * catQ) = (catalan n : ℚ) := by
    have hXmul := coeff_X_pow_mul (R := ℚ) catQ 1 n
    rw [show ((X : ℚ⟦X⟧)) = X ^ 1 from (pow_one X).symm, hXmul, coeff_catQ]
  rw [hQ_coeff]
  -- (catalan n : ℚ) = Nat.choose (2 * n) n / (n + 1).
  have hcat : catalan n * (n + 1) = Nat.centralBinom n := by
    rw [mul_comm]; exact succ_mul_catalan_eq_centralBinom n
  have hQ_eq : (catalan n : ℚ) * ((n : ℚ) + 1) = (Nat.choose (2 * n) n : ℚ) := by
    have : (catalan n * (n + 1) : ℚ) = (Nat.centralBinom n : ℚ) := by exact_mod_cast hcat
    rw [Nat.centralBinom_eq_two_mul_choose] at this
    linarith
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linarith

end Submission
