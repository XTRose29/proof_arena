import ChallengeDeps

namespace Submission.Helpers

open LeanEval.LinearAlgebra.TraceNewton
open Matrix Polynomial
open scoped BigOperators Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Formal differentiation of a determinant differentiates one column at a
time. -/
lemma derivative_det (M : Matrix n n R[X]) :
    derivative M.det =
      ∑ j, det (M.updateCol j fun i => derivative (M i j)) := by
  rw [Matrix.det_apply', derivative_sum]
  simp_rw [derivative_mul, derivative_prod_finset]
  simp only [derivative_intCast, zero_mul, zero_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)]
  simp only [Finset.sdiff_singleton_eq_erase, Matrix.updateCol_self]
  have hprod :
      (∏ i ∈ Finset.univ.erase j,
          (M.updateCol j fun i => derivative (M i j)) (σ i) i) =
        ∏ i ∈ Finset.univ.erase j, M (σ i) i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Matrix.updateCol_ne]
    simpa using hi
  rw [hprod]
  ac_rfl

/-- Jacobi's derivative formula specialized to the reverse characteristic
polynomial. -/
lemma derivative_charpolyRev (A : Matrix n n R) :
    derivative A.charpolyRev =
      -trace (adjugate (1 - (X : R[X]) • A.map C) * A.map C) := by
  rw [Matrix.charpolyRev, derivative_det]
  have hcol (j : n) :
      (fun i => derivative ((1 - (X : R[X]) • A.map C) i j)) =
        -(A.map C).col j := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  simp_rw [hcol, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.mul_apply]

/-- Extract a coefficient entrywise from a matrix of polynomials. -/
def coeffMatrix (M : Matrix n n R[X]) (k : ℕ) : Matrix n n R :=
  fun i j => (M i j).coeff k

/-- The degree-zero coefficient of the adjugate of `1 - X A` is the identity
matrix. -/
lemma coeffMatrix_adjugate_zero (A : Matrix n n R) :
    coeffMatrix (adjugate (1 - (X : R[X]) • A.map C)) 0 =
      (1 : Matrix n n R) := by
  let B : Matrix n n R[X] := 1 - (X : R[X]) • A.map C
  have hadj :
      adjugate B - (X : R[X]) • (adjugate B * A.map C) =
        B.det • (1 : Matrix n n R[X]) := by
    simpa [B, Matrix.mul_sub] using Matrix.adjugate_mul B
  ext i j
  have hij := congrArg (fun p : R[X] => p.coeff 0)
    (congrFun (congrFun hadj i) j)
  have hdet : B.det.coeff 0 = 1 := by
    change A.charpolyRev.coeff 0 = 1
    simp [coeff_zero_eq_eval_zero]
  by_cases h : i = j
  · simpa [B, coeffMatrix, Matrix.one_apply, coeff_zero_eq_eval_zero, h, hdet] using hij
  · simpa [B, coeffMatrix, Matrix.one_apply, coeff_zero_eq_eval_zero, h] using hij

/-- Successive coefficients of the adjugate of `1 - X A` obey the
Faddeev--LeVerrier recursion. -/
lemma coeffMatrix_adjugate_succ (A : Matrix n n R) (m : ℕ) :
    coeffMatrix (adjugate (1 - (X : R[X]) • A.map C)) (m + 1) =
      coeffMatrix (adjugate (1 - (X : R[X]) • A.map C)) m * A +
        A.charpolyRev.coeff (m + 1) • (1 : Matrix n n R) := by
  let B : Matrix n n R[X] := 1 - (X : R[X]) • A.map C
  have hadj :
      adjugate B - (X : R[X]) • (adjugate B * A.map C) =
        B.det • (1 : Matrix n n R[X]) := by
    simpa [B, Matrix.mul_sub] using Matrix.adjugate_mul B
  ext i j
  have hij := congrArg (fun p : R[X] => p.coeff (m + 1))
    (congrFun (congrFun hadj i) j)
  by_cases h : i = j
  · simp [B, Matrix.mul_apply, coeff_X_mul, h] at hij
    rw [sub_eq_iff_eq_add] at hij
    simpa [coeffMatrix, Matrix.mul_apply, Matrix.one_apply, h, add_comm,
      Matrix.charpolyRev] using hij
  · simp [B, Matrix.mul_apply, coeff_X_mul, h] at hij
    rw [sub_eq_iff_eq_add] at hij
    simpa [coeffMatrix, Matrix.mul_apply, Matrix.one_apply, h] using hij

/-- Closed form of the adjugate coefficient recursion. -/
lemma coeffMatrix_adjugate_eq_sum (A : Matrix n n R) (m : ℕ) :
    coeffMatrix (adjugate (1 - (X : R[X]) • A.map C)) m =
      ∑ i ∈ Finset.range (m + 1), A.charpolyRev.coeff i • A ^ (m - i) := by
  induction m with
  | zero =>
      rw [coeffMatrix_adjugate_zero]
      simp [coeff_zero_eq_eval_zero]
  | succ m ih =>
      rw [coeffMatrix_adjugate_succ, ih, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_range_succ]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Matrix.smul_mul, ← pow_succ]
        congr 2
        rw [Finset.mem_range] at hi
        have hi' : i ≤ m := by omega
        exact (Nat.sub_add_comm hi').symm
      · simp

omit [DecidableEq n] in
/-- Coefficient extraction commutes with multiplying a polynomial matrix by a
fixed matrix and taking its trace. -/
lemma coeff_trace_mul_map_C (M : Matrix n n R[X]) (A : Matrix n n R) (m : ℕ) :
    (trace (M * A.map C)).coeff m = trace (coeffMatrix M m * A) := by
  simp [Matrix.trace, Matrix.mul_apply, coeffMatrix]

/-- The trace of an adjugate coefficient times `A` is the corresponding
finite Newton sum. -/
lemma trace_coeffMatrix_adjugate_mul (A : Matrix n n R) (m : ℕ) :
    trace (coeffMatrix (adjugate (1 - (X : R[X]) • A.map C)) m * A) =
      ∑ i ∈ Finset.range (m + 1),
        A.charpolyRev.coeff i * trace (A ^ (m + 1 - i)) := by
  rw [coeffMatrix_adjugate_eq_sum, Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.smul_mul, Matrix.trace_smul, ← pow_succ]
  congr 2
  rw [Finset.mem_range] at hi
  have hi' : i ≤ m := by omega
  exact congrArg (fun e : ℕ => A ^ e) (Nat.sub_add_comm hi').symm

/-- Newton's recurrence written with ascending coefficients of
`charpolyRev`. -/
lemma charpolyRev_newton_range (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * A.charpolyRev.coeff k +
      ∑ i ∈ Finset.range k,
        A.charpolyRev.coeff i * trace (A ^ (k - i)) = 0 := by
  have hder := congrArg (fun p : R[X] => p.coeff (k - 1))
    (derivative_charpolyRev A)
  rw [coeff_derivative, coeff_neg, coeff_trace_mul_map_C] at hder
  have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hsub, trace_coeffMatrix_adjugate_mul, hsub] at hder
  have hcast : ((k - 1 : ℕ) : R) + 1 = (k : R) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun t : ℕ => (t : R)) hsub
  rw [hcast] at hder
  rw [mul_comm (k : R) (A.charpolyRev.coeff k), hder]
  exact neg_add_cancel _

/-- Newton's recurrence in the descending-index form used by the challenge. -/
lemma charpolyRev_newton_Icc (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * A.charpolyRev.coeff k +
      ∑ j ∈ Finset.Icc 1 k,
        trace (A ^ j) * A.charpolyRev.coeff (k - j) = 0 := by
  have href := Finset.sum_Ico_reflect
    (fun i => A.charpolyRev.coeff i * trace (A ^ (k - i))) 1
    (m := k + 1) (n := k) (by omega)
  have hsums :
      (∑ i ∈ Finset.range k,
          A.charpolyRev.coeff i * trace (A ^ (k - i))) =
        ∑ j ∈ Finset.Icc 1 k,
          trace (A ^ j) * A.charpolyRev.coeff (k - j) := by
    calc
      (∑ i ∈ Finset.range k,
          A.charpolyRev.coeff i * trace (A ^ (k - i))) =
          ∑ j ∈ Finset.Ico 1 (k + 1),
            A.charpolyRev.coeff (k - j) *
              trace (A ^ (k - (k - j))) := by
            simpa only [Nat.add_sub_cancel, Nat.sub_self,
              Nat.Ico_zero_eq_range] using href.symm
      _ = ∑ j ∈ Finset.Ico 1 (k + 1),
            trace (A ^ j) * A.charpolyRev.coeff (k - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mem_Ico] at hj
            have hkj : k - (k - j) = j := by omega
            rw [hkj, mul_comm]
      _ = ∑ j ∈ Finset.Icc 1 k,
            trace (A ^ j) * A.charpolyRev.coeff (k - j) := by
            rw [Finset.Ico_add_one_right_eq_Icc]
  rw [← hsums]
  exact charpolyRev_newton_range A hk

/-- The challenge's zero-extended descending coefficient is exactly the
corresponding coefficient of the reverse characteristic polynomial. -/
lemma charpolyDescendingCoeff_eq_coeff_charpolyRev
    (A : Matrix n n R) (k : ℕ) :
    charpolyDescendingCoeff A k = A.charpolyRev.coeff k := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    rw [← A.reverse_charpoly]
    by_cases hk : k ≤ Fintype.card n
    · simp [charpolyDescendingCoeff, coeff_reverse,
        A.charpoly_natDegree_eq_dim, hk]
    · rw [charpolyDescendingCoeff, if_neg hk, coeff_reverse,
        A.charpoly_natDegree_eq_dim,
        Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hk)]
      have hdeg : A.charpoly.natDegree < k := by
        simpa only [A.charpoly_natDegree_eq_dim] using Nat.lt_of_not_ge hk
      exact (coeff_eq_zero_of_natDegree_lt hdeg).symm
  · haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

end Submission.Helpers
