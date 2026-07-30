import ChallengeDeps
import Submission.Helpers

open LeanEval.LinearAlgebra.TraceNewton
open Matrix Polynomial
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Submission

/-ResultProofDefinitionsBegin-/

-- coefficient of the reverse characteristic polynomial, in the downstairs indexing
lemma desc_eq_coeff_rev {R : Type*} [CommRing R]
    (A : Matrix n n R) (i : ℕ) :
    charpolyDescendingCoeff A i = A.charpolyRev.coeff i := by
  classical
  nontriviality R
  rw [← Matrix.reverse_charpoly A, Polynomial.coeff_reverse]
  rw [Matrix.charpoly_natDegree_eq_dim]
  by_cases h : i ≤ Fintype.card n
  · simp [charpolyDescendingCoeff, h, Polynomial.revAt_le h]
  · have hi : Fintype.card n < i := Nat.lt_of_not_ge h
    rw [charpolyDescendingCoeff, if_neg h,
      Polynomial.revAt_eq_self_of_lt hi]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Matrix.charpoly_natDegree_eq_dim]
      exact hi)).symm


-- A derivation differentiates a determinant by differentiating its rows.
lemma derivative_det_rows {R : Type*} [CommRing R]
    (M : Matrix n n R[X]) :
    Polynomial.derivative M.det =
      ∑ i : n, (M.updateRow i (fun j => Polynomial.derivative (M i j))).det := by
  classical
  -- expand determinant as alternating products of columns
  simp only [Matrix.det_apply', Polynomial.derivative_sum,
    Polynomial.derivative_mul, Polynomial.derivative_intCast,
    zero_mul, zero_add, Polynomial.derivative_prod_finset]
  -- interchange the permutation and row sums
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  -- each permutation uses a given row in a single column
  have hterm (r : n) :
      (∏ i : n, M.updateRow r (fun j => Polynomial.derivative (M r j)) (σ i) i)
        = (∏ i ∈ (Finset.univ.erase (σ.symm r)), M (σ i) i) *
              Polynomial.derivative (M (σ (σ.symm r)) (σ.symm r)) := by
    classical
    -- split the distinguished element from the product
    have heq (i : n) : (σ i = r ↔ i = σ.symm r) := by
      constructor
      · intro hi; simpa using congrArg σ.symm hi
      · intro hi; simpa [hi]
    have hp := Finset.prod_erase_mul (Finset.univ) (fun i : n =>
          M.updateRow r (fun j => Polynomial.derivative (M r j)) (σ i) i)
          (Finset.mem_univ (σ.symm r))
    -- use the value on and off that column
    rw [← hp]
    -- off the distinguished column the row is unchanged
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      change M.updateRow r (fun j => Polynomial.derivative (M r j)) (σ i) i = _
      rw [Matrix.updateRow_apply]
      have hn : σ i ≠ r := by
        intro h
        have : i = σ.symm r := (heq i).1 h
        exact (Finset.mem_erase.mp hi).1 this
      simp [hn]
    · change M.updateRow r (fun j => Polynomial.derivative (M r j)) (σ (σ.symm r)) (σ.symm r) = _
      rw [Matrix.updateRow_apply]
      have hh : σ (σ.symm r) = r := σ.apply_symm_apply r
      simp [hh]
  simp_rw [hterm]
  rw [Finset.mul_sum]
  let g : n → R[X] := fun i =>
       (↑(↑(Equiv.Perm.sign σ) : ℤ) : R[X]) *
          ((∏ b ∈ Finset.univ.erase i, M (σ b) b) *
              Polynomial.derivative (M (σ i) i))
  change (∑ i : n, g i) = ∑ r : n, g (σ.symm r)
  exact (Equiv.sum_comp σ.symm g).symm

lemma det_updateRow_expand {S : Type*} [CommRing S]
    (M : Matrix n n S) (i : n) (v : n → S) :
    (M.updateRow i v).det = ∑ j : n, v j * M.adjugate j i := by
  classical
  -- write the row vector as a sum of singletons
  have hv : v = ∑ j : n, v j • (Pi.single j (1 : S) : n → S) := by
    classical
    ext t
    simp [Pi.single_apply]
  have hzero : (M.updateRow i (0 : n → S)).det = 0 := by
    have hz := Matrix.det_updateRow_smul M i (0:S) (0 : n → S)
    simpa using hz
  have hlin (s : Finset n) :
      (M.updateRow i (∑ j ∈ s, v j • (Pi.single j (1 : S) : n → S))).det =
        ∑ j ∈ s, v j * M.adjugate j i := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [Matrix.det_updateRow_add, ih, Matrix.det_updateRow_smul]
      rw [Matrix.adjugate_apply]
  calc
    (M.updateRow i v).det =
        (M.updateRow i (∑ j : n, v j • (Pi.single j (1 : S) : n → S))).det := congrArg (fun w : n → S => (M.updateRow i w).det) hv
    _ = _ := by simpa using (hlin Finset.univ)


lemma derivative_charpolyRev_adjugate {R : Type*} [CommRing R]
    (A : Matrix n n R) :
    Polynomial.derivative A.charpolyRev =
      - Matrix.trace (A.map Polynomial.C *
          (1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate) := by
  classical
  let B : Matrix n n R[X] := 1 - (Polynomial.X : R[X]) • A.map Polynomial.C
  change Polynomial.derivative B.det = _
  rw [derivative_det_rows B]
  -- compute one row
  simp_rw [det_updateRow_expand]
  -- derivative of a linear entry
  have he (i j : n) :
      Polynomial.derivative (B i j) = -(Polynomial.C (A i j)) := by
    classical
    rcases eq_or_ne i j with h | h <;>
      simp [B, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        h, Polynomial.derivative_sub, Polynomial.derivative_mul]
  simp_rw [he]
  change (∑ i : n, ∑ j : n, (-Polynomial.C (A i j)) * B.adjugate j i) =
    - Matrix.trace (A.map Polynomial.C * B.adjugate)
  simp [Matrix.trace, Matrix.mul_apply]


noncomputable def traceNewtonAdjCoeff {R : Type*} [CommRing R]
    (A : Matrix n n R) (s : ℕ) : Matrix n n R := fun i j =>
      Polynomial.coeff ((1 - (Polynomial.X : R[X]) •
        A.map Polynomial.C).adjugate i j) s

lemma traceNewtonAdjCoeff_zero {R : Type*} [CommRing R]
    (A : Matrix n n R) : traceNewtonAdjCoeff A 0 = 1 := by
  classical
  let B : Matrix n n R[X] := 1 - (Polynomial.X : R[X]) • A.map Polynomial.C
  let Q : Matrix n n R[X] := B.adjugate
  have hmul := Matrix.adjugate_mul B
  ext i l
  have h := congrArg (fun M : Matrix n n R[X] =>
       Polynomial.coeff (M i l) 0) hmul
  change Polynomial.coeff ((Q * B) i l) 0 = _ at h
  have hb : Q * B = Q - (Polynomial.X : R[X]) • (Q * A.map Polynomial.C) := by
    dsimp [B]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  rw [hb] at h
  have h' :
    Polynomial.coeff ((1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate i l) 0 =
       Polynomial.coeff ((if i = l then
          (1 - (Polynomial.X : R[X]) • A.map Polynomial.C).det else 0)) 0 := by
    simpa [Q, Matrix.sub_apply, Matrix.smul_apply,
       smul_eq_mul, Polynomial.coeff_sub, Matrix.one_apply,
       B, Matrix.mul_apply] using h
  change Polynomial.coeff ((1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate i l) 0
        = (1 : Matrix n n R) i l
  rw [Matrix.one_apply]
  by_cases hil : i = l
  · subst l
    have hh : Polynomial.coeff
        ((1 - (Polynomial.X : R[X]) • A.map Polynomial.C).det) 0 = (1:R) := by
      simpa [Matrix.charpolyRev, Polynomial.coeff_zero_eq_eval_zero]
        using (Matrix.eval_charpolyRev (M := A))
    simpa [hh] using h'
  · simpa [hil] using h'

lemma traceNewtonAdjCoeff_succ {R : Type*} [CommRing R]
    (A : Matrix n n R) (s : ℕ) :
    traceNewtonAdjCoeff A (s+1) =
       (A.charpolyRev.coeff (s+1)) • (1 : Matrix n n R) +
          traceNewtonAdjCoeff A s * A := by
  classical
  let B : Matrix n n R[X] := 1 - (Polynomial.X : R[X]) • A.map Polynomial.C
  let Q : Matrix n n R[X] := B.adjugate
  have hmul := Matrix.adjugate_mul B
  have hb : Q * B = Q - (Polynomial.X : R[X]) • (Q * A.map Polynomial.C) := by
    dsimp [B]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  ext i l
  have h := congrArg (fun M : Matrix n n R[X] =>
       Polynomial.coeff (M i l) (s+1)) hmul
  change Polynomial.coeff ((Q * B) i l) (s+1) = _ at h
  rw [hb] at h
  have h' :
      Polynomial.coeff ((1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate i l) (s+1)
        - ∑ x : n, Polynomial.coeff
            ((1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate i x) s * A x l =
          Polynomial.coeff (if i = l then
            (1 - (Polynomial.X : R[X]) • A.map Polynomial.C).det else 0) (s+1) := by
    simpa [Q, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Polynomial.coeff_sub, Matrix.mul_apply, B,
        Matrix.one_apply, Polynomial.coeff_X_mul,
        Polynomial.coeff_mul_C, Finset.mul_sum] using h
  rw [sub_eq_iff_eq_add] at h'
  change Polynomial.coeff ((1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate i l) (s+1) = _
  by_cases hil : i = l
  · subst l
    simpa [traceNewtonAdjCoeff, Matrix.add_apply, Matrix.smul_apply,
       Matrix.one_apply, Matrix.mul_apply, Matrix.charpolyRev] using h'
  · simpa [traceNewtonAdjCoeff, Matrix.add_apply, Matrix.smul_apply,
       Matrix.one_apply, Matrix.mul_apply, Matrix.charpolyRev, hil]
       using h'


lemma traceNewtonAdjCoeff_formula {R : Type*} [CommRing R]
    (A : Matrix n n R) (s : ℕ) :
    traceNewtonAdjCoeff A s =
      ∑ i ∈ Finset.range (s+1), (A.charpolyRev.coeff i) • A^(s-i) := by
  classical
  induction s with
  | zero =>
      rw [traceNewtonAdjCoeff_zero]
      simp [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  | succ t ih =>
      rw [traceNewtonAdjCoeff_succ, ih]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [Finset.sum_mul]
      simp_rw [Matrix.smul_mul]
      have hp : (∑ i ∈ Finset.range (t+1),
            A.charpolyRev.coeff i • (A ^ (t - i) * A)) =
          ∑ i ∈ Finset.range (t+1),
            A.charpolyRev.coeff i • A ^ (t+1-i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < t+1 := Finset.mem_range.mp hi
        have he : t+1-i = (t-i)+1 := by omega
        simp [he, pow_succ]
      rw [hp]
      simp
      ac_rfl


lemma coeff_derivative_charpolyRev {R : Type*} [CommRing R]
    (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    A.charpolyRev.coeff k * (k : R) =
       - Matrix.trace (A * traceNewtonAdjCoeff A (k-1)) := by
  classical
  have hd := congrArg (fun p : R[X] => Polynomial.coeff p (k-1))
       (derivative_charpolyRev_adjugate A)
  -- left derivative coefficient
  change (Polynomial.derivative A.charpolyRev).coeff (k-1) =
    (- Matrix.trace (A.map Polynomial.C *
          (1 - (Polynomial.X : R[X]) • A.map Polynomial.C).adjugate)).coeff (k-1) at hd
  rw [Polynomial.coeff_derivative] at hd
  have hs : k - 1 + 1 = k := by omega
  -- calculate right coefficient entry by entry
  -- simplify finite sums and constants
  simp [Matrix.trace, Matrix.mul_apply, traceNewtonAdjCoeff,
     Polynomial.coeff_neg, Finset.mul_sum,
     Polynomial.coeff_mul_C] at hd
  have hc : ( (k-1 : ℕ) : R) + 1 = (k:R) := by
    simpa using congrArg (fun z : ℕ => (z:R)) hs
  -- expand the ordinary trace as the same double sum
  simpa [hs, hc, Matrix.trace, Matrix.mul_apply,
      traceNewtonAdjCoeff] using hd


lemma trace_mul_adjCoeff {R : Type*} [CommRing R]
    (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    Matrix.trace (A * traceNewtonAdjCoeff A (k-1)) =
       ∑ i ∈ Finset.range k,
          (A.charpolyRev.coeff i) * Matrix.trace (A ^ (k-i)) := by
  classical
  rw [traceNewtonAdjCoeff_formula]
  have hs : k-1+1 = k := by omega
  rw [hs]
  rw [Matrix.mul_sum]
  -- expand both traces as diagonal sums
  simp only [Matrix.trace]
  simp_rw [Matrix.mul_smul]
  simp_rw [Matrix.diag_apply]
  simp_rw [Matrix.sum_apply]
  simp_rw [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < k := Finset.mem_range.mp hi
  have he : k-i = (k-1-i)+1 := by omega
  rw [he, pow_succ']
  rw [Finset.mul_sum]

/-ResultProofDefinitionsEnd-/


theorem trace_cayley_hamilton_newton {R : Type*} [CommRing R]
    (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * charpolyDescendingCoeff A k +
        ∑ j ∈ Finset.Icc 1 k,
          trace (A ^ j) * charpolyDescendingCoeff A (k - j) = 0 := by
  classical
  simp_rw [desc_eq_coeff_rev]
  have hd := coeff_derivative_charpolyRev A hk
  have hm := trace_mul_adjCoeff A hk
  have hsum :
      (∑ j ∈ Finset.Icc 1 k, (A^j).trace * A.charpolyRev.coeff (k-j)) =
        ∑ i ∈ Finset.range k, A.charpolyRev.coeff i * (A^(k-i)).trace := by
    symm
    refine Finset.sum_bij' (fun i _ => k-i) (fun j _ => k-j) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha' : a < k := Finset.mem_range.mp ha
      change k - a ∈ Finset.Icc 1 k
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    · intro a ha
      have ha' := Finset.mem_Icc.mp ha
      change k - a ∈ Finset.range k
      apply Finset.mem_range.mpr
      omega
    · intro a ha
      change k - (k - a) = a
      apply Nat.sub_sub_self
      exact Nat.le_of_lt (Finset.mem_range.mp ha)
    · intro a ha
      change k - (k - a) = a
      apply Nat.sub_sub_self
      exact (Finset.mem_Icc.mp ha).2
    · intro a ha
      have ha' : a ≤ k := Nat.le_of_lt (Finset.mem_range.mp ha)
      change A.charpolyRev.coeff a * (A ^ (k-a)).trace =
          (A ^ (k-a)).trace * A.charpolyRev.coeff (k-(k-a))
      rw [Nat.sub_sub_self ha']
      apply mul_comm
  rw [hsum, ← hm]
  have hd' : (k:R) * A.charpolyRev.coeff k =
       - (A * traceNewtonAdjCoeff A (k-1)).trace := by
    simpa [mul_comm] using hd
  rw [hd']
  simp


end Submission
