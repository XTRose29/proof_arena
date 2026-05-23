/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: oppenheim_inequality
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 469356690df9b9bcc7751388474ab1268c32c00e
issue_number: 106
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

open Submission.Helpers

/-- Helper: scaled outer product is PSD when the scalar is positive. -/
private lemma posSemidef_smul_vecMulVec_self {n : Type*} [Fintype n] (u : n → ℝ) {a : ℝ}
    (ha : 0 < a) :
    (a⁻¹ • Matrix.vecMulVec u u).PosSemidef := by
  have heq : a⁻¹ • Matrix.vecMulVec u u =
      Matrix.vecMulVec (fun i => u i / Real.sqrt a) (fun i => u i / Real.sqrt a) := by
    ext i j
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    show a⁻¹ * (u i * u j) = (u i / Real.sqrt a) * (u j / Real.sqrt a)
    rw [div_mul_div_comm, hsq]
    ring
  rw [heq]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- The Hadamard product distributes over matrix addition. -/
private lemma hadamard_add {n : Type*} (A B C : Matrix n n ℝ) :
    A ⊙ (B + C) = A ⊙ B + A ⊙ C := by
  ext i j
  simp [Matrix.hadamard_apply, mul_add]

private lemma add_hadamard {n : Type*} (A B C : Matrix n n ℝ) :
    (A + B) ⊙ C = A ⊙ C + B ⊙ C := by
  ext i j
  simp [Matrix.hadamard_apply, add_mul]

/-- Auxiliary form of Oppenheim on `Fin k`, suitable for induction. -/
theorem oppenheim_fin : ∀ (k : ℕ) {A B : Matrix (Fin k) (Fin k) ℝ},
    A.PosSemidef → B.PosSemidef → A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  intro k
  induction k with
  | zero =>
    intro A B _ _
    simp [Matrix.det_isEmpty]
  | succ k ih =>
    intro A B hA hB
    -- Case on A 0 0
    by_cases h00A : A 0 0 = 0
    · -- Row 0 of A is zero; both LHS and RHS are 0.
      have hrow_A : ∀ j, A 0 j = 0 := fun j =>
        posSemidef_row_zero_of_diag_zero hA h00A j
      have hrow_AB : ∀ j, (A ⊙ B) 0 j = 0 := fun j => by
        simp [Matrix.hadamard_apply, hrow_A]
      have hdetA : A.det = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero (i := 0)
        intro j
        rw [hrow_A]
      have hdetAB : (A ⊙ B).det = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero (i := 0)
        intro j
        rw [hrow_AB]
      rw [hdetA, hdetAB, zero_mul]
    · have h00A_pos : 0 < A 0 0 := lt_of_le_of_ne hA.diag_nonneg (Ne.symm h00A)
      by_cases h00B : B 0 0 = 0
      · -- B 0 0 = 0: row 0 of B is zero, det A⊙B = 0; LHS has factor B 0 0 = 0.
        have hrow_B : ∀ j, B 0 j = 0 := fun j =>
          posSemidef_row_zero_of_diag_zero hB h00B j
        have hrow_AB : ∀ j, (A ⊙ B) 0 j = 0 := fun j => by
          simp [Matrix.hadamard_apply, hrow_B]
        have hdetAB : (A ⊙ B).det = 0 := by
          apply Matrix.det_eq_zero_of_row_eq_zero (i := 0)
          intro j; rw [hrow_AB]
        have hprod : ∏ i, B i i = 0 := by
          rw [Fin.prod_univ_succ, h00B, zero_mul]
        rw [hprod, mul_zero, hdetAB]
      · -- Main case: A 0 0 > 0 and B 0 0 > 0.
        have h00B_pos : 0 < B 0 0 := lt_of_le_of_ne hB.diag_nonneg (Ne.symm h00B)
        set a := A 0 0 with ha_def
        set b := B 0 0 with hb_def
        have ha_pos : 0 < a := h00A_pos
        have hb_pos : 0 < b := h00B_pos
        have ha_ne : a ≠ 0 := ha_pos.ne'
        have hb_ne : b ≠ 0 := hb_pos.ne'
        have hab_pos : 0 < a * b := mul_pos ha_pos hb_pos
        have hab_ne : a * b ≠ 0 := hab_pos.ne'
        -- Define A_rest, B_rest, A', B', and the rank-1 matrices.
        set A_rest : Matrix (Fin k) (Fin k) ℝ :=
          fun i j => A i.succ j.succ with hA_rest_def
        set B_rest : Matrix (Fin k) (Fin k) ℝ :=
          fun i j => B i.succ j.succ with hB_rest_def
        set αA : Fin k → ℝ := fun i => A i.succ 0 with hαA_def
        set αB : Fin k → ℝ := fun i => B i.succ 0 with hαB_def
        -- By symmetry, A 0 j.succ = αA j and B 0 j.succ = αB j.
        have hsymA : ∀ a b, A a b = A b a := fun a b => by
          have := congr_fun (congr_fun hA.isHermitian b) a
          simpa using this
        have hsymB : ∀ a b, B a b = B b a := fun a b => by
          have := congr_fun (congr_fun hB.isHermitian b) a
          simpa using this
        have hαA_alt : ∀ j, A 0 j.succ = αA j := fun j => hsymA 0 j.succ
        have hαB_alt : ∀ j, B 0 j.succ = αB j := fun j => hsymB 0 j.succ
        set A' : Matrix (Fin k) (Fin k) ℝ :=
          fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / a with hA'_def
        set B' : Matrix (Fin k) (Fin k) ℝ :=
          fun i j => B i.succ j.succ - B i.succ 0 * B 0 j.succ / b with hB'_def
        have hA'_PSD : A'.PosSemidef := schur_complement_psd_scalar hA ha_pos
        have hB'_PSD : B'.PosSemidef := schur_complement_psd_scalar hB hb_pos
        have hB_rest_PSD : B_rest.PosSemidef := hB.submatrix Fin.succ
        -- Rank-1 scaled by 1/a is PSD.
        have hαAαA_PSD : (a⁻¹ • Matrix.vecMulVec αA αA).PosSemidef :=
          posSemidef_smul_vecMulVec_self αA ha_pos
        -- Schur complement of A ⊙ B (using (A ⊙ B) 0 0 as the divisor).
        set M_AB : Matrix (Fin k) (Fin k) ℝ :=
          fun i j => (A ⊙ B) i.succ j.succ
                   - (A ⊙ B) i.succ 0 * (A ⊙ B) 0 j.succ / ((A ⊙ B) 0 0)
          with hM_AB_def
        have hAB_top : (A ⊙ B) 0 0 = a * b := by
          simp [Matrix.hadamard_apply, ha_def, hb_def]
        have hAB_top_ne : (A ⊙ B) 0 0 ≠ 0 := by rw [hAB_top]; exact hab_ne
        -- Identity: M_AB = A' ⊙ B_rest + (a⁻¹ • vecMulVec αA αA) ⊙ B'
        have hM_AB_eq : M_AB = A' ⊙ B_rest + (a⁻¹ • Matrix.vecMulVec αA αA) ⊙ B' := by
          ext i j
          simp only [hM_AB_def, hA'_def, hB'_def, hB_rest_def, hαA_def,
                     Matrix.hadamard_apply, Matrix.add_apply,
                     Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
          rw [ha_def, hb_def, hsymA j.succ 0]
          field_simp
          ring
        -- Both terms in the sum are PSD.
        have hAB1_PSD : (A' ⊙ B_rest).PosSemidef := hA'_PSD.hadamard hB_rest_PSD
        have hAB2_PSD : ((a⁻¹ • Matrix.vecMulVec αA αA) ⊙ B').PosSemidef :=
          hαAαA_PSD.hadamard hB'_PSD
        -- det monotonicity: det(A' ⊙ B_rest) ≤ det(M_AB)
        have hdet_mono : (A' ⊙ B_rest).det ≤ M_AB.det := by
          rw [hM_AB_eq]
          exact det_le_det_add_of_posSemidef hAB1_PSD hAB2_PSD
        -- IH on A' and B_rest:
        have hih : A'.det * ∏ i, B_rest i i ≤ (A' ⊙ B_rest).det := ih hA'_PSD hB_rest_PSD
        have hih_chain : A'.det * ∏ i, B_rest i i ≤ M_AB.det := le_trans hih hdet_mono
        -- A.det = a * det A'
        have hdetA : A.det = a * A'.det := det_eq_topLeft_mul_schur A ha_ne
        -- (A⊙B).det = (A⊙B) 0 0 * det M_AB = (a*b) * det M_AB
        have hdetAB : (A ⊙ B).det = a * b * M_AB.det := by
          have h := det_eq_topLeft_mul_schur (A ⊙ B) hAB_top_ne
          rw [hAB_top] at h
          exact h
        -- ∏ i, B i i = b * ∏ i, B_rest i i
        have hprodB : ∏ i, B i i = b * ∏ i, B_rest i i := by
          rw [Fin.prod_univ_succ]
        -- Main calc
        calc A.det * ∏ i, B i i
            = (a * A'.det) * (b * ∏ i, B_rest i i) := by rw [hdetA, hprodB]
          _ = a * b * (A'.det * ∏ i, B_rest i i) := by ring
          _ ≤ a * b * M_AB.det := mul_le_mul_of_nonneg_left hih_chain hab_pos.le
          _ = (A ⊙ B).det := hdetAB.symm

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  -- Transport via Fintype.equivFin n.
  let e := Fintype.equivFin n
  let A' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ := A.submatrix e.symm e.symm
  let B' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ := B.submatrix e.symm e.symm
  have hA' : A'.PosSemidef := hA.submatrix _
  have hB' : B'.PosSemidef := hB.submatrix _
  have hAB' : A' ⊙ B' = (A ⊙ B).submatrix e.symm e.symm := by
    rw [Matrix.submatrix_hadamard]
  have hdetA : A'.det = A.det := Matrix.det_submatrix_equiv_self e.symm A
  have hdetB : (A' ⊙ B').det = (A ⊙ B).det := by
    rw [hAB', Matrix.det_submatrix_equiv_self]
  have hprod : ∏ i, B' i i = ∏ i, B i i := by
    show ∏ i, B (e.symm i) (e.symm i) = ∏ i, B i i
    exact Equiv.prod_comp e.symm (fun i => B i i)
  have := oppenheim_fin (Fintype.card n) hA' hB'
  rw [hdetA, hprod, hdetB] at this
  exact this

end Submission
