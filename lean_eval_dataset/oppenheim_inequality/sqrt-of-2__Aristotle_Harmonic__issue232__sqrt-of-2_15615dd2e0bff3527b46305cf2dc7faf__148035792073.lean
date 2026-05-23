/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: oppenheim_inequality
user: sqrt-of-2
model: Aristotle (Harmonic)
submission_repo: sqrt-of-2/15615dd2e0bff3527b46305cf2dc7faf
submission_ref: 148035792073a26034e8b165c6ee886369062fe8
issue_number: 232
-/
import Mathlib

open MatrixOrder Matrix Finset

namespace Submission

/-! ## Helper lemmas for Oppenheim's inequality -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-
Hadamard product commutes with submatrix extraction
-/
lemma hadamard_submatrix {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix n n ℝ) (f : m → n) :
    (A ⊙ B).submatrix f f = (A.submatrix f f) ⊙ (B.submatrix f f) := by
  ext i j; simp [Matrix.hadamard_apply, Matrix.submatrix_apply]

/-
If A is PSD and A i i = 0, then row i (and column i) of A is zero
-/
lemma PosSemidef.entry_eq_zero_of_diag_zero
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {i : n} (hi : A i i = 0) (j : n) :
    A i j = 0 := by
  by_contra h_neq;
  -- Consider the quadratic form $(e_i + t e_j)^T A (e_i + t e_j)$ for any $t \in \mathbb{R}$.
  have h_quad_form : ∀ t : ℝ, (t ^ 2 * A j j + 2 * t * A i j + A i i) ≥ 0 := by
    intro t
    have h_quad_form : ∀ x : n → ℝ, (∑ k, ∑ l, x k * A k l * x l) ≥ 0 := by
      intro x;
      have := hA.2;
      simpa [ Finsupp.sum_fintype ] using this ( Finsupp.equivFunOnFinite.symm x );
    convert h_quad_form ( fun k => if k = i then 1 else if k = j then t else 0 ) using 1 ; simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ; ring;
    by_cases hij : j = i <;> simp +decide [ Finset.sum_add_distrib, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', * ] ; ring;
    rw [ show A j i = A i j by simpa [ eq_comm ] using congr_fun ( congr_fun hA.1 j ) i ] ; ring;
  -- Since $A$ is positive semidefinite, $A j j \geq 0$.
  have h_Ajj_nonneg : A j j ≥ 0 := by
    simpa using h_quad_form 1 |> fun h => by linarith [ h_quad_form ( -1 ) ] ;
  cases lt_or_eq_of_le h_Ajj_nonneg <;> simp_all +decide;
  · exact h_neq ( by nlinarith [ h_quad_form ( -A i j / A j j ), mul_div_cancel₀ ( -A i j ) ( ne_of_gt ‹_› ) ] );
  · exact h_neq ( by nlinarith [ h_quad_form ( -1 ), h_quad_form 1 ] )

/-
Product of diagonal entries of a PSD matrix is non-negative
-/
lemma PosSemidef.prod_diag_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    0 ≤ ∏ i, A i i := by
  -- Each diagonal entry A i i of a PSD matrix is non-negative.
  have h_diag_nonneg : ∀ i, 0 ≤ A i i := by
    exact fun i => PosSemidef.diag_nonneg hA
  exact Finset.prod_nonneg (fun i _ => h_diag_nonneg i)

/-
Transfer of Oppenheim inequality along equivalences
-/
lemma oppenheim_of_equiv {m : Type*} [Fintype m] [DecidableEq m]
    (e : n ≃ m)
    (h : ∀ (A B : Matrix m m ℝ), A.PosSemidef → B.PosSemidef →
      A.det * ∏ i, B i i ≤ (A ⊙ B).det)
    (A B : Matrix n n ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  convert h ( Matrix.reindex e e A ) ( Matrix.reindex e e B ) ( ?_ ) ( ?_ ) using 1 <;> norm_num [ Matrix.reindex_apply ];
  · exact Or.inl ( by rw [ ← Equiv.prod_comp e.symm ] );
  · convert Matrix.det_reindex_self e.symm _ using 2 ; aesop;
  · exact hA;
  · exact hB

/-! ## Schur complement infrastructure for Fin (n+1) matrices -/

/-- The Schur complement of the (0,0) entry for a matrix over Fin (n+1).
  SC(M) = M[1:,1:] - (1/M₀₀) * v * vᵀ where v_i = M_{i+1,0}. -/
noncomputable def schurCompl {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  M.submatrix Fin.succ Fin.succ -
    (M 0 0)⁻¹ • Matrix.vecMulVec (fun i => M (Fin.succ i) 0) (fun j => M 0 (Fin.succ j))

/-
The determinant of a matrix over Fin (n+1) equals M₀₀ * det(Schur complement)
    when M₀₀ ≠ 0.
-/
lemma det_eq_corner_mul_schurCompl_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 * (schurCompl M).det := by
  -- Let $e := finSumFinEquiv : Fin 1 ⊕ Fin n ≃ Fin (n+1)$.
  let e := Equiv.ofBijective (fun i : Fin 1 ⊕ Fin n => i.elim (fun _ => 0) (Fin.succ)) (by
  constructor;
  · rintro ( _ | i ) ( _ | j ) <;> simp +decide [ Fin.ext_iff ];
  · intro i; induction i using Fin.inductionOn <;> aesop;)
  generalize_proofs at *;
  -- Apply the block matrix determinant formula.
  have h_det : Matrix.det (M.submatrix e e) = Matrix.det (Matrix.of ![![M 0 0]]) * Matrix.det (schurCompl M) := by
    have h_block : Matrix.det (Matrix.fromBlocks (Matrix.of ![![M 0 0]]) (Matrix.of (fun i j => M 0 (Fin.succ j))) (Matrix.of (fun i j => M (Fin.succ i) 0)) (M.submatrix Fin.succ Fin.succ)) = Matrix.det (Matrix.of ![![M 0 0]]) * Matrix.det (schurCompl M) := by
      convert Matrix.det_fromBlocks₁₁ _ _ _ _ using 1;
      congr! 2;
      ext i j; simp +decide [ Matrix.mul_apply, Matrix.inv_def ] ; ring;
      · unfold schurCompl; simp +decide [ Matrix.vecMulVec, Matrix.mul_apply ] ; ring;
      · exact ⟨ !![ ( M 0 0 ) ⁻¹ ], by ext i j; fin_cases i ; fin_cases j ; simp +decide [ h ], by ext i j; fin_cases i ; fin_cases j ; simp +decide [ h ] ⟩;
    convert h_block using 2;
    ext i j; rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> aesop;
  simp +zetaDelta at *;
  exact h_det

/-
The Schur complement of a PSD matrix (with positive corner entry) is PSD.
-/
lemma schurCompl_posSemidef {n : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hM : M.PosSemidef) (h : 0 < M 0 0) :
    (schurCompl M).PosSemidef := by
  constructor <;> norm_num [ schurCompl ] at *;
  · ext i j; simp +decide [ Matrix.IsHermitian, Matrix.submatrix, Matrix.vecMulVec ] ; ring;
    have := hM.1; simp_all +decide [ Matrix.IsHermitian, mul_comm ] ; ring;
    rw [ ← Matrix.ext_iff ] at this; have := this ( Fin.succ i ) ( Fin.succ j ) ; have := this; have := this; simp_all +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  · intro x
    have h_pos_semidef : ∀ (x : Fin (n + 1) → ℝ), 0 ≤ ∑ i, ∑ j, x i * M i j * x j := by
      have := hM.2;
      intro x; specialize this ( Finsupp.equivFunOnFinite.symm x ) ; simp_all +decide [ Finsupp.sum_fintype ] ;
    convert h_pos_semidef ( Fin.cons ( - ( ∑ i, x i * M ( Fin.succ i ) 0 ) / M 0 0 ) x ) using 1 ; simp +decide [ Fin.sum_univ_succ, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_inv_mul, h.ne' ] ; ring!;
    simp +decide [ Finsupp.sum_fintype, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, sq, vecMulVec ] ; ring!;
    exact congrArg₂ _ rfl ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) )

/-
Product of diagonal entries splits as M₀₀ * ∏ M_{i+1,i+1}
-/
lemma prod_diag_succ {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∏ i, M i i = M 0 0 * ∏ i : Fin n, M (Fin.succ i) (Fin.succ i) := by
  rw [ Fin.prod_univ_succ ]

/-- Submatrix of Hadamard product equals Hadamard product of submatrices -/
lemma hadamard_submatrix_succ {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (A ⊙ B).submatrix Fin.succ Fin.succ =
    A.submatrix Fin.succ Fin.succ ⊙ B.submatrix Fin.succ Fin.succ :=
  hadamard_submatrix A B Fin.succ

/-! ## Det monotonicity: det(D + E) ≥ det(D) for PSD D, E -/

/-
Det monotonicity: for PSD D, E, det(D + E) ≥ det(D)

A PD matrix can be factored as Pᵀ * P with P invertible
-/
set_option maxHeartbeats 800000 in
lemma posDef_factor {k : ℕ} {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) :
    ∃ P : Matrix (Fin k) (Fin k) ℝ, D = P.transpose * P ∧ IsUnit P := by
  set U := (hD.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
  set ev := hD.1.eigenvalues
  set P := Matrix.diagonal (fun i => Real.sqrt (ev i)) * U.transpose
  have hDP : D = P.transpose * P := by
    simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _)]
    rw [Matrix.diagonal_mul_diagonal]
    have hsq : (fun i => Real.sqrt (ev i) * Real.sqrt (ev i)) = ev := by
      funext i; exact Real.mul_self_sqrt (le_of_lt (hD.eigenvalues_pos i))
    rw [hsq]
    conv_lhs => rw [hD.1.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Function.id_comp]
    rw [Matrix.mul_assoc]
  refine ⟨P, hDP, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h
  have := hD.det_pos
  rw [hDP, Matrix.det_mul, Matrix.det_transpose, h, mul_zero] at this
  linarith

set_option maxHeartbeats 800000 in
lemma det_add_psd_le {k : ℕ}
    {D E : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosSemidef) (hE : E.PosSemidef) :
    D.det ≤ (D + E).det := by
  -- For positive definite $D$, we have $\det(D + E) \geq \det(D)$.
  have h_det_ineq_posDef (D E : Matrix (Fin k) (Fin k) ℝ) (hD : D.PosDef) (hE : E.PosSemidef) : D.det ≤ (D + E).det := by
    -- Use posDef_factor to get D = Pᵀ * P with P invertible.
    obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin k) (Fin k) ℝ, D = P.transpose * P ∧ IsUnit P := by
      -- Apply the lemma posDef_factor to obtain the existence of P.
      apply posDef_factor hD;
    have h_det_ineq_posDef : 1 ≤ (1 + P⁻¹.transpose * E * P⁻¹).det := by
      have h_det_ineq_posDef : ∀ (F : Matrix (Fin k) (Fin k) ℝ), F.PosSemidef → 1 ≤ (1 + F).det := by
        intro F hF;
        -- Since $F$ is PSD, we can write it as $F = Q \Lambda Q^T$ where $Q$ is orthogonal and $\Lambda$ is diagonal with non-negative entries.
        obtain ⟨Q, Λ, hQ, hΛ⟩ : ∃ Q : Matrix (Fin k) (Fin k) ℝ, ∃ Λ : Fin k → ℝ, Q.transpose * Q = 1 ∧ F = Q * Matrix.diagonal Λ * Q.transpose ∧ ∀ i, 0 ≤ Λ i := by
          have := hF.1.spectral_theorem;
          refine' ⟨ _, _, _, this, _ ⟩;
          · simp +decide [ mul_eq_one_comm ];
            have := hF.1.eigenvectorUnitary.2.2;
            convert this using 1;
          · exact fun i => hF.eigenvalues_nonneg i;
        -- Since $Q$ is orthogonal, we have $\det(1 + F) = \det(1 + Q \Lambda Q^T) = \det(Q (1 + \Lambda) Q^T) = \det(1 + \Lambda)$.
        have h_det_ineq_posDef : (1 + F).det = (1 + Matrix.diagonal Λ).det := by
          have h_det_ineq_posDef : (1 + F).det = (Q * (1 + Matrix.diagonal Λ) * Q.transpose).det := by
            simp +decide [ hΛ, mul_add, add_mul, mul_assoc, hQ ];
            rw [ mul_eq_one_comm.mp hQ ];
          simp_all +decide [ Matrix.det_mul ];
          have := congr_arg Matrix.det hQ; norm_num at this; rw [ mul_right_comm ] ; aesop;
        simp_all +decide [ Matrix.det_fin_two ];
        rw [ show ( 1 + diagonal Λ ) = diagonal ( fun i => 1 + Λ i ) by ext i j; by_cases hi : i = j <;> aesop ] ; rw [ Matrix.det_diagonal ] ; exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun _ _ => le_add_of_nonneg_right <| hΛ.2 _ ) ;
      apply h_det_ineq_posDef;
      convert hE.conjTranspose_mul_mul_same ( P⁻¹ ) using 1;
    have h_det_ineq_posDef : (D + E).det = (P.transpose * (1 + P⁻¹.transpose * E * P⁻¹) * P).det := by
      simp_all +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.transpose_nonsing_inv ];
      cases hP.2.nonempty_invertible ; aesop;
    simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
    nlinarith [ mul_self_pos.mpr hP.2 ];
  -- By continuity of the determinant, we can take the limit as ε approaches 0.
  have h_cont : Filter.Tendsto (fun ε : ℝ => (D + ε • 1).det) (nhdsWithin 0 (Set.Ioi 0)) (nhds (D.det)) ∧ Filter.Tendsto (fun ε : ℝ => ((D + ε • 1) + E).det) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((D + E).det)) := by
    constructor <;> refine' tendsto_nhdsWithin_of_tendsto_nhds _;
    · exact Continuous.tendsto' ( by exact Continuous.matrix_det <| by continuity ) _ _ <| by norm_num;
    · exact Continuous.tendsto' ( by exact Continuous.matrix_det <| by continuity ) _ _ <| by norm_num;
  have h_posDef : ∀ ε : ℝ, 0 < ε → (D + ε • 1).PosDef := by
    intro ε hε;
    constructor;
    · simp_all +decide [ Matrix.IsHermitian, Matrix.PosSemidef ];
    · intro x hx_ne; have := hD.2 x; simp_all +decide [ Matrix.add_apply, Matrix.smul_apply ];
      simp_all +decide [ Matrix.one_apply, mul_add, add_mul, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finsupp.sum_fintype ];
      exact add_pos_of_nonneg_of_pos this ( by rw [ ← Finset.mul_sum _ _ _ ] ; exact mul_pos hε ( lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ( Ne.symm <| by contrapose! hx_ne; ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_self_nonneg ] ) ) );
  exact le_of_tendsto_of_tendsto h_cont.1 h_cont.2 ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_det_ineq_posDef _ _ ( h_posDef ε hε ) hE )

/-!
The Schur complement of the Hadamard product dominates the Hadamard product of
the Schur complements.
-/
set_option maxHeartbeats 800000 in
lemma schurCompl_hadamard_dominates {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hA00 : 0 < A 0 0) (hB00 : 0 < B 0 0) :
    (schurCompl (A ⊙ B) - schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).PosSemidef := by
  refine' ⟨ _, _ ⟩;
  · simp_all +decide [ Matrix.IsHermitian, Matrix.PosSemidef ];
    unfold schurCompl; simp +decide [ Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA.1, hB.1 ] ;
    ext i j; simp +decide [ Matrix.submatrix, Matrix.transpose_apply, Matrix.mul_apply, Matrix.vecMulVec ] ; ring;
    rw [ ← Matrix.ext_iff ] at *;
    simp_all +decide [ Matrix.transpose_apply, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  · intro x
    have h_sum : ∑ i, ∑ j, x i * x j * (schurCompl (A ⊙ B) - schurCompl A ⊙ B.submatrix Fin.succ Fin.succ) i j = ∑ i, ∑ j, x i * x j * (1 / A 0 0) * A (Fin.succ i) 0 * A 0 (Fin.succ j) * (schurCompl B) i j := by
      unfold schurCompl; simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_comm ] ; ring;
      unfold vecMulVec; simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_comm ] ; ring;
      rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; ring;
    -- Since $schurCompl B$ is PSD, we have $\sum_{i,j} x_i x_j (schurCompl B)_{ij} \geq 0$.
    have h_schurCompl_B_nonneg : 0 ≤ ∑ i, ∑ j, (x i * A (Fin.succ i) 0) * (x j * A 0 (Fin.succ j)) * (schurCompl B) i j := by
      have h_schurCompl_B_nonneg : ∀ (y : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, y i * y j * (schurCompl B) i j := by
        have := schurCompl_posSemidef hB hB00;
        have := this.2;
        intro y; specialize this ( Finsupp.equivFunOnFinite.symm y ) ; simp_all +decide [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm ] ;
      convert h_schurCompl_B_nonneg ( fun i => x i * A ( Fin.succ i ) 0 ) using 1;
      have := hA.1; have := hB.1; simp_all +decide [ Matrix.IsHermitian, mul_assoc, mul_comm, mul_left_comm ] ;
      exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ ← Matrix.ext_iff ] at *; aesop;
    simp_all +decide [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    simpa only [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_nonneg ( inv_nonneg.2 hA00.le ) h_schurCompl_B_nonneg

/-- Oppenheim inequality for Fin k matrices, proved by induction on k -/
lemma oppenheim_fin (k : ℕ) :
    ∀ (A B : Matrix (Fin k) (Fin k) ℝ), A.PosSemidef → B.PosSemidef →
      A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  induction k with
  | zero =>
    intro A B _ _
    simp [Finset.univ_eq_empty]
  | succ n ih =>
    intro A B hA hB
    -- Easy cases
    by_cases hdetA : A.det = 0
    · simp [hdetA]; exact (hA.hadamard hB).det_nonneg
    by_cases hprodB : ∏ i, B i i = 0
    · simp [hprodB]; exact (hA.hadamard hB).det_nonneg
    -- A₀₀ > 0 (det A ≠ 0 implies all diagonal entries positive)
    have hA00 : 0 < A 0 0 := by
      rcases lt_or_eq_of_le (hA.diag_nonneg (i := (0 : Fin (n+1)))) with h | h
      · exact h
      · exfalso; apply hdetA
        have hzero : ∀ j, A 0 j = 0 :=
          PosSemidef.entry_eq_zero_of_diag_zero hA h.symm
        exact Matrix.det_eq_zero_of_row_eq_zero 0 hzero
    -- B₀₀ > 0 (∏ Bᵢᵢ ≠ 0 implies all diagonal entries positive)
    have hB00 : 0 < B 0 0 := by
      rcases lt_or_eq_of_le (hB.diag_nonneg (i := (0 : Fin (n+1)))) with h | h
      · exact h
      · exfalso; apply hprodB
        rw [prod_diag_succ, h.symm, zero_mul]
    -- Schur complement formulas
    rw [det_eq_corner_mul_schurCompl_det A (ne_of_gt hA00)]
    have hab00 : (A ⊙ B) 0 0 = A 0 0 * B 0 0 := by simp [hadamard_apply]
    rw [det_eq_corner_mul_schurCompl_det (A ⊙ B) (by rw [hab00]; positivity)]
    rw [prod_diag_succ B, hab00]
    -- Rearrange: suffices to show key inequality (after dividing by A₀₀*B₀₀ > 0)
    suffices h : (schurCompl A).det * ∏ i : Fin n, B (Fin.succ i) (Fin.succ i) ≤
        (schurCompl (A ⊙ B)).det by
      have hab_pos : 0 < A 0 0 * B 0 0 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt hab_pos)]
    -- Step 1: By IH
    have step1 : (schurCompl A).det * ∏ i : Fin n, B (Fin.succ i) (Fin.succ i) ≤
        (schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).det := by
      exact ih (schurCompl A) (B.submatrix Fin.succ Fin.succ)
        (schurCompl_posSemidef hA hA00) (hB.submatrix Fin.succ)
    -- Step 2: By det monotonicity
    have step2 : (schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).det ≤
        (schurCompl (A ⊙ B)).det := by
      have hSAB := schurCompl_hadamard_dominates hA hB hA00 hB00
      have hSAB' := (schurCompl_posSemidef hA hA00).hadamard (hB.submatrix Fin.succ)
      have : schurCompl (A ⊙ B) =
        schurCompl A ⊙ B.submatrix Fin.succ Fin.succ +
        (schurCompl (A ⊙ B) - schurCompl A ⊙ B.submatrix Fin.succ Fin.succ) := by
        simp [add_sub_cancel]
      rw [this]
      exact det_add_psd_le hSAB' hSAB
    linarith

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  exact oppenheim_of_equiv (Fintype.equivFin n)
    (fun A B hA hB => oppenheim_fin _ A B hA hB) A B hA hB

end Submission
