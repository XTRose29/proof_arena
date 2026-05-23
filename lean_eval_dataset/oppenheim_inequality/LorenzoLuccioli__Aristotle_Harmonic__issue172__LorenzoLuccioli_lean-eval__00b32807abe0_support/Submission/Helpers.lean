import Mathlib

open scoped MatrixOrder Matrix
open Matrix Finset

namespace Submission.Helpers

/-! ## Schur complement and helper lemmas for Oppenheim inequality -/

/-
Hadamard product of symmetric matrices is symmetric.
-/
lemma hadamard_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊙ B).IsHermitian := by
  ext i j; simp +decide [ *, Matrix.mul_apply ] ;
  exact congr_arg₂ _ ( congr_fun ( congr_fun hA i ) j ) ( congr_fun ( congr_fun hB i ) j )

/-
Schur product theorem: the Hadamard product of two PSD matrices is PSD.
-/
lemma hadamard_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef :=
  hA.hadamard hB

/-- The Schur complement of a (n+1)×(n+1) matrix at position (0,0). -/
noncomputable def schurCompl {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M (Fin.succ i) (Fin.succ j) - M (Fin.succ i) 0 * (M 0 0)⁻¹ * M 0 (Fin.succ j)

/-
Product of diagonal entries splits along Fin.succ.
-/
lemma prod_diag_fin_succ {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ∏ i, M i i = M 0 0 * ∏ i : Fin n, M (Fin.succ i) (Fin.succ i) := by
  exact Fin.prod_univ_succ _

/-
Hadamard product commutes with submatrix Fin.succ.
-/
lemma hadamard_submatrix_succ {n : ℕ} (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (A ⊙ B).submatrix Fin.succ Fin.succ =
    A.submatrix Fin.succ Fin.succ ⊙ B.submatrix Fin.succ Fin.succ := by
  ext i j; aesop

/-
Principal submatrix of PSD matrix is PSD.
-/
lemma posSemidef_submatrix_succ {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hM : M.PosSemidef) : (M.submatrix Fin.succ Fin.succ).PosSemidef := by
  exact hM.submatrix _

/-
For a PSD matrix, if a diagonal entry is zero, the entire row is zero.
-/
lemma psd_zero_diag_zero_row {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hM : M.PosSemidef) (h0 : M 0 0 = 0) : ∀ j, M 0 j = 0 := by
  intro j;
  have := hM.2;
  have := this ( Finsupp.single 0 1 + Finsupp.single j 1 ) ; simp_all +decide [ Finsupp.sum_add_index', add_mul, mul_add ];
  have := hM.2 ( Finsupp.single 0 1 - Finsupp.single j 1 ) ; simp_all +decide [ Finsupp.sum_sub_index, sub_mul, mul_sub ];
  have := hM.2 ( Finsupp.single 0 1 - Finsupp.single j ( M 0 j / M j j ) ) ; by_cases hj : M j j = 0 <;> simp_all +decide [ Finsupp.sum_sub_index, sub_mul, mul_sub ];
  · have := hM.1; simp_all +decide [ Matrix.IsHermitian, Matrix.mulVec ];
    replace this := congr_fun ( congr_fun this 0 ) j; norm_num at this; linarith;
  · have h_symm : M j 0 = M 0 j := by
      exact hM.1.apply _ _ ▸ rfl;
    cases lt_or_gt_of_ne hj <;> nlinarith [ mul_div_cancel₀ ( M 0 j ) hj ]

/-
For a PSD matrix, if a diagonal entry is zero, the entire column is zero.
-/
lemma psd_zero_diag_zero_col {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hM : M.PosSemidef) (h0 : M 0 0 = 0) : ∀ i, M i 0 = 0 := by
  have := hM.1;
  exact fun i => this.apply i 0 ▸ psd_zero_diag_zero_row hM h0 i

/-
For a PSD matrix, if the (0,0) entry is zero then the determinant is zero.
-/
lemma psd_zero_diag_det_zero {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hM : M.PosSemidef) (h0 : M 0 0 = 0) : M.det = 0 := by
  exact Matrix.det_eq_zero_of_row_eq_zero 0 fun i => by simpa [ h0 ] using psd_zero_diag_zero_row hM h0 i;

/-
The determinant of a matrix equals the pivot times the determinant of the Schur complement.
-/
lemma det_eq_mul_det_schurCompl {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 * (schurCompl M).det := by
  -- Define the matrix M' obtained by row reduction.
  set M' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of (fun i j => if i = 0 then M i j else M i j - M i 0 * (M 0 0)⁻¹ * M 0 j);
  -- By definition of $M'$, we have $\det(M') = \det(M)$.
  have h_det_M' : M'.det = M.det := by
    -- By definition of $M'$, we can write it as $M' = E \cdot M$, where $E$ is an elementary matrix.
    have hM'_eq_EM : ∃ E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, E.det = 1 ∧ M' = E * M := by
      refine' ⟨ Matrix.of fun i j => if i = 0 then if j = 0 then 1 else 0 else if j = 0 then -M i 0 * ( M 0 0 ) ⁻¹ else if i = j then 1 else 0, _, _ ⟩;
      · rw [ ← Matrix.det_transpose, Matrix.det_of_upperTriangular ];
        · aesop;
        · intro i j hij; aesop;
      · ext i j; simp +decide [ Matrix.mul_apply, Finset.sum_ite ] ;
        simp +zetaDelta at *;
        split_ifs <;> simp_all +decide [ Finset.sum_filter ] ; ring;
    aesop;
  rw [ ← h_det_M', Matrix.det_succ_column_zero ];
  rw [ Fin.sum_univ_succ ] ; aesop

/-
The Schur complement of a PSD matrix (with positive pivot) is PSD.
-/
lemma schurCompl_posSemidef {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hM : M.PosSemidef) (h : 0 < M 0 0) : (schurCompl M).PosSemidef := by
  constructor;
  · ext i j; simp +decide [ schurCompl ] ; ring;
    have := hM.1; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_apply ];
    rw [ ← Matrix.ext_iff ] at this; have := this ( Fin.succ i ) ( Fin.succ j ) ; have := this; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ; ring;
  · intro x;
    -- Define y : Fin (n+1) → ℝ by y 0 = -(M 0 0)⁻¹ * ∑ i, M 0 (succ i) * x i and y (succ i) = x i.
    set y : Fin (n + 1) → ℝ := fun i => if hi : i = 0 then -(M 0 0)⁻¹ * ∑ i, M 0 (Fin.succ i) * x i else x (Fin.pred i hi);
    -- Then star y ⬝ᵥ M *ᵥ y = star x ⬝ᵥ (schurCompl M) *ᵥ x (by direct calculation).
    have h_y_M_y : ∑ i, ∑ j, y i * M i j * y j = ∑ i, ∑ j, x i * (schurCompl M i j) * x j := by
      simp +zetaDelta at *;
      simp +decide [ Fin.sum_univ_succ, schurCompl ];
      simp +decide [ Finset.sum_add_distrib, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, h.ne' ] ; ring;
    -- Since M is PSD, star y ⬝ᵥ M *ᵥ y ≥ 0, so star x ⬝ᵥ (schurCompl M) *ᵥ x ≥ 0.
    have h_y_M_y_nonneg : 0 ≤ ∑ i, ∑ j, y i * M i j * y j := by
      have := hM.2;
      convert this ( Finsupp.equivFunOnFinite.symm y ) using 1 ; simp +decide [ Finsupp.sum_fintype ];
    simp_all +decide [ Finsupp.sum_fintype ]

/-
The difference schurCompl(A⊙B) - schurCompl(A)⊙B_sub equals
    a⁻¹ • (vecMulVec p p ⊙ schurCompl B) where p i = A (succ i) 0.
-/
lemma schurCompl_hadamard_diff {n : ℕ} {A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (ha : 0 < A 0 0) (hb : 0 < B 0 0) :
    schurCompl (A ⊙ B) - schurCompl A ⊙ B.submatrix Fin.succ Fin.succ =
    (A 0 0)⁻¹ • (vecMulVec (fun i => A (Fin.succ i) 0) (fun i => A 0 (Fin.succ i)) ⊙
      schurCompl B) := by
  ext i j; simp +decide [ schurCompl, vecMulVec ] ; ring;

/-
vecMulVec v v is positive semidefinite.
-/
lemma vecMulVec_self_posSemidef {m : ℕ} (v : Fin m → ℝ) :
    (vecMulVec v v).PosSemidef := by
  constructor;
  · ext i j; simp +decide [ mul_comm ] ;
    exact mul_comm _ _;
  · intro x
    simp [vecMulVec];
    -- The double sum can be rewritten as the square of a single sum, which is non-negative.
    have h_square : ∑ i, ∑ j, x i * (v i * v j) * x j = (∑ i, x i * v i) ^ 2 := by
      simp +decide only [mul_comm, mul_left_comm, pow_two, Finset.mul_sum _ _ _];
      ac_rfl;
    simp_all +decide [ Finsupp.sum_fintype ];
    positivity

/-
Key inequality: the Schur complement of A ⊙ B dominates
(Schur complement of A) ⊙ (submatrix of B) in the PSD order.
-/
lemma schurCompl_hadamard_le {n : ℕ} {A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (ha : 0 < A 0 0) (hb : 0 < B 0 0) :
    schurCompl A ⊙ B.submatrix Fin.succ Fin.succ ≤ schurCompl (A ⊙ B) := by
  -- The difference is PSD
  have h_diff : schurCompl (A ⊙ B) - schurCompl A ⊙ B.submatrix Fin.succ Fin.succ =
      (A 0 0)⁻¹ • (vecMulVec (fun i => A (Fin.succ i) 0) (fun i => A 0 (Fin.succ i)) ⊙ schurCompl B) :=
    schurCompl_hadamard_diff hA hB ha hb
  -- Since A is Hermitian, vecMulVec p q = vecMulVec p p where p i = A(si)(0), q j = A(0)(sj)
  have h_pq : vecMulVec (fun i => A (Fin.succ i) 0) (fun i => A 0 (Fin.succ i)) =
      vecMulVec (fun i => A (Fin.succ i) 0) (fun i => A (Fin.succ i) 0) := by
    ext i j; simp [vecMulVec]; left; exact hA.1.apply _ _ ▸ rfl
  have h_psd_diff : (schurCompl (A ⊙ B) - schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).PosSemidef := by
    rw [h_diff, h_pq]
    exact ((hadamard_posSemidef (vecMulVec_self_posSemidef _) (schurCompl_posSemidef hB hb)).smul (inv_nonneg.mpr ha.le))
  exact Matrix.le_iff.mpr h_psd_diff

/-
Determinant monotonicity: if A ≤ B in PSD order and B is PSD and A is Hermitian,
    then det(A) ≤ det(B).
-/
lemma det_le_det_of_posSemidef {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hle : A ≤ B) :
    A.det ≤ B.det := by
  by_contra h_contra;
  -- Since $A$ is strictly positive definite, we can write $B = A + C$ where $C$ is positive semidefinite.
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin m) (Fin m) ℝ, B = A + C ∧ C.PosSemidef := by
    exact ⟨ B - A, by rw [ add_sub_cancel ], by simpa using hle ⟩;
  -- Since $A$ is positive definite, we can write $A = L L^T$ where $L$ is invertible.
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin m) (Fin m) ℝ, A = L * L.transpose ∧ L.det ≠ 0 := by
    have hL : ∃ L : Matrix (Fin m) (Fin m) ℝ, A = L * L.transpose := by
      have := Matrix.IsHermitian.spectral_theorem hA.1;
      use (hA.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal (fun i => Real.sqrt (hA.1.eigenvalues i));
      convert this using 1;
      ext i j; simp +decide [ Matrix.mul_apply, Matrix.diagonal ] ; ring;
      exact Finset.sum_congr rfl fun _ _ => by rw [ Real.sq_sqrt ( hA.eigenvalues_nonneg _ ) ] ;

















    obtain ⟨ L, rfl ⟩ := hL; use L; simp_all +decide [ Matrix.det_mul ] ;
    nlinarith [ show 0 ≤ ( L * Lᵀ + C |> Matrix.det ) from hB.det_nonneg ];
  -- Since $C$ is positive semidefinite, we can write $C = L D L^T$ where $D$ is positive semidefinite.
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin m) (Fin m) ℝ, C = L * D * L.transpose ∧ D.PosSemidef := by
    refine' ⟨ L⁻¹ * C * ( L⁻¹ ) ᵀ, _, _ ⟩ <;> simp_all +decide [ Matrix.mul_assoc, isUnit_iff_ne_zero ];
    · simp +decide [ Matrix.transpose_nonsing_inv, hL.2 ];
    · convert hC.2.conjTranspose_mul_mul_same ( L⁻¹ᵀ ) using 1 ; simp +decide [ Matrix.mul_assoc, Matrix.transpose_nonsing_inv ];
  -- Since $D$ is positive semidefinite, we have $\det(I + D) \geq 1$.
  have h_det_D : Matrix.det (1 + D) ≥ 1 := by
    -- Since $D$ is positive semidefinite, we can write $D = Q \Lambda Q^T$ where $Q$ is orthogonal and $\Lambda$ is diagonal with non-negative entries.
    obtain ⟨Q, Λ, hQ, hΛ⟩ : ∃ Q : Matrix (Fin m) (Fin m) ℝ, ∃ Λ : Fin m → ℝ, Q.transpose * Q = 1 ∧ D = Q * Matrix.diagonal Λ * Q.transpose ∧ ∀ i, 0 ≤ Λ i := by
      have := hD.2.1.spectral_theorem;
      refine' ⟨ _, _, _, this, _ ⟩;
      · exact Units.mul_eq_one_iff_eq_inv.mpr rfl;
      · exact fun i => hD.2.eigenvalues_nonneg i;
    -- Since $Q$ is orthogonal, we have $\det(1 + D) = \det(1 + Q \Lambda Q^T) = \det(Q (1 + \Lambda) Q^T) = \det(1 + \Lambda)$.
    have h_det_Q : Matrix.det (1 + D) = Matrix.det (1 + Matrix.diagonal Λ) := by
      have h_det_Q : Matrix.det (1 + D) = Matrix.det (Q * (1 + Matrix.diagonal Λ) * Q.transpose) := by
        simp +decide [ hΛ, mul_add, add_mul, mul_assoc, hQ ];
        rw [ mul_eq_one_comm.mp hQ ];
      simp_all +decide [ Matrix.det_mul ];
      have := congr_arg Matrix.det hQ; norm_num at this; rw [ mul_right_comm ] ; aesop;
    rw [ h_det_Q, Matrix.det_of_upperTriangular ] <;> norm_num [ Matrix.diagonal ];
    · exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun _ _ => le_add_of_nonneg_right ( hΛ.2 _ ) );
    · intro i j hij; aesop;
  simp_all +decide [ mul_assoc, Matrix.det_mul ];
  rw [ show L * Lᵀ + L * ( D * Lᵀ ) = L * ( 1 + D ) * Lᵀ by simp +decide [ mul_add, add_mul, mul_assoc ] ] at h_contra ; simp_all +decide [ Matrix.det_mul ];
  nlinarith [ mul_self_pos.mpr hL.2 ]

/-
PSD diagonal entries are nonneg.
-/
lemma psd_diag_nonneg {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℝ} (hM : M.PosSemidef) (i : m) : 0 ≤ M i i := by
  have := hM.2;
  specialize this ( Finsupp.single i 1 ) ; aesop

/-- Oppenheim inequality for Fin n. -/
lemma oppenheim_fin : ∀ n : ℕ, ∀ A B : Matrix (Fin n) (Fin n) ℝ,
    A.PosSemidef → B.PosSemidef → A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  intro n
  induction n with
  | zero => intro A B _ _; simp [Matrix.det_fin_zero]
  | succ n ih =>
    intro A B hA hB
    -- Get that diagonal entries are nonneg
    have ha_nn : 0 ≤ A 0 0 := psd_diag_nonneg hA 0
    have hb_nn : 0 ≤ B 0 0 := psd_diag_nonneg hB 0
    -- Case split on whether A 0 0 = 0
    by_cases ha : A 0 0 = 0
    · -- A 0 0 = 0, so det A = 0, LHS = 0 ≤ det(A⊙B)
      rw [psd_zero_diag_det_zero hA ha, zero_mul]
      exact (hadamard_posSemidef hA hB).det_nonneg
    · by_cases hb : B 0 0 = 0
      · -- B 0 0 = 0, so ∏ B i i = 0, LHS = 0 ≤ det(A⊙B)
        rw [prod_diag_fin_succ, hb, zero_mul, mul_zero]
        exact (hadamard_posSemidef hA hB).det_nonneg
      · -- Both A 0 0 > 0 and B 0 0 > 0
        have ha_pos : 0 < A 0 0 := lt_of_le_of_ne ha_nn (Ne.symm ha)
        have hb_pos : 0 < B 0 0 := lt_of_le_of_ne hb_nn (Ne.symm hb)
        -- Schur complement facts
        have hSA := schurCompl_posSemidef hA ha_pos
        have hBsub := posSemidef_submatrix_succ hB
        -- Rewrite determinants using Schur complement
        rw [det_eq_mul_det_schurCompl A ha]
        rw [prod_diag_fin_succ]
        -- Now LHS = A 0 0 * det(SA) * (B 0 0 * ∏ B(si)(si))
        -- RHS = det(A ⊙ B)
        -- Hadamard product pivot
        have hab : (A ⊙ B) 0 0 = A 0 0 * B 0 0 := rfl
        have hab_ne : (A ⊙ B) 0 0 ≠ 0 := by rw [hab]; exact mul_ne_zero ha hb
        rw [det_eq_mul_det_schurCompl (A ⊙ B) hab_ne, hab]
        -- Now need: A 0 0 * det(SA) * (B 0 0 * ∏ B(si)(si)) ≤ A 0 0 * B 0 0 * det(S(A⊙B))
        -- Rearrange: suffices det(SA) * ∏ B(si)(si) ≤ det(S(A⊙B))
        -- since A 0 0 * B 0 0 > 0
        have hab_pos : 0 < A 0 0 * B 0 0 := mul_pos ha_pos hb_pos
        rw [show A 0 0 * (schurCompl A).det * (B 0 0 * ∏ i : Fin n, B (Fin.succ i) (Fin.succ i)) =
              A 0 0 * B 0 0 * ((schurCompl A).det * ∏ i : Fin n, B (Fin.succ i) (Fin.succ i))
          from by ring]
        apply mul_le_mul_of_nonneg_left _ hab_pos.le
        -- Need: det(SA) * ∏ B(si)(si) ≤ det(S(A⊙B))
        -- Step 1: By IH, det(SA) * ∏ B(si)(si) ≤ det(SA ⊙ B_sub)
        have step1 : (schurCompl A).det * ∏ i : Fin n, B (Fin.succ i) (Fin.succ i) ≤
            (schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).det := by
          exact ih _ _ hSA hBsub
        -- Step 2: SA ⊙ B_sub ≤ S(A⊙B) in PSD order
        have step2 : schurCompl A ⊙ B.submatrix Fin.succ Fin.succ ≤ schurCompl (A ⊙ B) :=
          schurCompl_hadamard_le hA hB ha_pos hb_pos
        -- Step 3: Determinant monotonicity
        have hSAB_psd : (schurCompl (A ⊙ B)).PosSemidef :=
          schurCompl_posSemidef (hadamard_posSemidef hA hB) (by rw [hab]; exact hab_pos)
        have hSAB_sub_herm : (schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).IsHermitian :=
          (hadamard_posSemidef hSA hBsub).1
        have step3 : (schurCompl A ⊙ B.submatrix Fin.succ Fin.succ).det ≤
            (schurCompl (A ⊙ B)).det :=
          det_le_det_of_posSemidef (hadamard_posSemidef hSA hBsub) hSAB_psd step2
        linarith

/-
Transfer: Oppenheim inequality for arbitrary Fintype.
-/
theorem oppenheim_general {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  -- By the properties of the determinant and the Schur complement, we can reduce the problem to the case where $n = 1$.
  have h_det_schur : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ), A.PosSemidef → B.PosSemidef → A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
    exact fun n A B a a_1 => oppenheim_fin n A B a a_1;
  -- Since $n$ is a finite type, we can use the fact that there's an equivalence between $n$ and $\text{Fin}(\text{Fintype.card } n)$.
  obtain ⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card n), True := by
    exact ⟨ Fintype.equivFin n, trivial ⟩;
  convert h_det_schur ( Fintype.card n ) ( Matrix.reindex e e A ) ( Matrix.reindex e e B ) _ _ using 1 <;> simp +decide [ Matrix.det_reindex_self ];
  · exact Or.inl ( by rw [ ← Equiv.prod_comp e.symm ] );
  · convert Matrix.det_reindex_self e.symm _ using 2 ; aesop;
  · exact hA;
  · exact hB

end Submission.Helpers