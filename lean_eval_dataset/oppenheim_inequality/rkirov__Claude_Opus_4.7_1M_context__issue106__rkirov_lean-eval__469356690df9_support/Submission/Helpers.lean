import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Matrix MatrixOrder

namespace Submission.Helpers

/-- The outer product of a Hadamard product factors as a Hadamard of outer products. -/
lemma vecMulVec_hadamard_eq {n : Type*} (u v : n → ℝ) :
    Matrix.vecMulVec (u * v) (u * v) =
      Matrix.vecMulVec u u ⊙ Matrix.vecMulVec v v := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.hadamard_apply, Pi.mul_apply]
  ring

/-- For PSD matrices over ℝ, a zero diagonal entry forces the corresponding row to be zero. -/
lemma posSemidef_row_zero_of_diag_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {i : n} (hii : A i i = 0) (j : n) :
    A i j = 0 := by
  have hAvec : A *ᵥ (Pi.single i (1 : ℝ)) = 0 := by
    refine (hA.dotProduct_mulVec_zero_iff (Pi.single i 1)).mp ?_
    have hstar : (star (Pi.single i (1 : ℝ))) = (Pi.single i 1 : n → ℝ) := by
      ext k; simp [Pi.star_apply, Pi.single_apply]
    rw [hstar, Matrix.mulVec_single_one]
    simp [dotProduct, Matrix.col_apply, Pi.single_apply, hii]
  have hcol : A.col i = 0 := by
    rw [← Matrix.mulVec_single_one]; exact hAvec
  -- Now A j i = 0, and A i j = A j i by Hermitianness over ℝ.
  have hji : A j i = 0 := by
    have := congr_fun hcol j
    simpa [Matrix.col_apply] using this
  have hsym : A i j = A j i := by
    have := congr_fun (congr_fun hA.isHermitian j) i
    simpa using this
  rw [hsym, hji]

open Matrix in
/-- For diagonal matrix `1 + diagonal d` with `d_i ≥ 0`, the determinant is ≥ 1. -/
private lemma det_one_add_diagonal_ge_one {m : Type*} [Fintype m] [DecidableEq m]
    {d : m → ℝ} (hd : ∀ i, 0 ≤ d i) :
    1 ≤ ((1 : Matrix m m ℝ) + diagonal d).det := by
  have h1 : (1 : Matrix m m ℝ) = diagonal (fun _ : m => (1 : ℝ)) := diagonal_one.symm
  rw [h1, diagonal_add, det_diagonal]
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := (Finset.prod_const_one).symm
    _ ≤ ∏ i, ((fun _ : m => (1 : ℝ)) + d) i :=
        Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by simpa [Pi.add_apply] using hd i)

open Matrix in
/-- For PSD `R : Matrix m m ℝ`, the determinant of `1 + R` is at least `1`. -/
private lemma det_one_add_psd_ge_one {m : Type*} [Fintype m] [DecidableEq m]
    {R : Matrix m m ℝ} (hR : R.PosSemidef) :
    1 ≤ ((1 : Matrix m m ℝ) + R).det := by
  classical
  have hHerm := hR.isHermitian
  have hd_nonneg : ∀ i, 0 ≤ hHerm.eigenvalues i := hR.eigenvalues_nonneg
  -- Spectral decomposition R = U * diag(d) * star U.
  have hRspec : R = (hHerm.eigenvectorUnitary : Matrix m m ℝ) *
        diagonal hHerm.eigenvalues *
        star (hHerm.eigenvectorUnitary : Matrix m m ℝ) := by
    have h := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hcomp : (RCLike.ofReal ∘ hHerm.eigenvalues : m → ℝ) = hHerm.eigenvalues := by
      funext i; rfl
    rw [hcomp] at h
    exact h
  have hUstar : (hHerm.eigenvectorUnitary : Matrix m m ℝ) *
                star (hHerm.eigenvectorUnitary : Matrix m m ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  -- Bind eigenvalues and unitary to fresh names to avoid `R`-dependent motives.
  set d : m → ℝ := hHerm.eigenvalues with hd_def
  set U : Matrix m m ℝ := (hHerm.eigenvectorUnitary : Matrix m m ℝ) with hU_def
  -- After `set`, `hUstar : U * star U = 1` and `hRspec : R = U * diag d * star U`.
  have hd_nn : ∀ i, 0 ≤ d i := hd_nonneg
  have h1R : (1 : Matrix m m ℝ) + R =
      U * ((1 : Matrix m m ℝ) + diagonal d) * star U := by
    calc (1 : Matrix m m ℝ) + R
        = 1 + U * diagonal d * star U := by rw [hRspec]
      _ = U * star U + U * diagonal d * star U := by rw [hUstar]
      _ = U * 1 * star U + U * diagonal d * star U := by rw [Matrix.mul_one]
      _ = (U * 1 + U * diagonal d) * star U := by rw [Matrix.add_mul]
      _ = U * (1 + diagonal d) * star U := by rw [Matrix.mul_add]
  rw [h1R, det_mul, det_mul]
  have hUdet_sq : U.det * (star U).det = 1 := by
    rw [← det_mul, hUstar, det_one]
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 1 * ((1 : Matrix m m ℝ) + diagonal d).det := by
        gcongr
        exact det_one_add_diagonal_ge_one hd_nn
    _ = (U.det * (star U).det) * ((1 : Matrix m m ℝ) + diagonal d).det := by rw [hUdet_sq]
    _ = U.det * ((1 : Matrix m m ℝ) + diagonal d).det * (star U).det := by ring

open Matrix in
/-- For PSD matrices `M, N : Matrix m m ℝ`, `det M ≤ det (M + N)`. -/
lemma det_le_det_add_of_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {M N : Matrix m m ℝ} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    M.det ≤ (M + N).det := by
  by_cases hPD : M.PosDef
  · -- Case: M PD. Use M^{1/2} factorization.
    set sM : Matrix m m ℝ := CFC.sqrt M with hsM_def
    have hMsqrt_PSD : sM.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
    have hMsqrt_sq : sM * sM = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
    have hMsqrt_PD : sM.PosDef := by
      rw [Matrix.PosSemidef.posDef_iff_isUnit hMsqrt_PSD,
          Matrix.isUnit_iff_isUnit_det, hM.det_sqrt,
          RCLike.sqrt_of_nonneg hM.det_nonneg]
      exact isUnit_iff_ne_zero.mpr (Real.sqrt_pos.mpr hPD.det_pos).ne'
    haveI : Invertible sM := hMsqrt_PD.isUnit.invertible
    -- R := sM⁻¹ * N * sM⁻¹.
    set R : Matrix m m ℝ := sM⁻¹ * N * sM⁻¹ with hR_def
    have hsM_inv_herm : (sM⁻¹ : Matrix m m ℝ).IsHermitian := by
      show ((CFC.sqrt M)⁻¹ : Matrix m m ℝ).IsHermitian
      rw [Matrix.PosSemidef.inv_sqrt hM]
      exact (CFC.sqrt_nonneg _).posSemidef.isHermitian
    -- R is PSD: it is Bᴴ * N * B with B = sM⁻¹ Hermitian.
    have hR_PSD : R.PosSemidef := by
      have h := hN.conjTranspose_mul_mul_same sM⁻¹
      rw [hsM_inv_herm.eq] at h
      simpa [R, Matrix.mul_assoc] using h
    -- M + N = sM * (1 + R) * sM.
    have hMN : M + N = sM * ((1 : Matrix m m ℝ) + R) * sM := by
      have hexpand : sM * ((1 : Matrix m m ℝ) + R) * sM = sM * sM + sM * R * sM := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
      have hsRsM : sM * R * sM = N := by
        show sM * (sM⁻¹ * N * sM⁻¹) * sM = N
        rw [show sM * (sM⁻¹ * N * sM⁻¹) * sM = (sM * sM⁻¹) * N * (sM⁻¹ * sM) by
              simp only [Matrix.mul_assoc],
            Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible,
            Matrix.one_mul, Matrix.mul_one]
      rw [hexpand, hMsqrt_sq, hsRsM]
    rw [hMN, Matrix.det_mul, Matrix.det_mul, ← hMsqrt_sq, Matrix.det_mul]
    have hsM_det_pos : 0 < sM.det := hMsqrt_PD.det_pos
    have hineq : 1 ≤ ((1 : Matrix m m ℝ) + R).det := det_one_add_psd_ge_one hR_PSD
    nlinarith [hineq, hsM_det_pos, mul_pos hsM_det_pos hsM_det_pos]
  · -- Case: M PSD but not PD. Then det M = 0.
    have hdet_zero : M.det = 0 := by
      by_contra h
      exact hPD ((Matrix.PosSemidef.posDef_iff_det_ne_zero hM).mpr h)
    rw [hdet_zero]
    exact (hM.add hN).det_nonneg

/-- The scalar Schur complement of a PSD matrix on `Fin (k+1)` with positive top-left
entry is PSD on `Fin k`. -/
lemma schur_complement_psd_scalar {k : ℕ} {A : Matrix (Fin k.succ) (Fin k.succ) ℝ}
    (hA : A.PosSemidef) (h00 : 0 < A 0 0) :
    Matrix.PosSemidef
      (fun i j : Fin k => A i.succ j.succ - (A i.succ 0 * A 0 j.succ) / (A 0 0)) := by
  classical
  have hAH := hA.isHermitian
  have hsym : ∀ a b, A a b = A b a := fun a b => by
    have := congr_fun (congr_fun hAH b) a
    simpa using this
  have h00_ne : A 0 0 ≠ 0 := h00.ne'
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · -- Hermitian (= symmetric for ℝ): the matrix is its own conjugate transpose.
    funext i j
    show (A j.succ i.succ - A j.succ 0 * A 0 i.succ / A 0 0 : ℝ)
       = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0
    rw [hsym j.succ i.succ, hsym j.succ 0, hsym 0 i.succ, mul_comm (A 0 j.succ)]
  · intro x
    -- c = ∑ j, A 0 j.succ * x j; by symmetry also = ∑ j, A j.succ 0 * x j.
    set c : ℝ := ∑ j, A 0 j.succ * x j with hc_def
    have hc_alt : (∑ i, A i.succ 0 * x i) = c := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsym i.succ 0]
    -- y = (-c/A 0 0) :: x
    set y : Fin k.succ → ℝ := Fin.cons (-c / A 0 0) x with hy_def
    have hAy_nn : 0 ≤ star y ⬝ᵥ A *ᵥ y := hA.dotProduct_mulVec_nonneg y
    -- Real ⇒ star is identity.
    have star_x : (star x : Fin k → ℝ) = x := rfl
    have star_y : (star y : Fin k.succ → ℝ) = y := rfl
    -- Define the Schur complement matrix S.
    set S : Matrix (Fin k) (Fin k) ℝ :=
      fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0 with hS_def
    -- Key equalities for A *ᵥ y at 0 and at i.succ.
    have hAy_zero : (A *ᵥ y) 0 = 0 := by
      show ∑ j, A 0 j * y j = 0
      rw [Fin.sum_univ_succ]
      have hy0 : y 0 = -c / A 0 0 := Fin.cons_zero _ _
      have hys : ∀ j : Fin k, y j.succ = x j := fun j => Fin.cons_succ _ _ _
      rw [hy0]
      simp_rw [hys]
      have : (∑ j, A 0 j.succ * x j) = c := hc_def.symm
      field_simp
      linear_combination this * A 0 0 - this * A 0 0
    have hAy_succ : ∀ i : Fin k, (A *ᵥ y) i.succ = (S *ᵥ x) i := by
      intro i
      show ∑ j, A i.succ j * y j = ∑ j, S i j * x j
      rw [Fin.sum_univ_succ]
      have hy0 : y 0 = -c / A 0 0 := Fin.cons_zero _ _
      have hys : ∀ j : Fin k, y j.succ = x j := fun j => Fin.cons_succ _ _ _
      rw [hy0]
      simp_rw [hys, hS_def]
      -- Goal: A i.succ 0 * (-c / A 0 0) + ∑ j, A i.succ j.succ * x j
      --     = ∑ j, (A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) * x j
      have hexp : ∀ j, (A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) * x j
          = A i.succ j.succ * x j - (A i.succ 0 / A 0 0) * (A 0 j.succ * x j) := fun j => by
        ring
      simp_rw [hexp, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [show (∑ j, A 0 j.succ * x j) = c from hc_def.symm]
      field_simp
      ring
    -- Now compute star y ⬝ᵥ A *ᵥ y = ∑ i, y i * (A *ᵥ y) i,
    -- splitting at i = 0 vs i.succ.
    have hyAy : star y ⬝ᵥ A *ᵥ y = star x ⬝ᵥ S *ᵥ x := by
      rw [star_y, star_x]
      show ∑ i, y i * (A *ᵥ y) i = ∑ i, x i * (S *ᵥ x) i
      rw [Fin.sum_univ_succ]
      rw [hAy_zero, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      have hys : y i.succ = x i := Fin.cons_succ _ _ _
      rw [hys, hAy_succ]
    rw [hyAy] at hAy_nn
    exact hAy_nn

/-- Equivalence `Fin (k+1) ≃ Fin 1 ⊕ Fin k` sending `0 ↦ inl 0` and `i.succ ↦ inr i`. -/
def consSplit (k : ℕ) : Fin (k + 1) ≃ Fin 1 ⊕ Fin k where
  toFun := Fin.cases (Sum.inl 0) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv s := by
    rcases s with i | j
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    · rfl

@[simp] lemma consSplit_zero (k : ℕ) : consSplit k 0 = Sum.inl 0 := rfl

@[simp] lemma consSplit_succ (k : ℕ) (i : Fin k) : consSplit k i.succ = Sum.inr i := rfl

@[simp] lemma consSplit_symm_inl (k : ℕ) (i : Fin 1) :
    (consSplit k).symm (Sum.inl i) = 0 := rfl

@[simp] lemma consSplit_symm_inr (k : ℕ) (i : Fin k) :
    (consSplit k).symm (Sum.inr i) = i.succ := rfl

open Matrix in
/-- For a matrix `A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ` with `A 0 0 ≠ 0`, the Schur complement
identity for the determinant. -/
lemma det_eq_topLeft_mul_schur {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (h00 : A 0 0 ≠ 0) :
    A.det = A 0 0 * Matrix.det
      (fun i j : Fin k => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) := by
  classical
  set e := consSplit k with he_def
  -- Reindex A via e.symm
  have hA_reindex : A = (A.submatrix e.symm e.symm).submatrix e e := by
    ext i j
    simp [e, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  -- Identify the reindexed matrix as fromBlocks
  set A11 : Matrix (Fin 1) (Fin 1) ℝ := !![A 0 0]
  set A12 : Matrix (Fin 1) (Fin k) ℝ := fun _ j => A 0 j.succ
  set A21 : Matrix (Fin k) (Fin 1) ℝ := fun i _ => A i.succ 0
  set A22 : Matrix (Fin k) (Fin k) ℝ := fun i j => A i.succ j.succ
  have hAblocks : A.submatrix e.symm e.symm = fromBlocks A11 A12 A21 A22 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have hi : i = 0 := Fin.fin_one_eq_zero _
      have hj : j = 0 := Fin.fin_one_eq_zero _
      subst hi
      subst hj
      simp [A11, Matrix.submatrix_apply, e]
    · simp [A12, Matrix.submatrix_apply, e]
    · simp [A21, Matrix.submatrix_apply, e]
    · simp [A22, Matrix.submatrix_apply, e]
  -- Use det_fromBlocks₁₁: det = det A11 * det (A22 - A21 * A11⁻¹ * A12)
  have hA11_inv : Invertible A11 := by
    apply Matrix.invertibleOfIsUnitDet
    show IsUnit (Matrix.det !![A 0 0])
    rw [Matrix.det_fin_one_of]
    exact isUnit_iff_ne_zero.mpr h00
  have hdet_blocks : (fromBlocks A11 A12 A21 A22).det = A11.det * (A22 - A21 * ⅟A11 * A12).det :=
    Matrix.det_fromBlocks₁₁ A11 A12 A21 A22
  -- A11.det = A 0 0
  have hA11_det : A11.det = A 0 0 := by
    show (!![A 0 0]).det = A 0 0
    simp
  -- ⅟A11 = !![1 / A 0 0]
  have hA11_invOf : (⅟A11 : Matrix (Fin 1) (Fin 1) ℝ) = !![1 / A 0 0] := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, hA11_det,
        Matrix.adjugate_fin_one]
    ext i j
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    show (Ring.inverse (A 0 0)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = (!![1 / A 0 0]) 0 0
    simp [Ring.inverse_eq_inv', div_eq_inv_mul]
  -- Compute A22 - A21 * ⅟A11 * A12 entry-wise
  have hSchur : A22 - A21 * ⅟A11 * A12 =
      fun i j : Fin k => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0 := by
    ext i j
    rw [hA11_invOf]
    simp only [A22, A21, A12, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
               Matrix.cons_val', Matrix.empty_val',
               Matrix.cons_val_fin_one, Matrix.of_apply]
    field_simp
  -- Combine
  calc A.det
      = (A.submatrix e.symm e.symm).det := by
          rw [Matrix.det_submatrix_equiv_self]
    _ = (fromBlocks A11 A12 A21 A22).det := by rw [hAblocks]
    _ = A11.det * (A22 - A21 * ⅟A11 * A12).det := hdet_blocks
    _ = A 0 0 * Matrix.det
        (fun i j : Fin k => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) := by
          rw [hA11_det, hSchur]

end Submission.Helpers
