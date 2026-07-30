import Mathlib

/-! A proof of Oppenheim's inequality for positive-semidefinite real matrices. -/

open scoped MatrixOrder Matrix

namespace Submission.Helpers

open Matrix

/-- Adding a positive-semidefinite real matrix to the identity cannot decrease
the determinant below one. -/
lemma one_le_det_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  let U := hA.isHermitian.eigenvectorUnitary
  let d := hA.isHermitian.eigenvalues
  have hspec : A = (U : Matrix n n ℝ) * diagonal d * star (U : Matrix n n ℝ) := by
    simpa [U, d, Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  have hunit :
      (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have hconj :
      1 + A =
        (U : Matrix n n ℝ) * (1 + diagonal d) * star (U : Matrix n n ℝ) := by
    rw [hspec]
    simp [Matrix.mul_add, Matrix.add_mul, hunit]
  have hdetunit :
      (U : Matrix n n ℝ).det * (star (U : Matrix n n ℝ)).det = 1 := by
    rw [← Matrix.det_mul, hunit, Matrix.det_one]
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  calc
    1 ≤ (1 + diagonal d).det := by
      rw [show (1 + diagonal d : Matrix n n ℝ) =
          diagonal (fun i => 1 + d i) by
        ext i j
        by_cases hij : i = j <;> simp [hij],
        Matrix.det_diagonal]
      exact Finset.one_le_prod fun i _ ↦ by
        simpa [d] using add_le_add_left (hA.eigenvalues_nonneg i) 1
    _ = (U : Matrix n n ℝ).det * (1 + diagonal d).det *
          (star (U : Matrix n n ℝ)).det := by
      calc
        (1 + diagonal d).det =
            (1 + diagonal d).det *
              ((U : Matrix n n ℝ).det * (star (U : Matrix n n ℝ)).det) := by
                rw [hdetunit, mul_one]
        _ = _ := by ring

/-- The determinant is monotone when a positive-semidefinite summand is added
to a positive-semidefinite real matrix. -/
lemma det_le_det_add {n : Type*} [Fintype n] [DecidableEq n]
    {A C : Matrix n n ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    A.det ≤ (A + C).det := by
  by_cases hdet : A.det = 0
  · rw [hdet]
    exact (hA.add hC).det_nonneg
  have hApos : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hdet
  obtain ⟨Y, hY, rfl⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hApos.isStrictlyPositive
  lift Y to (Matrix n n ℝ)ˣ using hY
  let P : Matrix n n ℝ :=
    star (Y⁻¹ : Matrix n n ℝ) * C * (Y⁻¹ : Matrix n n ℝ)
  have hP : P.PosSemidef := by
    simpa [P, star_eq_conjTranspose] using
      hC.conjTranspose_mul_mul_same (Y⁻¹ : Matrix n n ℝ)
  have hleft :
      star (Y : Matrix n n ℝ) * star (Y⁻¹ : Matrix n n ℝ) = 1 := by
    rw [← star_mul]
    simp
  have hright :
      (Y⁻¹ : Matrix n n ℝ) * (Y : Matrix n n ℝ) = 1 := by
    simp
  have hmiddle :
      star (Y : Matrix n n ℝ) * P * (Y : Matrix n n ℝ) = C := by
    calc
      star (Y : Matrix n n ℝ) * P * (Y : Matrix n n ℝ) =
          (star (Y : Matrix n n ℝ) * star (Y⁻¹ : Matrix n n ℝ)) *
            C * ((Y⁻¹ : Matrix n n ℝ) * (Y : Matrix n n ℝ)) := by
        simp only [P]
        noncomm_ring
      _ = C := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  have hfactor :
      star (Y : Matrix n n ℝ) * (Y : Matrix n n ℝ) + C =
        star (Y : Matrix n n ℝ) * (1 + P) * (Y : Matrix n n ℝ) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hmiddle]
  have hdetnonneg :
      0 ≤ (star (Y : Matrix n n ℝ)).det * (Y : Matrix n n ℝ).det := by
    rw [← Matrix.det_mul]
    exact hApos.det_pos.le
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  calc
    (star (Y : Matrix n n ℝ)).det * (Y : Matrix n n ℝ).det ≤
        ((star (Y : Matrix n n ℝ)).det * (Y : Matrix n n ℝ).det) *
          (1 + P).det :=
      by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (one_le_det_one_add hP) hdetnonneg
    _ = (star (Y : Matrix n n ℝ)).det * (1 + P).det *
          (Y : Matrix n n ℝ).det := by ring

end Submission.Helpers

namespace Submission

open Matrix
open Submission.Helpers

private theorem oppenheim_sum_unique
    {m u : Type*} [Fintype m] [DecidableEq m]
    [Fintype u] [DecidableEq u] [Unique u]
    (ih : ∀ {A B : Matrix m m ℝ}, A.PosSemidef → B.PosSemidef →
      A.det * ∏ i, B i i ≤ (A ⊙ B).det)
    {A B : Matrix (m ⊕ u) (m ⊕ u) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  by_cases hAdet : A.det = 0
  · rw [hAdet, zero_mul]
    exact (hA.hadamard hB).det_nonneg
  have hApos : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hAdet
  have hA22 : A.toBlocks₂₂.PosDef := by
    change (A.submatrix (Sum.inr : u → m ⊕ u) Sum.inr).PosDef
    exact hApos.submatrix Sum.inr_injective
  have hB22semidef : B.toBlocks₂₂.PosSemidef := by
    change (B.submatrix (Sum.inr : u → m ⊕ u) Sum.inr).PosSemidef
    exact hB.submatrix Sum.inr
  have ha : 0 < A.toBlocks₂₂ default default := hA22.diag_pos
  have hb_nonneg : 0 ≤ B.toBlocks₂₂ default default := hB22semidef.diag_nonneg
  have hprodB :
      ∏ i, B i i =
        (∏ i, B.toBlocks₁₁ i i) * B.toBlocks₂₂ default default := by
    rw [Fintype.prod_sum_type]
    have hu :
        (∏ j : u, B (Sum.inr j) (Sum.inr j)) =
          B (Sum.inr (default : u)) (Sum.inr default) :=
      Fintype.prod_unique _
    rw [hu]
    rfl
  by_cases hb : B.toBlocks₂₂ default default = 0
  · rw [hprodB, hb, mul_zero, mul_zero]
    exact (hA.hadamard hB).det_nonneg
  have hbpos : 0 < B.toBlocks₂₂ default default :=
    lt_of_le_of_ne hb_nonneg (Ne.symm hb)
  have hB22det : B.toBlocks₂₂.det ≠ 0 := by
    rw [Matrix.det_eq_elem_of_subsingleton B.toBlocks₂₂ default]
    exact hb
  have hB22 : B.toBlocks₂₂.PosDef :=
    hB22semidef.posDef_iff_det_ne_zero.mpr hB22det
  letI : Invertible A.toBlocks₂₂ := hA22.isUnit.invertible
  letI : Invertible B.toBlocks₂₂ := hB22.isUnit.invertible
  have hAB22 : (A.toBlocks₂₂ ⊙ B.toBlocks₂₂).PosDef :=
    hA22.hadamard hB22
  letI : Invertible (A.toBlocks₂₂ ⊙ B.toBlocks₂₂) :=
    hAB22.isUnit.invertible
  have hA21 : A.toBlocks₁₂ᴴ = A.toBlocks₂₁ := by
    have h :
        (Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂
          A.toBlocks₂₁ A.toBlocks₂₂).IsHermitian := by
      rw [Matrix.fromBlocks_toBlocks]
      exact hA.isHermitian
    exact (Matrix.isHermitian_fromBlocks_iff.mp h).2.1
  have hB21 : B.toBlocks₁₂ᴴ = B.toBlocks₂₁ := by
    have h :
        (Matrix.fromBlocks B.toBlocks₁₁ B.toBlocks₁₂
          B.toBlocks₂₁ B.toBlocks₂₂).IsHermitian := by
      rw [Matrix.fromBlocks_toBlocks]
      exact hB.isHermitian
    exact (Matrix.isHermitian_fromBlocks_iff.mp h).2.1
  let SA : Matrix m m ℝ :=
    A.toBlocks₁₁ - A.toBlocks₁₂ * A.toBlocks₂₂⁻¹ * A.toBlocks₂₁
  let SB : Matrix m m ℝ :=
    B.toBlocks₁₁ - B.toBlocks₁₂ * B.toBlocks₂₂⁻¹ * B.toBlocks₂₁
  let PA : Matrix m m ℝ :=
    A.toBlocks₁₂ * A.toBlocks₂₂⁻¹ * A.toBlocks₂₁
  let SAB : Matrix m m ℝ :=
    (A.toBlocks₁₁ ⊙ B.toBlocks₁₁) -
      (A.toBlocks₁₂ ⊙ B.toBlocks₁₂) *
        (A.toBlocks₂₂ ⊙ B.toBlocks₂₂)⁻¹ *
          (A.toBlocks₂₁ ⊙ B.toBlocks₂₁)
  have hSA : SA.PosSemidef := by
    have hfull :
        (Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂
          A.toBlocks₁₂ᴴ A.toBlocks₂₂).PosSemidef := by
      rw [hA21, Matrix.fromBlocks_toBlocks]
      exact hA
    have hs :=
      (Matrix.PosDef.fromBlocks₂₂
        A.toBlocks₁₁ A.toBlocks₁₂ hA22).mp hfull
    rw [hA21] at hs
    simpa only [SA] using hs
  have hSB : SB.PosSemidef := by
    have hfull :
        (Matrix.fromBlocks B.toBlocks₁₁ B.toBlocks₁₂
          B.toBlocks₁₂ᴴ B.toBlocks₂₂).PosSemidef := by
      rw [hB21, Matrix.fromBlocks_toBlocks]
      exact hB
    have hs :=
      (Matrix.PosDef.fromBlocks₂₂
        B.toBlocks₁₁ B.toBlocks₁₂ hB22).mp hfull
    rw [hB21] at hs
    simpa only [SB] using hs
  have hPA : PA.PosSemidef := by
    have hp :=
      hA22.inv.posSemidef.mul_mul_conjTranspose_same A.toBlocks₁₂
    rw [hA21] at hp
    simpa only [PA] using hp
  have hB11 : B.toBlocks₁₁.PosSemidef := by
    change (B.submatrix (Sum.inl : m → m ⊕ u) Sum.inl).PosSemidef
    exact hB.submatrix Sum.inl
  have hSAB :
      SAB = (SA ⊙ B.toBlocks₁₁) + (PA ⊙ SB) := by
    ext i j
    simp [SAB, SA, SB, PA, Matrix.mul_apply, Matrix.inv_subsingleton,
      Matrix.hadamard_apply, Ring.inverse_eq_inv]
    ring
  have hdetcomp : (SA ⊙ B.toBlocks₁₁).det ≤ SAB.det := by
    rw [hSAB]
    exact det_le_det_add (hSA.hadamard hB11) (hPA.hadamard hSB)
  have hind :
      SA.det * ∏ i, B.toBlocks₁₁ i i ≤ SAB.det :=
    (ih hSA hB11).trans hdetcomp
  have hdetA :
      A.det = A.toBlocks₂₂ default default * SA.det := by
    calc
      A.det =
          (Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂
            A.toBlocks₂₁ A.toBlocks₂₂).det :=
        congrArg Matrix.det (Matrix.fromBlocks_toBlocks A).symm
      _ = A.toBlocks₂₂.det *
          (A.toBlocks₁₁ - A.toBlocks₁₂ * ⅟A.toBlocks₂₂ *
            A.toBlocks₂₁).det :=
        Matrix.det_fromBlocks₂₂ _ _ _ _
      _ = A.toBlocks₂₂ default default * SA.det := by
        rw [Matrix.invOf_eq_nonsing_inv,
          Matrix.det_eq_elem_of_subsingleton A.toBlocks₂₂ default]
  have hABblocks :
      Matrix.fromBlocks
          (A.toBlocks₁₁ ⊙ B.toBlocks₁₁)
          (A.toBlocks₁₂ ⊙ B.toBlocks₁₂)
          (A.toBlocks₂₁ ⊙ B.toBlocks₂₁)
          (A.toBlocks₂₂ ⊙ B.toBlocks₂₂) =
        A ⊙ B := by
    rw [← Matrix.fromBlocks_toBlocks (A ⊙ B)]
    rfl
  have hdetAB :
      (A ⊙ B).det =
        (A.toBlocks₂₂ default default * B.toBlocks₂₂ default default) *
          SAB.det := by
    calc
      (A ⊙ B).det =
          (Matrix.fromBlocks
            (A.toBlocks₁₁ ⊙ B.toBlocks₁₁)
            (A.toBlocks₁₂ ⊙ B.toBlocks₁₂)
            (A.toBlocks₂₁ ⊙ B.toBlocks₂₁)
            (A.toBlocks₂₂ ⊙ B.toBlocks₂₂)).det :=
        congrArg Matrix.det hABblocks.symm
      _ = (A.toBlocks₂₂ ⊙ B.toBlocks₂₂).det *
          ((A.toBlocks₁₁ ⊙ B.toBlocks₁₁) -
            (A.toBlocks₁₂ ⊙ B.toBlocks₁₂) *
              ⅟(A.toBlocks₂₂ ⊙ B.toBlocks₂₂) *
                (A.toBlocks₂₁ ⊙ B.toBlocks₂₁)).det :=
        Matrix.det_fromBlocks₂₂ _ _ _ _
      _ =
          (A.toBlocks₂₂ default default * B.toBlocks₂₂ default default) *
            SAB.det := by
        rw [Matrix.invOf_eq_nonsing_inv,
          Matrix.det_eq_elem_of_subsingleton
            (A.toBlocks₂₂ ⊙ B.toBlocks₂₂) default]
        change
          (A.toBlocks₂₂ default default * B.toBlocks₂₂ default default) *
              SAB.det =
            (A.toBlocks₂₂ default default * B.toBlocks₂₂ default default) *
              SAB.det
        rfl
  rw [hdetA, hprodB, hdetAB]
  calc
    (A.toBlocks₂₂ default default * SA.det) *
        ((∏ i, B.toBlocks₁₁ i i) * B.toBlocks₂₂ default default) =
      (A.toBlocks₂₂ default default * B.toBlocks₂₂ default default) *
        (SA.det * ∏ i, B.toBlocks₁₁ i i) := by ring
    _ ≤ (A.toBlocks₂₂ default default * B.toBlocks₂₂ default default) *
        SAB.det :=
      mul_le_mul_of_nonneg_left hind (mul_nonneg ha.le hbpos.le)

private theorem oppenheim_fin :
    ∀ k : ℕ, ∀ {A B : Matrix (Fin k) (Fin k) ℝ},
      A.PosSemidef → B.PosSemidef →
        A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  intro k
  induction k with
  | zero =>
      intro A B hA hB
      simp
  | succ k ih =>
      intro A B hA hB
      let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
      let A' : Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℝ :=
        A.submatrix e e
      let B' : Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℝ :=
        B.submatrix e e
      have hA' : A'.PosSemidef := hA.submatrix e
      have hB' : B'.PosSemidef := hB.submatrix e
      have h := oppenheim_sum_unique ih hA' hB'
      have hprod :
          (∏ i : Fin k ⊕ Fin 1, B' i i) = ∏ i, B i i := by
        change (∏ i : Fin k ⊕ Fin 1, B (e i) (e i)) = _
        exact e.prod_comp (fun i => B i i)
      rw [hprod] at h
      simpa [A', B', ← Matrix.submatrix_hadamard] using h

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let A' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
    A.submatrix e.symm e.symm
  let B' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
    B.submatrix e.symm e.symm
  have hA' : A'.PosSemidef := hA.submatrix e.symm
  have hB' : B'.PosSemidef := hB.submatrix e.symm
  have h := oppenheim_fin (Fintype.card n) hA' hB'
  have hprod :
      (∏ i : Fin (Fintype.card n), B' i i) = ∏ i, B i i := by
    change (∏ i : Fin (Fintype.card n), B (e.symm i) (e.symm i)) = _
    exact e.symm.prod_comp (fun i => B i i)
  rw [hprod] at h
  simpa [A', B', ← Matrix.submatrix_hadamard] using h

end Submission
