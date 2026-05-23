/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: oppenheim_inequality
user: Morgan-Griffiths
model: GPT-5.5
submission_repo: Morgan-Griffiths/5a6dfcdd13165a579e6fe9101c1568a0
submission_ref: 9024c01533ea012383110196915bcb582331bcce
issue_number: 38
-/
import Mathlib

namespace Submission

open scoped MatrixOrder Matrix

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
universe u

set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

lemma posDef_toBlocks11 {α β : Type*} [Fintype α] [Fintype β]
    {A : Matrix (α ⊕ β) (α ⊕ β) ℝ} (hA : A.PosDef) :
    A.toBlocks₁₁.PosDef := by
  simpa [Matrix.toBlocks₁₁] using
    hA.submatrix (show Function.Injective (Sum.inl : α → α ⊕ β) by
      exact Sum.inl_injective)

lemma posSemidef_toBlocks11 {α β : Type*} [Fintype α] [Fintype β]
    {A : Matrix (α ⊕ β) (α ⊕ β) ℝ} (hA : A.PosSemidef) :
    A.toBlocks₁₁.PosSemidef := by
  simpa [Matrix.toBlocks₁₁] using hA.submatrix (Sum.inl : α → α ⊕ β)

lemma unit_det_le_of_sub_posSemidef {A B : Matrix PUnit PUnit ℝ}
    (h : (B - A).PosSemidef) : A.det ≤ B.det := by
  have hd := h.diag_nonneg (i := PUnit.unit)
  simpa [Matrix.det_unique] using hd

lemma unit_det_nonneg_of_posSemidef {A : Matrix PUnit PUnit ℝ} (h : A.PosSemidef) :
    0 ≤ A.det := by
  simpa [Matrix.det_unique] using h.diag_nonneg (i := PUnit.unit)

lemma toBlocks₂₁_eq_conjTranspose_toBlocks₁₂ {α β : Type*}
    {A : Matrix (α ⊕ β) (α ⊕ β) ℝ} (hA : A.IsHermitian) :
    A.toBlocks₂₁ = A.toBlocks₁₂ᴴ := by
  ext i j
  simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using hA.apply (Sum.inl j) (Sum.inr i)

lemma toBlocks₂₂_eq_one_of_diag {α : Type*}
    {C : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℝ}
    (hdiag : ∀ i, C i i = 1) :
    C.toBlocks₂₂ = (1 : Matrix PUnit PUnit ℝ) := by
  ext i j
  cases i
  cases j
  simp [Matrix.toBlocks₂₂, hdiag (Sum.inr PUnit.unit)]

lemma det_le_det_hadamard_correlation_posDef_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (IH : ∀ [DecidableEq α] {A C : Matrix α α ℝ}, A.PosDef → C.PosSemidef →
      (∀ i, C i i = 1) → A.det ≤ (A ⊙ C).det)
    {A C : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℝ}
    (hA : A.PosDef) (hC : C.PosSemidef) (hdiag : ∀ i, C i i = 1) :
    A.det ≤ (A ⊙ C).det := by
  classical
  let P : Matrix α α ℝ := A.toBlocks₁₁
  let U : Matrix α PUnit ℝ := A.toBlocks₁₂
  let D : Matrix PUnit PUnit ℝ := A.toBlocks₂₂
  let Q : Matrix α α ℝ := C.toBlocks₁₁
  let W : Matrix α PUnit ℝ := C.toBlocks₁₂
  let X : Matrix α α ℝ := P ⊙ Q
  let Y : Matrix α PUnit ℝ := U ⊙ W
  have hP : P.PosDef := by
    dsimp [P]
    exact posDef_toBlocks11 hA
  have hQ : Q.PosSemidef := by
    dsimp [Q]
    exact posSemidef_toBlocks11 hC
  have hdiagQ : ∀ i, Q i i = 1 := by
    intro i
    dsimp [Q]
    simpa [Matrix.toBlocks₁₁] using hdiag (Sum.inl i)
  have hdetPX : P.det ≤ X.det := by
    dsimp [X]
    exact IH (A := P) (C := Q) hP hQ hdiagQ
  have hXpsd : X.PosSemidef := by
    dsimp [X]
    exact hP.posSemidef.hadamard hQ
  have hXdet_pos : 0 < X.det := lt_of_lt_of_le hP.det_pos hdetPX
  have hX : X.PosDef := by
    exact (hXpsd.posDef_iff_det_ne_zero).mpr (ne_of_gt hXdet_pos)
  letI invP : Invertible P := hP.isUnit.invertible
  letI invX : Invertible X := hX.isUnit.invertible
  let R : Matrix PUnit PUnit ℝ := D - Uᴴ * ⅟P * U
  let S : Matrix PUnit PUnit ℝ := D - Yᴴ * ⅟X * Y
  have hA_blocks : A = Matrix.fromBlocks P U Uᴴ D := by
    rw [← Matrix.fromBlocks_toBlocks A]
    dsimp [P, U, D]
    congr 1
    exact toBlocks₂₁_eq_conjTranspose_toBlocks₁₂ hA.isHermitian
  have hC_blocks : C = Matrix.fromBlocks Q W Wᴴ (1 : Matrix PUnit PUnit ℝ) := by
    rw [← Matrix.fromBlocks_toBlocks C]
    dsimp [Q, W]
    congr 1
    · exact toBlocks₂₁_eq_conjTranspose_toBlocks₁₂ hC.isHermitian
    · exact toBlocks₂₂_eq_one_of_diag hdiag
  have hH_blocks : A ⊙ C = Matrix.fromBlocks X Y Yᴴ D := by
    rw [hA_blocks, hC_blocks]
    ext (i | i) (j | j) <;> simp [X, Y, Matrix.hadamard_apply]
  have hRpsd : R.PosSemidef := by
    dsimp [R]
    have hschur :=
      (Matrix.PosDef.fromBlocks₁₁ (A := P) (B := U) (D := D) hP).mp
        (by simpa [hA_blocks] using hA.posSemidef)
    simpa using hschur
  have hdetR_nonneg : 0 ≤ R.det := unit_det_nonneg_of_posSemidef hRpsd
  have hN0 : (Matrix.fromBlocks P U Uᴴ (Uᴴ * ⅟P * U)).PosSemidef := by
    have hz :
        ((Uᴴ * ⅟P * U) - Uᴴ * ⅟P * U : Matrix PUnit PUnit ℝ).PosSemidef := by
      rw [sub_self]
      exact Matrix.PosSemidef.zero
    exact
      (Matrix.PosDef.fromBlocks₁₁ (A := P) (B := U) (D := Uᴴ * ⅟P * U) hP).mpr
        (by simpa using hz)
  have hMpsd : (Matrix.fromBlocks X Y Yᴴ (Uᴴ * ⅟P * U)).PosSemidef := by
    have hhad := hN0.hadamard hC
    have heq :
        (Matrix.fromBlocks P U Uᴴ (Uᴴ * ⅟P * U)) ⊙ C =
          Matrix.fromBlocks X Y Yᴴ (Uᴴ * ⅟P * U) := by
      rw [hC_blocks]
      ext (i | i) (j | j) <;> simp [X, Y, Matrix.hadamard_apply]
    rw [heq] at hhad
    exact hhad
  have hdiff : (S - R).PosSemidef := by
    have hschur :=
      (Matrix.PosDef.fromBlocks₁₁ (A := X) (B := Y)
        (D := Uᴴ * ⅟P * U) hX).mp hMpsd
    have heq : S - R = (Uᴴ * ⅟P * U - Yᴴ * ⅟X * Y : Matrix PUnit PUnit ℝ) := by
      dsimp [S, R]
      abel_nf
    simpa [heq] using hschur
  have hdetRS : R.det ≤ S.det := unit_det_le_of_sub_posSemidef hdiff
  have hdetA : A.det = P.det * R.det := by
    rw [hA_blocks, Matrix.det_fromBlocks₁₁]
  have hdetH : (A ⊙ C).det = X.det * S.det := by
    rw [hH_blocks, Matrix.det_fromBlocks₁₁]
  rw [hdetA, hdetH]
  exact
    le_trans (mul_le_mul_of_nonneg_right hdetPX hdetR_nonneg)
      (mul_le_mul_of_nonneg_left hdetRS (le_of_lt hXdet_pos))

lemma det_le_det_hadamard_correlation_posDef_equiv
    {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β)
    (H : ∀ {A C : Matrix α α ℝ}, A.PosDef → C.PosSemidef →
      (∀ i, C i i = 1) → A.det ≤ (A ⊙ C).det)
    {A C : Matrix β β ℝ} (hA : A.PosDef) (hC : C.PosSemidef)
    (hdiag : ∀ i, C i i = 1) :
    A.det ≤ (A ⊙ C).det := by
  classical
  let A' : Matrix α α ℝ := A.submatrix e e
  let C' : Matrix α α ℝ := C.submatrix e e
  have hA' : A'.PosDef := by
    dsimp [A']
    exact hA.submatrix e.injective
  have hC' : C'.PosSemidef := by
    dsimp [C']
    exact hC.submatrix e
  have hdiag' : ∀ i, C' i i = 1 := by
    intro i
    dsimp [C']
    exact hdiag (e i)
  have hle := H hA' hC' hdiag'
  have hdetA' : A'.det = A.det := by
    dsimp [A']
    exact Matrix.det_submatrix_equiv_self e A
  have hdetHC' : (A' ⊙ C').det = (A ⊙ C).det := by
    dsimp [A', C']
    rw [← Matrix.det_submatrix_equiv_self e (A ⊙ C)]
    congr 1
  rwa [hdetA', hdetHC'] at hle

lemma det_le_det_hadamard_of_correlation_posDef {n : Type u} [Fintype n] [DecidableEq n]
    {A C : Matrix n n ℝ} (hA : A.PosDef) (hC : C.PosSemidef)
    (hdiag : ∀ i, C i i = 1) :
    A.det ≤ (A ⊙ C).det := by
  classical
  let P : ∀ (α : Type u) [Fintype α], Prop := fun α _ =>
    ∀ [DecidableEq α] {A C : Matrix α α ℝ}, A.PosDef → C.PosSemidef →
      (∀ i, C i i = 1) → A.det ≤ (A ⊙ C).det
  have hP : P n := by
    apply Fintype.induction_empty_option (P := P)
    · intro α β _ e hα
      letI : Fintype α := Fintype.ofEquiv β e.symm
      letI : DecidableEq α := Classical.decEq α
      intro _ A C hA hC hdiag
      exact
        det_le_det_hadamard_correlation_posDef_equiv (α := α) (β := β) e
          (H := by
            intro A C hA hC hdiag
            exact hα hA hC hdiag)
          hA hC hdiag
    · intro _ A C hA hC hdiag
      simp [Matrix.det_isEmpty]
    · intro α _ hα _ A C hA hC hdiag
      exact
        det_le_det_hadamard_correlation_posDef_equiv
          (α := α ⊕ PUnit) (β := Option α) (Equiv.optionEquivSumPUnit α).symm
          (H := by
            intro A C hA hC hdiag
            exact
              det_le_det_hadamard_correlation_posDef_sum
                (IH := by
                  intro _ A C hA hC hdiag
                  exact hα hA hC hdiag)
                hA hC hdiag)
          hA hC hdiag
  exact hP hA hC hdiag

lemma prod_diag_nonneg_of_posSemidef {n : Type*} [Fintype n]
    {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    0 ≤ ∏ i, B i i := by
  classical
  exact Finset.prod_nonneg fun i _ => hB.diag_nonneg

lemma normalized_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    let d : n → ℝ := fun i => Real.sqrt (B i i)
    let E : Matrix n n ℝ := Matrix.diagonal fun i => (d i)⁻¹
    (E * B * E).PosSemidef := by
  classical
  intro d E
  have h := hB.conjTranspose_mul_mul_same E
  simpa [E] using h

lemma normalized_diag_one {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hpos : ∀ i, 0 < B i i) :
    let d : n → ℝ := fun i => Real.sqrt (B i i)
    let E : Matrix n n ℝ := Matrix.diagonal fun i => (d i)⁻¹
    ∀ i, (E * B * E) i i = 1 := by
  classical
  intro d E i
  have hsqrt_ne : d i ≠ 0 := by
    dsimp [d]
    exact Real.sqrt_ne_zero'.mpr (hpos i)
  have hsq : d i * d i = B i i := by
    dsimp [d]
    rw [← sq, Real.sq_sqrt (le_of_lt (hpos i))]
  simp [Matrix.mul_apply, Matrix.diagonal, E]
  field_simp [hsqrt_ne, hsq]
  linarith [hpos i]

lemma hadamard_eq_diagonal_mul_normalized {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hpos : ∀ i, 0 < B i i) :
    let d : n → ℝ := fun i => Real.sqrt (B i i)
    let D : Matrix n n ℝ := Matrix.diagonal d
    let E : Matrix n n ℝ := Matrix.diagonal fun i => (d i)⁻¹
    let C : Matrix n n ℝ := E * B * E
    A ⊙ B = D * (A ⊙ C) * D := by
  classical
  intro d D E C
  ext i j
  have hdi : d i ≠ 0 := by
    dsimp [d]
    exact Real.sqrt_ne_zero'.mpr (hpos i)
  have hdj : d j ≠ 0 := by
    dsimp [d]
    exact Real.sqrt_ne_zero'.mpr (hpos j)
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.hadamard_apply, D, E, C]
  field_simp [hdi, hdj]

lemma det_hadamard_eq_prod_diag_mul_det_normalized {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hpos : ∀ i, 0 < B i i) :
    let d : n → ℝ := fun i => Real.sqrt (B i i)
    let D : Matrix n n ℝ := Matrix.diagonal d
    let E : Matrix n n ℝ := Matrix.diagonal fun i => (d i)⁻¹
    let C : Matrix n n ℝ := E * B * E
    (A ⊙ B).det = (∏ i, B i i) * (A ⊙ C).det := by
  classical
  intro d D E C
  have hmat : A ⊙ B = D * (A ⊙ C) * D :=
    hadamard_eq_diagonal_mul_normalized (A := A) (B := B) hpos
  have hprod_sq : (∏ i, d i) * (∏ i, d i) = ∏ i, B i i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i hi
    dsimp [d]
    rw [← sq, Real.sq_sqrt (le_of_lt (hpos i))]
  rw [hmat, Matrix.det_mul, Matrix.det_mul]
  simp only [D, Matrix.det_diagonal]
  rw [← hprod_sq]
  ring

lemma oppenheim_inequality_of_diag_pos_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosSemidef)
    (hpos : ∀ i, 0 < B i i) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  let d : n → ℝ := fun i => Real.sqrt (B i i)
  let E : Matrix n n ℝ := Matrix.diagonal fun i => (d i)⁻¹
  let C : Matrix n n ℝ := E * B * E
  have hC : C.PosSemidef := by
    dsimp [C, E, d]
    exact normalized_posSemidef (B := B) hB
  have hdiag : ∀ i, C i i = 1 := by
    dsimp [C, E, d]
    exact normalized_diag_one (B := B) hpos
  have hle : A.det ≤ (A ⊙ C).det :=
    det_le_det_hadamard_of_correlation_posDef hA hC hdiag
  have hprod_nonneg : 0 ≤ ∏ i, B i i := prod_diag_nonneg_of_posSemidef hB
  have hdet : (A ⊙ B).det = (∏ i, B i i) * (A ⊙ C).det := by
    dsimp [C, E, d]
    exact det_hadamard_eq_prod_diag_mul_det_normalized (A := A) (B := B) hpos
  calc
    A.det * ∏ i, B i i = (∏ i, B i i) * A.det := by ring
    _ ≤ (∏ i, B i i) * (A ⊙ C).det := mul_le_mul_of_nonneg_left hle hprod_nonneg
    _ = (A ⊙ B).det := hdet.symm

lemma prod_diag_eq_zero_of_diag_eq_zero {n : Type*} [Fintype n]
    {B : Matrix n n ℝ} {k : n} (hk : B k k = 0) :
    (∏ i, B i i) = 0 := by
  classical
  rw [Finset.prod_eq_zero_iff]
  exact ⟨k, Finset.mem_univ k, hk⟩

lemma oppenheim_inequality_of_exists_diag_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hzero : ∃ i, B i i = 0) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  rcases hzero with ⟨i, hi⟩
  have hprod : (∏ i, B i i) = 0 := prod_diag_eq_zero_of_diag_eq_zero hi
  calc
    A.det * ∏ i, B i i = 0 := by rw [hprod, mul_zero]
    _ ≤ (A ⊙ B).det := (hA.hadamard hB).det_nonneg
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det :=
/-ResultProofBegin-/by
  classical
  by_cases hAdet : A.det = 0
  · calc
      A.det * ∏ i, B i i = 0 := by rw [hAdet, zero_mul]
      _ ≤ (A ⊙ B).det := (hA.hadamard hB).det_nonneg
  · have hApos : A.PosDef := (hA.posDef_iff_det_ne_zero).mpr hAdet
    by_cases hzero : ∃ i, B i i = 0
    · exact oppenheim_inequality_of_exists_diag_zero hA hB hzero
    · have hpos : ∀ i, 0 < B i i := by
        intro i
        exact lt_of_le_of_ne hB.diag_nonneg (by
          exact Ne.symm (not_exists.mp hzero i))
      exact oppenheim_inequality_of_diag_pos_posDef hApos hB hpos
/-ResultProofEnd-/
/-ResultEnd-/
end Submission

