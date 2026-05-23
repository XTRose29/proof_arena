/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: oppenheim_inequality
user: daouid
model: Antigravity (Multi-Model Ensemble: Gemini 3.1 Pro, Gemini 3 Flash, Claude 4.6 Sonnet/Opus)
submission_repo: daouid/lean-eval
submission_ref: 26b8057f1ef181b15beeab762febd29bf3e6f895
issue_number: 268
-/
import Mathlib

namespace Submission

open scoped Matrix MatrixOrder
open Matrix

universe u v

variable {m n : Type*}

@[reducible]
noncomputable def invertible_of_posDef [Fintype m] [DecidableEq m] {A : Matrix m m ℝ} (hA : A.PosDef) : Invertible A :=
  ((nonempty_invertible_iff_isUnit A).mpr hA.isUnit).some

theorem posSemidef_M_X [Fintype m] [DecidableEq m] (X : Matrix m m ℝ) (u : Matrix m Unit ℝ) (hX : X.PosDef) [Invertible X] :
    (fromBlocks X u uᴴ (uᴴ * X⁻¹ * u)).PosSemidef := by
  rw [PosDef.fromBlocks₁₁ u (uᴴ * X⁻¹ * u) hX, sub_self]
  exact PosSemidef.zero

theorem fromBlocks_hadamard (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (E : Matrix m m ℝ) (F : Matrix m n ℝ) (G : Matrix n m ℝ) (H : Matrix n n ℝ) :
    fromBlocks A B C D ⊙ fromBlocks E F G H = fromBlocks (A ⊙ E) (B ⊙ F) (C ⊙ G) (D ⊙ H) := by
  ext i j; cases i <;> cases j <;> rfl

theorem reindex_hadamard (e : m ≃ n) (A B : Matrix m m ℝ) :
    reindex e e (A ⊙ B) = reindex e e A ⊙ reindex e e B := rfl

theorem prod_reindex_diag [Fintype m] [Fintype n] (e : m ≃ n) (B : Matrix m m ℝ) :
    ∏ i : n, reindex e e B i i = ∏ i : m, B i i :=
  Fintype.prod_equiv e.symm _ _ (fun _ => rfl)

theorem det_eq_zero_of_submatrix_det_eq_zero [Fintype m] [DecidableEq m] {A : Matrix (Sum m Unit) (Sum m Unit) ℝ}
    (hA : A.PosSemidef) (hA₀ : (A.submatrix Sum.inl Sum.inl).det = 0) : A.det = 0 := by
  by_contra h
  have h_def : A.PosDef := hA.posDef_iff_det_ne_zero.mpr h
  exact (h_def.submatrix Sum.inl_injective).posSemidef.posDef_iff_det_ne_zero.mp (h_def.submatrix Sum.inl_injective) hA₀

theorem oppenheim_base_isEmpty {n : Type*} [Fintype n] [DecidableEq n] [IsEmpty n]
    {A B : Matrix n n ℝ} (_hA : A.PosSemidef) (_hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  simp only [Matrix.det_isEmpty, Finset.univ_eq_empty, Finset.prod_empty, mul_one, le_refl]

theorem oppenheim_base_unique {n : Type*} [Fintype n] [DecidableEq n] [Unique n]
    {A B : Matrix n n ℝ} (_hA : A.PosSemidef) (_hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  simp only [det_unique, Fintype.prod_unique]
  rfl

def equiv_unit [DecidableEq n] (i : n) : {x // ¬(x ≠ i)} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨i, by simp⟩
  left_inv x := by ext; exact (not_not.mp x.2).symm
  right_inv _ := rfl

def equiv_sum_compl [DecidableEq n] (i : n) : n ≃ {x // x ≠ i} ⊕ Unit :=
  (Equiv.sumCompl (fun x => x ≠ i)).symm.trans (Equiv.sumCongr (Equiv.refl _) (equiv_unit i))

theorem block_representation {A : Matrix (Sum m Unit) (Sum m Unit) ℝ} (hA : A.PosSemidef) :
    A = fromBlocks (A.submatrix Sum.inl Sum.inl) (A.submatrix Sum.inl Sum.inr)
      (A.submatrix Sum.inl Sum.inr)ᴴ (A.submatrix Sum.inr Sum.inr) := by
  ext i j; cases i <;> cases j <;> try rfl
  dsimp [conjTranspose]; nth_rw 1 [← hA.isHermitian]; rfl

theorem det_pos_of_posDef [Fintype m] [DecidableEq m] {A : Matrix m m ℝ} (hA : A.PosDef) : 0 < A.det :=
  lt_of_le_of_ne hA.posSemidef.det_nonneg (hA.posSemidef.posDef_iff_det_ne_zero.mp hA).symm

theorem pos_schur_of_posDef [Fintype m] [DecidableEq m] {A : Matrix m m ℝ} (B : Matrix m Unit ℝ) (C : Matrix Unit Unit ℝ)
    (hM : (fromBlocks A B Bᴴ C).PosDef) [Invertible A] :
    0 < (C - Bᴴ * A⁻¹ * B) () () := by
  have h_det : (fromBlocks A B Bᴴ C).det = A.det * (C - Bᴴ * ⅟A * B) () () := by rw [det_fromBlocks₁₁, det_unique (C - Bᴴ * ⅟A * B)]
  have h_S : 0 < A.det * (C - Bᴴ * ⅟A * B) () () := h_det ▸ det_pos_of_posDef hM
  rw [← invOf_eq_nonsing_inv]
  exact pos_of_mul_pos_right h_S (det_pos_of_posDef (hM.submatrix Sum.inl_injective)).le

lemma schur_complement_nonneg_of_posSemidef [Fintype m] [DecidableEq m] {A : Matrix m m ℝ} (B : Matrix m Unit ℝ) (C : Matrix Unit Unit ℝ)
    (hM : (fromBlocks A B Bᴴ C).PosSemidef) (hA : A.PosDef) [Invertible A] :
    0 ≤ (C - Bᴴ * A⁻¹ * B) () () := by
  have h_det_eq : (fromBlocks A B Bᴴ C).det = A.det * (C - Bᴴ * ⅟A * B) () () := by rw [det_fromBlocks₁₁, det_unique (C - Bᴴ * ⅟A * B)]
  have h_mul := nonneg_of_mul_nonneg_right (h_det_eq ▸ hM.det_nonneg) (det_pos_of_posDef hA)
  rwa [invOf_eq_nonsing_inv] at h_mul

theorem oppenheim_posDef_of_card (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n] (hk : Fintype.card n = k)
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  induction' k using Nat.strong_induction_on with k ih generalizing n
  rcases k with _ | k
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hk
    exact oppenheim_base_isEmpty hA.posSemidef hB
  · by_cases hk0 : k = 0
    · subst hk0
      let ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hk
      haveI : Unique n := ⟨⟨x⟩, hx⟩
      exact oppenheim_base_unique hA.posSemidef hB
    haveI : Nonempty n := Fintype.card_pos_iff.mp (by omega)
    let i := Classical.arbitrary n
    let e := equiv_sum_compl i
    let m' := {x // x ≠ i}
    have h_card_m' : Fintype.card m' = k := by
      have h_card_eq := Fintype.card_congr e
      rw [hk] at h_card_eq
      simp only [Fintype.card_sum, Fintype.card_unit] at h_card_eq
      exact Nat.add_right_cancel h_card_eq.symm
    let A' := reindex e e A
    let B' := reindex e e B
    have hA' : A'.PosDef := hA.submatrix e.symm.injective
    have hB' : B'.PosSemidef := hB.submatrix e.symm
    rw [← det_reindex_self e A, ← det_reindex_self e (A ⊙ B), reindex_hadamard, ← prod_reindex_diag e B]
    let X := A'.submatrix Sum.inl Sum.inl
    let Y := B'.submatrix Sum.inl Sum.inl
    have hX : X.PosDef := hA'.submatrix Sum.inl_injective
    have hY : Y.PosSemidef := hB'.submatrix Sum.inl
    let u := A'.submatrix Sum.inl Sum.inr
    let v := B'.submatrix Sum.inl Sum.inr
    let d_A := A'.submatrix Sum.inr Sum.inr
    let d_B := B'.submatrix Sum.inr Sum.inr
    have h_repA : A' = fromBlocks X u uᴴ d_A := block_representation hA'.posSemidef
    have h_repB : B' = fromBlocks Y v vᴴ d_B := block_representation hB'
    have hA'_fromBlocks_posDef : (fromBlocks X u uᴴ d_A).PosDef := by rwa [← h_repA]
    letI := invertible_of_posDef hX
    let cA := (uᴴ * X⁻¹ * u) () ()
    have h_detA : A'.det = X.det * (d_A () () - cA) := by
      rw [h_repA, det_fromBlocks₁₁]
      have h_det_unique : (d_A - uᴴ * ⅟X * u).det = (d_A - uᴴ * ⅟X * u) () () := det_unique _
      rw [h_det_unique, invOf_eq_nonsing_inv]
      rfl
    have h_prodB : ∏ j : Sum m' Unit, B' j j = (∏ j : m', Y j j) * d_B () () := by
      rw [Fintype.prod_sum_type, Fintype.prod_unique (ι := Unit)]; rfl
    have hXY := PosSemidef.hadamard hX.posSemidef hY
    by_cases hXY_det : (X ⊙ Y).det = 0
    · have hAB_det : (A' ⊙ B').det = 0 :=
        det_eq_zero_of_submatrix_det_eq_zero (PosSemidef.hadamard hA'.posSemidef hB') (by rwa [show ((A' ⊙ B').submatrix Sum.inl Sum.inl) = X ⊙ Y from rfl])
      have h_ih := @ih k (Nat.lt_succ_self k) m' _ _ h_card_m' X Y hX hY
      rw [hXY_det] at h_ih
      have h_prodY_zero : ∏ j : m', Y j j = 0 :=
        le_antisymm (nonpos_of_mul_nonpos_right h_ih (det_pos_of_posDef hX)) (Finset.prod_nonneg (fun j _ => hY.diag_nonneg))
      rw [hAB_det, h_prodB, h_prodY_zero, zero_mul, mul_zero]
    · have hXY_def : (X ⊙ Y).PosDef := hXY.posDef_iff_det_ne_zero.mpr hXY_det
      letI instXY : Invertible (X ⊙ Y) := invertible_of_posDef hXY_def
      let cAB := ((u ⊙ v)ᴴ * (X ⊙ Y)⁻¹ * (u ⊙ v)) () ()
      have h_repAB : A' ⊙ B' = fromBlocks (X ⊙ Y) (u ⊙ v) (u ⊙ v)ᴴ (d_A ⊙ d_B) := by
        rw [h_repA, h_repB, fromBlocks_hadamard]
        have h_eq : uᴴ ⊙ vᴴ = (u ⊙ v)ᴴ := by ext j l; rfl
        rw [h_eq]
      have h_detAB : (A' ⊙ B').det = (X ⊙ Y).det * (d_A () () * d_B () () - cAB) := by
        rw [h_repAB, det_fromBlocks₁₁]
        have h_det_unique : (d_A ⊙ d_B - (u ⊙ v)ᴴ * ⅟(X ⊙ Y) * (u ⊙ v)).det = (d_A ⊙ d_B - (u ⊙ v)ᴴ * ⅟(X ⊙ Y) * (u ⊙ v)) () () := det_unique _
        rw [h_det_unique, invOf_eq_nonsing_inv]
        rfl
      have h_MX : (fromBlocks X u uᴴ (uᴴ * X⁻¹ * u)).PosSemidef := posSemidef_M_X X u hX
      have h_had_semidef : ((fromBlocks X u uᴴ (uᴴ * X⁻¹ * u)) ⊙ B').PosSemidef := PosSemidef.hadamard h_MX hB'
      rw [h_repB, fromBlocks_hadamard] at h_had_semidef
      have h_eq_u_v : uᴴ ⊙ vᴴ = (u ⊙ v)ᴴ := by ext j l; rfl
      rw [h_eq_u_v] at h_had_semidef
      have hcAB_le : cAB ≤ cA * d_B () () := by
        have h_schur := schur_complement_nonneg_of_posSemidef (u ⊙ v) ((uᴴ * X⁻¹ * u) ⊙ d_B) h_had_semidef hXY_def
        change 0 ≤ cA * d_B () () - cAB at h_schur
        exact sub_nonneg.mp h_schur
      have h_ih := @ih k (Nat.lt_succ_self k) m' _ _ h_card_m' X Y hX hY
      have h_le3 : d_A () () * d_B () () - cA * d_B () () ≤ d_A () () * d_B () () - cAB := by linarith
      have h_eq3 : d_A () () * d_B () () - cA * d_B () () = (d_A () () - cA) * d_B () () := by ring
      rw [h_eq3] at h_le3
      have h_detX_pos : 0 < X.det := det_pos_of_posDef hX
      have h_prodY_nonneg : 0 ≤ ∏ j : m', Y j j := Finset.prod_nonneg (fun j _ => hY.diag_nonneg)
      have hcA_lt : cA < d_A () () := sub_pos.mp (pos_schur_of_posDef u d_A hA'_fromBlocks_posDef)
      have h_sub_pos : 0 < d_A () () - cA := sub_pos.mpr hcA_lt
      have hd_B_nonneg : 0 ≤ d_B () () := hB'.diag_nonneg (i := Sum.inr ())
      have h_factor_nonneg : 0 ≤ (d_A () () - cA) * d_B () () := mul_nonneg h_sub_pos.le hd_B_nonneg
      have h_mul_le := mul_le_mul h_ih h_le3 h_factor_nonneg hXY_def.posSemidef.det_nonneg
      rw [h_detA, h_prodB, h_detAB]
      have h_assoc : X.det * (d_A () () - cA) * ((∏ j : m', Y j j) * d_B () ()) = (X.det * ∏ j : m', Y j j) * ((d_A () () - cA) * d_B () ()) := by ring
      rw [h_assoc]
      exact h_mul_le

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  by_cases hA_det : A.det = 0
  · rw [hA_det, zero_mul]
    have hAB_semidef := PosSemidef.hadamard hA hB
    exact hAB_semidef.det_nonneg
  · have hA_def : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hA_det
    exact oppenheim_posDef_of_card (Fintype.card n) rfl hA_def hB

end Submission