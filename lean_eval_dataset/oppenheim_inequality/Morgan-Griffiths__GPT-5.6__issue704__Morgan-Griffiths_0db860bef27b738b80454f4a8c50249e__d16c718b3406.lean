import Mathlib
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  have det_one_add_psd {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) :
      1 ≤ (1 + Z).det := by
    classical
    let hH : Z.IsHermitian := hZ.isHermitian
    let U := hH.eigenvectorUnitary
    let d : n → ℝ := hH.eigenvalues
    have hzspec : Z = (↑U : Matrix n n ℝ) * Matrix.diagonal d * star (↑U : Matrix n n ℝ) := by
      -- spectral theorem
      simpa [hH, U, d, Unitary.conjStarAlgAut_apply, Function.comp_def,
        Matrix.star_eq_conjTranspose] using hH.spectral_theorem
    have hunit : (↑U : Matrix n n ℝ) * star (↑U : Matrix n n ℝ) = 1 := by
      -- unitary
      simpa [U, Unitary.coe_star] using (Unitary.coe_mul_star_self U)
    have hrew : (1 + Z) = (↑U : Matrix n n ℝ) * (1 + Matrix.diagonal d) * star (↑U : Matrix n n ℝ) := by
      rw [hzspec]
      -- ring expand
      -- matrices noncomm
      calc
        1 + (↑U : Matrix n n ℝ) * Matrix.diagonal d * star (↑U : Matrix n n ℝ) =
            (↑U : Matrix n n ℝ) * star (↑U : Matrix n n ℝ) + (↑U : Matrix n n ℝ) * Matrix.diagonal d * star (↑U : Matrix n n ℝ) := by rw [hunit]
        _ = (↑U : Matrix n n ℝ) * (1 + Matrix.diagonal d) * star (↑U : Matrix n n ℝ) := by
          simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    have hdetu : (↑U : Matrix n n ℝ).det * (star (↑U : Matrix n n ℝ)).det = 1 := by
      -- from hunit determinant
      rw [← Matrix.det_mul, hunit, Matrix.det_one]
    have hdet : (1 + Z).det = ∏ i, (1 + d i) := by
      rw [hrew]
      -- determinants
      rw [Matrix.det_mul, Matrix.det_mul]
      have hdiag : (1 + Matrix.diagonal d : Matrix n n ℝ) = Matrix.diagonal (fun i => 1 + d i) := by
        -- diagonal add
        rw [← Matrix.diagonal_add]
        simp
      rw [hdiag, Matrix.det_diagonal]
      -- combine dets
      -- det U * prod * det starU = prod
      -- ring using commutativity
      calc
        (↑U : Matrix n n ℝ).det * (∏ i : n, (1 + d i)) * (star (↑U : Matrix n n ℝ)).det =
            ((↑U : Matrix n n ℝ).det * (star (↑U : Matrix n n ℝ)).det) * (∏ i : n, (1 + d i)) := by ring
        _ = ∏ i : n, (1 + d i) := by rw [hdetu]; simp
    rw [hdet]
    have hd_nonneg (i : n) : 0 ≤ d i := by
      -- eigenvalues nonneg
      simpa [d, hH] using hZ.eigenvalues_nonneg i
    exact hdet ▸ (Finset.one_le_prod (fun i hi =>
      (show (1:ℝ) ≤ 1 + d i from le_add_of_nonneg_right (hd_nonneg i))))
  have det_mono_add {X Y : Matrix n n ℝ} (hX : X.PosDef) (hY : Y.PosSemidef) :
      X.det ≤ (X + Y).det := by
    classical
    let S : Matrix n n ℝ := CFC.sqrt X
    have hXs : X.PosSemidef := hX.posSemidef
    have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)
    have hSS : S * S = X := by
      have := CFC.sq_sqrt X hXs.nonneg
      simpa [S, sq] using this
    have hdetSpos : 0 < S.det := by
      change 0 < (CFC.sqrt X).det
      rw [hXs.det_sqrt, RCLike.sqrt_real]
      exact Real.sqrt_pos.2 hX.det_pos
    have hdetSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hdetSpos)
    have hSinvherm : (S⁻¹ : Matrix n n ℝ)ᴴ = S⁻¹ := hS.isHermitian.inv.eq
    let Z : Matrix n n ℝ := S⁻¹ * Y * S⁻¹
    have hZ : Z.PosSemidef := by
      have ht := hY.conjTranspose_mul_mul_same (S⁻¹ : Matrix n n ℝ)
      -- ht : (S⁻¹)ᴴ * Y * S⁻¹
      rw [hSinvherm] at ht
      exact ht
    have hcancel : S * S⁻¹ = (1 : Matrix n n ℝ) := Matrix.mul_nonsing_inv _ hdetSunit
    have hrew : X + Y = S * (1 + Z) * S := by
      rw [← hSS]
      -- algebra
      simp [Z, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv S hdetSunit]
      symm
      exact Matrix.nonsing_inv_mul_cancel_right S Y hdetSunit
    have hdetrew : (X + Y).det = X.det * (1 + Z).det := by
      rw [hrew, Matrix.det_mul, Matrix.det_mul, hSS.symm, Matrix.det_mul]
      ring
    rw [hdetrew]
    nlinarith [det_one_add_psd hZ, hX.det_pos]
  -- The remaining finite-dimensional pivot step; the singular cases below need only the
  -- two determinant lemmas just proved.
  have positive_core : ∀ {X Y : Matrix n n ℝ}, X.PosDef → Y.PosSemidef →
        (∀ i, 0 < Y i i) → X.det * ∏ i, Y i i ≤ (X ⊙ Y).det := by
    classical
    have core_sum_step {m : Type} [Fintype m] [DecidableEq m]
     (IH : ∀ {X Y : Matrix m m ℝ}, X.PosDef → Y.PosSemidef →
              (∀ i, 0 < Y i i) → X.det * ∏ i, Y i i ≤ (X ⊙ Y).det) :
     ∀ {X Y : Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ}, X.PosDef → Y.PosSemidef →
           (∀ i, 0 < Y i i) → X.det * ∏ i, Y i i ≤ (X ⊙ Y).det := by
     classical
     intro X Y hX hY hdiag
     let A : Matrix m m ℝ := X.toBlocks₁₁
     let u : Matrix m Unit ℝ := X.toBlocks₁₂
     let a : Matrix Unit Unit ℝ := X.toBlocks₂₂
     let D : Matrix m m ℝ := Y.toBlocks₁₁
     let v : Matrix m Unit ℝ := Y.toBlocks₁₂
     let d : Matrix Unit Unit ℝ := Y.toBlocks₂₂
     have hx21 : uᴴ = X.toBlocks₂₁ := by
       have hh : (Matrix.fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂).IsHermitian := by
         rw [Matrix.fromBlocks_toBlocks]
         exact hX.isHermitian
       have := (Matrix.isHermitian_fromBlocks_iff.mp hh).2.1
       simpa [u] using this
     have hy21 : vᴴ = Y.toBlocks₂₁ := by
       have hh : (Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂).IsHermitian := by
         rw [Matrix.fromBlocks_toBlocks]
         exact hY.isHermitian
       have := (Matrix.isHermitian_fromBlocks_iff.mp hh).2.1
       simpa [v] using this
     have hxform : Matrix.fromBlocks A u uᴴ a = X := by
       change Matrix.fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ (X.toBlocks₁₂)ᴴ X.toBlocks₂₂ = X
       change (X.toBlocks₁₂)ᴴ = X.toBlocks₂₁ at hx21
       rw [hx21]
       exact Matrix.fromBlocks_toBlocks X
     have hyform : Matrix.fromBlocks D v vᴴ d = Y := by
       change Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ (Y.toBlocks₁₂)ᴴ Y.toBlocks₂₂ = Y
       change (Y.toBlocks₁₂)ᴴ = Y.toBlocks₂₁ at hy21
       rw [hy21]
       exact Matrix.fromBlocks_toBlocks Y
     have hAp : A.PosDef := by
       simpa [A, Matrix.toBlocks₁₁, Matrix.submatrix] using
         (hX.submatrix (e := (Sum.inl : m → m ⊕ Unit)) Sum.inl_injective)
     have hDs : D.PosSemidef := by
       simpa [D, Matrix.toBlocks₁₁, Matrix.submatrix] using
         (hY.submatrix (Sum.inl : m → m ⊕ Unit))
     have hDpos : ∀ i : m, 0 < D i i := by
       intro i; simpa [D, Matrix.toBlocks₁₁] using hdiag (Sum.inl i)
     have hdpos : 0 < d () () := by
       simpa [d, Matrix.toBlocks₂₂] using hdiag (Sum.inr ())
     have ih := IH hAp hDs hDpos
     let C : Matrix m m ℝ := A ⊙ D
     have hCs : C.PosSemidef := by simpa [C] using hAp.posSemidef.hadamard hDs
     have hpD : 0 < ∏ i:m, D i i := Finset.prod_pos (fun i hi => hDpos i)
     have hleftpos : 0 < A.det * ∏ i:m, D i i :=
       mul_pos hAp.det_pos hpD
     have hCpos : 0 < C.det := lt_of_lt_of_le hleftpos (by simpa [C] using ih)
     have hCp : C.PosDef := hCs.posDef_iff_det_ne_zero.mpr (ne_of_gt hCpos)
     letI iA : Invertible A := hAp.isUnit.invertible
     letI iC : Invertible C := hCp.isUnit.invertible
     let k0 : Matrix Unit Unit ℝ := uᴴ * A⁻¹ * u
     let r : Matrix Unit Unit ℝ := a - k0
     have hr : r.PosSemidef := by
       have hxps : (Matrix.fromBlocks A u uᴴ a).PosSemidef := by rw [hxform]; exact hX.posSemidef
       have hh := (Matrix.PosDef.fromBlocks₁₁ (A:=A) u a hAp).mp hxps
       simpa [r,k0] using hh
     have hdetX : X.det = A.det * r.det := by
       rw [← hxform]
       simpa [r,k0, Matrix.invOf_eq_nonsing_inv] using
         (Matrix.det_fromBlocks₁₁ A u uᴴ a)
     have hK : (Matrix.fromBlocks A u uᴴ k0).PosSemidef := by
       apply (Matrix.PosDef.fromBlocks₁₁ (A:=A) u k0 hAp).mpr
       simpa [k0] using (Matrix.PosSemidef.zero :
              (0 : Matrix Unit Unit ℝ).PosSemidef)
     let w : Matrix m Unit ℝ := u ⊙ v
     have hblockK :
         (Matrix.fromBlocks A u uᴴ k0 ⊙ Matrix.fromBlocks D v vᴴ d) =
           Matrix.fromBlocks C w wᴴ (k0 ⊙ d) := by
       ext i j
       cases i with
       | inl i =>
         cases j with
         | inl j => rfl
         | inr j => rfl
       | inr i =>
         cases j with
         | inl j =>
           -- conjugate transpose product
           simp [Matrix.fromBlocks_apply₂₁, Matrix.hadamard_apply,
             Matrix.fromBlocks_apply₂₁, w, Matrix.conjTranspose_apply, mul_comm]
         | inr j => rfl
     have hfullT : (Matrix.fromBlocks C w wᴴ (k0 ⊙ d)).PosSemidef := by
       rw [← hblockK]
       exact hK.hadamard (by rw [hyform]; exact hY)
     let t : Matrix Unit Unit ℝ := (k0 ⊙ d) - wᴴ * C⁻¹ * w
     have ht : t.PosSemidef := by
       have hh := (Matrix.PosDef.fromBlocks₁₁ (A:=C) w (k0 ⊙ d) hCp).mp hfullT
       simpa [t] using hh
     have hblockXY : (X ⊙ Y) = Matrix.fromBlocks C w wᴴ (a ⊙ d) := by
       rw [← hxform, ← hyform]
       ext i j
       cases i with
       | inl i => cases j with
         | inl j => rfl
         | inr j => rfl
       | inr i => cases j with
         | inl j =>
           simp [Matrix.fromBlocks_apply₂₁, Matrix.hadamard_apply,
             w, Matrix.conjTranspose_apply, mul_comm]
         | inr j => rfl
     let z : Matrix Unit Unit ℝ := (a ⊙ d) - wᴴ * C⁻¹ * w
     have hdetXY : (X ⊙ Y).det = C.det * z.det := by
       rw [hblockXY]
       simpa [z, Matrix.invOf_eq_nonsing_inv] using
         (Matrix.det_fromBlocks₁₁ C w wᴴ (a ⊙ d))
     have hzentry : z () () = t () () + r () () * d () () := by
       simp [z,t,r,k0, Matrix.hadamard_apply, Matrix.sub_apply]
       ring
     have hprodY : (∏ i:m ⊕ Unit, Y i i) = (∏ i:m, D i i) * d () () := by
       rw [← hyform, Fintype.prod_sum_type]
       simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
          Fintype.prod_unique]
     have hr0 : 0 ≤ r () () := hr.diag_nonneg
     have ht0 : 0 ≤ t () () := ht.diag_nonneg
     have hih : A.det * ∏ i:m, D i i ≤ C.det := by simpa [C] using ih
     calc
       X.det * (∏ i:m ⊕ Unit, Y i i) =
            (A.det * ∏ i:m, D i i) * (r () () * d () ()) := by
              rw [hdetX, hprodY, Matrix.det_unique r]
              ring
       _ ≤ C.det * (r () () * d () ()) :=
          mul_le_mul_of_nonneg_right hih (mul_nonneg hr0 (le_of_lt hdpos))
       _ ≤ C.det * (t () () + r () () * d () ()) := by
          have hc0 : 0 ≤ C.det := le_of_lt hCpos
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ht0) hc0
       _ = (X ⊙ Y).det := by
          rw [hdetXY, Matrix.det_unique z, hzentry]
    have hfin : ∀ k : ℕ,
        ∀ {X Y : Matrix (Fin k) (Fin k) ℝ}, X.PosDef → Y.PosSemidef →
          (∀ i, 0 < Y i i) → X.det * ∏ i, Y i i ≤ (X ⊙ Y).det := by
      intro k
      induction k with
      | zero =>
        intro X Y hX hY hd
        simpa [Matrix.det_fin_zero] using (show (1 : ℝ) ≤ 1 from le_rfl)
      | succ k ih =>
        classical
        let t1 : (Fin k ⊕ Unit) ≃ Fin (k+1) :=
          (Equiv.sumCongr (Equiv.refl (Fin k)) (finOneEquiv.symm)).trans
            (finSumFinEquiv (m:=k) (n:=1))
        let e : Fin (Nat.succ k) ≃ (Fin k ⊕ Unit) :=
          (finCongr (Nat.succ_eq_add_one k)).trans t1.symm
        intro X Y hX hY hd
        let X' : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ :=
          Matrix.reindex e e X
        let Y' : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ :=
          Matrix.reindex e e Y
        have hX' : X'.PosDef := by
          change (X.submatrix e.symm e.symm).PosDef
          exact hX.submatrix e.symm.injective
        have hY' : Y'.PosSemidef := by
          change (Y.submatrix e.symm e.symm).PosSemidef
          exact hY.submatrix e.symm
        have hd' : ∀ i, 0 < Y' i i := by
          intro i
          change 0 < Y (e.symm i) (e.symm i)
          exact hd _
        have hi := core_sum_step (m := Fin k) ih hX' hY' hd'
        have hxdet : X'.det = X.det := by
          simpa [X'] using (Matrix.det_reindex_self e X)
        have hprod' : (∏ i : (Fin k ⊕ Unit), Y' i i) =
              ∏ j : Fin (Nat.succ k), Y j j := by
          symm
          refine Fintype.prod_equiv e (fun j : Fin (Nat.succ k) => Y j j)
            (fun i : (Fin k ⊕ Unit) => Y' i i) ?_
          intro j
          simp [Y', Matrix.reindex_apply, Matrix.submatrix_apply]
        have hxydet : (X' ⊙ Y').det = (X ⊙ Y).det := by
          calc
            (X' ⊙ Y').det = (Matrix.reindex e e (X ⊙ Y)).det := by
              congr 1
            _ = (X ⊙ Y).det := Matrix.det_reindex_self e (X ⊙ Y)
        rw [hxdet, hprod', hxydet] at hi
        exact hi
    -- Reindex the given type by its equivalence with a `Fin` type.
    intro X Y hX hY hd
    let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
    let X' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
      Matrix.reindex e e X
    let Y' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
      Matrix.reindex e e Y
    have hX' : X'.PosDef := by
      change (X.submatrix e.symm e.symm).PosDef
      exact hX.submatrix e.symm.injective
    have hY' : Y'.PosSemidef := by
      change (Y.submatrix e.symm e.symm).PosSemidef
      exact hY.submatrix e.symm
    have hd' : ∀ i, 0 < Y' i i := by
      intro i
      change 0 < Y (e.symm i) (e.symm i)
      exact hd _
    have hi := hfin (Fintype.card n) hX' hY' hd'
    have hxdet : X'.det = X.det := by
      simpa [X'] using (Matrix.det_reindex_self e X)
    have hprod' : (∏ i : Fin (Fintype.card n), Y' i i) =
          ∏ j : n, Y j j := by
      symm
      refine Fintype.prod_equiv e (fun j : n => Y j j)
        (fun i : Fin (Fintype.card n) => Y' i i) ?_
      intro j
      simp [Y', Matrix.reindex_apply, Matrix.submatrix_apply]
    have hxydet : (X' ⊙ Y').det = (X ⊙ Y).det := by
      calc
        (X' ⊙ Y').det = (Matrix.reindex e e (X ⊙ Y)).det := by
          congr 1
        _ = (X ⊙ Y).det := Matrix.det_reindex_self e (X ⊙ Y)
    rw [hxdet, hprod', hxydet] at hi
    exact hi
  by_cases ha : A.det = 0
  · rw [ha, zero_mul]
    exact (hA.hadamard hB).det_nonneg
  have hAp : A.PosDef := hA.posDef_iff_det_ne_zero.mpr ha
  by_cases hb : ∃ i, B i i = 0
  · obtain ⟨i, hi⟩ := hb
    have hz : (∏ j, B j j) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hz, mul_zero]
    exact (hA.hadamard hB).det_nonneg
  · have hbpos : ∀ i, 0 < B i i := by
      intro i
      exact lt_of_le_of_ne hB.diag_nonneg (Ne.symm (fun h => hb ⟨i, h⟩))
    exact positive_core hAp hB hbpos


end Submission
