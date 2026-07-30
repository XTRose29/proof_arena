import Submission.Helpers
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Data.Matrix.Block

namespace Submission.Compression

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {I J : Type*}
variable [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

local instance matrixCStarAlgebra (K : Type*) [Fintype K] [DecidableEq K] :
    CStarAlgebra (Matrix K K ℂ) := {
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance }

local instance matrixPairCStarAlgebra :
    CStarAlgebra (Matrix I I ℂ × Matrix J J ℂ) := inferInstance

local instance matrixPairCFC :
    IsometricContinuousFunctionalCalculus ℝ
      (Matrix I I ℂ × Matrix J J ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

/-- The unital star homomorphism which realizes a pair of square matrices as a block-diagonal
matrix. -/
def blockDiagonalStarAlgHom :
    (Matrix I I ℂ × Matrix J J ℂ) →⋆ₐ[ℂ] Matrix (I ⊕ J) (I ⊕ J) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_zero' := by
    ext i j
    cases i <;> cases j <;> rfl
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Prod.fst_mul, Prod.snd_mul]
  map_add' p q := by
    simpa using
      (Matrix.fromBlocks_add p.1 0 0 p.2 q.1 0 0 q.2).symm
  commutes' r := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.algebraMap_matrix_apply]
  map_star' p := by
    simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

lemma continuous_blockDiagonalStarAlgHom :
    Continuous (blockDiagonalStarAlgHom :
      (Matrix I I ℂ × Matrix J J ℂ) → Matrix (I ⊕ J) (I ⊕ J) ℂ) := by
  unfold blockDiagonalStarAlgHom
  fun_prop

lemma cfc_blockDiagonal (f : ℝ → ℝ) (A : Matrix I I ℂ) (D : Matrix J J ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ D)) :
    cfc f (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (cfc f A) 0 0 (cfc f D) := by
  let φ := blockDiagonalStarAlgHom (I := I) (J := J)
  have hAD : IsSelfAdjoint (A, D) := Prod.ext hA.eq hD.eq
  have hprod :
      cfc f (A, D) = (cfc f A, cfc f D) :=
    cfc_map_prod (S := ℂ) (pab := IsSelfAdjoint) (pa := IsSelfAdjoint)
      (pb := IsSelfAdjoint) f A D hf hAD hA.isSelfAdjoint hD.isSelfAdjoint
  calc
    cfc f (Matrix.fromBlocks A 0 0 D) = cfc f (φ (A, D)) := rfl
    _ = φ (cfc f (A, D)) := by
      symm
      exact φ.map_cfc f (A, D) (by simpa [Prod.spectrum_eq] using hf)
        continuous_blockDiagonalStarAlgHom hAD
        (by
          change IsSelfAdjoint (Matrix.fromBlocks A 0 0 D)
          exact (hA.fromBlocks (by simp) hD).isSelfAdjoint)
    _ = Matrix.fromBlocks (cfc f A) 0 0 (cfc f D) := by rw [hprod]; rfl

lemma log_blockDiagonal (A : Matrix I I ℂ) (D : Matrix J J ℂ)
    (hA : A.PosDef) (hD : D.PosDef) :
    CFC.log (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (CFC.log A) 0 0 (CFC.log D) := by
  unfold CFC.log
  exact cfc_blockDiagonal Real.log A D hA.isHermitian hD.isHermitian
    ((A.finite_real_spectrum.union D.finite_real_spectrum).continuousOn Real.log)

lemma posDef_blockDiagonal (A : Matrix I I ℂ) (D : Matrix J J ℂ)
    (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  letI := hA.isUnit.invertible
  have hPSD : (Matrix.fromBlocks A 0 0 D).PosSemidef := by
    simpa using
      (Matrix.PosDef.fromBlocks₁₁ (B := (0 : Matrix I J ℂ)) D hA).2
        (by simpa using hD.posSemidef)
  rw [hPSD.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit).mul
    ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)

omit [DecidableEq I] in
lemma posDef_compression (A : Matrix I I ℂ) (V : Matrix I J ℂ)
    (hA : A.PosDef) (hV : Matrix.conjTranspose V * V = 1) :
    (Matrix.conjTranspose V * A * V).PosDef := by
  apply hA.conjTranspose_mul_mul_same
  intro x y hxy
  apply_fun (Matrix.mulVec (Matrix.conjTranspose V)) at hxy
  calc
    x = Matrix.mulVec (1 : Matrix J J ℂ) x := by simp
    _ = Matrix.mulVec (Matrix.conjTranspose V * V) x := by rw [hV]
    _ = Matrix.mulVec (Matrix.conjTranspose V) (Matrix.mulVec V x) :=
      (Matrix.mulVec_mulVec x (Matrix.conjTranspose V) V).symm
    _ = Matrix.mulVec (Matrix.conjTranspose V) (Matrix.mulVec V y) := hxy
    _ = Matrix.mulVec (Matrix.conjTranspose V * V) y :=
      Matrix.mulVec_mulVec y (Matrix.conjTranspose V) V
    _ = Matrix.mulVec (1 : Matrix J J ℂ) y := by rw [hV]
    _ = y := by simp

/-- The self-adjoint Halmos dilation of a rectangular isometry. -/
def halmosMatrix (V : Matrix I J ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks (1 - V * Matrix.conjTranspose V) V (Matrix.conjTranspose V) 0

omit [Fintype I] [DecidableEq J] in
lemma halmosMatrix_isHermitian (V : Matrix I J ℂ) :
    (halmosMatrix V).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_one.sub (Matrix.isHermitian_mul_conjTranspose_self V)
  · rfl
  · exact Matrix.isHermitian_zero

lemma halmosMatrix_sq (V : Matrix I J ℂ)
    (hV : Matrix.conjTranspose V * V = 1) :
    halmosMatrix V * halmosMatrix V = 1 := by
  let W := Matrix.conjTranspose V
  let P := V * W
  have hPV : P * V = V := by
    simp [P, W, Matrix.mul_assoc, hV]
  have hWP : W * P = W := by
    simp [P, W, ← Matrix.mul_assoc, hV]
  have hP2 : P * P = P := by
    calc
      P * P = V * (W * V) * W := by simp [P, Matrix.mul_assoc]
      _ = P := by rw [show W * V = 1 by simpa [W] using hV]; simp [P]
  rw [halmosMatrix, show V * Matrix.conjTranspose V = P by rfl,
    show Matrix.conjTranspose V = W by rfl, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (1 - P) * (1 - P) + V * W = 1 - P - P + P * P + P := by
        rw [show V * W = P by rfl]
        noncomm_ring
      _ = 1 := by rw [hP2]; abel
  · simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.sub_mul, Matrix.one_mul, hPV, sub_self]
  · simp only [Matrix.zero_mul, add_zero]
    rw [Matrix.mul_sub, Matrix.mul_one, hWP, sub_self]
  · simpa [W] using hV

def halmosUnitary (V : Matrix I J ℂ)
    (hV : Matrix.conjTranspose V * V = 1) :
    unitary (Matrix (I ⊕ J) (I ⊕ J) ℂ) :=
  ⟨halmosMatrix V, by
    have hstar : star (halmosMatrix V) = halmosMatrix V := by
      rw [Matrix.star_eq_conjTranspose, (halmosMatrix_isHermitian V).eq]
    change star (halmosMatrix V) * halmosMatrix V = 1 ∧
      halmosMatrix V * star (halmosMatrix V) = 1
    rw [hstar]
    exact ⟨halmosMatrix_sq V hV, halmosMatrix_sq V hV⟩⟩

/-- The block sign used to pinch a matrix to its two diagonal blocks. -/
def blockSign : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

omit [Fintype I] [Fintype J] in
lemma blockSign_isHermitian :
    (blockSign (I := I) (J := J)).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_one
  · simp
  · exact Matrix.isHermitian_one.neg

lemma blockSign_sq :
    blockSign (I := I) (J := J) * blockSign = 1 := by
  simp [blockSign, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

def blockSignUnitary : unitary (Matrix (I ⊕ J) (I ⊕ J) ℂ) :=
  ⟨blockSign, by
    have hstar : star (blockSign (I := I) (J := J)) = blockSign := by
      rw [Matrix.star_eq_conjTranspose, blockSign_isHermitian.eq]
    change star (blockSign (I := I) (J := J)) * blockSign = 1 ∧
      blockSign * star (blockSign (I := I) (J := J)) = 1
    rw [hstar]
    exact ⟨blockSign_sq, blockSign_sq⟩⟩

lemma log_unitary_conjugate {K : Type*} [Fintype K] [DecidableEq K]
    (U : unitary (Matrix K K ℂ)) (A : Matrix K K ℂ) (hA : A.PosDef) :
    CFC.log ((U : Matrix K K ℂ) * A * star (U : Matrix K K ℂ)) =
      (U : Matrix K K ℂ) * CFC.log A * star (U : Matrix K K ℂ) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix K K ℂ) U
  unfold CFC.log
  simpa only [φ, Unitary.conjStarAlgAut_apply] using
    (StarAlgHomClass.map_cfc φ Real.log A
      (A.finite_real_spectrum.continuousOn Real.log)
      (by
        unfold φ
        fun_prop)
      hA.isHermitian.isSelfAdjoint).symm

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma toBlocks₂₂_mono {P Q : Matrix (I ⊕ J) (I ⊕ J) ℂ} (h : P ≤ Q) :
    P.toBlocks₂₂ ≤ Q.toBlocks₂₂ := by
  rw [Matrix.le_iff] at h ⊢
  have hs := h.submatrix (fun j : J ↦ Sum.inr j)
  have heq :
      (Q - P).submatrix (fun j : J ↦ Sum.inr j) (fun j : J ↦ Sum.inr j) =
        Q.toBlocks₂₂ - P.toBlocks₂₂ := by
    ext i j
    rfl
  rwa [heq] at hs

/-- Jensen's operator inequality for compressing the logarithm by a rectangular isometry. -/
theorem log_compression_le (A : Matrix I I ℂ) (V : Matrix I J ℂ)
    (hA : A.PosDef) (hV : Matrix.conjTranspose V * V = 1) :
    Matrix.conjTranspose V * CFC.log A * V ≤
      CFC.log (Matrix.conjTranspose V * A * V) := by
  let u := halmosUnitary V hV
  let r : unitary (Matrix (I ⊕ J) (I ⊕ J) ℂ) := blockSignUnitary
  let X : Matrix (I ⊕ J) (I ⊕ J) ℂ := Matrix.fromBlocks A 0 0 1
  let Y : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
    (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) * X * star (u : Matrix (I ⊕ J) (I ⊕ J) ℂ)
  let Z : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
    (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) * Y * star (r : Matrix (I ⊕ J) (I ⊕ J) ℂ)
  let half : ℝ := 1 / 2
  let H : Matrix (I ⊕ J) (I ⊕ J) ℂ := half • Y + half • Z

  have hhalf : 0 < half := by norm_num [half]
  have hXpos : X.PosDef := by
    exact posDef_blockDiagonal A 1 hA Matrix.PosDef.one
  have hYpos : Y.PosDef := by
    have hu : IsUnit (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) := Unitary.isUnit_coe
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).mpr hXpos
  have hZpos : Z.PosDef := by
    have hr : IsUnit (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) := Unitary.isUnit_coe
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hr).mpr hYpos
  have hHpos : H.PosDef := (hYpos.smul hhalf).add (hZpos.smul hhalf)

  have hstarU :
      star (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) =
        (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) := by
    change star (halmosMatrix V) = halmosMatrix V
    rw [Matrix.star_eq_conjTranspose, (halmosMatrix_isHermitian V).eq]
  have hstarR :
      star (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) =
        (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) := by
    change star (blockSign (I := I) (J := J)) = blockSign
    rw [Matrix.star_eq_conjTranspose, blockSign_isHermitian.eq]

  have hlogX :
      CFC.log X = Matrix.fromBlocks (CFC.log A) 0 0 0 := by
    simpa [X] using log_blockDiagonal A (1 : Matrix J J ℂ) hA Matrix.PosDef.one
  have hlogY :
      CFC.log Y =
        (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) * CFC.log X *
          star (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) :=
    log_unitary_conjugate u X hXpos
  have hlogZ :
      CFC.log Z =
        (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) * CFC.log Y *
          star (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) :=
    log_unitary_conjugate r Y hYpos

  have hbottomY :
      Y.toBlocks₂₂ = Matrix.conjTranspose V * A * V := by
    rw [show Y =
      (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) * X *
        star (u : Matrix (I ⊕ J) (I ⊕ J) ℂ) by rfl, hstarU]
    simp [u, halmosUnitary, halmosMatrix, X, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc]
  have hbottomLogY :
      (CFC.log Y).toBlocks₂₂ =
        Matrix.conjTranspose V * CFC.log A * V := by
    rw [hlogY, hlogX, hstarU]
    simp [u, halmosUnitary, halmosMatrix, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc]
  have hbottomLogZ :
      (CFC.log Z).toBlocks₂₂ = (CFC.log Y).toBlocks₂₂ := by
    rw [hlogZ, hstarR]
    rw [show CFC.log Y = Matrix.fromBlocks (CFC.log Y).toBlocks₁₁
      (CFC.log Y).toBlocks₁₂ (CFC.log Y).toBlocks₂₁
      (CFC.log Y).toBlocks₂₂ from (Matrix.fromBlocks_toBlocks _).symm]
    simp [r, blockSignUnitary, blockSign, Matrix.fromBlocks_multiply]

  have hHblocks :
      H = Matrix.fromBlocks Y.toBlocks₁₁ 0 0 Y.toBlocks₂₂ := by
    rw [show H = half • Y + half • Z by rfl,
      show Z = (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) * Y *
        star (r : Matrix (I ⊕ J) (I ⊕ J) ℂ) by rfl,
      hstarR,
      show Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂
        Y.toBlocks₂₁ Y.toBlocks₂₂ from (Matrix.fromBlocks_toBlocks Y).symm]
    simp [r, blockSignUnitary, blockSign, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
      Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← add_smul, show half + half = 1 by norm_num [half], one_smul]
    · simp
    · simp
    · rw [← add_smul, show half + half = 1 by norm_num [half], one_smul]
  have hTop : Y.toBlocks₁₁.PosDef := by
    have hprincipal :=
      hHpos.submatrix (e := fun i : I ↦ Sum.inl i) Sum.inl_injective
    change H.toBlocks₁₁.PosDef at hprincipal
    rw [hHblocks] at hprincipal
    exact hprincipal
  have hBottom : Y.toBlocks₂₂.PosDef := by
    rw [hbottomY]
    exact posDef_compression A V hA hV
  have hlogH :
      CFC.log H =
        Matrix.fromBlocks (CFC.log Y.toBlocks₁₁) 0 0
          (CFC.log Y.toBlocks₂₂) := by
    rw [hHblocks]
    exact log_blockDiagonal Y.toBlocks₁₁ Y.toBlocks₂₂ hTop hBottom
  have hbottomLogH :
      (CFC.log H).toBlocks₂₂ =
        CFC.log (Matrix.conjTranspose V * A * V) := by
    rw [hlogH, Matrix.toBlocks_fromBlocks₂₂, hbottomY]

  have hconcave :
      half • CFC.log Y + half • CFC.log Z ≤ CFC.log H := by
    exact CFC.concaveOn_log.2 hYpos.isStrictlyPositive hZpos.isStrictlyPositive
      hhalf.le hhalf.le (by norm_num [half])
  have hbottom := toBlocks₂₂_mono hconcave
  change half • (CFC.log Y).toBlocks₂₂ + half • (CFC.log Z).toBlocks₂₂ ≤
    (CFC.log H).toBlocks₂₂ at hbottom
  rw [hbottomLogZ, hbottomLogY, hbottomLogH] at hbottom
  have haverage (M : Matrix J J ℂ) : half • M + half • M = M := by
    rw [← add_smul, show half + half = 1 by norm_num [half], one_smul]
  rw [haverage] at hbottom
  exact hbottom

end

end Submission.Compression
