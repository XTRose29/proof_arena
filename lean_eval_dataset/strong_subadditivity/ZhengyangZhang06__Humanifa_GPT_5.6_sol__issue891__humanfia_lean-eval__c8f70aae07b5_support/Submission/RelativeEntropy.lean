import Submission.DataProcessing
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace Submission.RelativeEntropy

open Submission.DataProcessing
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

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

def kroneckerLeftStarAlgHom :
    Matrix I I ℂ →⋆ₐ[ℂ] Matrix (I × J) (I × J) ℂ where
  toFun X := X ⊗ₖ (1 : Matrix J J ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  map_add' X Y := Matrix.add_kronecker X Y 1
  commutes' r := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [Matrix.algebraMap_matrix_apply, h₁, h₂]
  map_star' X := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

def kroneckerRightStarAlgHom :
    Matrix J J ℂ →⋆ₐ[ℂ] Matrix (I × J) (I × J) ℂ where
  toFun X := (1 : Matrix I I ℂ) ⊗ₖ X
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  map_add' X Y := Matrix.kronecker_add 1 X Y
  commutes' r := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [Matrix.algebraMap_matrix_apply, h₁, h₂]
  map_star' X := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

lemma continuous_kroneckerLeftStarAlgHom :
    Continuous (kroneckerLeftStarAlgHom :
      Matrix I I ℂ → Matrix (I × J) (I × J) ℂ) := by
  unfold kroneckerLeftStarAlgHom
  fun_prop

lemma continuous_kroneckerRightStarAlgHom :
    Continuous (kroneckerRightStarAlgHom :
      Matrix J J ℂ → Matrix (I × J) (I × J) ℂ) := by
  unfold kroneckerRightStarAlgHom
  fun_prop

lemma cfc_kronecker_one (f : ℝ → ℝ) (X : Matrix I I ℂ)
    (hX : X.IsHermitian) (hf : ContinuousOn f (spectrum ℝ X)) :
    cfc f (X ⊗ₖ (1 : Matrix J J ℂ)) =
      cfc f X ⊗ₖ (1 : Matrix J J ℂ) := by
  let φ := kroneckerLeftStarAlgHom (I := I) (J := J)
  change cfc f (φ X) = φ (cfc f X)
  symm
  exact φ.map_cfc f X hf continuous_kroneckerLeftStarAlgHom
    hX.isSelfAdjoint (by
      change IsSelfAdjoint (X ⊗ₖ (1 : Matrix J J ℂ))
      rw [← Matrix.isHermitian_iff_isSelfAdjoint]
      change Matrix.conjTranspose (X ⊗ₖ (1 : Matrix J J ℂ)) = X ⊗ₖ 1
      rw [Matrix.conjTranspose_kronecker, hX.eq]
      simp)

lemma cfc_one_kronecker (f : ℝ → ℝ) (X : Matrix J J ℂ)
    (hX : X.IsHermitian) (hf : ContinuousOn f (spectrum ℝ X)) :
    cfc f ((1 : Matrix I I ℂ) ⊗ₖ X) =
      (1 : Matrix I I ℂ) ⊗ₖ cfc f X := by
  let φ := kroneckerRightStarAlgHom (I := I) (J := J)
  change cfc f (φ X) = φ (cfc f X)
  symm
  exact φ.map_cfc f X hf continuous_kroneckerRightStarAlgHom
    hX.isSelfAdjoint (by
      change IsSelfAdjoint ((1 : Matrix I I ℂ) ⊗ₖ X)
      rw [← Matrix.isHermitian_iff_isSelfAdjoint]
      change Matrix.conjTranspose ((1 : Matrix I I ℂ) ⊗ₖ X) = 1 ⊗ₖ X
      rw [Matrix.conjTranspose_kronecker, hX.eq]
      simp)

lemma log_kronecker_one (X : Matrix I I ℂ) (hX : X.PosDef) :
    CFC.log (X ⊗ₖ (1 : Matrix J J ℂ)) =
      CFC.log X ⊗ₖ (1 : Matrix J J ℂ) := by
  unfold CFC.log
  exact cfc_kronecker_one Real.log X hX.isHermitian
    (X.finite_real_spectrum.continuousOn Real.log)

lemma log_one_kronecker (X : Matrix J J ℂ) (hX : X.PosDef) :
    CFC.log ((1 : Matrix I I ℂ) ⊗ₖ X) =
      (1 : Matrix I I ℂ) ⊗ₖ CFC.log X := by
  unfold CFC.log
  exact cfc_one_kronecker Real.log X hX.isHermitian
    (X.finite_real_spectrum.continuousOn Real.log)

lemma log_mul_of_commute_pos {K : Type*} [Fintype K] [DecidableEq K]
    (X Y : Matrix K K ℂ) (hX : X.PosDef) (hY : Y.PosDef)
    (hXY : Commute X Y) :
    CFC.log (X * Y) = CFC.log X + CFC.log Y := by
  have hlogs : Commute (CFC.log X) (CFC.log Y) :=
    ((hXY.cfc_real Real.log).symm.cfc_real Real.log).symm
  calc
    CFC.log (X * Y) =
        CFC.log (NormedSpace.exp (CFC.log X + CFC.log Y)) := by
      rw [Matrix.exp_add_of_commute _ _ hlogs, CFC.exp_log X hX.isStrictlyPositive,
        CFC.exp_log Y hY.isStrictlyPositive]
    _ = CFC.log X + CFC.log Y :=
      CFC.log_exp _ (IsSelfAdjoint.log.add IsSelfAdjoint.log)

lemma log_ringInverse {K : Type*} [Fintype K] [DecidableEq K]
    (X : Matrix K K ℂ) (hX : X.PosDef) :
    CFC.log (Ring.inverse X) = -CFC.log X := by
  have hcomm : Commute X (Ring.inverse X) := by
    rw [Commute]
    exact (Ring.mul_inverse_cancel X hX.isUnit).trans
      (Ring.inverse_mul_cancel X hX.isUnit).symm
  have h := log_mul_of_commute_pos X (Ring.inverse X) hX
    (Matrix.isStrictlyPositive_iff_posDef.mp hX.isStrictlyPositive.ringInverse) hcomm
  rw [Ring.mul_inverse_cancel X hX.isUnit, CFC.log_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

def matrixConjStarAlgHom :
    Matrix I I ℂ →⋆ₐ[ℝ] Matrix I I ℂ where
  toFun X := X.map Complex.conjAe
  map_zero' := by ext; simp
  map_one' := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  map_mul' X Y := Matrix.map_mul
  map_add' X Y := by ext; simp
  commutes' r := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  map_star' X := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

lemma continuous_matrixConjStarAlgHom :
    Continuous (matrixConjStarAlgHom : Matrix I I ℂ → Matrix I I ℂ) := by
  change Continuous
    (fun X : Matrix I I ℂ ↦ fun i j ↦ Complex.conjAe (X i j))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))

omit [Fintype I] [DecidableEq I] in
lemma map_conj_eq_transpose_of_isHermitian (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    X.map Complex.conjAe = X.transpose := by
  ext i j
  have h := congrArg (fun M : Matrix I I ℂ ↦ M j i) hX.eq
  simpa [Matrix.conjTranspose_apply] using h

lemma map_conj_cfc (f : ℝ → ℝ) (X : Matrix I I ℂ)
    (hX : X.IsHermitian) (hf : ContinuousOn f (spectrum ℝ X)) :
    (cfc f X).map Complex.conjAe = cfc f (X.map Complex.conjAe) := by
  let φ := matrixConjStarAlgHom (I := I)
  change φ (cfc f X) = cfc f (φ X)
  exact φ.map_cfc f X hf continuous_matrixConjStarAlgHom hX.isSelfAdjoint (by
    change (X.map Complex.conjAe).IsHermitian
    rw [map_conj_eq_transpose_of_isHermitian X hX]
    exact hX.transpose)

lemma cfc_transpose (f : ℝ → ℝ) (X : Matrix I I ℂ)
    (hX : X.IsHermitian) (hf : ContinuousOn f (spectrum ℝ X)) :
    cfc f X.transpose = (cfc f X).transpose := by
  calc
    cfc f X.transpose = cfc f (X.map Complex.conjAe) := by
      rw [map_conj_eq_transpose_of_isHermitian X hX]
    _ = (cfc f X).map Complex.conjAe := (map_conj_cfc f X hX hf).symm
    _ = (cfc f X).transpose := by
      exact map_conj_eq_transpose_of_isHermitian _
        (cfc_predicate f X).isHermitian

lemma log_transpose_ringInverse (X : Matrix I I ℂ) (hX : X.PosDef) :
    CFC.log (Matrix.transpose (Ring.inverse X)) =
      -Matrix.transpose (CFC.log X) := by
  have hinv : (Ring.inverse X).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp hX.isStrictlyPositive.ringInverse
  calc
    CFC.log (Matrix.transpose (Ring.inverse X)) =
        Matrix.transpose (CFC.log (Ring.inverse X)) := by
      unfold CFC.log
      exact cfc_transpose Real.log (Ring.inverse X) hinv.isHermitian
        ((Ring.inverse X).finite_real_spectrum.continuousOn Real.log)
    _ = -Matrix.transpose (CFC.log X) := by
      rw [log_ringInverse X hX, Matrix.transpose_neg]

lemma relativeModular_log (P Q : Matrix I I ℂ) (hP : P.PosDef) (hQ : Q.PosDef) :
    CFC.log (relativeModular P Q) =
      (-Matrix.transpose (CFC.log P)) ⊗ₖ (1 : Matrix I I ℂ) +
        (1 : Matrix I I ℂ) ⊗ₖ CFC.log Q := by
  let L : Matrix (I × I) (I × I) ℂ :=
    Matrix.transpose (Ring.inverse P) ⊗ₖ (1 : Matrix I I ℂ)
  let R : Matrix (I × I) (I × I) ℂ :=
    (1 : Matrix I I ℂ) ⊗ₖ Q
  have hinv : (Ring.inverse P).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp hP.isStrictlyPositive.ringInverse
  have hL : L.PosDef := hinv.transpose.kronecker Matrix.PosDef.one
  have hR : R.PosDef := Matrix.PosDef.one.kronecker hQ
  have hcomm : Commute L R := by
    change L * R = R * L
    simp only [L, R, ← Matrix.mul_kronecker_mul]
    simp
  have hfactor : relativeModular P Q = L * R := by
    change Matrix.transpose (Ring.inverse P) ⊗ₖ Q =
      (Matrix.transpose (Ring.inverse P) ⊗ₖ (1 : Matrix I I ℂ)) *
        ((1 : Matrix I I ℂ) ⊗ₖ Q)
    rw [← Matrix.mul_kronecker_mul]
    simp
  rw [hfactor, log_mul_of_commute_pos L R hL hR hcomm]
  simp only [L, R, log_kronecker_one _ hinv.transpose, log_one_kronecker Q hQ,
    log_transpose_ringInverse P hP]

def matrixRelativeEntropy (P Q : Matrix I I ℂ) : ℝ :=
  Complex.re (Matrix.trace (P * (CFC.log P - CFC.log Q)))

lemma relativeModular_log_mulVec_sqrt (P Q : Matrix I I ℂ)
    (hP : P.PosDef) (hQ : Q.PosDef) :
    Matrix.mulVec (CFC.log (relativeModular P Q)) (Matrix.vec (CFC.sqrt P)) =
      Matrix.vec
        (-(CFC.sqrt P * CFC.log P) + CFC.log Q * CFC.sqrt P) := by
  rw [relativeModular_log P Q hP hQ, Matrix.add_mulVec,
    Matrix.kronecker_mulVec_vec, Matrix.kronecker_mulVec_vec]
  simp [Matrix.transpose_neg]

lemma matrixRelativeEntropy_eq_neg_re_quadratic
    (P Q : Matrix I I ℂ) (hP : P.PosDef) (hQ : Q.PosDef) :
    matrixRelativeEntropy P Q =
      -Complex.re
        (star (Matrix.vec (CFC.sqrt P)) ⬝ᵥ
          Matrix.mulVec (CFC.log (relativeModular P Q))
            (Matrix.vec (CFC.sqrt P))) := by
  let S : Matrix I I ℂ := CFC.sqrt P
  have hS : S.IsHermitian := (CFC.sqrt_nonneg P).isSelfAdjoint.isHermitian
  have hSsq : S * S = P := CFC.sqrt_mul_sqrt_self P
  have htrace :
      Matrix.trace
          (Matrix.conjTranspose S *
            (-(S * CFC.log P) + CFC.log Q * S)) =
        -Matrix.trace (P * CFC.log P) + Matrix.trace (P * CFC.log Q) := by
    rw [hS.eq]
    calc
      Matrix.trace (S * (-(S * CFC.log P) + CFC.log Q * S)) =
          -Matrix.trace ((S * S) * CFC.log P) +
            Matrix.trace (S * (CFC.log Q * S)) := by
        simp [Matrix.mul_add, Matrix.mul_assoc]
      _ = -Matrix.trace (P * CFC.log P) +
          Matrix.trace (S * (S * CFC.log Q)) := by
        rw [hSsq, Matrix.trace_mul_cycle']
      _ = -Matrix.trace (P * CFC.log P) +
          Matrix.trace (P * CFC.log Q) := by rw [← Matrix.mul_assoc, hSsq]
  rw [relativeModular_log_mulVec_sqrt P Q hP hQ,
    Matrix.star_vec_dotProduct_vec]
  change matrixRelativeEntropy P Q =
    -Complex.re
      (Matrix.trace
        (Matrix.conjTranspose S *
          (-(S * CFC.log P) + CFC.log Q * S)))
  rw [htrace]
  simp [matrixRelativeEntropy, Matrix.mul_sub]
  ring

lemma quadratic_compression {K L : Type*}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (M : Matrix K K ℂ) (V : Matrix K L ℂ) (x : L → ℂ) :
    star x ⬝ᵥ
        Matrix.mulVec (Matrix.conjTranspose V * M * V) x =
      star (Matrix.mulVec V x) ⬝ᵥ
        Matrix.mulVec M (Matrix.mulVec V x) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem matrixRelativeEntropy_traceLeft_le
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A]
    (P Q : Matrix (A × B) (A × B) ℂ) (hP : P.PosDef) (hQ : Q.PosDef) :
    matrixRelativeEntropy P.traceLeft Q.traceLeft ≤ matrixRelativeEntropy P Q := by
  let PB : Matrix B B ℂ := P.traceLeft
  let QB : Matrix B B ℂ := Q.traceLeft
  let S : Matrix (A × B) (A × B) ℂ := CFC.sqrt P
  let R : Matrix B B ℂ := CFC.sqrt (Ring.inverse PB)
  let W : Matrix ((A × B) × (A × B)) (B × B) ℂ :=
    petzLiftOperator R S

  have hPB : PB.PosDef := Submission.Helpers.posDef_traceLeft P hP
  have hQB : QB.PosDef := Submission.Helpers.posDef_traceLeft Q hQ
  have hS : S.IsHermitian := (CFC.sqrt_nonneg P).isSelfAdjoint.isHermitian
  have hSsq : S * S = P := CFC.sqrt_mul_sqrt_self P
  have hR : R.IsHermitian :=
    (CFC.sqrt_nonneg (Ring.inverse PB)).isSelfAdjoint.isHermitian
  have hRsq : R * R = Ring.inverse PB :=
    CFC.sqrt_mul_sqrt_self (Ring.inverse PB)
  have hRPR : R * PB * R = 1 := by
    simpa [R, CFC.conjSqrt_apply] using
      (CFC.conjSqrt_ringInverse_self PB)
  have hSinv : S * Ring.inverse P * S = 1 := by
    have hinvP : (Ring.inverse P).PosDef :=
      Matrix.isStrictlyPositive_iff_posDef.mp hP.isStrictlyPositive.ringInverse
    have h := CFC.conjSqrt_ringInverse_self (Ring.inverse P)
    rw [CFC.conjSqrt_apply, Ring.inverse_inverse hP.isUnit] at h
    exact h
  have hsqrt_mul_R : CFC.sqrt PB * R = 1 := by
    change CFC.sqrt PB * CFC.sqrt (Ring.inverse PB) = 1
    rw [CFC.sqrt_ringInverse]
    exact Ring.mul_inverse_cancel _ hPB.isStrictlyPositive.isUnit_cfcSqrt
  have hWv :
      Matrix.mulVec W (Matrix.vec (CFC.sqrt PB)) =
        Matrix.vec (CFC.sqrt P) := by
    change Matrix.mulVec (petzLiftOperator R S) (Matrix.vec (CFC.sqrt PB)) =
      Matrix.vec S
    rw [petzLiftOperator_mulVec]
    simp [petzLiftMatrix, hsqrt_mul_R]
  have hW : Matrix.conjTranspose W * W = 1 :=
    petzLiftOperator_isometry P R S hS hSsq hR (by simpa [PB] using hRPR)
  have hcompress :
      Matrix.conjTranspose W * relativeModular P Q * W =
        relativeModular PB QB := by
    exact petzLiftOperator_compress_relativeModular P Q R S hS hSinv hR
      (by simpa [PB] using hRsq)

  have hmod : (relativeModular P Q).PosDef :=
    relativeModular_posDef P Q hP hQ
  have hlog :
      Matrix.conjTranspose W * CFC.log (relativeModular P Q) * W ≤
        CFC.log (relativeModular PB QB) := by
    have h := Submission.Compression.log_compression_le
      (relativeModular P Q) W hmod hW
    rwa [hcompress] at h
  have hdiff :
      (CFC.log (relativeModular PB QB) -
        Matrix.conjTranspose W * CFC.log (relativeModular P Q) * W).PosSemidef :=
    Matrix.le_iff.mp hlog
  let v : B × B → ℂ := Matrix.vec (CFC.sqrt PB)
  have hquad₀ := hdiff.dotProduct_mulVec_nonneg v
  have hquad :
      star v ⬝ᵥ
          Matrix.mulVec
            (Matrix.conjTranspose W * CFC.log (relativeModular P Q) * W) v ≤
        star v ⬝ᵥ Matrix.mulVec (CFC.log (relativeModular PB QB)) v := by
    rw [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hquad₀
    exact hquad₀
  have hquadRe := RCLike.re_le_re hquad
  rw [quadratic_compression, hWv] at hquadRe
  rw [matrixRelativeEntropy_eq_neg_re_quadratic P.traceLeft Q.traceLeft
      (by simpa [PB] using hPB) (by simpa [QB] using hQB),
    matrixRelativeEntropy_eq_neg_re_quadratic P Q hP hQ]
  exact neg_le_neg hquadRe

end

end Submission.RelativeEntropy
