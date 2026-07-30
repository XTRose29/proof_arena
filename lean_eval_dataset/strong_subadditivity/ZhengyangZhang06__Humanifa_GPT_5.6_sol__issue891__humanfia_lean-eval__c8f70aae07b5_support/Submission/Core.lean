import Submission.RelativeEntropy
import Submission.Reduction

namespace Submission.Core

open LeanEval.Physics
open Submission.Reduction
open Submission.RelativeEntropy
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {I J K : Type*}
variable [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

local instance matrixCStarAlgebra (L : Type*) [Fintype L] [DecidableEq L] :
    CStarAlgebra (Matrix L L ℂ) := {
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance }

/-- Simultaneously reindexing the rows and columns is a star-algebra equivalence. -/
def reindexStarAlgEquiv (e : I ≃ J) :
    Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_smul' r M := by
    ext i j
    rfl
  map_star' M := by
    change Matrix.conjTranspose (Matrix.reindex e e M) =
      Matrix.reindex e e (Matrix.conjTranspose M)
    exact Matrix.conjTranspose_reindex e e M

lemma continuous_reindexStarAlgEquiv (e : I ≃ J) :
    Continuous (reindexStarAlgEquiv e : Matrix I I ℂ → Matrix J J ℂ) := by
  change Continuous
    (fun M : Matrix I I ℂ ↦ fun i j ↦ M (e.symm i) (e.symm j))
  fun_prop

lemma log_reindex (M : Matrix I I ℂ) (hM : M.IsHermitian) (e : I ≃ J) :
    CFC.log (M.reindex e e) = (CFC.log M).reindex e e := by
  let φ := reindexStarAlgEquiv e
  unfold CFC.log
  change cfc Real.log (φ M) = φ (cfc Real.log M)
  symm
  exact StarAlgHomClass.map_cfc φ Real.log M
    (M.finite_real_spectrum.continuousOn Real.log)
    (continuous_reindexStarAlgEquiv e)
    hM.isSelfAdjoint
    (hM.reindex e).isSelfAdjoint

omit [DecidableEq I] [DecidableEq J] [DecidableEq K] [Fintype K] in
lemma trace_reindex (M : Matrix I I ℂ) (e : I ≃ J) :
    Matrix.trace (M.reindex e e) = Matrix.trace M := by
  unfold Matrix.trace Matrix.diag
  exact (Fintype.sum_equiv e (fun i ↦ M i i)
    (fun j ↦ M (e.symm j) (e.symm j)) (fun i ↦ by simp)).symm

omit [Fintype K] [DecidableEq K] in
lemma entropy_reindex (M : Matrix I I ℂ) (hM : M.IsHermitian) (e : I ≃ J) :
    entropy (M.reindex e e) = entropy M := by
  rw [entropy, entropy]
  change -Complex.re
      (Matrix.trace (M.reindex e e * CFC.log (M.reindex e e))) =
    -Complex.re (Matrix.trace (M * CFC.log M))
  rw [log_reindex M hM e]
  have hmul :
      M.reindex e e * (CFC.log M).reindex e e =
        (M * CFC.log M).reindex e e := by
    exact Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ) e e e M (CFC.log M)
  rw [hmul, trace_reindex (M * CFC.log M) e]

omit [Fintype K] [DecidableEq K] in
lemma matrixRelativeEntropy_reindex
    (P Q : Matrix I I ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian) (e : I ≃ J) :
    matrixRelativeEntropy (P.reindex e e) (Q.reindex e e) =
      matrixRelativeEntropy P Q := by
  rw [matrixRelativeEntropy, matrixRelativeEntropy]
  change Complex.re
      (Matrix.trace
        (P.reindex e e *
          (CFC.log (P.reindex e e) - CFC.log (Q.reindex e e)))) =
    Complex.re (Matrix.trace (P * (CFC.log P - CFC.log Q)))
  rw [log_reindex P hP e, log_reindex Q hQ e]
  have hsub :
      (CFC.log P).reindex e e - (CFC.log Q).reindex e e =
        (CFC.log P - CFC.log Q).reindex e e := rfl
  have hmul :
      P.reindex e e * (CFC.log P - CFC.log Q).reindex e e =
        (P * (CFC.log P - CFC.log Q)).reindex e e := by
    exact Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ) e e e P
      (CFC.log P - CFC.log Q)
  rw [hsub, hmul, trace_reindex (P * (CFC.log P - CFC.log Q)) e]

lemma log_kronecker (X : Matrix I I ℂ) (Y : Matrix J J ℂ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    CFC.log (X ⊗ₖ Y) =
      CFC.log X ⊗ₖ (1 : Matrix J J ℂ) +
        (1 : Matrix I I ℂ) ⊗ₖ CFC.log Y := by
  let L : Matrix (I × J) (I × J) ℂ := X ⊗ₖ (1 : Matrix J J ℂ)
  let R : Matrix (I × J) (I × J) ℂ := (1 : Matrix I I ℂ) ⊗ₖ Y
  have hL : L.PosDef := hX.kronecker Matrix.PosDef.one
  have hR : R.PosDef := Matrix.PosDef.one.kronecker hY
  have hcomm : Commute L R := by
    change L * R = R * L
    simp only [L, R, ← Matrix.mul_kronecker_mul]
    simp
  have hfactor : X ⊗ₖ Y = L * R := by
    change X ⊗ₖ Y =
      (X ⊗ₖ (1 : Matrix J J ℂ)) * ((1 : Matrix I I ℂ) ⊗ₖ Y)
    rw [← Matrix.mul_kronecker_mul]
    simp
  rw [hfactor, log_mul_of_commute_pos L R hL hR hcomm]
  simp only [L, R, log_kronecker_one X hX, log_one_kronecker Y hY]

omit [DecidableEq I] [DecidableEq K] [Fintype K] in
lemma trace_kronecker_mul_one_mul (X : Matrix I I ℂ)
    (M : Matrix (I × J) (I × J) ℂ) :
    Matrix.trace (((X ⊗ₖ (1 : Matrix J J ℂ)) * M)) =
      Matrix.trace (X * M.traceRight) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.traceRight, Fintype.sum_prod_type,
    Matrix.one_apply]
  simp_rw [Finset.mul_sum]
  change
    (∑ x : I, ∑ y : J, ∑ x' : I, X x x' * M (x', y) (x, y)) =
      ∑ x : I, ∑ x' : I, ∑ y : J, X x x' * M (x', y) (x, y)
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_comm

variable [Nonempty I] [Nonempty J]

omit [Fintype K] [DecidableEq K] in
lemma matrixRelativeEntropy_marginals (P : Matrix (I × J) (I × J) ℂ)
    (hP : P.PosDef) :
    matrixRelativeEntropy P (P.traceRight ⊗ₖ P.traceLeft) =
      -entropy P + entropy P.traceRight + entropy P.traceLeft := by
  have hRight : P.traceRight.PosDef :=
    Submission.Helpers.posDef_traceRight P hP
  have hLeft : P.traceLeft.PosDef :=
    Submission.Helpers.posDef_traceLeft P hP
  have hlog :
      CFC.log (P.traceRight ⊗ₖ P.traceLeft) =
        CFC.log P.traceRight ⊗ₖ (1 : Matrix J J ℂ) +
          (1 : Matrix I I ℂ) ⊗ₖ CFC.log P.traceLeft :=
    log_kronecker P.traceRight P.traceLeft hRight hLeft
  have htraceRight :
      Matrix.trace
          (P * (CFC.log P.traceRight ⊗ₖ (1 : Matrix J J ℂ))) =
        Matrix.trace (P.traceRight * CFC.log P.traceRight) := by
    calc
      Matrix.trace
          (P * (CFC.log P.traceRight ⊗ₖ (1 : Matrix J J ℂ))) =
          Matrix.trace
            ((CFC.log P.traceRight ⊗ₖ (1 : Matrix J J ℂ)) * P) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (CFC.log P.traceRight * P.traceRight) :=
        trace_kronecker_mul_one_mul (CFC.log P.traceRight) P
      _ = Matrix.trace (P.traceRight * CFC.log P.traceRight) :=
        Matrix.trace_mul_comm _ _
  have htraceLeft :
      Matrix.trace
          (P * ((1 : Matrix I I ℂ) ⊗ₖ CFC.log P.traceLeft)) =
        Matrix.trace (P.traceLeft * CFC.log P.traceLeft) := by
    calc
      Matrix.trace
          (P * ((1 : Matrix I I ℂ) ⊗ₖ CFC.log P.traceLeft)) =
          Matrix.trace
            (((1 : Matrix I I ℂ) ⊗ₖ CFC.log P.traceLeft) * P) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (CFC.log P.traceLeft * P.traceLeft) :=
        Submission.DataProcessing.trace_kronecker_one_mul (CFC.log P.traceLeft) P
      _ = Matrix.trace (P.traceLeft * CFC.log P.traceLeft) :=
        Matrix.trace_mul_comm _ _
  rw [matrixRelativeEntropy, hlog, Matrix.mul_sub, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add, htraceRight, htraceLeft]
  simp [entropy, CFC.log]
  ring

omit [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Nonempty I] [Nonempty J] in
lemma traceLeft_reindex_assoc_kronecker (X : Matrix (I × J) (I × J) ℂ)
    (Y : Matrix K K ℂ) :
    ((X ⊗ₖ Y).reindex (Equiv.prodAssoc I J K) (Equiv.prodAssoc I J K)).traceLeft =
      X.traceLeft ⊗ₖ Y := by
  ext ⟨j, k⟩ ⟨j', k'⟩
  simp [Matrix.traceLeft, Matrix.reindex_apply, Matrix.submatrix_apply,
    Finset.sum_mul]

omit [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Nonempty I] [Nonempty J] in
lemma traceLeft_reindex_symm_assoc
    (M : Matrix (I × (J × K)) (I × (J × K)) ℂ) :
    (M.reindex (Equiv.prodAssoc I J K).symm
      (Equiv.prodAssoc I J K).symm).traceLeft =
      M.traceLeft.traceLeft := by
  ext k k'
  simp [Matrix.traceLeft, Matrix.reindex_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Nonempty I] [Nonempty J] in
lemma traceLeft_traceRight_reindex_symm_assoc
    (M : Matrix (I × (J × K)) (I × (J × K)) ℂ) :
    ((M.reindex (Equiv.prodAssoc I J K).symm
      (Equiv.prodAssoc I J K).symm).traceRight).traceLeft =
      M.traceLeft.traceRight := by
  ext j j'
  simp [Matrix.traceLeft, Matrix.traceRight, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [Finset.sum_comm]

variable [Nonempty K]

theorem strong_subadditivity_posDef
    (M : Matrix (I × J × K) (I × J × K) ℂ) (hM : M.PosDef) :
    SSA M := by
  let e := Equiv.prodAssoc I J K
  let P : Matrix ((I × J) × K) ((I × J) × K) ℂ :=
    M.reindex e.symm e.symm
  let Q₀ : Matrix ((I × J) × K) ((I × J) × K) ℂ :=
    P.traceRight ⊗ₖ P.traceLeft
  let Q : Matrix (I × (J × K)) (I × (J × K)) ℂ :=
    Q₀.reindex e e

  have hP : P.PosDef :=
    Submission.Helpers.posDef_reindex M hM e.symm
  have hPRight : P.traceRight.PosDef :=
    Submission.Helpers.posDef_traceRight P hP
  have hPLeft : P.traceLeft.PosDef :=
    Submission.Helpers.posDef_traceLeft P hP
  have hQ₀ : Q₀.PosDef := by
    exact hPRight.kronecker hPLeft
  have hQ : Q.PosDef :=
    Submission.Helpers.posDef_reindex Q₀ hQ₀ e

  have hP_reindex : P.reindex e e = M := by
    simp [P, e]
  have hQ_traceLeft :
      Q.traceLeft = P.traceRight.traceLeft ⊗ₖ P.traceLeft := by
    exact traceLeft_reindex_assoc_kronecker P.traceRight P.traceLeft
  have hP_left :
      P.traceLeft = M.traceLeft.traceLeft := by
    exact traceLeft_reindex_symm_assoc M
  have hP_right_left :
      P.traceRight.traceLeft = M.traceLeft.traceRight := by
    exact traceLeft_traceRight_reindex_symm_assoc M
  have hQ_reduced :
      Q.traceLeft = M.traceLeft.traceRight ⊗ₖ M.traceLeft.traceLeft := by
    rw [hQ_traceLeft, hP_right_left, hP_left]

  have hDPI :
      matrixRelativeEntropy M.traceLeft Q.traceLeft ≤
        matrixRelativeEntropy M Q :=
    matrixRelativeEntropy_traceLeft_le M Q hM hQ
  have hMLeft : M.traceLeft.PosDef :=
    Submission.Helpers.posDef_traceLeft M hM
  have hReduced :
      matrixRelativeEntropy M.traceLeft Q.traceLeft =
        -entropy M.traceLeft +
          entropy M.traceLeft.traceRight + entropy M.traceLeft.traceLeft := by
    rw [hQ_reduced]
    exact matrixRelativeEntropy_marginals M.traceLeft hMLeft
  have hFull :
      matrixRelativeEntropy M Q =
        -entropy M + entropy P.traceRight + entropy P.traceLeft := by
    calc
      matrixRelativeEntropy M Q =
          matrixRelativeEntropy (P.reindex e e) (Q₀.reindex e e) := by
        rw [hP_reindex]
      _ = matrixRelativeEntropy P Q₀ :=
        matrixRelativeEntropy_reindex P Q₀ hP.isHermitian hQ₀.isHermitian e
      _ = -entropy P + entropy P.traceRight + entropy P.traceLeft :=
        matrixRelativeEntropy_marginals P hP
      _ = -entropy M + entropy P.traceRight + entropy P.traceLeft := by
        rw [← entropy_reindex P hP.isHermitian e, hP_reindex]
  rw [hReduced, hFull, hP_left] at hDPI
  change entropy M + entropy M.traceLeft.traceRight ≤
    entropy P.traceRight + entropy M.traceLeft
  linarith

end

end Submission.Core
