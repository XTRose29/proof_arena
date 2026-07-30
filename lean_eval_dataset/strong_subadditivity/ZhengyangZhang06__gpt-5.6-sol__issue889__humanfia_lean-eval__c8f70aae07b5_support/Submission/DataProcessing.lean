import Submission.Compression
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.LinearAlgebra.Matrix.Vec

namespace Submission.DataProcessing

open LeanEval.Physics
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {A B : Type*}
variable [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
variable [Nonempty A]

local instance matrixCStarAlgebra (K : Type*) [Fintype K] [DecidableEq K] :
    CStarAlgebra (Matrix K K ℂ) := {
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance }

def unvec (x : B × B → ℂ) : Matrix B B ℂ :=
  Matrix.of fun i j ↦ x (j, i)

omit [Fintype B] [DecidableEq B] in
@[simp]
lemma vec_unvec (x : B × B → ℂ) : Matrix.vec (unvec x) = x := rfl

omit [Fintype B] [DecidableEq B] in
@[simp]
lemma unvec_vec (X : Matrix B B ℂ) : unvec (Matrix.vec X) = X := rfl

def relativeModular (P Q : Matrix B B ℂ) : Matrix (B × B) (B × B) ℂ :=
  Matrix.transpose (Ring.inverse P) ⊗ₖ Q

lemma relativeModular_mulVec_vec (P Q X : Matrix B B ℂ) :
    Matrix.mulVec (relativeModular P Q) (Matrix.vec X) =
      Matrix.vec (Q * X * Ring.inverse P) := by
  simpa [relativeModular] using
    Matrix.kronecker_mulVec_vec Q X (Matrix.transpose (Ring.inverse P))

lemma relativeModular_posDef (P Q : Matrix B B ℂ) (hP : P.PosDef) (hQ : Q.PosDef) :
    (relativeModular P Q).PosDef := by
  have hinv : IsStrictlyPositive (Ring.inverse P) := hP.isStrictlyPositive.ringInverse
  have hinvPos : (Ring.inverse P).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp hinv
  exact hinvPos.transpose.kronecker hQ

omit [DecidableEq B] [Nonempty A] in
lemma trace_kronecker_one_mul (K : Matrix B B ℂ)
    (M : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (((1 : Matrix A A ℂ) ⊗ₖ K) * M) =
      Matrix.trace (K * M.traceLeft) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.traceLeft, Fintype.sum_prod_type,
    Matrix.one_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

def petzLiftMatrix (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (X : Matrix B B ℂ) : Matrix (A × B) (A × B) ℂ :=
  ((1 : Matrix A A ℂ) ⊗ₖ (X * R)) * S

def petzLiftLinear (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ) :
    (B × B → ℂ) →ₗ[ℂ] (A × B) × (A × B) → ℂ where
  toFun x := Matrix.vec (petzLiftMatrix R S (unvec x))
  map_add' x y := by
    have hu : unvec (x + y) = unvec x + unvec y := by
      ext i j
      rfl
    rw [hu]
    simp [petzLiftMatrix, Matrix.add_mul, Matrix.kronecker_add]
  map_smul' c x := by
    have hu : unvec (c • x) = c • unvec x := by
      ext i j
      rfl
    rw [hu]
    simp [petzLiftMatrix, Matrix.kronecker_smul]

def petzLiftOperator (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ) :
    Matrix ((A × B) × (A × B)) (B × B) ℂ :=
  LinearMap.toMatrix' (petzLiftLinear R S)

omit [Nonempty A] in
lemma petzLiftOperator_mulVec (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (x : B × B → ℂ) :
    Matrix.mulVec (petzLiftOperator R S) x =
      Matrix.vec (petzLiftMatrix R S (unvec x)) :=
  LinearMap.toMatrix'_mulVec _ _

omit [Nonempty A] in
lemma trace_petzLift_inner (P : Matrix (A × B) (A × B) ℂ)
    (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (hS : S.IsHermitian) (hSsq : S * S = P)
    (hR : R.IsHermitian) (hRPR : R * P.traceLeft * R = 1)
    (X Y : Matrix B B ℂ) :
    Matrix.trace (Matrix.conjTranspose (petzLiftMatrix R S X) * petzLiftMatrix R S Y) =
      Matrix.trace (Matrix.conjTranspose X * Y) := by
  let K : Matrix B B ℂ := R * Matrix.conjTranspose X * Y * R
  have hproducts :
      ((1 : Matrix A A ℂ) ⊗ₖ (R * Matrix.conjTranspose X)) *
          ((1 : Matrix A A ℂ) ⊗ₖ (Y * R)) =
        (1 : Matrix A A ℂ) ⊗ₖ K := by
    rw [← Matrix.mul_kronecker_mul]
    simp [K, Matrix.mul_assoc]
  have hconjX :
    Matrix.conjTranspose (petzLiftMatrix R S X) =
        S * ((1 : Matrix A A ℂ) ⊗ₖ (R * Matrix.conjTranspose X)) := by
    simp [petzLiftMatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
      hS.eq, hR.eq]
  calc
    Matrix.trace (Matrix.conjTranspose (petzLiftMatrix R S X) * petzLiftMatrix R S Y) =
        Matrix.trace
          (S * (((1 : Matrix A A ℂ) ⊗ₖ (R * Matrix.conjTranspose X)) *
            ((1 : Matrix A A ℂ) ⊗ₖ (Y * R))) * S) := by
      rw [hconjX]
      simp [petzLiftMatrix, Matrix.mul_assoc]
    _ = Matrix.trace (S * (((1 : Matrix A A ℂ) ⊗ₖ K) * S)) := by
      rw [hproducts]
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (((1 : Matrix A A ℂ) ⊗ₖ K) * (S * S)) := by
      rw [Matrix.trace_mul_comm]
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (((1 : Matrix A A ℂ) ⊗ₖ K) * P) := by rw [hSsq]
    _ = Matrix.trace (K * P.traceLeft) := trace_kronecker_one_mul K P
    _ = Matrix.trace (R * (Matrix.conjTranspose X * Y * R * P.traceLeft)) := by
      simp [K, Matrix.mul_assoc]
    _ = Matrix.trace ((Matrix.conjTranspose X * Y * R * P.traceLeft) * R) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Matrix.conjTranspose X * Y * (R * P.traceLeft * R)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.conjTranspose X * Y) := by rw [hRPR, Matrix.mul_one]

omit [Nonempty A] in
lemma petzLift_inner (P : Matrix (A × B) (A × B) ℂ)
    (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (hS : S.IsHermitian) (hSsq : S * S = P)
    (hR : R.IsHermitian) (hRPR : R * P.traceLeft * R = 1)
    (x y : B × B → ℂ) :
    star (petzLiftLinear R S x) ⬝ᵥ petzLiftLinear R S y = star x ⬝ᵥ y := by
  change star (Matrix.vec (petzLiftMatrix R S (unvec x))) ⬝ᵥ
      Matrix.vec (petzLiftMatrix R S (unvec y)) = _
  rw [Matrix.star_vec_dotProduct_vec,
    trace_petzLift_inner P R S hS hSsq hR hRPR,
    ← Matrix.star_vec_dotProduct_vec]
  rfl

omit [Nonempty A] in
lemma petzLiftOperator_isometry (P : Matrix (A × B) (A × B) ℂ)
    (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (hS : S.IsHermitian) (hSsq : S * S = P)
    (hR : R.IsHermitian) (hRPR : R * P.traceLeft * R = 1) :
    Matrix.conjTranspose (petzLiftOperator R S) * petzLiftOperator R S = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change star (petzLiftLinear R S (Pi.single i 1)) ⬝ᵥ
      petzLiftLinear R S (Pi.single j 1) = _
  rw [petzLift_inner P R S hS hSsq hR hRPR]
  rw [Pi.star_single, star_one, single_one_dotProduct]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

omit [DecidableEq B] [Nonempty A] in
lemma trace_kronecker_sandwich (U V : Matrix B B ℂ)
    (Q : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace
        ((((1 : Matrix A A ℂ) ⊗ₖ U) * Q) * ((1 : Matrix A A ℂ) ⊗ₖ V)) =
      Matrix.trace (U * Q.traceLeft * V) := by
  calc
    Matrix.trace
        ((((1 : Matrix A A ℂ) ⊗ₖ U) * Q) * ((1 : Matrix A A ℂ) ⊗ₖ V)) =
        Matrix.trace
          ((((1 : Matrix A A ℂ) ⊗ₖ V) * ((1 : Matrix A A ℂ) ⊗ₖ U)) * Q) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (((1 : Matrix A A ℂ) ⊗ₖ (V * U)) * Q) := by
      rw [← Matrix.mul_kronecker_mul]
      simp
    _ = Matrix.trace ((V * U) * Q.traceLeft) :=
      trace_kronecker_one_mul (V * U) Q
    _ = Matrix.trace (U * Q.traceLeft * V) := by
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
      simp [Matrix.mul_assoc]

omit [Nonempty A] in
lemma trace_petzLift_relativeModular_inner
    (P Q : Matrix (A × B) (A × B) ℂ)
    (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (hS : S.IsHermitian) (hSinv : S * Ring.inverse P * S = 1)
    (hR : R.IsHermitian) (hRsq : R * R = Ring.inverse P.traceLeft)
    (X Y : Matrix B B ℂ) :
    Matrix.trace
        (Matrix.conjTranspose (petzLiftMatrix R S X) *
          (Q * petzLiftMatrix R S Y * Ring.inverse P)) =
      Matrix.trace
        (Matrix.conjTranspose X *
          (Q.traceLeft * Y * Ring.inverse P.traceLeft)) := by
  let U : Matrix (A × B) (A × B) ℂ :=
    (1 : Matrix A A ℂ) ⊗ₖ (R * Matrix.conjTranspose X)
  let V : Matrix (A × B) (A × B) ℂ :=
    (1 : Matrix A A ℂ) ⊗ₖ (Y * R)
  have hconjX : Matrix.conjTranspose (petzLiftMatrix R S X) = S * U := by
    simp [U, petzLiftMatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
      hS.eq, hR.eq]
  calc
    Matrix.trace
        (Matrix.conjTranspose (petzLiftMatrix R S X) *
          (Q * petzLiftMatrix R S Y * Ring.inverse P)) =
        Matrix.trace (S * (U * Q * V * S * Ring.inverse P)) := by
      rw [hconjX]
      simp [V, petzLiftMatrix, Matrix.mul_assoc]
    _ = Matrix.trace ((U * Q * V * S * Ring.inverse P) * S) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((U * Q * V) * (S * Ring.inverse P * S)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (U * Q * V) := by rw [hSinv, Matrix.mul_one]
    _ = Matrix.trace
        ((R * Matrix.conjTranspose X) * Q.traceLeft * (Y * R)) := by
      exact trace_kronecker_sandwich _ _ Q
    _ = Matrix.trace
        (R * (Matrix.conjTranspose X * Q.traceLeft * Y * R)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace
        ((Matrix.conjTranspose X * Q.traceLeft * Y * R) * R) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (Matrix.conjTranspose X * Q.traceLeft * Y * (R * R)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace
        (Matrix.conjTranspose X *
          (Q.traceLeft * Y * Ring.inverse P.traceLeft)) := by
      rw [hRsq]
      simp [Matrix.mul_assoc]

omit [Nonempty A] in
lemma petzLift_relativeModular_inner
    (P Q : Matrix (A × B) (A × B) ℂ)
    (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (hS : S.IsHermitian) (hSinv : S * Ring.inverse P * S = 1)
    (hR : R.IsHermitian) (hRsq : R * R = Ring.inverse P.traceLeft)
    (x y : B × B → ℂ) :
    star (petzLiftLinear R S x) ⬝ᵥ
        Matrix.mulVec (relativeModular P Q) (petzLiftLinear R S y) =
      star x ⬝ᵥ Matrix.mulVec
        (relativeModular P.traceLeft Q.traceLeft) y := by
  change star (Matrix.vec (petzLiftMatrix R S (unvec x))) ⬝ᵥ
      Matrix.mulVec (relativeModular P Q)
        (Matrix.vec (petzLiftMatrix R S (unvec y))) =
      star (Matrix.vec (unvec x)) ⬝ᵥ
        Matrix.mulVec (relativeModular P.traceLeft Q.traceLeft)
          (Matrix.vec (unvec y))
  rw [relativeModular_mulVec_vec, relativeModular_mulVec_vec,
    Matrix.star_vec_dotProduct_vec,
    trace_petzLift_relativeModular_inner P Q R S hS hSinv hR hRsq,
    ← Matrix.star_vec_dotProduct_vec]

omit [Nonempty A] in
lemma petzLiftOperator_compress_relativeModular
    (P Q : Matrix (A × B) (A × B) ℂ)
    (R : Matrix B B ℂ) (S : Matrix (A × B) (A × B) ℂ)
    (hS : S.IsHermitian) (hSinv : S * Ring.inverse P * S = 1)
    (hR : R.IsHermitian) (hRsq : R * R = Ring.inverse P.traceLeft) :
    Matrix.conjTranspose (petzLiftOperator R S) * relativeModular P Q *
        petzLiftOperator R S =
      relativeModular P.traceLeft Q.traceLeft := by
  rw [Matrix.mul_assoc]
  ext i j
  rw [Matrix.mul_apply]
  change star (petzLiftLinear R S (Pi.single i 1)) ⬝ᵥ
      Matrix.mulVec (relativeModular P Q)
        (petzLiftLinear R S (Pi.single j 1)) = _
  rw [petzLift_relativeModular_inner P Q R S hS hSinv hR hRsq]
  simp only [Pi.star_single, star_one, single_one_dotProduct,
    Matrix.mulVec_single_one, Matrix.col_apply]

end

end Submission.DataProcessing
