import Mathlib
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace Submission.Signature

noncomputable section

open Matrix QuadraticMap

def signedInertia {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) : ℤ :=
  (sigPos Q : ℤ) - (sigNeg Q : ℤ)

@[simp] theorem signedInertia_neg {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) : signedInertia (-Q) = -signedInertia Q := by
  simp [signedInertia]

theorem signedInertia_eq_of_equivalent
    {M M' : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup M'] [Module ℝ M']
    {Q : QuadraticForm ℝ M} {Q' : QuadraticForm ℝ M'}
    (h : QuadraticMap.Equivalent Q Q') :
    signedInertia Q = signedInertia Q' := by
  simp [signedInertia, h.sigPos_eq, h.sigNeg_eq]

def trefoilSeifertMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; -1, 1]

def trefoilSymmetricMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, -1; -1, 2]

@[simp] theorem trefoilSeifertMatrix_symmetrization :
    trefoilSeifertMatrix + trefoilSeifertMatrix.transpose =
      trefoilSymmetricMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [trefoilSeifertMatrix, trefoilSymmetricMatrix]

def trefoilSignatureForm : QuadraticForm ℝ (Fin 2 → ℝ) :=
  trefoilSymmetricMatrix.toQuadraticForm'

@[simp] theorem trefoilSignatureForm_apply (x : Fin 2 → ℝ) :
    trefoilSignatureForm x =
      2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 := by
  simp [trefoilSignatureForm, trefoilSymmetricMatrix, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply]
  ring

theorem trefoilSignatureForm_posDef : trefoilSignatureForm.PosDef := by
  intro x hx
  rw [trefoilSignatureForm_apply]
  have hcoord : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i <;> simp [h]
  rcases hcoord with h0 | h1
  · nlinarith [sq_nonneg (x 0 - x 1), sq_pos_of_ne_zero h0]
  · nlinarith [sq_nonneg (x 0 - x 1), sq_pos_of_ne_zero h1]

@[simp] theorem trefoilSignatureForm_sigPos : sigPos trefoilSignatureForm = 2 := by
  have hlower : 2 ≤ sigPos trefoilSignatureForm := by
    have h := le_sigPos_of_posDef trefoilSignatureForm (V := ⊤) (by
      intro x hx
      exact trefoilSignatureForm_posDef x (by simpa using hx))
    simpa using h
  have hupper := sigPos_le_finrank trefoilSignatureForm
  rw [Module.finrank_fin_fun] at hupper
  omega

@[simp] theorem trefoilSignatureForm_sigNeg : sigNeg trefoilSignatureForm = 0 := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := trefoilSignatureForm)
  rw [trefoilSignatureForm_sigPos, Module.finrank_fin_fun] at hsum
  omega

@[simp] theorem trefoilSignatureForm_signedInertia :
    signedInertia trefoilSignatureForm = 2 := by
  simp [signedInertia]

@[simp] theorem mirrorTrefoilSignatureForm_signedInertia :
    signedInertia (-trefoilSignatureForm) = -2 := by
  simp

end

end Submission.Signature
