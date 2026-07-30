import Mathlib
import Submission.SphereRegularApprox

open scoped ContDiff

noncomputable section

namespace Submission.SphereDegreeForm

open Submission.SphereRegularApprox

/-- The continuous determinant alternating form on the ambient Euclidean
space of the `m`-sphere. -/
def determinantForm (m : ℕ) :
    Target m [⋀^Fin (m + 2)]→L[ℝ] ℝ :=
  { (EuclideanSpace.basisFun (Fin (m + 2)) ℝ).toBasis.det with
    cont := by
      change Continuous fun v : Fin (m + 2) → Target m =>
        (EuclideanSpace.basisFun (Fin (m + 2)) ℝ).toBasis.det v
      simp_rw [Module.Basis.det_apply]
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i j
      simp only [Module.Basis.toMatrix_apply,
        EuclideanSpace.basisFun_toBasis,
        PiLp.basisFun_repr]
      fun_prop }

theorem determinantForm_apply (m : ℕ)
    (v : Fin (m + 2) → Target m) :
    determinantForm m v =
      (Matrix.of fun i j => v j i).det := by
  change
    (EuclideanSpace.basisFun (Fin (m + 2)) ℝ).toBasis.det v =
      (Matrix.of fun i j => v j i).det
  rw [Module.Basis.det_apply]
  apply congrArg Matrix.det
  ext i j
  simp [Module.Basis.toMatrix_apply,
    EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr]

/-- Contract the ambient determinant with the radial vector.  Its restriction
to the unit sphere is the standard oriented volume form, without any
normalizing scalar. -/
def volumeForm (m : ℕ) :
    Target m →L[ℝ] Target m [⋀^Fin (m + 1)]→L[ℝ] ℝ :=
  (determinantForm m).curryLeft

@[simp]
theorem volumeForm_apply (m : ℕ) (y : Target m)
    (v : Fin (m + 1) → Target m) :
    volumeForm m y v =
      determinantForm m (Matrix.vecCons y v) := by
  rfl

theorem volumeForm_apply_det (m : ℕ) (y : Target m)
    (v : Fin (m + 1) → Target m) :
    volumeForm m y v =
      (Matrix.of fun i j => (Matrix.vecCons y v) j i).det := by
  rw [volumeForm_apply, determinantForm_apply]

@[fun_prop]
theorem contDiff_volumeForm (m : ℕ) :
    ContDiff ℝ ∞ (volumeForm m) :=
  (volumeForm m).contDiff

@[fun_prop]
theorem continuous_volumeForm (m : ℕ) :
    Continuous (volumeForm m) :=
  (volumeForm m).continuous

/-- The ambient exterior derivative of the radial volume form is the
dimension scalar times the constant determinant form. -/
theorem extDeriv_volumeForm (m : ℕ) (y : Target m) :
    extDeriv (volumeForm m) y =
      (m + 2) • determinantForm m := by
  rw [extDeriv, ContinuousLinearMap.fderiv]
  simpa only [volumeForm, Nat.add_assoc] using
    (ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft
      (determinantForm m))

end Submission.SphereDegreeForm
