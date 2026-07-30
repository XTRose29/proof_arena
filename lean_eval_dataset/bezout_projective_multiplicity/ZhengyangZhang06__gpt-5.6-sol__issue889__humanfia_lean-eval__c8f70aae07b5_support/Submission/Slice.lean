import Submission.Helpers

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

namespace Submission.Helpers

variable {K : Type*} [Field K]

lemma eval_affineConeCoord_linearForm_ne_zero {n : ℕ} (a : Fin (n + 1) → K)
    (p : ProjSpace K n) (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    eval (affineConeCoord p) (linearForm a) ≠ 0 := by
  rw [eval_affineConeCoord_eq p (linearForm_isHomogeneous a)]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (chartIndex_rep_ne_zero p))) hne

lemma linearSliceCoord_eq_normalize_affineConeCoord {n : ℕ} (a : Fin (n + 1) → K)
    (p : ProjSpace K n) (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceCoord a p = fun i =>
      affineConeCoord p i / eval (affineConeCoord p) (linearForm a) := by
  funext i
  rw [linearSliceCoord, affineConeCoord, eval_affineConeCoord_eq p (linearForm_isHomogeneous a)]
  field_simp [chartIndex_rep_ne_zero p, hne]

end Submission.Helpers
