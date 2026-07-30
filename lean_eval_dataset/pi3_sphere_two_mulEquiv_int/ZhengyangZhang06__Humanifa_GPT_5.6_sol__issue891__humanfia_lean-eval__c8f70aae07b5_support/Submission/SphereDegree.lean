import Submission.SphereRegularApprox

open scoped unitInterval

noncomputable section

namespace Submission.SphereDegree

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}
variable {q : GenLoop (Fin (m + 1)) (UnitSphere m)
  (SphereGenerator.canonicalBasepoint m)}

/-- The local orientation attached to a regular point of the horizontal
coordinate map. -/
def localIndex
    (a : SmoothSphereApprox.Approximation q)
    (t : Fin (m + 1) → I) : ℤ :=
  if 0 < (fderiv ℝ (horizontalMap a) (cubeDomain m t)).det then 1 else -1

theorem localIndex_eq_one_of_det_pos
    (a : SmoothSphereApprox.Approximation q)
    (t : Fin (m + 1) → I)
    (ht : 0 < (fderiv ℝ (horizontalMap a) (cubeDomain m t)).det) :
    localIndex a t = 1 := by
  simp [localIndex, ht]

theorem localIndex_eq_neg_one_of_det_neg
    (a : SmoothSphereApprox.Approximation q)
    (t : Fin (m + 1) → I)
    (ht : (fderiv ℝ (horizontalMap a) (cubeDomain m t)).det < 0) :
    localIndex a t = -1 := by
  simp [localIndex, not_lt_of_ge ht.le]

theorem localIndex_eq_one_or_neg_one
    (a : SmoothSphereApprox.Approximation q)
    (t : Fin (m + 1) → I) :
    localIndex a t = 1 ∨ localIndex a t = -1 := by
  by_cases ht : 0 < (fderiv ℝ (horizontalMap a) (cubeDomain m t)).det
  · exact Or.inl (localIndex_eq_one_of_det_pos a t ht)
  · exact Or.inr (by simp [localIndex, ht])

theorem localIndex_ne_zero
    (a : SmoothSphereApprox.Approximation q)
    (t : Fin (m + 1) → I) :
    localIndex a t ≠ 0 := by
  rcases localIndex_eq_one_or_neg_one a t with h | h <;> simp [h]

theorem det_horizontalMap_ne_zero_of_antipode
    (a : SmoothSphereApprox.Approximation q) {y : Domain m}
    (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0)
    (t : Fin (m + 1) → I)
    (ht :
      regularizedGenLoop a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    (fderiv ℝ (horizontalMap a) (cubeDomain m t)).det ≠ 0 :=
  hregular _ (horizontalMap_eq_of_regularizedMap_eq_antipode a hy t ht)

/-- The finite set of antipode preimages of a regularized representative. -/
def antipodeFinset
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0) :
    Finset (Fin (m + 1) → I) :=
  (finite_regularized_antipode_preimage a hy hregular).toFinset

@[simp]
theorem mem_antipodeFinset_iff
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0)
    (t : Fin (m + 1) → I) :
    t ∈ antipodeFinset a y hy hregular ↔
      regularizedGenLoop a y hy t =
        -(SphereGenerator.canonicalBasepoint m) := by
  simp [antipodeFinset]

theorem antipodeFinset_points_are_interior
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0)
    {t : Fin (m + 1) → I}
    (ht : t ∈ antipodeFinset a y hy hregular)
    (i : Fin (m + 1)) :
    0 < (t i : ℝ) ∧ (t i : ℝ) < 1 :=
  regularized_antipode_coordinate_strict a hy t
    ((mem_antipodeFinset_iff a y hy hregular t).mp ht) i

/-- The signed count of the transverse antipode fiber. This is the concrete
integer that the degree-classification argument must prove independent of the
chosen regularization. -/
def signedAntipodeCount
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0) : ℤ :=
  ∑ t ∈ antipodeFinset a y hy hregular, localIndex a t

end Submission.SphereDegree
