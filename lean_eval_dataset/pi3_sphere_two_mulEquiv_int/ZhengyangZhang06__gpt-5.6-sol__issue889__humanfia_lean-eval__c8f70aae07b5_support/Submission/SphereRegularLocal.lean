import Submission.SphereDegree
import Submission.SphereUpperChart

open scoped ContDiff unitInterval Topology

noncomputable section

namespace Submission.SphereRegularLocal

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}
variable
  {q : GenLoop (Fin (m + 1)) (UnitSphere m)
    (SphereGenerator.canonicalBasepoint m)}

/-- The globally smooth normalization underlying a regularized cubical map. -/
def normalizedTransformed
    (a : SmoothSphereApprox.Approximation q)
    (y : Domain m) (v : Domain m) : Target m :=
  NormedSpace.normalize (transformedRaw a y v)

theorem contDiff_normalizedTransformed
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2) :
    ContDiff ℝ ∞ (normalizedTransformed a y) := by
  change ContDiff ℝ ∞
    (fun v => ‖transformedRaw a y v‖⁻¹ •
      transformedRaw a y v)
  exact
    (((contDiff_transformedRaw a y).norm ℝ
      (transformedRaw_ne_zero a hy)).inv fun v =>
        norm_ne_zero_iff.mpr (transformedRaw_ne_zero a hy v)).smul
      (contDiff_transformedRaw a y)

theorem norm_normalizedTransformed
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2)
    (v : Domain m) :
    ‖normalizedTransformed a y v‖ = 1 :=
  NormedSpace.norm_normalize (transformedRaw_ne_zero a hy v)

/-- The horizontal coordinate of the globally smooth regularized map. -/
def horizontalNormalized
    (a : SmoothSphereApprox.Approximation q)
    (y : Domain m) (v : Domain m) : Domain m :=
  horizontal m (normalizedTransformed a y v)

theorem contDiff_horizontalNormalized
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2) :
    ContDiff ℝ ∞ (horizontalNormalized a y) :=
  (contDiff_horizontal m).comp
    (contDiff_normalizedTransformed a hy)

theorem horizontalNormalized_cubeDomain
    (a : SmoothSphereApprox.Approximation q)
    (y : Domain m) (hy : ‖y‖ < 1 / 2)
    (t : Fin (m + 1) → I) :
    horizontalNormalized a y (cubeDomain m t) =
      horizontal m (regularizedMap a y hy t) :=
  rfl

theorem horizontalNormalized_eq_zero_of_antipode
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2)
    {t : Fin (m + 1) → I}
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    horizontalNormalized a y (cubeDomain m t) = 0 := by
  rw [horizontalNormalized_cubeDomain a y hy t, ht]
  exact SphereUpperChart.horizontal_antipode

/-- The horizontal part before the final normalization. -/
def transformedHorizontal
    (a : SmoothSphereApprox.Approximation q)
    (y : Domain m) (v : Domain m) : Domain m :=
  horizontal m (transformedRaw a y v)

theorem contDiff_transformedHorizontal
    (a : SmoothSphereApprox.Approximation q)
    (y : Domain m) :
    ContDiff ℝ ∞ (transformedHorizontal a y) :=
  (contDiff_horizontal m).comp (contDiff_transformedRaw a y)

theorem transformedHorizontal_eventuallyEq
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2)
    {t : Fin (m + 1) → I}
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    transformedHorizontal a y =ᶠ[𝓝 (cubeDomain m t)]
      fun v => horizontalMap a v - y := by
  let U : Set (Domain m) :=
    {v | 1 / 2 < vertical m (normalizedRaw a v)}
  have hU : IsOpen U :=
    isOpen_lt continuous_const <|
      (contDiff_vertical m).continuous.comp <|
        (contDiff_normalizedRaw a).continuous
  have htU : cubeDomain m t ∈ U :=
    vertical_normalizedRaw_gt_half_of_regularizedMap_eq_antipode
      a hy t ht
  filter_upwards [hU.mem_nhds htU] with v hv
  change 1 / 2 < vertical m (normalizedRaw a v) at hv
  ext i
  change
    transformedRaw a y v i.castSucc =
      horizontalMap a v i - y i
  rw [transformedRaw_castSucc]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp [horizontalMap]

theorem horizontalNormalized_formula
    (a : SmoothSphereApprox.Approximation q)
    (y : Domain m) (v : Domain m) :
    horizontalNormalized a y v =
      ‖transformedRaw a y v‖⁻¹ •
        transformedHorizontal a y v := by
  ext i
  rfl

/-- At a transverse antipode preimage, the final normalization only
multiplies the horizontal derivative by a positive scalar. -/
theorem fderiv_horizontalNormalized_at_antipode
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2)
    {t : Fin (m + 1) → I}
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    fderiv ℝ (horizontalNormalized a y) (cubeDomain m t) =
      ‖transformedRaw a y (cubeDomain m t)‖⁻¹ •
        fderiv ℝ (horizontalMap a) (cubeDomain m t) := by
  let c : Domain m := cubeDomain m t
  let scalar : Domain m → ℝ :=
    fun v => ‖transformedRaw a y v‖⁻¹
  have hscalar :
      ContDiff ℝ ∞ scalar := by
    dsimp only [scalar]
    exact
      ((contDiff_transformedRaw a y).norm ℝ
        (transformedRaw_ne_zero a hy)).inv fun v =>
          norm_ne_zero_iff.mpr (transformedRaw_ne_zero a hy v)
  have htrans :
      fderiv ℝ (transformedHorizontal a y) c =
        fderiv ℝ (horizontalMap a) c := by
    rw [(transformedHorizontal_eventuallyEq a hy ht).fderiv_eq]
    exact fderiv_sub_const y
  have hzero : transformedHorizontal a y c = 0 := by
    have hn :=
      horizontalNormalized_eq_zero_of_antipode a hy ht
    rw [horizontalNormalized_formula] at hn
    exact (smul_eq_zero.mp hn).resolve_left <|
      inv_ne_zero <|
        norm_ne_zero_iff.mpr <|
          transformedRaw_ne_zero a hy c
  rw [show horizontalNormalized a y =
      fun v => scalar v • transformedHorizontal a y v by
    funext v
    exact horizontalNormalized_formula a y v]
  rw [fderiv_fun_smul
    ((hscalar.differentiable (by norm_num)).differentiableAt)
    (((contDiff_transformedHorizontal a y).differentiable
      (by norm_num)).differentiableAt)]
  rw [hzero, ContinuousLinearMap.smulRight_zero, add_zero, htrans]

theorem det_fderiv_horizontalNormalized_ne_zero
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0)
    {t : Fin (m + 1) → I}
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    (fderiv ℝ (horizontalNormalized a y)
      (cubeDomain m t)).det ≠ 0 := by
  rw [fderiv_horizontalNormalized_at_antipode a hy ht]
  change
    LinearMap.det
        (‖transformedRaw a y (cubeDomain m t)‖⁻¹ •
          (fderiv ℝ (horizontalMap a)
            (cubeDomain m t)).toLinearMap) ≠ 0
  rw [LinearMap.det_smul]
  apply mul_ne_zero
  · apply pow_ne_zero
    exact inv_ne_zero <|
      norm_ne_zero_iff.mpr <|
        transformedRaw_ne_zero a hy (cubeDomain m t)
  · exact hregular _ <|
      horizontalMap_eq_of_regularizedMap_eq_antipode a hy t ht

end Submission.SphereRegularLocal
