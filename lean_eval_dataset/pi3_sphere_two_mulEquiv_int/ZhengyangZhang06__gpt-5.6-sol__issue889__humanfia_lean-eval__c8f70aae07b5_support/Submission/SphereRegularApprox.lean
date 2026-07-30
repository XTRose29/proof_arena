import Mathlib
import Submission.RegularValue
import Submission.SmoothSphereApprox
import Submission.SphereGenerator

open scoped unitInterval Topology ContDiff

noncomputable section

namespace Submission.SphereRegularApprox

open Set
open Submission.SphereHomotopy

abbrev Domain (m : ℕ) :=
  EuclideanSpace ℝ (Fin (m + 1))

abbrev Target (m : ℕ) :=
  EuclideanSpace ℝ (Fin (m + 2))

abbrev UnitSphere (m : ℕ) :=
  Metric.sphere (0 : Target m) 1

/-- The first `m + 1` coordinates of a vector in `ℝ^(m+2)`. -/
def horizontal (m : ℕ) (w : Target m) : Domain m :=
  WithLp.toLp 2 fun i => w i.castSucc

/-- The last coordinate of a vector in `ℝ^(m+2)`. -/
def vertical (m : ℕ) (w : Target m) : ℝ :=
  w (Fin.last (m + 1))

@[simp]
theorem horizontal_apply (m : ℕ) (w : Target m) (i : Fin (m + 1)) :
    horizontal m w i = w i.castSucc :=
  rfl

@[simp]
theorem vertical_apply (m : ℕ) (w : Target m) :
    vertical m w = w (Fin.last (m + 1)) :=
  rfl

theorem norm_sq_horizontal_add_vertical (m : ℕ) (w : Target m) :
    ‖w‖ ^ 2 = ‖horizontal m w‖ ^ 2 + (vertical m w) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_castSucc]
  rfl

@[fun_prop]
theorem contDiff_horizontal (m : ℕ) :
    ContDiff ℝ ∞ (horizontal m) := by
  apply contDiff_piLp' 2
  intro i
  change ContDiff ℝ ∞ (fun w : Target m => w i.castSucc)
  fun_prop

@[fun_prop]
theorem contDiff_vertical (m : ℕ) :
    ContDiff ℝ ∞ (vertical m) := by
  unfold vertical
  fun_prop

/-- Regard an `L²` Euclidean vector as an ordinary coordinate function, the
ambient domain used by `SmoothSphereApprox.Approximation.raw`. -/
def domainCoe (m : ℕ) (v : Domain m) : Fin (m + 1) → ℝ :=
  WithLp.ofLp v

@[fun_prop]
theorem contDiff_domainCoe (m : ℕ) :
    ContDiff ℝ ∞ (domainCoe m) := by
  unfold domainCoe
  exact PiLp.contDiff_ofLp

variable {m : ℕ}
variable {x : UnitSphere m}
variable {p : GenLoop (Fin (m + 1)) (UnitSphere m) x}

/-- Normalize a smooth nonvanishing ambient approximation on an `L²`
Euclidean copy of its domain. -/
def normalizedRaw
    (a : SmoothSphereApprox.Approximation p) (v : Domain m) :
    Target m :=
  NormedSpace.normalize (a.raw (domainCoe m v))

@[fun_prop]
theorem contDiff_normalizedRaw
    (a : SmoothSphereApprox.Approximation p) :
    ContDiff ℝ ∞ (normalizedRaw a) := by
  have hraw : ContDiff ℝ ∞ (fun v : Domain m => a.raw (domainCoe m v)) :=
    a.contDiff_raw.comp (contDiff_domainCoe m)
  change ContDiff ℝ ∞
    (fun v : Domain m =>
      ‖a.raw (domainCoe m v)‖⁻¹ • a.raw (domainCoe m v))
  exact
    ((hraw.norm ℝ fun v => a.raw_ne_zero (domainCoe m v)).inv fun v =>
      norm_ne_zero_iff.mpr (a.raw_ne_zero (domainCoe m v))).smul hraw

theorem norm_normalizedRaw
    (a : SmoothSphereApprox.Approximation p) (v : Domain m) :
    ‖normalizedRaw a v‖ = 1 :=
  NormedSpace.norm_normalize (a.raw_ne_zero (domainCoe m v))

@[fun_prop]
theorem continuous_normalizedRaw
    (a : SmoothSphereApprox.Approximation p) :
    Continuous (normalizedRaw a) :=
  (contDiff_normalizedRaw a).continuous

/-- The horizontal component of the normalized smooth approximation. -/
def horizontalMap
    (a : SmoothSphereApprox.Approximation p) (v : Domain m) :
    Domain m :=
  horizontal m (normalizedRaw a v)

theorem contDiff_horizontalMap
    (a : SmoothSphereApprox.Approximation p) :
    ContDiff ℝ 1 (horizontalMap a) :=
  ((contDiff_horizontal m).comp
    (contDiff_normalizedRaw a)).of_le (by norm_num)

/-- Include a cubical point in the `L²` Euclidean copy of the ambient
domain. -/
def cubeDomain (m : ℕ) (t : Fin (m + 1) → I) : Domain m :=
  WithLp.toLp 2 (SmoothSphereApprox.cubeCoe t)

@[simp]
theorem domainCoe_cubeDomain (m : ℕ) (t : Fin (m + 1) → I) :
    domainCoe m (cubeDomain m t) = SmoothSphereApprox.cubeCoe t :=
  rfl

@[fun_prop]
theorem continuous_cubeDomain (m : ℕ) :
    Continuous (cubeDomain m) := by
  unfold cubeDomain
  exact
    (PiLp.continuous_toLp 2
      (fun _ : Fin (m + 1) => ℝ)).comp
        SmoothSphereApprox.continuous_cubeCoe

theorem dist_cube_le_norm_cubeDomain_sub
    (m : ℕ) (s t : Fin (m + 1) → I) :
    dist s t ≤ ‖cubeDomain m s - cubeDomain m t‖ := by
  apply (dist_pi_le_iff (norm_nonneg _)).2
  intro i
  change
    dist (s i : ℝ) (t i : ℝ) ≤
      ‖cubeDomain m s - cubeDomain m t‖
  rw [Real.dist_eq]
  exact PiLp.norm_apply_le
    (cubeDomain m s - cubeDomain m t) i

theorem normalizedRaw_cubeDomain
    (a : SmoothSphereApprox.Approximation p) (t : Fin (m + 1) → I) :
    normalizedRaw a (cubeDomain m t) = a.representative t := by
  change
    NormedSpace.normalize
        (a.raw (SmoothSphereApprox.cubeCoe t)) =
      (a.representative t : Target m)
  exact (a.representative_apply t).symm

theorem exists_small_regular_value
    (a : SmoothSphereApprox.Approximation p) :
    ∃ y : Domain m, ‖y‖ < 1 / 2 ∧
      ∀ v, horizontalMap a v = y →
        (fderiv ℝ (horizontalMap a) v).det ≠ 0 := by
  obtain ⟨y, hy, hregular⟩ :=
    RegularValue.exists_regular_value_in_ball
      (horizontalMap a) (contDiff_horizontalMap a) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨y, ?_, hregular⟩
  simpa only [Metric.mem_ball, dist_zero_right] using hy

/-- The standard south pole is the concrete base point chosen by
`SphereGenerator`. -/
theorem coe_canonicalBasepoint (m : ℕ) :
    (SphereGenerator.canonicalBasepoint m : Target m) =
      -EuclideanSpace.single (Fin.last (m + 1)) 1 := by
  classical
  let z : Fin (m + 1) → I := fun _ => 0
  have hz : z ∈ Cube.boundary (Fin (m + 1)) :=
    ⟨0, Or.inl rfl⟩
  have hradius : SphereGenerator.cubeRadius m z = 1 :=
    SphereGenerator.cubeRadius_eq_one_of_mem_boundary m z hz
  have hraw :
      SphereGenerator.rawGenerator m z =
        -EuclideanSpace.single (Fin.last (m + 1)) 1 := by
    ext i
    cases i using Fin.lastCases with
    | last =>
        norm_num [SphereGenerator.rawGenerator, hradius]
    | cast j =>
        simp [SphereGenerator.rawGenerator, hradius]
  have hnorm : ‖SphereGenerator.rawGenerator m z‖ = 1 := by
    rw [hraw]
    simp
  change
    NormedSpace.normalize (SphereGenerator.rawGenerator m z) =
      -EuclideanSpace.single (Fin.last (m + 1)) 1
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm, hraw]

@[simp]
theorem horizontal_canonicalBasepoint (m : ℕ) :
    horizontal m (SphereGenerator.canonicalBasepoint m) = 0 := by
  classical
  rw [coe_canonicalBasepoint]
  ext i
  simp

@[simp]
theorem vertical_canonicalBasepoint (m : ℕ) :
    vertical m (SphereGenerator.canonicalBasepoint m) = -1 := by
  classical
  rw [coe_canonicalBasepoint]
  simp [vertical]

theorem canonicalBasepoint_ne_neg (m : ℕ) :
    SphereGenerator.canonicalBasepoint m ≠
      -(SphereGenerator.canonicalBasepoint m) := by
  intro h
  have hv := congrArg
    (fun z : UnitSphere m => vertical m z) h
  norm_num [vertical, coe_canonicalBasepoint] at hv

/-- A smooth deformation of a normalized representative which pushes the
equator downward and perturbs its horizontal coordinate by `y`. -/
def transformedRaw
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (v : Domain m) : Target m :=
  let u := normalizedRaw a v
  let c := Real.smoothTransition (2 * vertical m u)
  WithLp.toLp 2 <|
    Fin.lastCases (2 * vertical m u - 1)
      fun i => horizontal m u i - c * y i

@[simp]
theorem transformedRaw_last
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (v : Domain m) :
    transformedRaw a y v (Fin.last (m + 1)) =
      2 * vertical m (normalizedRaw a v) - 1 := by
  simp [transformedRaw]

@[simp]
theorem transformedRaw_castSucc
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (v : Domain m) (i : Fin (m + 1)) :
    transformedRaw a y v i.castSucc =
      horizontal m (normalizedRaw a v) i -
        Real.smoothTransition (2 * vertical m (normalizedRaw a v)) * y i := by
  simp [transformedRaw]

theorem transformedRaw_ne_zero
    (a : SmoothSphereApprox.Approximation p) {y : Domain m}
    (hy : ‖y‖ < 1 / 2) (v : Domain m) :
    transformedRaw a y v ≠ 0 := by
  intro hzero
  let u := normalizedRaw a v
  have hlast := congrArg
    (fun w : Target m => w (Fin.last (m + 1))) hzero
  have hk : vertical m u = 1 / 2 := by
    rw [transformedRaw_last] at hlast
    simp only [PiLp.zero_apply] at hlast
    dsimp only [u]
    linarith
  have hhorizontal : horizontal m u = y := by
    ext i
    have hi := congrArg (fun w : Target m => w i.castSucc) hzero
    rw [transformedRaw_castSucc] at hi
    simp only [PiLp.zero_apply] at hi
    dsimp only [u] at hk ⊢
    rw [hk] at hi
    norm_num [Real.smoothTransition.one] at hi
    change (normalizedRaw a v) i.castSucc = y i
    exact sub_eq_zero.mp hi
  have hdecomp := norm_sq_horizontal_add_vertical m u
  rw [norm_normalizedRaw a v, hhorizontal, hk] at hdecomp
  have hynonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hySq : ‖y‖ ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hynonneg (by norm_num)).2 hy
  nlinarith

theorem contDiff_transformedRaw
    (a : SmoothSphereApprox.Approximation p) (y : Domain m) :
    ContDiff ℝ ∞ (transformedRaw a y) := by
  apply contDiff_piLp' 2
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [transformedRaw_last]
      fun_prop
  | cast j =>
      simp only [transformedRaw_castSucc]
      fun_prop

/-- The straight deformation from `normalizedRaw` to `transformedRaw`,
written in coordinates so that it stays nonzero. -/
def deformationRaw
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (z : I × Domain m) : Target m :=
  let s : ℝ := z.1
  let u := normalizedRaw a z.2
  let c := Real.smoothTransition (2 * vertical m u)
  WithLp.toLp 2 <|
    Fin.lastCases ((1 + s) * vertical m u - s)
      fun i => horizontal m u i - (s * c) * y i

@[simp]
theorem deformationRaw_last
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (z : I × Domain m) :
    deformationRaw a y z (Fin.last (m + 1)) =
      (1 + (z.1 : ℝ)) * vertical m (normalizedRaw a z.2) - z.1 := by
  simp [deformationRaw]

@[simp]
theorem deformationRaw_castSucc
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (z : I × Domain m) (i : Fin (m + 1)) :
    deformationRaw a y z i.castSucc =
      horizontal m (normalizedRaw a z.2) i -
        ((z.1 : ℝ) *
          Real.smoothTransition
            (2 * vertical m (normalizedRaw a z.2))) * y i := by
  simp [deformationRaw]

theorem deformationRaw_ne_zero
    (a : SmoothSphereApprox.Approximation p) {y : Domain m}
    (hy : ‖y‖ < 1 / 2) (z : I × Domain m) :
    deformationRaw a y z ≠ 0 := by
  intro hzero
  let s : ℝ := z.1
  let u := normalizedRaw a z.2
  let k : ℝ := vertical m u
  let c : ℝ := Real.smoothTransition (2 * k)
  have hs0 : 0 ≤ s := z.1.property.1
  have hs1 : s ≤ 1 := z.1.property.2
  have hc0 : 0 ≤ c := Real.smoothTransition.nonneg _
  have hc1 : c ≤ 1 := Real.smoothTransition.le_one _
  have hlast := congrArg
    (fun w : Target m => w (Fin.last (m + 1))) hzero
  have hkrel : (1 + s) * k - s = 0 := by
    simpa only [deformationRaw_last, PiLp.zero_apply, s, u, k] using hlast
  have hden : 0 < 1 + s := by linarith
  have hk : k = s / (1 + s) := by
    apply (eq_div_iff hden.ne').2
    linarith
  have hk0 : 0 ≤ k := by
    rw [hk]
    positivity
  have hkhalf : k ≤ 1 / 2 := by
    rw [hk]
    apply (div_le_iff₀ hden).2
    linarith
  have hhorizontal : horizontal m u = (s * c) • y := by
    ext i
    have hi := congrArg (fun w : Target m => w i.castSucc) hzero
    rw [deformationRaw_castSucc] at hi
    simp only [PiLp.zero_apply] at hi
    dsimp only [s, u, k, c] at hi ⊢
    change
      horizontal m (normalizedRaw a z.2) i =
        ((z.1 : ℝ) *
          Real.smoothTransition
            (2 * vertical m (normalizedRaw a z.2))) * y i
    linarith
  have hsc0 : 0 ≤ s * c := mul_nonneg hs0 hc0
  have hsc1 : s * c ≤ 1 := mul_le_one₀ hs1 hc0 hc1
  have hnormHorizontal :
      ‖horizontal m u‖ = (s * c) * ‖y‖ := by
    rw [hhorizontal, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsc0]
  have hnormHorizontalLt : ‖horizontal m u‖ < 1 / 2 := by
    rw [hnormHorizontal]
    calc
      (s * c) * ‖y‖ ≤ 1 * ‖y‖ :=
        mul_le_mul_of_nonneg_right hsc1 (norm_nonneg y)
      _ < 1 / 2 := by simpa using hy
  have hdecomp := norm_sq_horizontal_add_vertical m u
  rw [norm_normalizedRaw a z.2] at hdecomp
  have hnormHorizontal0 : 0 ≤ ‖horizontal m u‖ := norm_nonneg _
  have hnormHorizontalSq :
      ‖horizontal m u‖ ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hnormHorizontal0 (by norm_num)).2 hnormHorizontalLt
  have hkSq : k ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    (sq_le_sq₀ hk0 (by norm_num)).2 hkhalf
  nlinarith

@[simp]
theorem deformationRaw_zero
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (v : Domain m) :
    deformationRaw a y (0, v) = normalizedRaw a v := by
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [deformationRaw, vertical]
  | cast j =>
      simp [deformationRaw, horizontal]

@[simp]
theorem deformationRaw_one
    (a : SmoothSphereApprox.Approximation p) (y : Domain m)
    (v : Domain m) :
    deformationRaw a y (1, v) = transformedRaw a y v := by
  ext i
  cases i using Fin.lastCases with
  | last =>
      rw [deformationRaw_last, transformedRaw_last]
      norm_num
  | cast j =>
      rw [deformationRaw_castSucc, transformedRaw_castSucc]
      norm_num

theorem continuous_deformationRaw
    (a : SmoothSphereApprox.Approximation p) (y : Domain m) :
    Continuous (deformationRaw a y) := by
  unfold deformationRaw
  refine
    (PiLp.continuous_toLp 2
      (fun _ : Fin (m + 2) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [Fin.lastCases_last]
      fun_prop
  | cast j =>
      simp only [Fin.lastCases_castSucc]
      fun_prop

theorem cube_coordinate_strict_of_not_mem_boundary
    (t : Fin (m + 1) → I)
    (ht : t ∉ Cube.boundary (Fin (m + 1)))
    (i : Fin (m + 1)) :
    0 < (t i : ℝ) ∧ (t i : ℝ) < 1 := by
  have hne0 : t i ≠ 0 := by
    intro hi
    exact ht ⟨i, Or.inl hi⟩
  have hne1 : t i ≠ 1 := by
    intro hi
    exact ht ⟨i, Or.inr hi⟩
  have hne0' : (t i : ℝ) ≠ 0 := by
    intro hi
    apply hne0
    exact Subtype.ext hi
  have hne1' : (t i : ℝ) ≠ 1 := by
    intro hi
    apply hne1
    exact Subtype.ext hi
  exact
    ⟨lt_of_le_of_ne (t i).property.1 hne0'.symm,
      lt_of_le_of_ne (t i).property.2 hne1'⟩

section CanonicalBasepoint

variable {q : GenLoop (Fin (m + 1)) (UnitSphere m)
  (SphereGenerator.canonicalBasepoint m)}

theorem transformedRaw_boundary
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (t : Fin (m + 1) → I) (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    transformedRaw a y (cubeDomain m t) =
      (3 : ℝ) •
        (SphereGenerator.canonicalBasepoint m : Target m) := by
  have hu :
      normalizedRaw a (cubeDomain m t) =
        SphereGenerator.canonicalBasepoint m := by
    rw [normalizedRaw_cubeDomain]
    exact congrArg Subtype.val (a.representative.property t ht)
  ext i
  cases i using Fin.lastCases with
  | last =>
      norm_num [transformedRaw, hu, coe_canonicalBasepoint]
  | cast j =>
      simp [transformedRaw, hu, coe_canonicalBasepoint,
        Real.smoothTransition.zero_of_nonpos]

theorem deformationRaw_boundary
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (s : I) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    deformationRaw a y (s, cubeDomain m t) =
      (1 + 2 * (s : ℝ)) •
        (SphereGenerator.canonicalBasepoint m : Target m) := by
  have hu :
      normalizedRaw a (cubeDomain m t) =
        SphereGenerator.canonicalBasepoint m := by
    rw [normalizedRaw_cubeDomain]
    exact congrArg Subtype.val (a.representative.property t ht)
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [deformationRaw, hu, coe_canonicalBasepoint]
      ring
  | cast j =>
      simp [deformationRaw, hu, coe_canonicalBasepoint,
        Real.smoothTransition.zero_of_nonpos]

/-- The regularized sphere-valued cubical map. -/
def regularizedMap
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I) :
    UnitSphere m :=
  ⟨NormedSpace.normalize
      (transformedRaw a y (cubeDomain m t)), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize
      (transformedRaw_ne_zero a hy (cubeDomain m t))⟩

theorem continuous_regularizedMap
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) :
    Continuous (regularizedMap a y hy) := by
  apply Continuous.subtype_mk
  let r : (Fin (m + 1) → I) → Target m :=
    fun t => transformedRaw a y (cubeDomain m t)
  have hr : Continuous r :=
    (contDiff_transformedRaw a y).continuous.comp (continuous_cubeDomain m)
  change Continuous (fun t => ‖r t‖⁻¹ • r t)
  exact
    (hr.norm.inv₀ fun t =>
      norm_ne_zero_iff.mpr
        (transformedRaw_ne_zero a hy (cubeDomain m t))).smul hr

theorem regularizedMap_boundary
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    regularizedMap a y hy t =
      SphereGenerator.canonicalBasepoint m := by
  apply Subtype.ext
  change
    NormedSpace.normalize
        (transformedRaw a y (cubeDomain m t)) =
      (SphereGenerator.canonicalBasepoint m : Target m)
  rw [transformedRaw_boundary a y t ht,
    NormedSpace.normalize_smul_of_pos (by norm_num)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (SphereGenerator.sphere_norm_eq_one m
      (SphereGenerator.canonicalBasepoint m))

theorem regularizedMap_ne_antipode_of_mem_boundary
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    regularizedMap a y hy t ≠
      -(SphereGenerator.canonicalBasepoint m) := by
  rw [regularizedMap_boundary a y hy t ht]
  exact canonicalBasepoint_ne_neg m

theorem not_mem_boundary_of_regularizedMap_eq_antipode
    (a : SmoothSphereApprox.Approximation q) {y : Domain m}
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I)
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    t ∉ Cube.boundary (Fin (m + 1)) := by
  intro hboundary
  exact
    (regularizedMap_ne_antipode_of_mem_boundary
      a y hy t hboundary) ht

theorem regularized_antipode_coordinate_strict
    (a : SmoothSphereApprox.Approximation q) {y : Domain m}
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I)
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m))
    (i : Fin (m + 1)) :
    0 < (t i : ℝ) ∧ (t i : ℝ) < 1 :=
  cube_coordinate_strict_of_not_mem_boundary t
    (not_mem_boundary_of_regularizedMap_eq_antipode a hy t ht) i

/-- The regularized generalized loop. -/
def regularizedGenLoop
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨regularizedMap a y hy, continuous_regularizedMap a y hy⟩,
    regularizedMap_boundary a y hy⟩

/-- The coordinate deformation, normalized to the sphere, is relative to the
cubical boundary. -/
def regularizationHomotopyRel
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) :
    a.representative.1.HomotopyRel
      (regularizedGenLoop a y hy).1 (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    ⟨NormedSpace.normalize
        (deformationRaw a y (z.1, cubeDomain m z.2)), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize
        (deformationRaw_ne_zero a hy (z.1, cubeDomain m z.2))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    let r : I × (Fin (m + 1) → I) → Target m :=
      fun z => deformationRaw a y (z.1, cubeDomain m z.2)
    have hr : Continuous r :=
      (continuous_deformationRaw a y).comp <|
        continuous_fst.prodMk ((continuous_cubeDomain m).comp continuous_snd)
    change Continuous (fun z => ‖r z‖⁻¹ • r z)
    exact
      (hr.norm.inv₀ fun z =>
        norm_ne_zero_iff.mpr
          (deformationRaw_ne_zero a hy
            (z.1, cubeDomain m z.2))).smul hr
  map_zero_left t := by
    apply Subtype.ext
    change
      NormedSpace.normalize
          (deformationRaw a y (0, cubeDomain m t)) =
        (a.representative t : Target m)
    rw [deformationRaw_zero, normalizedRaw_cubeDomain]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (norm_coe_unitSphere (a.representative t))
  map_one_left t := by
    apply Subtype.ext
    change
      NormedSpace.normalize
          (deformationRaw a y (1, cubeDomain m t)) =
        NormedSpace.normalize
          (transformedRaw a y (cubeDomain m t))
    rw [deformationRaw_one]
  prop' s t ht := by
    apply Subtype.ext
    change
      NormedSpace.normalize
          (deformationRaw a y (s, cubeDomain m t)) =
        (a.representative t : Target m)
    rw [deformationRaw_boundary a y s t ht,
      NormedSpace.normalize_smul_of_pos (by
        have hs : 0 ≤ (s : ℝ) := s.property.1
        linarith)]
    calc
      NormedSpace.normalize
          (SphereGenerator.canonicalBasepoint m : Target m) =
          (SphereGenerator.canonicalBasepoint m : Target m) :=
        NormedSpace.normalize_eq_self_of_norm_eq_one
          (SphereGenerator.sphere_norm_eq_one m
            (SphereGenerator.canonicalBasepoint m))
      _ = (a.representative t : Target m) :=
        (congrArg Subtype.val
          (a.representative.property t ht)).symm

theorem homotopic_regularizedGenLoop
    (a : SmoothSphereApprox.Approximation q) (y : Domain m)
    (hy : ‖y‖ < 1 / 2) :
    GenLoop.Homotopic q (regularizedGenLoop a y hy) :=
  a.homotopic.trans ⟨regularizationHomotopyRel a y hy⟩

theorem cubeDomain_injective (m : ℕ) :
    Function.Injective (cubeDomain m) := by
  intro s t h
  funext i
  apply Subtype.ext
  exact congrArg (fun v : Domain m => v i) h

theorem isCompact_range_cubeDomain (m : ℕ) :
    IsCompact (range (cubeDomain m)) :=
  isCompact_range (continuous_cubeDomain m)

theorem vertical_normalizedRaw_gt_half_of_regularizedMap_eq_antipode
    (a : SmoothSphereApprox.Approximation q) {y : Domain m}
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I)
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    1 / 2 <
      vertical m (normalizedRaw a (cubeDomain m t)) := by
  let v := cubeDomain m t
  let w := transformedRaw a y v
  have hwne : w ≠ 0 := transformedRaw_ne_zero a hy v
  have hnormalize :
      NormedSpace.normalize w =
        -(SphereGenerator.canonicalBasepoint m : Target m) := by
    simpa only [regularizedMap, coe_neg_sphere] using
      congrArg Subtype.val ht
  have hw :
      w = ‖w‖ •
        (-(SphereGenerator.canonicalBasepoint m : Target m)) := by
    calc
      w = ‖w‖ • NormedSpace.normalize w :=
        (NormedSpace.norm_smul_normalize w).symm
      _ = ‖w‖ •
          (-(SphereGenerator.canonicalBasepoint m : Target m)) := by
        rw [hnormalize]
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hwlast : vertical m w = ‖w‖ := by
    calc
      vertical m w =
          vertical m
            (‖w‖ •
              (-(SphereGenerator.canonicalBasepoint m : Target m))) :=
        congrArg (vertical m) hw
      _ = ‖w‖ := by
        simp [vertical, coe_canonicalBasepoint]
  have hcoord := transformedRaw_last a y v
  change
    vertical m w =
      2 * vertical m (normalizedRaw a v) - 1 at hcoord
  rw [hwlast] at hcoord
  linarith

theorem horizontalMap_eq_of_regularizedMap_eq_antipode
    (a : SmoothSphereApprox.Approximation q) {y : Domain m}
    (hy : ‖y‖ < 1 / 2) (t : Fin (m + 1) → I)
    (ht :
      regularizedMap a y hy t =
        -(SphereGenerator.canonicalBasepoint m)) :
    horizontalMap a (cubeDomain m t) = y := by
  let v := cubeDomain m t
  let u := normalizedRaw a v
  let w := transformedRaw a y v
  have hnormalize :
      NormedSpace.normalize w =
        -(SphereGenerator.canonicalBasepoint m : Target m) := by
    simpa only [regularizedMap, coe_neg_sphere] using
      congrArg Subtype.val ht
  have hw :
      w = ‖w‖ •
        (-(SphereGenerator.canonicalBasepoint m : Target m)) := by
    calc
      w = ‖w‖ • NormedSpace.normalize w :=
        (NormedSpace.norm_smul_normalize w).symm
      _ = ‖w‖ •
          (-(SphereGenerator.canonicalBasepoint m : Target m)) := by
        rw [hnormalize]
  have hk : 1 / 2 < vertical m u :=
    vertical_normalizedRaw_gt_half_of_regularizedMap_eq_antipode
      a hy t ht
  have hcutoff :
      Real.smoothTransition (2 * vertical m u) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  change horizontal m u = y
  ext i
  have hwi : w i.castSucc = 0 := by
    rw [hw]
    simp [coe_canonicalBasepoint]
  have hcoord := transformedRaw_castSucc a y v i
  change
    w i.castSucc =
      horizontal m u i -
        Real.smoothTransition (2 * vertical m u) * y i at hcoord
  rw [hwi, hcutoff] at hcoord
  linarith

theorem finite_regularized_antipode_preimage
    (a : SmoothSphereApprox.Approximation q) {y : Domain m}
    (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0) :
    {t |
      regularizedGenLoop a y hy t =
        -(SphereGenerator.canonicalBasepoint m)}.Finite := by
  let K : Set (Domain m) := range (cubeDomain m)
  have hfiber : (K ∩ horizontalMap a ⁻¹' {y}).Finite :=
    RegularValue.finite_regular_fiber_inter
      (horizontalMap a) (contDiff_horizontalMap a) y hregular K
        (isCompact_range_cubeDomain m)
  have hpreimage :
      (cubeDomain m ⁻¹' (K ∩ horizontalMap a ⁻¹' {y})).Finite :=
    hfiber.preimage (cubeDomain_injective m).injOn
  apply hpreimage.subset
  intro t ht
  refine ⟨⟨t, rfl⟩, ?_⟩
  exact horizontalMap_eq_of_regularizedMap_eq_antipode a hy t ht

/-- Every based cubical self-map of the sphere is homotopic to a smooth
representative with a finite, transverse antipode fiber. -/
theorem exists_regularization (q :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    ∃ a : SmoothSphereApprox.Approximation q,
      ∃ y : Domain m,
        ∃ hy : ‖y‖ < 1 / 2,
          (∀ v, horizontalMap a v = y →
            (fderiv ℝ (horizontalMap a) v).det ≠ 0) ∧
          GenLoop.Homotopic q (regularizedGenLoop a y hy) ∧
          {t |
            regularizedGenLoop a y hy t =
              -(SphereGenerator.canonicalBasepoint m)}.Finite := by
  obtain ⟨a⟩ := SmoothSphereApprox.exists_approximation q
  obtain ⟨y, hy, hregular⟩ := exists_small_regular_value a
  exact ⟨a, y, hy, hregular, homotopic_regularizedGenLoop a y hy,
    finite_regularized_antipode_preimage a hy hregular⟩

end CanonicalBasepoint

end Submission.SphereRegularApprox
