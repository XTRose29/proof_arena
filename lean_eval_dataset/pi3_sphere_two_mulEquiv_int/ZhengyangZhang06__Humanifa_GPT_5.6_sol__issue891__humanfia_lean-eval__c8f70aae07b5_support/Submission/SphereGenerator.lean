import Mathlib

open scoped unitInterval

noncomputable section

namespace Submission.SphereGenerator

/-- Affinely center the unit cube at the origin. -/
def centered (n : ℕ) (t : Fin (n + 1) → I) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun i => 2 * (t i : ℝ) - 1

@[simp]
theorem centered_apply (n : ℕ) (t : Fin (n + 1) → I) (i : Fin (n + 1)) :
    centered n t i = 2 * (t i : ℝ) - 1 :=
  rfl

/-- The radial coordinate on the centered cube, measured in the sup norm. -/
def cubeRadius (n : ℕ) (t : Fin (n + 1) → I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |centered n t i|

theorem abs_centered_le_one (n : ℕ) (t : Fin (n + 1) → I) (i : Fin (n + 1)) :
    |centered n t i| ≤ 1 := by
  rw [centered_apply, abs_le]
  constructor <;> linarith [(t i).property.1, (t i).property.2]

theorem cubeRadius_nonneg (n : ℕ) (t : Fin (n + 1) → I) :
    0 ≤ cubeRadius n t := by
  calc
    0 ≤ |centered n t 0| := abs_nonneg _
    _ ≤ cubeRadius n t :=
      Finset.le_sup' (fun i : Fin (n + 1) => |centered n t i|) (Finset.mem_univ 0)

theorem cubeRadius_le_one (n : ℕ) (t : Fin (n + 1) → I) :
    cubeRadius n t ≤ 1 :=
  Finset.sup'_le Finset.univ_nonempty _ fun i _ => abs_centered_le_one n t i

theorem cubeRadius_eq_one_of_mem_boundary (n : ℕ) (t : Fin (n + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    cubeRadius n t = 1 := by
  apply le_antisymm (cubeRadius_le_one n t)
  obtain ⟨i, hi | hi⟩ := ht
  · have hcoord : |centered n t i| = 1 := by norm_num [centered_apply, hi]
    rw [← hcoord]
    exact Finset.le_sup' (fun j : Fin (n + 1) => |centered n t j|) (Finset.mem_univ i)
  · have hcoord : |centered n t i| = 1 := by norm_num [centered_apply, hi]
    rw [← hcoord]
    exact Finset.le_sup' (fun j : Fin (n + 1) => |centered n t j|) (Finset.mem_univ i)

theorem continuous_centered (n : ℕ) : Continuous (centered n) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp <|
    continuous_pi fun i => by fun_prop

theorem continuous_cubeRadius (n : ℕ) : Continuous (cubeRadius n) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  have hi : Continuous (fun t => centered n t i) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) i).comp
      (continuous_centered n)
  exact hi.abs

/-- An everywhere nonzero vector that runs from the north pole to the
south pole along each radial segment of the cube. -/
def rawGenerator (n : ℕ) (t : Fin (n + 1) → I) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 <|
    Fin.lastCases (1 - 2 * cubeRadius n t)
      fun i => (1 - cubeRadius n t) * centered n t i

@[simp]
theorem rawGenerator_last (n : ℕ) (t : Fin (n + 1) → I) :
    rawGenerator n t (Fin.last (n + 1)) = 1 - 2 * cubeRadius n t := by
  simp [rawGenerator]

@[simp]
theorem rawGenerator_castSucc (n : ℕ) (t : Fin (n + 1) → I) (i : Fin (n + 1)) :
    rawGenerator n t i.castSucc = (1 - cubeRadius n t) * centered n t i := by
  simp [rawGenerator]

theorem rawGenerator_ne_zero (n : ℕ) (t : Fin (n + 1) → I) :
    rawGenerator n t ≠ 0 := by
  intro hzero
  have hlast := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 2)) =>
    v (Fin.last (n + 1))) hzero
  simp only [rawGenerator_last, PiLp.zero_apply] at hlast
  have hradius : cubeRadius n t = 1 / 2 := by linarith
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j : Fin (n + 1) => |centered n t j|)
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 2)) => v i.castSucc) hzero
  simp only [rawGenerator_castSucc, PiLp.zero_apply, hradius] at hcoord
  have hcentered : centered n t i = 0 := by linarith
  have hi' : cubeRadius n t = |centered n t i| := hi
  have : cubeRadius n t = 0 := hi'.trans (abs_eq_zero.mpr hcentered)
  linarith

theorem continuous_rawGenerator (n : ℕ) : Continuous (rawGenerator n) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 2) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [Fin.lastCases_last]
      change Continuous ((fun _ => (1 : ℝ)) - (fun _ => (2 : ℝ)) * cubeRadius n)
      exact continuous_const.sub (continuous_const.mul (continuous_cubeRadius n))
  | cast j =>
      simp only [Fin.lastCases_castSucc]
      change Continuous
        ((fun a => 1 - cubeRadius n a) * (fun a => centered n a j))
      exact (continuous_const.sub (continuous_cubeRadius n)).mul <|
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) j).comp
          (continuous_centered n)

/-- The canonical cubical representative of the diagonal sphere generator,
based at the south pole. -/
def canonicalGenerator (n : ℕ) (t : Fin (n + 1) → I) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  ⟨NormedSpace.normalize (rawGenerator n t), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize (rawGenerator_ne_zero n t)⟩

theorem continuous_canonicalGenerator (n : ℕ) : Continuous (canonicalGenerator n) := by
  apply Continuous.subtype_mk
  change Continuous (fun t => ‖rawGenerator n t‖⁻¹ • rawGenerator n t)
  exact ((continuous_rawGenerator n).norm.inv₀ fun t =>
    norm_ne_zero_iff.mpr (rawGenerator_ne_zero n t)).smul (continuous_rawGenerator n)

/-- The distinguished base point of the canonical generator. -/
def canonicalBasepoint (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  canonicalGenerator n fun _ => 0

theorem canonicalGenerator_boundary (n : ℕ) (t : Fin (n + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    canonicalGenerator n t = canonicalBasepoint n := by
  have htRadius : cubeRadius n t = 1 :=
    cubeRadius_eq_one_of_mem_boundary n t ht
  have hzeroBoundary :
      (fun _ : Fin (n + 1) => (0 : I)) ∈ Cube.boundary (Fin (n + 1)) :=
    ⟨0, Or.inl rfl⟩
  have hzeroRadius : cubeRadius n (fun _ : Fin (n + 1) => (0 : I)) = 1 :=
    cubeRadius_eq_one_of_mem_boundary n _ hzeroBoundary
  have hraw :
      rawGenerator n t = rawGenerator n (fun _ : Fin (n + 1) => (0 : I)) := by
    ext i
    cases i using Fin.lastCases with
    | last => simp [rawGenerator, htRadius, hzeroRadius]
    | cast j => simp [rawGenerator, htRadius, hzeroRadius]
  apply Subtype.ext
  exact congrArg NormedSpace.normalize hraw

/-- The canonical generator as a continuous map. -/
def canonicalContinuousMap (n : ℕ) :
    C((Fin (n + 1) → I),
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  ⟨canonicalGenerator n, continuous_canonicalGenerator n⟩

/-- A concrete generalized loop representing the positive sphere class. -/
def canonicalGenLoop (n : ℕ) :
    GenLoop (Fin (n + 1))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (canonicalBasepoint n) :=
  ⟨canonicalContinuousMap n, canonicalGenerator_boundary n⟩

/-- The homotopy class of the canonical cubical sphere generator. -/
def canonicalGeneratorClass (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (canonicalBasepoint n) :=
  Quotient.mk' (canonicalGenLoop n)

theorem sphere_norm_eq_one (n : ℕ)
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    ‖(y : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
  have hy : dist (y : EuclideanSpace ℝ (Fin (n + 2))) 0 = 1 := y.property
  rw [dist_zero_right] at hy
  exact hy

/-- A reflection carrying the canonical base point to a prescribed point of
the sphere. -/
def basepointReflection (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 2)) :=
  Submodule.reflection
    (ℝ ∙ ((canonicalBasepoint n : EuclideanSpace ℝ (Fin (n + 2))) - x.1))ᗮ

theorem basepointReflection_canonicalBasepoint (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    basepointReflection n x (canonicalBasepoint n) = x := by
  exact Submodule.reflection_sub <|
    (sphere_norm_eq_one n (canonicalBasepoint n)).trans (sphere_norm_eq_one n x).symm

/-- Restrict the basepoint reflection to the unit sphere. -/
def rotateToBasepoint (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  fun y => ⟨basepointReflection n x y, by
    rw [Metric.mem_sphere, dist_zero_right, (basepointReflection n x).norm_map]
    exact sphere_norm_eq_one n y⟩

theorem continuous_rotateToBasepoint (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Continuous (rotateToBasepoint n x) :=
  Continuous.subtype_mk
    ((basepointReflection n x).continuous.comp continuous_subtype_val) _

/-- The basepoint reflection bundled as a self-homeomorphism of the sphere. -/
def rotateToBasepointHomeomorph (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 where
  toFun := rotateToBasepoint n x
  invFun := rotateToBasepoint n x
  left_inv y := by
    apply Subtype.ext
    exact Submodule.reflection_reflection _ _
  right_inv y := by
    apply Subtype.ext
    exact Submodule.reflection_reflection _ _
  continuous_toFun := continuous_rotateToBasepoint n x
  continuous_invFun := continuous_rotateToBasepoint n x

@[simp]
theorem rotateToBasepoint_canonicalBasepoint (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    rotateToBasepoint n x (canonicalBasepoint n) = x :=
  Subtype.ext (basepointReflection_canonicalBasepoint n x)

/-- The concrete sphere generator transported to an arbitrary base point. -/
def generatorAt (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (t : Fin (n + 1) → I) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  rotateToBasepoint n x (canonicalGenerator n t)

theorem continuous_generatorAt (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Continuous (generatorAt n x) :=
  (continuous_rotateToBasepoint n x).comp (continuous_canonicalGenerator n)

theorem generatorAt_boundary (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (t : Fin (n + 1) → I) (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    generatorAt n x t = x := by
  rw [generatorAt, canonicalGenerator_boundary n t ht,
    rotateToBasepoint_canonicalBasepoint]

/-- The transported generator as a generalized loop based at `x`. -/
def genLoopAt (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    GenLoop (Fin (n + 1))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) x :=
  ⟨⟨generatorAt n x, continuous_generatorAt n x⟩, generatorAt_boundary n x⟩

/-- The concrete candidate generator in the exact homotopy group of the
benchmark statement. -/
def generatorClassAt (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    HomotopyGroup.Pi (n + 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) x :=
  Quotient.mk' (genLoopAt n x)

/-- Integer powers of the concrete generator. Proving that this homomorphism is
bijective is the remaining degree-classification statement. -/
def generatorZPowersHomAt (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Multiplicative ℤ →*
      HomotopyGroup.Pi (n + 1)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) x :=
  zpowersHom _ (generatorClassAt n x)

end Submission.SphereGenerator
