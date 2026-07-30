import Submission.SphereSmoothRepresentative

open scoped ContDiff unitInterval Topology

noncomputable section

namespace Submission.SphereSmoothBubble

open Set
open Submission.SphereRegularApprox
open Submission.SphereSmoothRepresentative

abbrev Space :=
  Fin 3 → ℝ

/-- Squared Euclidean radius on the ambient coordinate space. -/
def radiusSq (u : Space) : ℝ :=
  ∑ i, u i ^ 2

theorem radiusSq_nonneg (u : Space) :
    0 ≤ radiusSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[fun_prop]
theorem contDiff_radiusSq :
    ContDiff ℝ ∞ radiusSq := by
  unfold radiusSq
  fun_prop

/-- A flat radial cutoff, positive on the open unit ball and zero outside
the closed unit ball. -/
def bump (u : Space) : ℝ :=
  expNegInvGlue (1 - radiusSq u)

@[fun_prop]
theorem contDiff_bump :
    ContDiff ℝ ∞ bump :=
  expNegInvGlue.contDiff.comp
    (contDiff_const.sub contDiff_radiusSq)

theorem bump_nonneg (u : Space) :
    0 ≤ bump u :=
  expNegInvGlue.nonneg _

theorem bump_pos_of_radiusSq_lt_one
    {u : Space} (hu : radiusSq u < 1) :
    0 < bump u :=
  expNegInvGlue.pos_of_pos (sub_pos.mpr hu)

theorem bump_eq_zero_of_one_le_radiusSq
    {u : Space} (hu : 1 ≤ radiusSq u) :
    bump u = 0 :=
  expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hu)

def denominator (u : Space) : ℝ :=
  bump u ^ 2 + radiusSq u

theorem denominator_pos (u : Space) :
    0 < denominator u := by
  by_cases hu : radiusSq u = 0
  · have hb : 0 < bump u := by
      apply bump_pos_of_radiusSq_lt_one
      rw [hu]
      norm_num
    rw [denominator, hu, add_zero]
    exact sq_pos_of_pos hb
  · have hs : 0 < radiusSq u :=
      lt_of_le_of_ne (radiusSq_nonneg u) (Ne.symm hu)
    exact lt_of_lt_of_le hs
      (le_add_of_nonneg_left (sq_nonneg _))

@[fun_prop]
theorem contDiff_denominator :
    ContDiff ℝ ∞ denominator := by
  unfold denominator
  fun_prop

/-- Smooth homogeneous coordinates for a compact stereographic bubble. -/
def raw (u : Space) : Target 2 :=
  WithLp.toLp 2 <|
    Fin.lastCases (bump u ^ 2 - radiusSq u)
      fun i => 2 * bump u * u i

@[simp]
theorem raw_last (u : Space) :
    raw u (Fin.last 3) =
      bump u ^ 2 - radiusSq u := by
  change
    Fin.lastCases (bump u ^ 2 - radiusSq u)
        (fun i => 2 * bump u * u i) (Fin.last 3) =
      bump u ^ 2 - radiusSq u
  simp only [Fin.lastCases_last]

@[simp]
theorem raw_castSucc (u : Space) (i : Fin 3) :
    raw u i.castSucc = 2 * bump u * u i := by
  change
    Fin.lastCases (bump u ^ 2 - radiusSq u)
        (fun j => 2 * bump u * u j) i.castSucc =
      2 * bump u * u i
  simp only [Fin.lastCases_castSucc]

@[fun_prop]
theorem contDiff_raw :
    ContDiff ℝ ∞ raw := by
  unfold raw
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 4 => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
    fun_prop
  · simp only [Fin.lastCases_castSucc]
    fun_prop

theorem norm_raw_sq (u : Space) :
    ‖raw u‖ ^ 2 = denominator u ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  change
    (2 * bump u * u 0) ^ 2 +
          (2 * bump u * u 1) ^ 2 +
        (2 * bump u * u 2) ^ 2 +
      (bump u ^ 2 - radiusSq u) ^ 2 =
        denominator u ^ 2
  have hradius :
      radiusSq u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    simp [radiusSq, Fin.sum_univ_three]
  simp only [denominator, hradius]
  ring

theorem norm_raw (u : Space) :
    ‖raw u‖ = denominator u := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (denominator_pos u).le]
  exact norm_raw_sq u

theorem raw_ne_zero (u : Space) :
    raw u ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_raw]
  exact (denominator_pos u).ne'

/-- The smooth compact stereographic bubble. -/
def sphereMap (u : Space) : Target 2 :=
  NormedSpace.normalize (raw u)

@[fun_prop]
theorem contDiff_sphereMap :
    ContDiff ℝ ∞ sphereMap := by
  change ContDiff ℝ ∞
    (fun u => ‖raw u‖⁻¹ • raw u)
  exact
    ((contDiff_raw.norm ℝ raw_ne_zero).inv fun u =>
      norm_ne_zero_iff.mpr (raw_ne_zero u)).smul contDiff_raw

theorem norm_sphereMap (u : Space) :
    ‖sphereMap u‖ = 1 :=
  NormedSpace.norm_normalize (raw_ne_zero u)

theorem sphereMap_formula (u : Space) :
    sphereMap u = (denominator u)⁻¹ • raw u := by
  rw [sphereMap, NormedSpace.normalize, norm_raw]

theorem sphereMap_eq_basepoint_of_one_le_radiusSq
    {u : Space} (hu : 1 ≤ radiusSq u) :
    sphereMap u =
      (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
  have hb := bump_eq_zero_of_one_le_radiusSq hu
  rw [sphereMap_formula]
  rw [SphereRegularApprox.coe_canonicalBasepoint]
  have hs : 0 < radiusSq u :=
    zero_lt_one.trans_le hu
  ext i
  cases i using Fin.lastCases with
  | last =>
      change
        (denominator u)⁻¹ * (bump u ^ 2 - radiusSq u) = -1
      simp [denominator, hb, hs.ne']
  | cast j =>
      simp [denominator, hb]
      change j.castSucc ≠ Fin.last 3
      exact j.castSucc_ne_last

/-- Affine coordinates placing the support ball strictly inside the cube. -/
def localCoordinates (x : Space) : Space :=
  fun i => 4 * (x i - 1 / 2)

@[fun_prop]
theorem contDiff_localCoordinates :
    ContDiff ℝ ∞ localCoordinates := by
  unfold localCoordinates
  fun_prop

theorem one_le_radiusSq_localCoordinates_of_outer
    {x : Space} {i : Fin 3}
    (hi : x i ≤ 0 ∨ 1 ≤ x i) :
    1 ≤ radiusSq (localCoordinates x) := by
  have hcoord : 2 ≤ ‖localCoordinates x i‖ := by
    rcases hi with hi | hi
    · rw [Real.norm_eq_abs, abs_of_nonpos]
      · dsimp [localCoordinates]
        linarith
      · dsimp [localCoordinates]
        linarith
    · rw [Real.norm_eq_abs, abs_of_nonneg]
      · dsimp [localCoordinates]
        linarith
      · dsimp [localCoordinates]
        linarith
  have hsingle :
      (localCoordinates x i) ^ 2 ≤
        radiusSq (localCoordinates x) := by
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (localCoordinates x j))
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs] at hcoord
  have hcoordSq :
      (2 : ℝ) ^ 2 ≤ |localCoordinates x i| ^ 2 :=
    (sq_le_sq₀ (by norm_num) (abs_nonneg _)).mpr hcoord
  rw [sq_abs] at hcoordSq
  nlinarith

theorem one_le_radiusSq_localCoordinates_of_quarter
    {x : Space} {i : Fin 3}
    (hi : x i ≤ 1 / 4 ∨ 3 / 4 ≤ x i) :
    1 ≤ radiusSq (localCoordinates x) := by
  have hcoord : 1 ≤ ‖localCoordinates x i‖ := by
    rcases hi with hi | hi
    · rw [Real.norm_eq_abs, abs_of_nonpos]
      · dsimp [localCoordinates]
        linarith
      · dsimp [localCoordinates]
        linarith
    · rw [Real.norm_eq_abs, abs_of_nonneg]
      · dsimp [localCoordinates]
        linarith
      · dsimp [localCoordinates]
        linarith
  have hsingle :
      (localCoordinates x i) ^ 2 ≤
        radiusSq (localCoordinates x) := by
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (localCoordinates x j))
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs] at hcoord
  have hcoordSq :
      (1 : ℝ) ^ 2 ≤ |localCoordinates x i| ^ 2 :=
    (sq_le_sq₀ (by norm_num) (abs_nonneg _)).mpr hcoord
  rw [sq_abs] at hcoordSq
  nlinarith

/-- The compact bubble as a smooth ambient representative of a cubical
3-loop. -/
def smoothMap : Map 2 where
  toFun := sphereMap ∘ localCoordinates
  contDiff_toFun :=
    contDiff_sphereMap.comp contDiff_localCoordinates
  norm_toFun := fun _ => norm_sphereMap _
  map_outer := fun x i hi =>
    sphereMap_eq_basepoint_of_one_le_radiusSq <|
      one_le_radiusSq_localCoordinates_of_outer (x := x) (i := i) hi

end Submission.SphereSmoothBubble
