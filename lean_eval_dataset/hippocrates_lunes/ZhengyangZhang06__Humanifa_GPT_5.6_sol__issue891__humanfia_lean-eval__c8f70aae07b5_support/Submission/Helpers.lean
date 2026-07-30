import ChallengeDeps
import Mathlib.LinearAlgebra.Basis.Fin

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory

namespace Submission.Helpers

noncomputable section

/-- A fixed unit semidisk used as the common model for all three semidisks. -/
def unitLowerSemidisk : Set Plane :=
  closedHalfDisk A (B 1) (fun t => t ≤ 0)

/-- The similarity taking the unit semidisk to the horizontal-leg semidisk. -/
def horizontalMap (a : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := (a * p.1, a * p.2)
  map_add' p q := by ext <;> simp [mul_add]
  map_smul' c p := by ext <;> dsimp <;> ring

/-- The similarity taking the unit semidisk to the vertical-leg semidisk. -/
def verticalMap (b : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := (b * p.2, b * p.1)
  map_add' p q := by ext <;> simp [mul_add]
  map_smul' c p := by ext <;> dsimp <;> ring

/-- The linear part of the affine similarity taking the unit semidisk to the
hypotenuse semidisk. -/
def hypotenuseMap (a b : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := (-a * p.1 + b * p.2, b * p.1 + a * p.2)
  map_add' p q := by ext <;> simp [mul_add] <;> ring
  map_smul' c p := by ext <;> simp <;> ring

@[simp] theorem horizontalMap_apply (a : ℝ) (p : Plane) :
    horizontalMap a p = (a * p.1, a * p.2) := rfl

@[simp] theorem verticalMap_apply (b : ℝ) (p : Plane) :
    verticalMap b p = (b * p.2, b * p.1) := rfl

@[simp] theorem hypotenuseMap_apply (a b : ℝ) (p : Plane) :
    hypotenuseMap a b p = (-a * p.1 + b * p.2, b * p.1 + a * p.2) := rfl

theorem det_horizontalMap (a : ℝ) : LinearMap.det (horizontalMap a) = a ^ 2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [horizontalMap, LinearMap.toMatrix_apply]
  ring

theorem det_verticalMap (b : ℝ) : LinearMap.det (verticalMap b) = -(b ^ 2) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [verticalMap, LinearMap.toMatrix_apply]
  ring

theorem det_hypotenuseMap (a b : ℝ) :
    LinearMap.det (hypotenuseMap a b) = -(a ^ 2 + b ^ 2) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [hypotenuseMap, LinearMap.toMatrix_apply]
  ring

@[simp] theorem mem_unitLowerSemidisk (p : Plane) :
    p ∈ unitLowerSemidisk ↔ p.1 ^ 2 + p.2 ^ 2 ≤ p.1 ∧ p.2 ≤ 0 := by
  simp only [unitLowerSemidisk, closedHalfDisk, Set.mem_setOf_eq, euclideanDistSq,
    LeanEval.Geometry.HippocratesLunes.midpoint, A, B, det2, vec]
  constructor
  · rintro ⟨hcircle, hside⟩
    constructor <;> norm_num at hcircle hside ⊢ <;> nlinarith
  · rintro ⟨hcircle, hside⟩
    constructor <;> norm_num at hcircle hside ⊢ <;> nlinarith

theorem mem_horizontalSemidisk (a : ℝ) (ha : 0 < a) (p : Plane) :
    p ∈ closedHalfDisk A (B a) (fun t => t ≤ 0) ↔
      p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1 ∧ p.2 ≤ 0 := by
  simp only [closedHalfDisk, Set.mem_setOf_eq, euclideanDistSq,
    LeanEval.Geometry.HippocratesLunes.midpoint, A, B, det2, vec]
  constructor
  · rintro ⟨hcircle, hside⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hcircle, hside⟩
    constructor
    · nlinarith
    · nlinarith

theorem mem_verticalSemidisk (b : ℝ) (hb : 0 < b) (p : Plane) :
    p ∈ closedHalfDisk A (C b) (fun t => 0 ≤ t) ↔
      p.1 ^ 2 + p.2 ^ 2 ≤ b * p.2 ∧ p.1 ≤ 0 := by
  simp only [closedHalfDisk, Set.mem_setOf_eq, euclideanDistSq,
    LeanEval.Geometry.HippocratesLunes.midpoint, A, C, det2, vec]
  constructor
  · rintro ⟨hcircle, hside⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hcircle, hside⟩
    constructor
    · nlinarith
    · nlinarith

theorem mem_hypotenuseSemidisk (a b : ℝ) (p : Plane) :
    p ∈ hypotenuseSemidisk a b ↔
      p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1 + b * p.2 ∧
        b * p.1 + a * p.2 ≤ a * b := by
  simp only [hypotenuseSemidisk, closedHalfDisk, Set.mem_setOf_eq, euclideanDistSq,
    LeanEval.Geometry.HippocratesLunes.midpoint, B, C, det2, vec]
  constructor
  · rintro ⟨hcircle, hside⟩
    constructor <;> nlinarith
  · rintro ⟨hcircle, hside⟩
    constructor <;> nlinarith

theorem horizontalSemidisk_eq_image (a : ℝ) (ha : 0 < a) :
    closedHalfDisk A (B a) (fun t => t ≤ 0) = horizontalMap a '' unitLowerSemidisk := by
  ext p
  constructor
  · intro hp
    have hp' := (mem_horizontalSemidisk a ha p).1 hp
    let q : Plane := (a⁻¹ * p.1, a⁻¹ * p.2)
    refine ⟨q, ?_, ?_⟩
    · rw [mem_unitLowerSemidisk]
      constructor
      · have hscaled := mul_le_mul_of_nonneg_left hp'.1 (sq_nonneg a⁻¹)
        dsimp [q]
        calc
          (a⁻¹ * p.1) ^ 2 + (a⁻¹ * p.2) ^ 2 =
              (a⁻¹) ^ 2 * (p.1 ^ 2 + p.2 ^ 2) := by ring
          _ ≤ (a⁻¹) ^ 2 * (a * p.1) := hscaled
          _ = a⁻¹ * p.1 := by field_simp [ha.ne']
      · exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ha.le) hp'.2
    · ext <;> dsimp [q, horizontalMap] <;> field_simp [ha.ne']
  · rintro ⟨q, hq, rfl⟩
    rw [mem_unitLowerSemidisk] at hq
    rw [mem_horizontalSemidisk a ha]
    constructor
    · have hscaled := mul_le_mul_of_nonneg_left hq.1 (sq_nonneg a)
      calc
        (a * q.1) ^ 2 + (a * q.2) ^ 2 = a ^ 2 * (q.1 ^ 2 + q.2 ^ 2) := by ring
        _ ≤ a ^ 2 * q.1 := hscaled
        _ = a * (a * q.1) := by ring
    · exact mul_nonpos_of_nonneg_of_nonpos ha.le hq.2

theorem verticalSemidisk_eq_image (b : ℝ) (hb : 0 < b) :
    closedHalfDisk A (C b) (fun t => 0 ≤ t) = verticalMap b '' unitLowerSemidisk := by
  ext p
  constructor
  · intro hp
    have hp' := (mem_verticalSemidisk b hb p).1 hp
    let q : Plane := (b⁻¹ * p.2, b⁻¹ * p.1)
    refine ⟨q, ?_, ?_⟩
    · rw [mem_unitLowerSemidisk]
      constructor
      · have hscaled := mul_le_mul_of_nonneg_left hp'.1 (sq_nonneg b⁻¹)
        dsimp [q]
        calc
          (b⁻¹ * p.2) ^ 2 + (b⁻¹ * p.1) ^ 2 =
              (b⁻¹) ^ 2 * (p.1 ^ 2 + p.2 ^ 2) := by ring
          _ ≤ (b⁻¹) ^ 2 * (b * p.2) := hscaled
          _ = b⁻¹ * p.2 := by field_simp [hb.ne']
      · exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hb.le) hp'.2
    · ext <;> dsimp [q, verticalMap] <;> field_simp [hb.ne']
  · rintro ⟨q, hq, rfl⟩
    rw [mem_unitLowerSemidisk] at hq
    rw [mem_verticalSemidisk b hb]
    constructor
    · have hscaled := mul_le_mul_of_nonneg_left hq.1 (sq_nonneg b)
      calc
        (b * q.2) ^ 2 + (b * q.1) ^ 2 = b ^ 2 * (q.1 ^ 2 + q.2 ^ 2) := by ring
        _ ≤ b ^ 2 * q.1 := hscaled
        _ = b * (b * q.1) := by ring
    · exact mul_nonpos_of_nonneg_of_nonpos hb.le hq.2

set_option maxHeartbeats 800000 in
theorem hypotenuseSemidisk_eq_image (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    hypotenuseSemidisk a b =
      (fun q => B a + hypotenuseMap a b q) '' unitLowerSemidisk := by
  let c := a ^ 2 + b ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  ext p
  constructor
  · intro hp
    have hp' := (mem_hypotenuseSemidisk a b p).1 hp
    let q : Plane :=
      ((-a * (p.1 - a) + b * p.2) / c, (b * (p.1 - a) + a * p.2) / c)
    refine ⟨q, ?_, ?_⟩
    · rw [mem_unitLowerSemidisk]
      have hcircle :
          q.1 ^ 2 + q.2 ^ 2 - q.1 =
            (p.1 ^ 2 + p.2 ^ 2 - a * p.1 - b * p.2) / c := by
        dsimp [q]
        field_simp [hc.ne']
        ring
      have hcircle' :
          (p.1 ^ 2 + p.2 ^ 2 - a * p.1 - b * p.2) / c ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [hp'.1]) hc.le
      have hside' : (b * (p.1 - a) + a * p.2) / c ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [hp'.2]) hc.le
      constructor
      · nlinarith [hcircle, hcircle']
      · simpa [q] using hside'
    · ext <;> dsimp [q, B, hypotenuseMap]
      · field_simp [hc.ne']
        dsimp [c]
        ring
      · field_simp [hc.ne']
        dsimp [c]
        ring
  · rintro ⟨q, hq, rfl⟩
    rw [mem_unitLowerSemidisk] at hq
    rw [mem_hypotenuseSemidisk]
    have hcircle := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hq.1)
    have hside := mul_nonpos_of_nonneg_of_nonpos hc.le hq.2
    dsimp [B, hypotenuseMap] at hcircle hside ⊢
    constructor <;> nlinarith

theorem volume_image_add (x : Plane) (s : Set Plane) :
    volume ((fun y => x + y) '' s) = volume s := by
  have hset : (fun y => x + y) '' s = (fun y => -x + y) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [Set.mem_preimage, neg_add_cancel_left] using hz
    · intro hy
      exact ⟨-x + y, hy, by simp⟩
  rw [hset, measure_preimage_add]

theorem volume_horizontalSemidisk (a : ℝ) (ha : 0 < a) :
    volume (closedHalfDisk A (B a) (fun t => t ≤ 0)) =
      ENNReal.ofReal (a ^ 2) * volume unitLowerSemidisk := by
  rw [horizontalSemidisk_eq_image a ha,
    MeasureTheory.Measure.addHaar_image_linearMap, det_horizontalMap]
  simp only [abs_of_nonneg (sq_nonneg a)]

theorem volume_verticalSemidisk (b : ℝ) (hb : 0 < b) :
    volume (closedHalfDisk A (C b) (fun t => 0 ≤ t)) =
      ENNReal.ofReal (b ^ 2) * volume unitLowerSemidisk := by
  rw [verticalSemidisk_eq_image b hb,
    MeasureTheory.Measure.addHaar_image_linearMap, det_verticalMap]
  simp only [abs_neg, abs_of_nonneg (sq_nonneg b)]

theorem volume_hypotenuseSemidisk (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (hypotenuseSemidisk a b) =
      ENNReal.ofReal (a ^ 2 + b ^ 2) * volume unitLowerSemidisk := by
  rw [hypotenuseSemidisk_eq_image a b ha hb]
  rw [show (fun q => B a + hypotenuseMap a b q) '' unitLowerSemidisk =
      (fun z => B a + z) '' (hypotenuseMap a b '' unitLowerSemidisk) by
        rw [Set.image_image]]
  rw [volume_image_add, MeasureTheory.Measure.addHaar_image_linearMap,
    det_hypotenuseMap]
  simp only [abs_neg, abs_of_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))]

theorem volume_legSemidisks_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (closedHalfDisk A (B a) (fun t => t ≤ 0)) +
        volume (closedHalfDisk A (C b) (fun t => 0 ≤ t)) =
      volume (hypotenuseSemidisk a b) := by
  rw [volume_horizontalSemidisk a ha, volume_verticalSemidisk b hb,
    volume_hypotenuseSemidisk a b ha hb, ← add_mul,
    ← ENNReal.ofReal_add (sq_nonneg a) (sq_nonneg b)]

theorem rightTriangle_coordinates (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {p : Plane} (hp : p ∈ rightTriangle a b) :
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧ b * p.1 + a * p.2 ≤ a * b := by
  let s : Set Plane :=
    {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ b * q.1 + a * q.2 ≤ a * b}
  have hs_convex : Convex ℝ s := by
    rintro x ⟨hx₁, hx₂, hx₃⟩ y ⟨hy₁, hy₂, hy₃⟩ u v hu hv huv
    change 0 ≤ u * x.1 + v * y.1 ∧ 0 ≤ u * x.2 + v * y.2 ∧
      b * (u * x.1 + v * y.1) + a * (u * x.2 + v * y.2) ≤ a * b
    constructor
    · positivity
    constructor
    · positivity
    · have hx₃' := mul_le_mul_of_nonneg_left hx₃ hu
      have hy₃' := mul_le_mul_of_nonneg_left hy₃ hv
      calc
        b * (u * x.1 + v * y.1) + a * (u * x.2 + v * y.2) =
            u * (b * x.1 + a * x.2) + v * (b * y.1 + a * y.2) := by ring
        _ ≤ u * (a * b) + v * (a * b) := add_le_add hx₃' hy₃'
        _ = a * b := by rw [← add_mul, huv, one_mul]
  have hvertices : ({A, B a, C b} : Set Plane) ⊆ s := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · dsimp [s, A]
      constructor
      · exact le_rfl
      constructor
      · exact le_rfl
      · norm_num
        positivity
    · dsimp [s, B]
      constructor
      · exact ha.le
      constructor
      · exact le_rfl
      · nlinarith
    · dsimp [s, C]
      constructor
      · exact le_rfl
      constructor
      · exact hb.le
      · nlinarith
  have hp' : p ∈ s := by
    apply convexHull_min hvertices hs_convex
    exact hp
  exact hp'

set_option maxHeartbeats 800000 in
theorem mem_rightTriangle_of_coordinates (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {p : Plane} (hp₁ : 0 ≤ p.1) (hp₂ : 0 ≤ p.2)
    (hp₃ : b * p.1 + a * p.2 ≤ a * b) : p ∈ rightTriangle a b := by
  let w : Fin 3 → ℝ :=
    ![(a * b - b * p.1 - a * p.2) / (a * b), p.1 / a, p.2 / b]
  let z : Fin 3 → Plane := ![A, B a, C b]
  change p ∈ convexHull ℝ ({A, B a, C b} : Set Plane)
  refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · dsimp [w]
      exact div_nonneg (by nlinarith) (mul_pos ha hb).le
    · dsimp [w]
      exact div_nonneg hp₁ ha.le
    · dsimp [w]
      exact div_nonneg hp₂ hb.le
  · dsimp [w]
    simp [Fin.sum_univ_succ, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
    field_simp [ha.ne', hb.ne']
    ring
  · intro i
    fin_cases i <;> simp [z, A, B, C]
  · apply Prod.ext
    · dsimp [w, z, A, B, C]
      simp [Fin.sum_univ_succ, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
      field_simp [ha.ne', hb.ne']
    · dsimp [w, z, A, B, C]
      simp [Fin.sum_univ_succ, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
      field_simp [ha.ne', hb.ne']

theorem rightTriangle_subset_hypotenuseSemidisk (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    rightTriangle a b ⊆ hypotenuseSemidisk a b := by
  intro p hp
  obtain ⟨hp₁, hp₂, hp₃⟩ := rightTriangle_coordinates a b ha hb hp
  have hp₁a : p.1 ≤ a := by nlinarith
  have hp₂b : p.2 ≤ b := by nlinarith
  have h₁ := mul_nonneg hp₁ (sub_nonneg.mpr hp₁a)
  have h₂ := mul_nonneg hp₂ (sub_nonneg.mpr hp₂b)
  rw [mem_hypotenuseSemidisk]
  constructor
  · nlinarith
  · exact hp₃

theorem hypotenuseSemidisk_subset_decomposition (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    hypotenuseSemidisk a b ⊆
      (rightTriangle a b ∪
          (closedHalfDisk A (B a) (fun t => t ≤ 0) ∩ hypotenuseSemidisk a b)) ∪
        (closedHalfDisk A (C b) (fun t => 0 ≤ t) ∩ hypotenuseSemidisk a b) := by
  intro p hp
  have hp' := (mem_hypotenuseSemidisk a b p).1 hp
  by_cases hp₁ : 0 ≤ p.1
  · by_cases hp₂ : 0 ≤ p.2
    · exact Or.inl (Or.inl (mem_rightTriangle_of_coordinates a b ha hb hp₁ hp₂ hp'.2))
    · have hp₂' : p.2 ≤ 0 := le_of_not_ge hp₂
      have hcircle : p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1 := by
        have hb₂ : b * p.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hp₂'
        nlinarith
      have hpH : p ∈ closedHalfDisk A (B a) (fun t => t ≤ 0) :=
        (mem_horizontalSemidisk a ha p).2 ⟨hcircle, hp₂'⟩
      exact Or.inl (Or.inr ⟨hpH, hp⟩)
  · have hp₁' : p.1 ≤ 0 := le_of_not_ge hp₁
    have hcircle : p.1 ^ 2 + p.2 ^ 2 ≤ b * p.2 := by
      have ha₁ : a * p.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hp₁'
      nlinarith
    have hpV : p ∈ closedHalfDisk A (C b) (fun t => 0 ≤ t) :=
      (mem_verticalSemidisk b hb p).2 ⟨hcircle, hp₁'⟩
    exact Or.inr ⟨hpV, hp⟩

theorem hypotenuseSemidisk_decomposition (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    hypotenuseSemidisk a b =
      (rightTriangle a b ∪
          (closedHalfDisk A (B a) (fun t => t ≤ 0) ∩ hypotenuseSemidisk a b)) ∪
        (closedHalfDisk A (C b) (fun t => 0 ≤ t) ∩ hypotenuseSemidisk a b) := by
  apply Set.Subset.antisymm (hypotenuseSemidisk_subset_decomposition a b ha hb)
  rintro p (hp | hp)
  · rcases hp with hpT | ⟨_, hpK⟩
    · exact rightTriangle_subset_hypotenuseSemidisk a b ha hb hpT
    · exact hpK
  · exact hp.2

theorem measurableSet_horizontalSemidisk (a : ℝ) (ha : 0 < a) :
    MeasurableSet (closedHalfDisk A (B a) (fun t => t ≤ 0)) := by
  rw [show closedHalfDisk A (B a) (fun t => t ≤ 0) =
      {p : Plane | p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1 ∧ p.2 ≤ 0} by
        ext p
        exact mem_horizontalSemidisk a ha p]
  measurability

theorem measurableSet_verticalSemidisk (b : ℝ) (hb : 0 < b) :
    MeasurableSet (closedHalfDisk A (C b) (fun t => 0 ≤ t)) := by
  rw [show closedHalfDisk A (C b) (fun t => 0 ≤ t) =
      {p : Plane | p.1 ^ 2 + p.2 ^ 2 ≤ b * p.2 ∧ p.1 ≤ 0} by
        ext p
        exact mem_verticalSemidisk b hb p]
  measurability

theorem measurableSet_hypotenuseSemidisk (a b : ℝ) :
    MeasurableSet (hypotenuseSemidisk a b) := by
  rw [show hypotenuseSemidisk a b =
      {p : Plane | p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1 + b * p.2 ∧
        b * p.1 + a * p.2 ≤ a * b} by
        ext p
        exact mem_hypotenuseSemidisk a b p]
  measurability

def horizontalAxis : Set Plane := {p | p.2 = 0}

def verticalAxis : Set Plane := {p | p.1 = 0}

theorem volume_horizontalAxis : volume horizontalAxis = 0 := by
  let s : Submodule ℝ Plane := LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)
  have hs : s ≠ ⊤ := by
    intro hs'
    have hmem : ((0, 1) : Plane) ∈ s := by rw [hs']; exact Submodule.mem_top
    simp [s] at hmem
  have hset : horizontalAxis = (s : Set Plane) := by
    ext p
    simp [horizontalAxis, s]
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule volume s hs

theorem volume_verticalAxis : volume verticalAxis = 0 := by
  let s : Submodule ℝ Plane := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)
  have hs : s ≠ ⊤ := by
    intro hs'
    have hmem : ((1, 0) : Plane) ∈ s := by rw [hs']; exact Submodule.mem_top
    simp [s] at hmem
  have hset : verticalAxis = (s : Set Plane) := by
    ext p
    simp [verticalAxis, s]
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule volume s hs

theorem aedisjoint_rightTriangle_horizontal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    AEDisjoint volume (rightTriangle a b) (closedHalfDisk A (B a) (fun t => t ≤ 0)) := by
  rw [AEDisjoint]
  apply measure_mono_null _ volume_horizontalAxis
  rintro p ⟨hpT, hpH⟩
  have hpT' := rightTriangle_coordinates a b ha hb hpT
  have hpH' := (mem_horizontalSemidisk a ha p).1 hpH
  change p.2 = 0
  nlinarith

theorem aedisjoint_rightTriangle_vertical (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    AEDisjoint volume (rightTriangle a b) (closedHalfDisk A (C b) (fun t => 0 ≤ t)) := by
  rw [AEDisjoint]
  apply measure_mono_null _ volume_verticalAxis
  rintro p ⟨hpT, hpV⟩
  have hpT' := rightTriangle_coordinates a b ha hb hpT
  have hpV' := (mem_verticalSemidisk b hb p).1 hpV
  change p.1 = 0
  nlinarith

theorem aedisjoint_horizontal_vertical (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    AEDisjoint volume (closedHalfDisk A (B a) (fun t => t ≤ 0))
      (closedHalfDisk A (C b) (fun t => 0 ≤ t)) := by
  rw [AEDisjoint]
  apply measure_mono_null _ volume_horizontalAxis
  rintro p ⟨hpH, hpV⟩
  have hpH' := (mem_horizontalSemidisk a ha p).1 hpH
  have hpV' := (mem_verticalSemidisk b hb p).1 hpV
  have hax : a * p.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hpV'.2
  change p.2 = 0
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

theorem volume_unitLowerSemidisk_ne_top : volume unitLowerSemidisk ≠ ⊤ := by
  have hsub : unitLowerSemidisk ⊆
      Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro p hp
    have hp' := mem_unitLowerSemidisk p |>.1 hp
    have hp₁0 : 0 ≤ p.1 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    have hp₁1 : p.1 ≤ 1 := by nlinarith [sq_nonneg (p.1 - 1), sq_nonneg p.2]
    have hp₂sq : p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.1]
    constructor
    · constructor <;> nlinarith [sq_nonneg (p.1 + 1), sq_nonneg (p.1 - 1)]
    · constructor <;> nlinarith [sq_nonneg (p.2 + 1), sq_nonneg (p.2 - 1)]
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  exact ((measure_mono hsub).trans_lt hcompact.measure_lt_top).ne

theorem volume_hypotenuseSemidisk_ne_top (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (hypotenuseSemidisk a b) ≠ ⊤ := by
  rw [volume_hypotenuseSemidisk a b ha hb]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top volume_unitLowerSemidisk_ne_top

theorem volume_hypotenuseSemidisk_decomposition (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (hypotenuseSemidisk a b) =
      (volume (rightTriangle a b) +
          volume (closedHalfDisk A (B a) (fun t => t ≤ 0) ∩ hypotenuseSemidisk a b)) +
        volume (closedHalfDisk A (C b) (fun t => 0 ≤ t) ∩ hypotenuseSemidisk a b) := by
  let H := closedHalfDisk A (B a) (fun t => t ≤ 0)
  let V := closedHalfDisk A (C b) (fun t => 0 ≤ t)
  let K := hypotenuseSemidisk a b
  let T := rightTriangle a b
  have hH : MeasurableSet H := measurableSet_horizontalSemidisk a ha
  have hV : MeasurableSet V := measurableSet_verticalSemidisk b hb
  have hK : MeasurableSet K := measurableSet_hypotenuseSemidisk a b
  have hTH : AEDisjoint volume T H := aedisjoint_rightTriangle_horizontal a b ha hb
  have hTV : AEDisjoint volume T V := aedisjoint_rightTriangle_vertical a b ha hb
  have hHV : AEDisjoint volume H V := aedisjoint_horizontal_vertical a b ha hb
  have hTHK : AEDisjoint volume T (H ∩ K) :=
    hTH.mono Set.Subset.rfl Set.inter_subset_left
  have hTVK : AEDisjoint volume T (V ∩ K) :=
    hTV.mono Set.Subset.rfl Set.inter_subset_left
  have hHKVK : AEDisjoint volume (H ∩ K) (V ∩ K) :=
    hHV.mono Set.inter_subset_left Set.inter_subset_left
  have hUnion : AEDisjoint volume (T ∪ (H ∩ K)) (V ∩ K) :=
    hTVK.union_left hHKVK
  have hdecomp : K = (T ∪ (H ∩ K)) ∪ (V ∩ K) :=
    hypotenuseSemidisk_decomposition a b ha hb
  change volume K = (volume T + volume (H ∩ K)) + volume (V ∩ K)
  calc
    volume K = volume ((T ∪ (H ∩ K)) ∪ (V ∩ K)) := congr_arg volume hdecomp
    _ = volume (T ∪ (H ∩ K)) + volume (V ∩ K) :=
      measure_union₀ (hV.inter hK).nullMeasurableSet hUnion
    _ = (volume T + volume (H ∩ K)) + volume (V ∩ K) := by
      rw [measure_union₀ (hH.inter hK).nullMeasurableSet hTHK]

theorem hippocrates_lunes_measure (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b) := by
  let H := closedHalfDisk A (B a) (fun t => t ≤ 0)
  let V := closedHalfDisk A (C b) (fun t => 0 ≤ t)
  let K := hypotenuseSemidisk a b
  let T := rightTriangle a b
  change volume (H \ K) + volume (V \ K) = volume T
  have hKmeas : MeasurableSet K := measurableSet_hypotenuseSemidisk a b
  have hHsplit : volume (H \ K) + volume (H ∩ K) = volume H :=
    measure_sdiff_add_inter H hKmeas
  have hVsplit : volume (V \ K) + volume (V ∩ K) = volume V :=
    measure_sdiff_add_inter V hKmeas
  have hlegs : volume H + volume V = volume K := volume_legSemidisks_add a b ha hb
  have hdecomp : volume K = (volume T + volume (H ∩ K)) + volume (V ∩ K) :=
    volume_hypotenuseSemidisk_decomposition a b ha hb
  have hKfin : volume K ≠ ⊤ := volume_hypotenuseSemidisk_ne_top a b ha hb
  have hHKfin : volume (H ∩ K) ≠ ⊤ :=
    ne_of_lt ((measure_mono Set.inter_subset_right).trans_lt
      (lt_top_iff_ne_top.mpr hKfin))
  have hVKfin : volume (V ∩ K) ≠ ⊤ :=
    ne_of_lt ((measure_mono Set.inter_subset_right).trans_lt
      (lt_top_iff_ne_top.mpr hKfin))
  have hcommon : volume (H ∩ K) + volume (V ∩ K) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hHKfin, hVKfin⟩
  have heq :
      (volume (H \ K) + volume (V \ K)) + (volume (H ∩ K) + volume (V ∩ K)) =
        volume T + (volume (H ∩ K) + volume (V ∩ K)) := by
    calc
      (volume (H \ K) + volume (V \ K)) + (volume (H ∩ K) + volume (V ∩ K)) =
          (volume (H \ K) + volume (H ∩ K)) +
            (volume (V \ K) + volume (V ∩ K)) := by ac_rfl
      _ = volume H + volume V := by rw [hHsplit, hVsplit]
      _ = volume K := hlegs
      _ = (volume T + volume (H ∩ K)) + volume (V ∩ K) := hdecomp
      _ = volume T + (volume (H ∩ K) + volume (V ∩ K)) := by ac_rfl
  exact (ENNReal.add_left_inj hcommon).1 heq

end

end Submission.Helpers
