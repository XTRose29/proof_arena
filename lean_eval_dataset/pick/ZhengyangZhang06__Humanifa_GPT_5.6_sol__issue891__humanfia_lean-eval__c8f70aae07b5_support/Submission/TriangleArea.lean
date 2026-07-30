import Mathlib
import Submission.Triangle

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.TriangleArea

/-- The open standard two-simplex in Cartesian coordinates. -/
def standardInterior : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}

/-- The standard two-simplex is a region between the zero function and
`x ↦ 1 - x` over the unit interval. -/
theorem standardInterior_eq_regionBetween :
    standardInterior =
      regionBetween (fun _ : ℝ => 0) (fun x : ℝ => 1 - x)
        (Set.Ioo 0 1) := by
  ext q
  simp only [standardInterior, Set.mem_setOf_eq, regionBetween,
    Set.mem_Ioo]
  constructor
  · rintro ⟨hq₁, hq₂, hsum⟩
    exact ⟨⟨hq₁, by linarith⟩, hq₂, by linarith⟩
  · rintro ⟨⟨hq₁, _⟩, hq₂, hq₂'⟩
    exact ⟨hq₁, hq₂, by linarith⟩

/-- The open standard two-simplex has Lebesgue area `1 / 2`. -/
theorem volume_standardInterior :
    volume standardInterior = (2 : ENNReal)⁻¹ := by
  rw [standardInterior_eq_regionBetween, Measure.volume_eq_prod,
    volume_regionBetween_eq_lintegral'
      (μ := volume) (f := fun _ : ℝ => 0)
      (g := fun x : ℝ => 1 - x) (s := Set.Ioo 0 1)
      measurable_const (measurable_const.sub measurable_id)
      measurableSet_Ioo]
  have hintegrable :
      IntegrableOn (fun x : ℝ => 1 - x) (Set.Ioo 0 1) :=
    ((continuous_const.sub continuous_id).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => 1 - x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact sub_nonneg.mpr hx.2.le
  simp only [Pi.sub_apply, sub_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnonneg,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hintegral :
      (∫ x : ℝ in 0..1, 1 - x) = (2 : ℝ)⁻¹ := by
    rw [intervalIntegral.integral_sub
      intervalIntegral.intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const,
      integral_id]
    norm_num
  rw [hintegral, ENNReal.ofReal_inv_of_pos
    (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The linear part of the barycentric parametrization of a triangle. -/
def triangleLinearMap (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun q :=
    q.1 • (t.points 1 - t.points 0) +
      q.2 • (t.points 2 - t.points 0)
  map_add' q r := by
    dsimp
    module
  map_smul' c q := by
    dsimp
    module

/-- The two edge vectors based at vertex `0` are linearly independent. -/
theorem edgeVectors_linearIndependent
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    LinearIndependent ℝ
      ![t.points 1 - t.points 0,
        t.points 2 - t.points 0] := by
  have h :=
    (affineIndependent_iff_linearIndependent_vsub ℝ
      t.points 0).mp t.independent
  have hcomp :=
    h.comp
      (fun i : Fin 2 =>
        (⟨i.succ, Fin.succ_ne_zero i⟩ :
          {j : Fin 3 // j ≠ 0}))
      (by
        intro i j hij
        exact Fin.succ_injective 2 (congrArg Subtype.val hij))
  have hv :
      ((fun i : {j : Fin 3 // j ≠ 0} =>
          t.points i - t.points 0) ∘
        (fun i : Fin 2 =>
          (⟨i.succ, Fin.succ_ne_zero i⟩ :
            {j : Fin 3 // j ≠ 0}))) =
        ![t.points 1 - t.points 0,
          t.points 2 - t.points 0] := by
    funext i
    fin_cases i <;> rfl
  simp only [vsub_eq_sub] at hcomp
  rw [hv] at hcomp
  exact hcomp

/-- Nondegeneracy of the triangle makes its barycentric linear
parametrization injective. -/
theorem triangleLinearMap_injective
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Function.Injective (triangleLinearMap t) := by
  intro q r hqr
  have hsum :
      ∑ i : Fin 2,
          ![q.1, q.2] i •
            ![t.points 1 - t.points 0,
              t.points 2 - t.points 0] i =
        ∑ i : Fin 2,
          ![r.1, r.2] i •
            ![t.points 1 - t.points 0,
              t.points 2 - t.points 0] i := by
    simpa [triangleLinearMap, Fin.sum_univ_succ] using hqr
  apply Prod.ext
  · exact
      (edgeVectors_linearIndependent t).eq_coords_of_eq
        hsum 0
  · exact
      (edgeVectors_linearIndependent t).eq_coords_of_eq
        hsum 1

/-- The barycentric linear parametrization as an equivalence of the plane. -/
noncomputable def triangleLinearEquiv
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.ofInjectiveEndo
    (triangleLinearMap t)
    (triangleLinearMap_injective t)

@[simp]
theorem triangleLinearEquiv_apply
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (q : ℝ × ℝ) :
    triangleLinearEquiv t q = triangleLinearMap t q :=
  rfl

/-- The edge vectors, in order, as a real basis of the plane. -/
noncomputable def edgeBasis
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Module.Basis (Fin 2) ℝ (ℝ × ℝ) :=
  (Module.Basis.finTwoProd ℝ).map
    (triangleLinearEquiv t)

@[simp]
theorem edgeBasis_zero
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    edgeBasis t 0 = t.points 1 - t.points 0 := by
  simp [edgeBasis, triangleLinearEquiv, triangleLinearMap]

@[simp]
theorem edgeBasis_one
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    edgeBasis t 1 = t.points 2 - t.points 0 := by
  simp [edgeBasis, triangleLinearEquiv, triangleLinearMap]

/-- Coordinates in the edge basis are exactly the input coordinates of the
barycentric linear parametrization. -/
@[simp]
theorem edgeBasis_repr_triangleLinearMap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (q : ℝ × ℝ)
    (i : Fin 2) :
    (edgeBasis t).repr (triangleLinearMap t q) i =
      ![q.1, q.2] i := by
  have hinv :
      (triangleLinearEquiv t).symm
          (triangleLinearMap t q) = q := by
    rw [← triangleLinearEquiv_apply]
    exact (triangleLinearEquiv t).symm_apply_apply q
  change
    (Module.Basis.finTwoProd ℝ).repr
        ((triangleLinearEquiv t).symm
          (triangleLinearMap t q)) i =
      ![q.1, q.2] i
  rw [hinv]
  fin_cases i <;> rfl

/-- Coordinates with respect to the two edge vectors. -/
noncomputable def edgeCoords (t : Affine.Triangle ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) : ℝ × ℝ :=
  ((edgeBasis t).repr x 0, (edgeBasis t).repr x 1)

/-- Reconstructing a vector from its two edge coordinates. -/
@[simp]
theorem triangleLinearMap_edgeCoords
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    triangleLinearMap t (edgeCoords t x) = x := by
  have hsum := (edgeBasis t).sum_repr x
  change
    ((edgeBasis t).repr x 0) •
          (t.points 1 - t.points 0) +
        ((edgeBasis t).repr x 1) •
          (t.points 2 - t.points 0) = x
  simpa only [Fin.sum_univ_two, edgeBasis_zero,
    edgeBasis_one] using hsum

/-- Reading coordinates after the edge parametrization recovers the original
pair. -/
@[simp]
theorem edgeCoords_triangleLinearMap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (q : ℝ × ℝ) :
    edgeCoords t (triangleLinearMap t q) = q := by
  apply Prod.ext <;>
    simp [edgeCoords]

/-- The affine barycentric parametrization based at vertex `0`. -/
def triangleMap (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun q := t.points 0 + triangleLinearMap t q
  linear := triangleLinearMap t
  map_vadd' q r := by
    dsimp [triangleLinearMap]
    module

/-- Barycentric weights associated to Cartesian standard-simplex
coordinates. -/
def triangleWeights (q : ℝ × ℝ) : Fin 3 → ℝ :=
  ![1 - q.1 - q.2, q.1, q.2]

@[simp]
theorem triangleWeights_zero (q : ℝ × ℝ) :
    triangleWeights q 0 = 1 - q.1 - q.2 :=
  rfl

@[simp]
theorem triangleWeights_one (q : ℝ × ℝ) :
    triangleWeights q 1 = q.1 :=
  rfl

@[simp]
theorem triangleWeights_two (q : ℝ × ℝ) :
    triangleWeights q 2 = q.2 :=
  rfl

theorem sum_triangleWeights (q : ℝ × ℝ) :
    ∑ i, triangleWeights q i = 1 := by
  simp [Fin.sum_univ_succ]

/-- The explicit affine map agrees with the corresponding barycentric affine
combination. -/
theorem affineCombination_triangleWeights
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (q : ℝ × ℝ) :
    Finset.univ.affineCombination ℝ t.points
        (triangleWeights q) =
      triangleMap t q := by
  rw [Finset.univ.affineCombination_eq_linear_combination
    t.points (triangleWeights q) (sum_triangleWeights q)]
  simp [triangleWeights, triangleMap, triangleLinearMap,
    Fin.sum_univ_succ]
  module

/-- The explicit barycentric map sends the open standard simplex exactly
onto the intrinsic interior of the given affine triangle. -/
theorem image_triangleMap_standardInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    triangleMap t '' standardInterior = t.interior := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [← affineCombination_triangleWeights]
    rw [t.affineCombination_mem_interior_iff
      (sum_triangleWeights q)]
    intro i
    fin_cases i
    · change
        0 < 1 - q.1 - q.2 ∧
          1 - q.1 - q.2 < 1
      constructor <;> linarith [hq.1, hq.2.1, hq.2.2]
    · change 0 < q.1 ∧ q.1 < 1
      constructor <;> linarith [hq.1, hq.2.1, hq.2.2]
    · change 0 < q.2 ∧ q.2 < 1
      constructor <;> linarith [hq.1, hq.2.1, hq.2.2]
  · rintro ⟨w, hsum, hw, rfl⟩
    let q : ℝ × ℝ := (w 1, w 2)
    have hsum' : w 0 + w 1 + w 2 = 1 := by
      rw [add_assoc]
      simpa [Fin.sum_univ_succ] using hsum
    have hq : q ∈ standardInterior := by
      refine ⟨(hw 1).1, (hw 2).1, ?_⟩
      linarith [(hw 0).1]
    refine ⟨q, hq, ?_⟩
    rw [← affineCombination_triangleWeights]
    apply Finset.affineCombination_congr
    · intro i _
      fin_cases i
      · simp [triangleWeights, q]
        linarith
      · simp [triangleWeights, q]
      · simp [triangleWeights, q]
    · intro i _
      rfl

/-- Intrinsic triangle interior expressed in edge coordinates based at
vertex `0`. -/
theorem mem_interior_iff_edgeCoords
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    x ∈ t.interior ↔
      edgeCoords t (x - t.points 0) ∈ standardInterior := by
  rw [← image_triangleMap_standardInterior]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [triangleMap] using hq
  · intro hx
    refine
      ⟨edgeCoords t (x - t.points 0), hx, ?_⟩
    simp [triangleMap]

/-- The closed standard two-simplex. -/
def standardClosedInterior : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ 1}

/-- The boundary of the closed standard two-simplex. -/
def standardBoundary : Set (ℝ × ℝ) :=
  {q |
    q ∈ standardClosedInterior ∧
      (q.1 = 0 ∨ q.2 = 0 ∨ q.1 + q.2 = 1)}

/-- Closed triangle interior expressed in edge coordinates. -/
theorem mem_closedInterior_iff_edgeCoords
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    x ∈ t.closedInterior ↔
      edgeCoords t (x - t.points 0) ∈
        standardClosedInterior := by
  let q := edgeCoords t (x - t.points 0)
  let w : Fin 3 → ℝ := triangleWeights q
  have hsum := sum_triangleWeights q
  have hxcomb :
      Finset.univ.affineCombination ℝ t.points w = x := by
    rw [affineCombination_triangleWeights]
    simp [triangleMap, q]
  have hxmem :
      x ∈ t.closedInterior ↔
        ∀ i, w i ∈ Set.Icc 0 1 := by
    rw [← hxcomb,
      t.affineCombination_mem_closedInterior_iff hsum]
  rw [hxmem]
  change
    (∀ i, w i ∈ Set.Icc 0 1) ↔
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ 1
  constructor
  · intro hw
    exact
      ⟨(hw 1).1, (hw 2).1,
        by
          have := (hw 0).1
          simp [w, triangleWeights] at this
          linarith⟩
  · rintro ⟨hq₁, hq₂, hsumq⟩ i
    fin_cases i
    · change
        0 ≤ 1 - q.1 - q.2 ∧
          1 - q.1 - q.2 ≤ 1
      constructor <;> linarith
    · change 0 ≤ q.1 ∧ q.1 ≤ 1
      constructor <;> linarith
    · change 0 ≤ q.2 ∧ q.2 ≤ 1
      constructor <;> linarith

/-- The polygonal boundary of a triangle expressed in edge coordinates. -/
theorem mem_toPolygon_boundary_iff_edgeCoords
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    x ∈ t.toPolygon.boundary (R := ℝ) ↔
      edgeCoords t (x - t.points 0) ∈
        standardBoundary := by
  rw [Submission.Triangle.toPolygon_boundary_eq_surface]
  change
    (x ∈ t.closedInterior ∧ x ∉ t.interior) ↔ _
  rw [mem_closedInterior_iff_edgeCoords,
    mem_interior_iff_edgeCoords]
  let q := edgeCoords t (x - t.points 0)
  change
    (q ∈ standardClosedInterior ∧
      q ∉ standardInterior) ↔
      q ∈ standardBoundary
  simp only [standardClosedInterior, standardInterior,
    standardBoundary, Set.mem_setOf_eq, not_and_or,
    not_lt]
  constructor
  · rintro ⟨hq, hqnot⟩
    refine ⟨hq, ?_⟩
    rcases hqnot with hq₁ | hq₂ | hsum
    · exact Or.inl (le_antisymm hq₁ hq.1)
    · exact Or.inr (Or.inl (le_antisymm hq₂ hq.2.1))
    · exact
        Or.inr (Or.inr
          (le_antisymm hq.2.2 hsum))
  · rintro ⟨hq, hqeq⟩
    refine ⟨hq, ?_⟩
    rcases hqeq with hq₁ | hq₂ | hsum
    · exact Or.inl hq₁.le
    · exact Or.inr (Or.inl hq₂.le)
    · exact Or.inr (Or.inr hsum.ge)

/-- Translation by the base vertex does not change the measure of a linear
image. -/
theorem volume_image_triangleMap
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (s : Set (ℝ × ℝ)) :
    volume (triangleMap t '' s) =
      volume (triangleLinearMap t '' s) := by
  have himage :
      triangleMap t '' s =
        (fun x => -t.points 0 + x) ⁻¹'
          (triangleLinearMap t '' s) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, hq, ?_⟩
      simp [triangleMap]
    · rintro ⟨q, hq, hqeq⟩
      refine ⟨q, hq, ?_⟩
      apply_fun (fun y => t.points 0 + y) at hqeq
      simpa [triangleMap] using hqeq
  rw [himage, measure_preimage_add]

/-- Lebesgue area of an affine triangle in terms of the determinant of its
two edge vectors. -/
theorem volume_interior_eq_det
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    volume t.interior =
      ENNReal.ofReal |LinearMap.det (triangleLinearMap t)| / 2 := by
  rw [← image_triangleMap_standardInterior,
    volume_image_triangleMap,
    Measure.addHaar_image_linearMap,
    volume_standardInterior]
  rw [div_eq_mul_inv]

/-- Real-valued version of the determinant area formula. -/
theorem volume_interior_toReal_eq_det
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (volume t.interior).toReal =
      |LinearMap.det (triangleLinearMap t)| / 2 := by
  rw [volume_interior_eq_det]
  simp

/-- The benchmark area of the boundary of an affine triangle is half the
absolute determinant of its two edge vectors. -/
theorem area_toPolygon_boundary_eq_det
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    area (t.toPolygon.boundary (R := ℝ)) =
      |LinearMap.det (triangleLinearMap t)| / 2 := by
  rw [Submission.Triangle.area_toPolygon_boundary_eq_volume_interior,
    volume_interior_toReal_eq_det]

end Submission.TriangleArea
