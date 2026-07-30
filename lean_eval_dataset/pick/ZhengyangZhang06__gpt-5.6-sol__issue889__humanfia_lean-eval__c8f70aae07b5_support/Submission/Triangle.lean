import Mathlib
import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.Triangle

/-- Exhaust the three possible indices of a triangle without leaving dependent
casts in subsequent goals. -/
theorem fin_three_eq_zero_or_one_or_two (i : Fin 3) :
    i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-- Cyclic rotation has no fixed point on the three vertex indices of a
triangle. -/
theorem finRotate_three_ne_self (i : Fin 3) :
    finRotate 3 i ≠ i := by
  fin_cases i <;> decide

/-- Two adjacent sides cut out of an affinely independent family meet only
at their shared endpoint.  Expressing each side inside its affine span makes
this a direct application of independence to the two index pairs. -/
theorem affineSegment_inter_adjacent_of_affineIndependent
    {ι : Type*} {p : ι → ℝ × ℝ}
    (h : AffineIndependent ℝ p)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    affineSegment ℝ (p i) (p j) ∩
        affineSegment ℝ (p j) (p k) =
      {p j} := by
  have image_pair (a b : ι) :
      p '' ({a, b} : Set ι) =
        ({p a, p b} : Set (ℝ × ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨a, Or.inl rfl, rfl⟩
      · exact ⟨b, Or.inr rfl, rfl⟩
  ext x
  constructor
  · rintro ⟨hxij, hxjk⟩
    have hxij' :
        x ∈ affineSpan ℝ
          (p '' ({i, j} : Set ι)) := by
      have hxline :=
        affineSegment_subset_affineSpan ℝ (p i) (p j) hxij
      rw [image_pair]
      exact hxline
    have hxjk' :
        x ∈ affineSpan ℝ
          (p '' ({j, k} : Set ι)) := by
      have hxline :=
        affineSegment_subset_affineSpan ℝ (p j) (p k) hxjk
      rw [image_pair]
      exact hxline
    have hxboth :
        x ∈
          affineSpan ℝ (p '' ({i, j} : Set ι)) ⊓
            affineSpan ℝ (p '' ({j, k} : Set ι)) :=
      ⟨hxij', hxjk'⟩
    rw [h.inf_affineSpan_eq_affineSpan_inter] at hxboth
    have hinter :
        ({i, j} : Set ι) ∩ {j, k} = {j} := by
      ext l
      simp only [Set.mem_inter_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      aesop
    rw [hinter] at hxboth
    simpa using hxboth
  · rintro rfl
    exact
      ⟨right_mem_affineSegment ℝ _ _,
        left_mem_affineSegment ℝ _ _⟩

/-- Conversely to `affineIndependent_of_isSimple`, three affinely
independent planar vertices form a simple polygon. -/
theorem isSimple_of_affineIndependent
    (poly : Polygon (ℝ × ℝ) 3)
    (h : AffineIndependent ℝ poly.vertices) :
    IsSimple poly := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact h.injective.ne (finRotate_three_ne_self i).symm
  · intro i j hij hnotAdjacent
    fin_cases i <;> fin_cases j <;>
      simp [Adjacent] at hij hnotAdjacent
  · intro i
    fin_cases i
    · change
        affineSegment ℝ (poly 0) (poly 1) ∩
            affineSegment ℝ (poly 1) (poly 2) =
          {poly 1}
      exact
        affineSegment_inter_adjacent_of_affineIndependent
          h 0 1 2 (by decide) (by decide) (by decide)
    · change
        affineSegment ℝ (poly 1) (poly 2) ∩
            affineSegment ℝ (poly 2) (poly 0) =
          {poly 2}
      exact
        affineSegment_inter_adjacent_of_affineIndependent
          h 1 2 0 (by decide) (by decide) (by decide)
    · change
        affineSegment ℝ (poly 2) (poly 0) ∩
            affineSegment ℝ (poly 0) (poly 1) =
          {poly 0}
      exact
        affineSegment_inter_adjacent_of_affineIndependent
          h 2 0 1 (by decide) (by decide) (by decide)

/-- A simple three-vertex polygon cannot be collinear: whichever vertex lay
between the other two would make two adjacent edges overlap beyond their
prescribed common endpoint. -/
theorem affineIndependent_of_isSimple
    (poly : Polygon (ℝ × ℝ) 3) (hsimple : IsSimple poly) :
    AffineIndependent ℝ poly.vertices := by
  rw [affineIndependent_iff_not_collinear]
  intro hcollinear
  have hrange :
      Set.range poly.vertices =
        {poly 0, poly 1, poly 2} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases fin_three_eq_zero_or_one_or_two i with rfl | rfl | rfl <;>
        simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [hrange] at hcollinear
  rcases hcollinear.wbtw_or_wbtw_or_wbtw with hbetween | hbetween | hbetween
  · have hmem :
        poly 1 ∈
          poly.edgeSet ℝ 2 ∩ poly.edgeSet ℝ 0 := by
      constructor
      · change
          poly 1 ∈ affineSegment ℝ (poly 2) (poly 0)
        exact hbetween.symm
      · exact right_mem_affineSegment ℝ _ _
    have hsingleton :
        poly.edgeSet ℝ 2 ∩ poly.edgeSet ℝ 0 =
          {poly 0} := by
      simpa using hsimple.2.2 2
    rw [hsingleton] at hmem
    have heq : poly 1 = poly 0 := by
      simpa using hmem
    exact
      (by decide : (1 : Fin 3) ≠ 0)
        (Submission.Helpers.vertex_injective_of_isSimple
          hsimple heq)
  · have hmem :
        poly 2 ∈
          poly.edgeSet ℝ 0 ∩ poly.edgeSet ℝ 1 := by
      constructor
      · change
          poly 2 ∈ affineSegment ℝ (poly 0) (poly 1)
        exact hbetween.symm
      · exact right_mem_affineSegment ℝ _ _
    have hsingleton :
        poly.edgeSet ℝ 0 ∩ poly.edgeSet ℝ 1 =
          {poly 1} := by
      simpa using hsimple.2.2 0
    rw [hsingleton] at hmem
    have heq : poly 2 = poly 1 := by
      simpa using hmem
    exact
      (by decide : (2 : Fin 3) ≠ 1)
        (Submission.Helpers.vertex_injective_of_isSimple
          hsimple heq)
  · have hmem :
        poly 0 ∈
          poly.edgeSet ℝ 1 ∩ poly.edgeSet ℝ 2 := by
      constructor
      · change
          poly 0 ∈ affineSegment ℝ (poly 1) (poly 2)
        exact hbetween.symm
      · exact right_mem_affineSegment ℝ _ _
    have hsingleton :
        poly.edgeSet ℝ 1 ∩ poly.edgeSet ℝ 2 =
          {poly 2} := by
      simpa using hsimple.2.2 1
    rw [hsingleton] at hmem
    have heq : poly 0 = poly 2 := by
      simpa using hmem
    exact
      (by decide : (0 : Fin 3) ≠ 2)
        (Submission.Helpers.vertex_injective_of_isSimple
          hsimple heq)

/-- A simple three-vertex polygon satisfies Mathlib's nondegenerate-vertices
condition and therefore canonically determines an affine triangle. -/
theorem hasNondegenerateVertices_of_isSimple
    (poly : Polygon (ℝ × ℝ) 3) (hsimple : IsSimple poly) :
    poly.HasNondegenerateVertices ℝ := by
  have h := affineIndependent_of_isSimple poly hsimple
  have hv :
      poly.vertices =
        ![poly.vertices 0, poly.vertices 1, poly.vertices 2] :=
    List.ofFn_inj.mp rfl
  have hbase :
      AffineIndependent ℝ
        ![poly.vertices 0, poly.vertices 1, poly.vertices 2] := by
    simpa [← hv] using h
  intro i
  fin_cases i <;> dsimp
  exacts
    [hbase, hbase.comm_left.comm_right,
      hbase.comm_right.comm_left]

/-- The three points of an affine triangle form an affine basis of the real
plane. -/
def affineBasis (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    AffineBasis (Fin 3) ℝ (ℝ × ℝ) where
  toFun := t.points
  ind' := t.independent
  tot' := t.span_eq_top (by simp)

@[simp]
theorem affineBasis_apply (t : Affine.Triangle ℝ (ℝ × ℝ))
    (i : Fin 3) :
    affineBasis t i = t.points i :=
  rfl

/-- Membership in the intrinsic interior of a planar affine triangle is
equivalent to positivity of all three barycentric coordinates. -/
theorem mem_interior_iff_coord_pos
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    x ∈ t.interior ↔
      ∀ i : Fin 3, 0 < (affineBasis t).coord i x := by
  let b := affineBasis t
  constructor
  · rintro ⟨w, hw, hwIoo, hx⟩ i
    have hcoord :
        b.coord i
            (Finset.univ.affineCombination ℝ t.points w) =
          w i := by
      change
        b.coord i
            (Finset.univ.affineCombination ℝ b w) =
          w i
      exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
    rw [← hx, hcoord]
    exact (hwIoo i).1
  · intro hcoord
    let w : Fin 3 → ℝ := fun i => b.coord i x
    refine ⟨w, b.sum_coord_apply_eq_one x, ?_, ?_⟩
    · intro i
      refine ⟨hcoord i, ?_⟩
      have hlt :
          b.coord i x < ∑ k : Fin 3, b.coord k x :=
        Finset.single_lt_sum
          (finRotate_three_ne_self i)
          (Finset.mem_univ i)
          (Finset.mem_univ (finRotate 3 i))
          (hcoord (finRotate 3 i))
          (fun k _ _ => (hcoord k).le)
      simpa using hlt
    · change
        Finset.univ.affineCombination ℝ b
            (fun i => b.coord i x) =
          x
      exact b.affineCombination_coord_eq_self x

/-- The intrinsic interior of a planar affine triangle is the intersection
of the three open positive barycentric half-spaces. -/
theorem interior_eq_iInter_coord_Ioi
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    t.interior =
      ⋂ i : Fin 3, (affineBasis t).coord i ⁻¹' Set.Ioi 0 := by
  ext x
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
  exact mem_interior_iff_coord_pos t x

/-- The intrinsic interior of a planar affine triangle is open in the
ambient plane. -/
theorem isOpen_interior (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    IsOpen t.interior := by
  rw [interior_eq_iInter_coord_Ioi]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioi.preimage
      ((affineBasis t).coord i).continuous_of_finiteDimensional

/-- The intrinsic interior of a planar affine triangle is convex. -/
theorem convex_interior (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Convex ℝ t.interior := by
  rw [interior_eq_iInter_coord_Ioi]
  exact convex_iInter fun i =>
    Convex.affine_preimage
      ((affineBasis t).coord i) (convex_Ioi 0)

/-- The closed interior of an affine triangle is convex. -/
theorem convex_closedInterior (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    Convex ℝ t.closedInterior := by
  rw [← t.convexHull_eq_closedInterior]
  exact convex_convexHull ℝ (Set.range t.points)

/-- The face opposite vertex `0` of an affine triangle is its edge from
vertex `1` to vertex `2`. -/
theorem closedInterior_faceOpposite_zero
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (t.faceOpposite 0).closedInterior =
      affineSegment ℝ (t.points 1) (t.points 2) := by
  rw [Affine.Simplex.closedInterior_eq_affineSegment]
  congr 1 <;>
    simp [Affine.Simplex.faceOpposite_point_eq_point_succAbove]

/-- The face opposite vertex `1` of an affine triangle is its edge from
vertex `0` to vertex `2`. -/
theorem closedInterior_faceOpposite_one
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (t.faceOpposite 1).closedInterior =
      affineSegment ℝ (t.points 0) (t.points 2) := by
  rw [Affine.Simplex.closedInterior_eq_affineSegment]
  congr 1 <;>
    simp [Affine.Simplex.faceOpposite_point_eq_point_succAbove]

/-- The face opposite vertex `2` of an affine triangle is its edge from
vertex `0` to vertex `1`. -/
theorem closedInterior_faceOpposite_two
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (t.faceOpposite 2).closedInterior =
      affineSegment ℝ (t.points 0) (t.points 1) := by
  rw [Affine.Simplex.closedInterior_eq_affineSegment]
  congr 1
  · simp [Affine.Simplex.faceOpposite_point_eq_point_succAbove]
  · rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove]
    apply congrArg t.points
    decide

/-- The polygonal boundary of an affine triangle is exactly the surface of
the simplex. -/
theorem toPolygon_boundary_eq_surface
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    t.toPolygon.boundary (R := ℝ) =
      t.closedInterior \ t.interior := by
  rw [Polygon.boundary,
    Affine.Simplex.closedInterior_sdiff_interior (n := 2) t]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    have hi_cases := fin_three_eq_zero_or_one_or_two i
    rcases hi_cases with rfl | rfl | rfl
    · exact ⟨2, by
        rw [closedInterior_faceOpposite_two]
        simpa [Polygon.edgeSet] using hi⟩
    · exact ⟨0, by
        rw [closedInterior_faceOpposite_zero]
        simpa [Polygon.edgeSet] using hi⟩
    · exact ⟨1, by
        rw [closedInterior_faceOpposite_one]
        simpa [Polygon.edgeSet, affineSegment_comm] using hi⟩
  · rintro ⟨i, hi⟩
    have hi_cases := fin_three_eq_zero_or_one_or_two i
    rcases hi_cases with rfl | rfl | rfl
    · exact ⟨1, by
        rw [closedInterior_faceOpposite_zero] at hi
        simpa [Polygon.edgeSet] using hi⟩
    · exact ⟨2, by
        rw [closedInterior_faceOpposite_one] at hi
        simpa [Polygon.edgeSet, affineSegment_comm] using hi⟩
    · exact ⟨0, by
        rw [closedInterior_faceOpposite_two] at hi
        simpa [Polygon.edgeSet] using hi⟩

/-- The complement of a triangle's surface splits into its open interior and
the complement of its closed interior. -/
theorem compl_surface_eq
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    (t.closedInterior \ t.interior)ᶜ =
      t.interior ∪ t.closedInteriorᶜ := by
  ext x
  constructor
  · intro hx
    by_cases hxI : x ∈ t.interior
    · exact Or.inl hxI
    · exact Or.inr fun hxC =>
        hx ⟨hxC, hxI⟩
  · rintro (hxI | hxC) hx
    · exact hx.2 hxI
    · exact hxC hx.1

/-- The connected component of a point in a triangle's open interior,
relative to the complement of the surface, is exactly that interior. -/
theorem connectedComponentIn_compl_surface_eq_interior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) {x : ℝ × ℝ}
    (hx : x ∈ t.interior) :
    connectedComponentIn
        (t.closedInterior \ t.interior)ᶜ x =
      t.interior := by
  have hx_compl :
      x ∈ (t.closedInterior \ t.interior)ᶜ := by
    rw [compl_surface_eq]
    exact Or.inl hx
  apply Set.Subset.antisymm
  · apply
      isPreconnected_connectedComponentIn.subset_left_of_subset_union
        (isOpen_interior t)
        t.isClosed_closedInterior.isOpen_compl
        (Set.disjoint_left.mpr fun _ hyI hyC =>
          hyC (t.interior_subset_closedInterior hyI))
    · rw [← compl_surface_eq]
      exact connectedComponentIn_subset _ _
    · exact
        ⟨x, mem_connectedComponentIn hx_compl, hx⟩
  · exact
      (convex_interior t).isPreconnected.subset_connectedComponentIn
        hx (by
          intro y hy
          rw [compl_surface_eq]
          exact Or.inl hy)

/-- Consequently, the surface-complement component containing an interior
point is bounded. -/
theorem isBounded_connectedComponentIn_compl_surface_of_mem_interior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) {x : ℝ × ℝ}
    (hx : x ∈ t.interior) :
    Bornology.IsBounded
      (connectedComponentIn
        (t.closedInterior \ t.interior)ᶜ x) := by
  rw [connectedComponentIn_compl_surface_eq_interior t hx]
  exact t.isCompact_closedInterior.isBounded.subset
    t.interior_subset_closedInterior

/-- The ray starting at an affine triangle's vertex `0`, passing through
`x`, and continuing outwards. -/
def outwardRay (t : Affine.Triangle ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun r : ℝ =>
    t.points 0 + r • (x - t.points 0)) '' Set.Ici 1

/-- The point defining an outward ray lies on that ray. -/
theorem self_mem_outwardRay
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    x ∈ outwardRay t x := by
  refine ⟨1, Set.mem_Ici.mpr le_rfl, ?_⟩
  simp

/-- If `x` is outside a closed triangle, its outward ray remains outside:
otherwise convexity between vertex `0` and a later ray point would put `x`
back in the triangle. -/
theorem outwardRay_subset_compl_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) {x : ℝ × ℝ}
    (hx : x ∉ t.closedInterior) :
    outwardRay t x ⊆ t.closedInteriorᶜ := by
  rintro _ ⟨r, hr, rfl⟩
  intro hyr
  have hr_pos : 0 < r := zero_lt_one.trans_le hr
  have hcombo :=
    (convex_closedInterior t).add_smul_mem
      (t.point_mem_closedInterior 0) hyr
      ⟨inv_nonneg.mpr hr_pos.le,
        inv_le_one_of_one_le₀ hr⟩
  apply hx
  simpa [smul_smul, hr_pos.ne'] using hcombo

/-- An outward ray is preconnected. -/
theorem isPreconnected_outwardRay
    (t : Affine.Triangle ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    IsPreconnected (outwardRay t x) := by
  exact
    isPreconnected_Ici.image
      (fun r : ℝ =>
        t.points 0 + r • (x - t.points 0))
      ((continuous_const.add
        (continuous_id.smul continuous_const)).continuousOn)

/-- An outward ray from a point outside the closed triangle is unbounded. -/
theorem not_isBounded_outwardRay
    (t : Affine.Triangle ℝ (ℝ × ℝ)) {x : ℝ × ℝ}
    (hx : x ∉ t.closedInterior) :
    ¬ Bornology.IsBounded (outwardRay t x) := by
  intro hbounded
  rw [outwardRay] at hbounded
  obtain ⟨C, hC⟩ := Metric.isBounded_image_iff.mp hbounded
  have hxc : x ≠ t.points 0 := by
    intro h
    apply hx
    rw [h]
    exact t.point_mem_closedInterior 0
  have hd_pos : 0 < ‖x - t.points 0‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
  let r : ℝ :=
    1 + (|C| + 1) / ‖x - t.points 0‖
  have hr : 1 ≤ r := by
    have hquot :
        0 < (|C| + 1) / ‖x - t.points 0‖ :=
      div_pos (by positivity) hd_pos
    dsimp [r]
    linarith
  have hbound :=
    hC 1 (Set.mem_Ici.mpr le_rfl)
      r (Set.mem_Ici.mpr hr)
  have hdist :
      dist
          (t.points 0 +
            (1 : ℝ) • (x - t.points 0))
          (t.points 0 +
            r • (x - t.points 0)) =
        (r - 1) * ‖x - t.points 0‖ := by
    calc
      _ = ‖((1 : ℝ) - r) •
          (x - t.points 0)‖ := by
            rw [dist_eq_norm]
            congr 1
            module
      _ = |(1 : ℝ) - r| *
          ‖x - t.points 0‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (r - 1) * ‖x - t.points 0‖ := by
            rw [abs_of_nonpos (sub_nonpos.mpr hr)]
            ring
  rw [hdist] at hbound
  have hr_eval :
      (r - 1) * ‖x - t.points 0‖ = |C| + 1 := by
    dsimp [r]
    rw [add_sub_cancel_left,
      div_mul_cancel₀ _ hd_pos.ne']
  rw [hr_eval] at hbound
  have hC_le_abs : C ≤ |C| := le_abs_self C
  linarith

/-- Every point outside the closed triangle belongs to an unbounded component
of the surface complement. -/
theorem not_isBounded_connectedComponentIn_compl_surface_of_not_mem_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) {x : ℝ × ℝ}
    (hx : x ∉ t.closedInterior) :
    ¬ Bornology.IsBounded
      (connectedComponentIn
        (t.closedInterior \ t.interior)ᶜ x) := by
  have hray_compl :
      outwardRay t x ⊆
        (t.closedInterior \ t.interior)ᶜ := by
    intro y hy hysurface
    exact
      (outwardRay_subset_compl_closedInterior t hx hy)
        hysurface.1
  have hray_component :
      outwardRay t x ⊆
        connectedComponentIn
          (t.closedInterior \ t.interior)ᶜ x :=
    (isPreconnected_outwardRay t x).subset_connectedComponentIn
      (self_mem_outwardRay t x) hray_compl
  intro hcomponent
  exact not_isBounded_outwardRay t hx
    (hcomponent.subset hray_component)

/-- For an affine triangle, the trusted bounded-component definition of
`inside` is exactly the simplex interior. -/
theorem inside_toPolygon_boundary_eq_interior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    inside (t.toPolygon.boundary (R := ℝ)) =
      t.interior := by
  rw [toPolygon_boundary_eq_surface]
  ext x
  change
    (x ∉ t.closedInterior \ t.interior ∧
      Bornology.IsBounded
        (connectedComponentIn
          (t.closedInterior \ t.interior)ᶜ x)) ↔
      x ∈ t.interior
  constructor
  · rintro ⟨hxsurface, hxbounded⟩
    have hx_compl :
        x ∈ (t.closedInterior \ t.interior)ᶜ :=
      hxsurface
    rw [compl_surface_eq] at hx_compl
    rcases hx_compl with hxI | hxC
    · exact hxI
    · exact False.elim
        (not_isBounded_connectedComponentIn_compl_surface_of_not_mem_closedInterior
          t hxC hxbounded)
  · intro hxI
    exact
      ⟨(fun hxsurface => hxsurface.2 hxI),
        isBounded_connectedComponentIn_compl_surface_of_mem_interior
          t hxI⟩

/-- For a triangle, the challenge's `area` is the Lebesgue volume of the
usual affine-simplex interior. -/
theorem area_toPolygon_boundary_eq_volume_interior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    area (t.toPolygon.boundary (R := ℝ)) =
      (volume t.interior).toReal := by
  unfold area
  rw [inside_toPolygon_boundary_eq_interior]

end Submission.Triangle
