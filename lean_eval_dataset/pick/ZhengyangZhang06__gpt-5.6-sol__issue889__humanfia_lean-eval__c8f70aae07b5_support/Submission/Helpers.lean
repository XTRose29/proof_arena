import Mathlib
import ChallengeDeps

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.Helpers

/-- The coordinatewise embedding of the integer lattice into the real plane is
a closed topological embedding. -/
theorem isClosedEmbedding_toPlane : Topology.IsClosedEmbedding toPlane := by
  have hmap :
      toPlane =
        Prod.map ((↑) : ℤ → ℝ) ((↑) : ℤ → ℝ) := by
    funext z
    rcases z with ⟨x, y⟩
    rfl
  rw [hmap]
  exact Int.isClosedEmbedding_coe_real.prodMap
    Int.isClosedEmbedding_coe_real

/-- A bounded planar set contains only finitely many lattice points. -/
theorem finite_latticePoints_of_isBounded {s : Set (ℝ × ℝ)}
    (hs : Bornology.IsBounded s) :
    Set.Finite {z : ℤ × ℤ | toPlane z ∈ s} := by
  have hrange : Set.Finite (s ∩ Set.range toPlane) :=
    Metric.finite_isBounded_inter_isClosed
      (IsInducing.isDiscrete_range isClosedEmbedding_toPlane.isInducing) hs
      isClosedEmbedding_toPlane.isClosed_range
  have hpreimage :
      toPlane ⁻¹' s = toPlane ⁻¹' (s ∩ Set.range toPlane) := by
    ext z
    simp
  rw [show {z : ℤ × ℤ | toPlane z ∈ s} = toPlane ⁻¹' s by rfl, hpreimage]
  exact hrange.preimage isClosedEmbedding_toPlane.injective.injOn

/-- Every edge of a real planar polygon is compact. -/
theorem isCompact_edgeSet {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (i : Fin n) :
    IsCompact (poly.edgeSet ℝ i) := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  exact isCompact_Icc.image
    (poly.edgePath ℝ i).continuous_of_finiteDimensional

/-- Every edge of a real planar polygon is bounded. -/
theorem isBounded_edgeSet {n : ℕ} (poly : Polygon (ℝ × ℝ) n)
    (i : Fin n) :
    Bornology.IsBounded (poly.edgeSet ℝ i) :=
  (isCompact_edgeSet poly i).isBounded

/-- A finite polygonal boundary is compact. -/
theorem isCompact_boundary {n : ℕ} (poly : Polygon (ℝ × ℝ) n) :
    IsCompact (poly.boundary (R := ℝ)) := by
  rw [Polygon.boundary]
  exact isCompact_iUnion fun i => isCompact_edgeSet poly i

/-- A finite polygonal boundary is bounded. -/
theorem isBounded_boundary {n : ℕ} (poly : Polygon (ℝ × ℝ) n) :
    Bornology.IsBounded (poly.boundary (R := ℝ)) :=
  (isCompact_boundary poly).isBounded

/-- In particular, the lattice points on a polygonal boundary form a finite
set. -/
theorem finite_boundary_latticePoints {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    Set.Finite
      {z : ℤ × ℤ |
        toPlane z ∈ (latPoly v).boundary (R := ℝ)} :=
  finite_latticePoints_of_isBounded (isBounded_boundary (latPoly v))

/-- A polygon satisfying the supplied simplicity predicate has pairwise
distinct vertices. -/
theorem vertex_injective_of_isSimple {n : ℕ}
    {poly : Polygon (ℝ × ℝ) n} (hsimple : IsSimple poly) :
    Function.Injective poly := by
  intro i j hv
  by_contra hij
  rcases hsimple with
    ⟨hnondegenerate, hdisjoint, _⟩
  by_cases hadjacent : Adjacent i j
  · rcases hadjacent with hforward | hbackward
    · exact hnondegenerate i (by simpa [hforward] using hv)
    · exact hnondegenerate j (by simpa [hbackward] using hv.symm)
  · have hedges_disjoint :=
      hdisjoint i j hij hadjacent
    have hi : poly i ∈ poly.edgeSet ℝ i :=
      left_mem_affineSegment ℝ _ _
    have hj : poly i ∈ poly.edgeSet ℝ j := by
      rw [hv]
      exact left_mem_affineSegment ℝ _ _
    exact Set.disjoint_left.mp hedges_disjoint hi hj

/-- Consequently, a simple lattice polygon's original integer vertices are
pairwise distinct. -/
theorem lattice_vertex_injective_of_isSimple {n : ℕ}
    {v : Fin n → ℤ × ℤ} (hsimple : IsSimple (latPoly v)) :
    Function.Injective v := by
  intro i j hv
  apply vertex_injective_of_isSimple hsimple
  exact congrArg toPlane hv

/-- Regard a vertex of a lattice polygon as a lattice point on its
boundary. -/
def boundaryVertex {n : ℕ} (v : Fin n → ℤ × ℤ) (i : Fin n) :
    {z : ℤ × ℤ |
      toPlane z ∈ (latPoly v).boundary (R := ℝ)} :=
  ⟨v i, by
    rw [Polygon.boundary]
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact left_mem_affineSegment ℝ _ _⟩

/-- For a simple lattice polygon, the map from vertex indices to boundary
lattice points is injective. -/
theorem boundaryVertex_injective_of_isSimple {n : ℕ}
    {v : Fin n → ℤ × ℤ} (hsimple : IsSimple (latPoly v)) :
    Function.Injective (boundaryVertex v) := by
  intro i j hij
  apply lattice_vertex_injective_of_isSimple hsimple
  exact congrArg Subtype.val hij

/-- A simple lattice polygon has at least as many boundary lattice points as
listed vertices. -/
theorem vertexCount_le_boundaryPts {n : ℕ}
    {v : Fin n → ℤ × ℤ} (hsimple : IsSimple (latPoly v)) :
    n ≤ boundaryPts v := by
  letI : Fintype
      {z : ℤ × ℤ |
        toPlane z ∈ (latPoly v).boundary (R := ℝ)} :=
    (finite_boundary_latticePoints v).fintype
  simpa [boundaryPts] using
    Nat.card_le_card_of_injective
      (boundaryVertex v)
      (boundaryVertex_injective_of_isSimple hsimple)

/-- If an obstacle is bounded, then the union of the bounded connected
components of its complement is bounded as well. -/
theorem isBounded_inside_of_isBounded {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (inside S) := by
  obtain ⟨R, hR, hSR⟩ := hS.subset_ball_lt 0 0
  refine
    (Metric.isBounded_ball (x := (0 : ℝ × ℝ)) (r := R)).subset ?_
  intro x hx
  by_contra hxball
  change x ∉ S ∧
    Bornology.IsBounded (connectedComponentIn Sᶜ x) at hx
  rcases hx with ⟨hxS, hxcomponent⟩
  have hxnorm : R ≤ ‖x‖ := by
    simpa [Metric.mem_ball, dist_zero_right, not_lt] using hxball
  have hxnorm_pos : 0 < ‖x‖ := hR.trans_le hxnorm
  let ray : Set (ℝ × ℝ) :=
    (fun t : ℝ => t • x) '' Set.Ici 1
  have hxray : x ∈ ray := by
    refine ⟨1, Set.mem_Ici.mpr le_rfl, ?_⟩
    simp
  have hray_compl : ray ⊆ Sᶜ := by
    rintro y ⟨t, ht, rfl⟩
    rw [Set.mem_compl_iff]
    intro htxS
    have htxball := hSR htxS
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hnorm_mono : ‖x‖ ≤ ‖t • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      simpa using mul_le_mul_of_nonneg_right ht (norm_nonneg x)
    have hlarge : R ≤ ‖t • x‖ := hxnorm.trans hnorm_mono
    have hsmall : ‖t • x‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using htxball
    exact (not_lt_of_ge hlarge) hsmall
  have hray_preconnected : IsPreconnected ray := by
    exact
      isPreconnected_Ici.image (fun t : ℝ => t • x)
        ((continuous_id.smul continuous_const).continuousOn)
  have hray_component : ray ⊆ connectedComponentIn Sᶜ x :=
    hray_preconnected.subset_connectedComponentIn hxray hray_compl
  have hray_unbounded : ¬ Bornology.IsBounded ray := by
    intro hray
    obtain ⟨C, hC⟩ := hray.exists_norm_le
    let t : ℝ := max 1 ((C + 1) / ‖x‖)
    have ht : 1 ≤ t := le_max_left _ _
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have htmem : t • x ∈ ray :=
      ⟨t, Set.mem_Ici.mpr ht, rfl⟩
    have hupper := hC (t • x) htmem
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hupper
    have hlower :
        (C + 1) / ‖x‖ * ‖x‖ ≤ t * ‖x‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x)
    rw [div_mul_cancel₀ (C + 1) hxnorm_pos.ne'] at hlower
    linarith
  exact hray_unbounded (hxcomponent.subset hray_component)

/-- For a closed planar obstacle, `inside` is open: each of its points lies in
an open connected component of the complement, and boundedness is unchanged
throughout that component. -/
theorem isOpen_inside_of_isClosed {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) :
    IsOpen (inside S) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change x ∉ S ∧
    Bornology.IsBounded (connectedComponentIn Sᶜ x) at hx
  rcases hx with ⟨hxS, hxbounded⟩
  have hxcompl : x ∈ Sᶜ := hxS
  have hxcomponent :
      x ∈ connectedComponentIn Sᶜ x :=
    mem_connectedComponentIn hxcompl
  refine Filter.mem_of_superset
    (hS.isOpen_compl.connectedComponentIn.mem_nhds hxcomponent) ?_
  intro y hy
  change y ∉ S ∧
    Bornology.IsBounded (connectedComponentIn Sᶜ y)
  have hycompl : y ∈ Sᶜ :=
    connectedComponentIn_subset Sᶜ x hy
  refine ⟨hycompl, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hxbounded

/-- The region selected by `inside` for a polygonal boundary is open. -/
theorem isOpen_polygon_inside {n : ℕ}
    (poly : Polygon (ℝ × ℝ) n) :
    IsOpen (inside (poly.boundary (R := ℝ))) :=
  isOpen_inside_of_isClosed (isCompact_boundary poly).isClosed

/-- The enclosed region of a polygon has finite Lebesgue measure. -/
theorem volume_inside_lt_top {n : ℕ}
    (poly : Polygon (ℝ × ℝ) n) :
    volume (inside (poly.boundary (R := ℝ))) < ⊤ :=
  (isBounded_inside_of_isBounded
    (isBounded_boundary poly)).measure_lt_top

/-- On polygonal boundaries, converting `area` back to `ℝ≥0∞` recovers the
Lebesgue measure because the enclosed region has finite measure. -/
theorem ofReal_area_eq_volume {n : ℕ}
    (poly : Polygon (ℝ × ℝ) n) :
    ENNReal.ofReal (area (poly.boundary (R := ℝ))) =
      volume (inside (poly.boundary (R := ℝ))) := by
  unfold area
  exact ENNReal.ofReal_toReal (volume_inside_lt_top poly).ne

/-- Enclosed polygonal area is nonnegative. -/
theorem area_nonneg {n : ℕ} (poly : Polygon (ℝ × ℝ) n) :
    0 ≤ area (poly.boundary (R := ℝ)) :=
  ENNReal.toReal_nonneg

/-- Therefore the lattice points selected by `interiorPts` form a finite
set, independently of the simplicity assumption. -/
theorem finite_interior_latticePoints {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    Set.Finite
      {z : ℤ × ℤ |
        toPlane z ∈ inside ((latPoly v).boundary (R := ℝ))} :=
  finite_latticePoints_of_isBounded
    (isBounded_inside_of_isBounded
      (isBounded_boundary (latPoly v)))

/-- The numerical core of Pick's theorem.  In a triangulated polygonal disk,
`I + B` is the number of vertices, `E` the number of edges, and `F` the number
of triangular faces.  Euler's formula and edge-face incidence then determine
the area when every face has area `1 / 2`. -/
theorem pick_count_identity {I B E F : ℕ}
    (hEuler : I + B + F = E + 1)
    (hIncidence : 3 * F + B = 2 * E) :
    (F : ℝ) / 2 = (I : ℝ) + (B : ℝ) / 2 - 1 := by
  have hEuler' :
      (I : ℝ) + (B : ℝ) + (F : ℝ) = (E : ℝ) + 1 := by
    exact_mod_cast hEuler
  have hIncidence' :
      3 * (F : ℝ) + (B : ℝ) = 2 * (E : ℝ) := by
    exact_mod_cast hIncidence
  linarith

/-- The finite data and geometric equalities supplied by a lattice
triangulation of a simple polygon.  This separates the geometric construction
from the numerical conclusion of Pick's theorem. -/
structure PickCertificate {n : ℕ} (v : Fin n → ℤ × ℤ) where
  /-- Number of edges in the triangulation. -/
  edgeCount : ℕ
  /-- Number of triangular faces. -/
  faceCount : ℕ
  /-- Euler's formula for a triangulated disk. -/
  euler :
    interiorPts v + boundaryPts v + faceCount = edgeCount + 1
  /-- Double-counting incidences between triangular faces and edges. -/
  incidence :
    3 * faceCount + boundaryPts v = 2 * edgeCount
  /-- Additivity of area, with every elementary lattice face of area `1 / 2`. -/
  area_eq :
    area ((latPoly v).boundary (R := ℝ)) = (faceCount : ℝ) / 2

/-- A lattice-triangulation certificate implies the exact Pick formula. -/
theorem PickCertificate.area_formula {n : ℕ}
    {v : Fin n → ℤ × ℤ} (certificate : PickCertificate v) :
    area ((latPoly v).boundary (R := ℝ))
      = (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1 := by
  rw [certificate.area_eq]
  exact pick_count_identity certificate.euler certificate.incidence

end Submission.Helpers
