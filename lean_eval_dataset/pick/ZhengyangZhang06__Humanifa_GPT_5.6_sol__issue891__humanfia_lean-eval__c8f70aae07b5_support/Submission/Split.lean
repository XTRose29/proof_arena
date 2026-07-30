import Submission.Dissection

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.Split

/-- Lattice points in the bounded-component interior of a lattice polygon. -/
def interiorLatticeSet {n : ℕ} (v : Fin n → ℤ × ℤ) :
    Set (ℤ × ℤ) :=
  {z |
    toPlane z ∈
      inside ((latPoly v).boundary (R := ℝ))}

/-- Lattice points on the boundary of a lattice polygon. -/
def boundaryLatticeSet {n : ℕ} (v : Fin n → ℤ × ℤ) :
    Set (ℤ × ℤ) :=
  {z |
    toPlane z ∈
      (latPoly v).boundary (R := ℝ)}

@[simp]
theorem ncard_interiorLatticeSet {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    (interiorLatticeSet v).ncard = interiorPts v :=
  rfl

@[simp]
theorem ncard_boundaryLatticeSet {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    (boundaryLatticeSet v).ncard = boundaryPts v :=
  rfl

theorem finite_interiorLatticeSet {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    (interiorLatticeSet v).Finite :=
  Helpers.finite_interior_latticePoints v

theorem finite_boundaryLatticeSet {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    (boundaryLatticeSet v).Finite :=
  Helpers.finite_boundary_latticePoints v

/-- Cardinality balance for the interiors in a diagonal split.  The set `D`
is the relative-interior lattice points of the diagonal, so its cardinality
is two less than the cardinality of the closed diagonal. -/
theorem interior_count_balance
    {whole left right diagonalInterior : Set (ℤ × ℤ)}
    {diagonalPoints : ℕ}
    (hwhole :
      whole = (left ∪ right) ∪ diagonalInterior)
    (hleftRight : Disjoint left right)
    (hdiagonal :
      Disjoint (left ∪ right) diagonalInterior)
    (hleftFinite : left.Finite)
    (hrightFinite : right.Finite)
    (hdiagonalFinite : diagonalInterior.Finite)
    (hdiagonalCard :
      diagonalInterior.ncard + 2 = diagonalPoints) :
    whole.ncard + 2 =
      left.ncard + right.ncard + diagonalPoints := by
  rw [hwhole,
    Set.ncard_union_eq hdiagonal
      (hs := hleftFinite.union hrightFinite)
      (ht := hdiagonalFinite),
    Set.ncard_union_eq hleftRight
      (hs := hleftFinite)
      (ht := hrightFinite)]
  omega

/-- Cardinality balance for the boundaries in a diagonal split.  The two
child boundaries meet in the closed diagonal.  The closed diagonal meets the
outer boundary in exactly its two endpoints. -/
theorem boundary_count_balance
    {whole left right diagonal : Set (ℤ × ℤ)}
    (hunion : left ∪ right = whole ∪ diagonal)
    (hinter : left ∩ right = diagonal)
    (hendpoints : (whole ∩ diagonal).ncard = 2)
    (hwholeFinite : whole.Finite)
    (hleftFinite : left.Finite)
    (hrightFinite : right.Finite)
    (hdiagonalFinite : diagonal.Finite) :
    whole.ncard + 2 * diagonal.ncard =
      left.ncard + right.ncard + 2 := by
  have hchildren :=
    Set.ncard_union_add_ncard_inter left right
      (hs := hleftFinite) (ht := hrightFinite)
  rw [hunion, hinter] at hchildren
  have houter :=
    Set.ncard_union_add_ncard_inter whole diagonal
      (hs := hwholeFinite) (ht := hdiagonalFinite)
  rw [hendpoints] at houter
  omega

/-- Area is additive when the whole bounded-component interior partitions
into two disjoint child interiors and a null seam. -/
theorem area_add_of_inside_partition
    {n leftSize rightSize : ℕ}
    (v : Fin n → ℤ × ℤ)
    (left : Fin leftSize → ℤ × ℤ)
    (right : Fin rightSize → ℤ × ℤ)
    (seam : Set (ℝ × ℝ))
    (hinside :
      inside ((latPoly v).boundary (R := ℝ)) =
        (inside ((latPoly left).boundary (R := ℝ)) ∪
          inside ((latPoly right).boundary (R := ℝ))) ∪ seam)
    (hleftRight :
      Disjoint
        (inside ((latPoly left).boundary (R := ℝ)))
        (inside ((latPoly right).boundary (R := ℝ))))
    (hseam :
      Disjoint
        (inside ((latPoly left).boundary (R := ℝ)) ∪
          inside ((latPoly right).boundary (R := ℝ)))
        seam)
    (hseamMeasurable : MeasurableSet seam)
    (hseamNull : volume seam = 0) :
    area ((latPoly v).boundary (R := ℝ)) =
      area ((latPoly left).boundary (R := ℝ)) +
        area ((latPoly right).boundary (R := ℝ)) := by
  unfold area
  rw [hinside,
    measure_union hseam hseamMeasurable,
    measure_union hleftRight
      (Helpers.isOpen_polygon_inside (latPoly right)).measurableSet,
    hseamNull, add_zero,
    ENNReal.toReal_add
      (Helpers.volume_inside_lt_top (latPoly left)).ne
      (Helpers.volume_inside_lt_top (latPoly right)).ne]

/-- Package the geometric and finite-set facts of one diagonal split into a
branch of a recursively checked Pick decomposition. -/
noncomputable def glueDecompositions
    {n leftSize rightSize : ℕ}
    (v : Fin n → ℤ × ℤ)
    (left : Fin leftSize → ℤ × ℤ)
    (right : Fin rightSize → ℤ × ℤ)
    (diagonal diagonalInterior : Set (ℤ × ℤ))
    (harea :
      area ((latPoly v).boundary (R := ℝ)) =
        area ((latPoly left).boundary (R := ℝ)) +
          area ((latPoly right).boundary (R := ℝ)))
    (hinterior :
      interiorLatticeSet v =
        (interiorLatticeSet left ∪ interiorLatticeSet right) ∪
          diagonalInterior)
    (hinteriorLeftRight :
      Disjoint (interiorLatticeSet left) (interiorLatticeSet right))
    (hinteriorDiagonal :
      Disjoint
        (interiorLatticeSet left ∪ interiorLatticeSet right)
        diagonalInterior)
    (hdiagonalInteriorFinite : diagonalInterior.Finite)
    (hdiagonalCard :
      diagonalInterior.ncard + 2 = diagonal.ncard)
    (hboundary :
      boundaryLatticeSet left ∪ boundaryLatticeSet right =
        boundaryLatticeSet v ∪ diagonal)
    (hboundaryInter :
      boundaryLatticeSet left ∩ boundaryLatticeSet right = diagonal)
    (hboundaryEndpoints :
      (boundaryLatticeSet v ∩ diagonal).ncard = 2)
    (hdiagonalFinite : diagonal.Finite)
    (leftDecomposition : Dissection.PickDecomposition left)
    (rightDecomposition : Dissection.PickDecomposition right) :
    Dissection.PickDecomposition v := by
  apply Dissection.PickDecomposition.glue v left right diagonal.ncard
  · exact harea
  · simpa only [ncard_interiorLatticeSet] using
      interior_count_balance hinterior hinteriorLeftRight
        hinteriorDiagonal
        (finite_interiorLatticeSet left)
        (finite_interiorLatticeSet right)
        hdiagonalInteriorFinite hdiagonalCard
  · simpa only [ncard_boundaryLatticeSet] using
      boundary_count_balance hboundary hboundaryInter
        hboundaryEndpoints
        (finite_boundaryLatticeSet v)
        (finite_boundaryLatticeSet left)
        (finite_boundaryLatticeSet right)
        hdiagonalFinite
  · exact leftDecomposition
  · exact rightDecomposition

end Submission.Split
