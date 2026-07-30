import Submission.LatticeTriangle

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.Dissection

/-- The numerical form of additivity for Pick's expression.  When two
polygons are glued along a lattice segment with `diagonalPoints` lattice
points, the points in the relative interior of that segment become interior
points, while its two endpoints remain on the outer boundary. -/
theorem pick_of_additive_split
    {wholeArea leftArea rightArea : ℝ}
    {wholeInterior wholeBoundary : ℕ}
    {leftInterior leftBoundary : ℕ}
    {rightInterior rightBoundary diagonalPoints : ℕ}
    (harea : wholeArea = leftArea + rightArea)
    (hinterior :
      wholeInterior + 2 =
        leftInterior + rightInterior + diagonalPoints)
    (hboundary :
      wholeBoundary + 2 * diagonalPoints =
        leftBoundary + rightBoundary + 2)
    (hleft :
      leftArea =
        (leftInterior : ℝ) + (leftBoundary : ℝ) / 2 - 1)
    (hright :
      rightArea =
        (rightInterior : ℝ) + (rightBoundary : ℝ) / 2 - 1) :
    wholeArea =
      (wholeInterior : ℝ) + (wholeBoundary : ℝ) / 2 - 1 := by
  have hinterior' :
      (wholeInterior : ℝ) + 2 =
        (leftInterior : ℝ) + (rightInterior : ℝ) +
          (diagonalPoints : ℝ) := by
    exact_mod_cast hinterior
  have hboundary' :
      (wholeBoundary : ℝ) + 2 * (diagonalPoints : ℝ) =
        (leftBoundary : ℝ) + (rightBoundary : ℝ) + 2 := by
    exact_mod_cast hboundary
  rw [harea, hleft, hright]
  linarith

/-- A recursively checked lattice dissection.  Triangle leaves carry the
already verified simple-lattice-triangle theorem.  A branch records exactly
the area and lattice-count balances needed when gluing its two children along
a diagonal. -/
inductive PickDecomposition :
    {n : ℕ} → (Fin n → ℤ × ℤ) → Type
  | triangle (v : Fin 3 → ℤ × ℤ)
      (hsimple : IsSimple (latPoly v)) :
      PickDecomposition v
  | glue {n leftSize rightSize : ℕ}
      (v : Fin n → ℤ × ℤ)
      (left : Fin leftSize → ℤ × ℤ)
      (right : Fin rightSize → ℤ × ℤ)
      (diagonalPoints : ℕ)
      (harea :
        area ((latPoly v).boundary (R := ℝ)) =
          area ((latPoly left).boundary (R := ℝ)) +
            area ((latPoly right).boundary (R := ℝ)))
      (hinterior :
        interiorPts v + 2 =
          interiorPts left + interiorPts right + diagonalPoints)
      (hboundary :
        boundaryPts v + 2 * diagonalPoints =
          boundaryPts left + boundaryPts right + 2)
      (leftDecomposition : PickDecomposition left)
      (rightDecomposition : PickDecomposition right) :
      PickDecomposition v
  | transport {n : ℕ}
      (v w : Fin n → ℤ × ℤ)
      (harea :
        area ((latPoly v).boundary (R := ℝ)) =
          area ((latPoly w).boundary (R := ℝ)))
      (hinterior : interiorPts v = interiorPts w)
      (hboundary : boundaryPts v = boundaryPts w)
      (decomposition : PickDecomposition w) :
      PickDecomposition v

/-- Every checked lattice dissection satisfies Pick's formula. -/
theorem PickDecomposition.pick
    {n : ℕ} {v : Fin n → ℤ × ℤ}
    (decomposition : PickDecomposition v) :
    area ((latPoly v).boundary (R := ℝ)) =
      (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1 := by
  induction decomposition with
  | triangle v hsimple =>
      exact LatticeTriangle.pick_three v hsimple
  | glue v left right diagonalPoints harea hinterior hboundary
      leftDecomposition rightDecomposition leftPick rightPick =>
      exact
        pick_of_additive_split harea hinterior hboundary
          leftPick rightPick
  | transport v w harea hinterior hboundary
      decomposition pick =>
      rw [harea, hinterior, hboundary]
      exact pick

end Submission.Dissection
