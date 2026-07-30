import Submission.FilledRegion
import Submission.TriangleCoords

namespace Submission.TriangleFill

/-- Filling a triangle boundary recovers the usual closed affine triangle. -/
theorem fill_toPolygon_boundary_eq_closedInterior
    (t : Affine.Triangle ℝ (ℝ × ℝ)) :
    FilledRegion.fill
        (t.toPolygon.boundary (R := ℝ)) =
      t.closedInterior := by
  rw [FilledRegion.fill,
    Submission.Triangle.inside_toPolygon_boundary_eq_interior,
    Submission.Triangle.toPolygon_boundary_eq_surface]
  exact
    Set.sdiff_union_of_subset
      t.interior_subset_closedInterior

end Submission.TriangleFill
