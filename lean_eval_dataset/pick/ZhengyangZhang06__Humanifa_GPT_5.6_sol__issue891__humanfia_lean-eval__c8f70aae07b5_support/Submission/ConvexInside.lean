import Submission.HalfspaceEscape

open LeanEval.Geometry.PicksTheorem

namespace Submission.ConvexInside

/-- For a nonempty compact convex planar set, the challenge's
bounded-component interior of its frontier is its ordinary topological
interior.  Exterior points escape along a Hahn--Banach supporting
half-space. -/
theorem inside_frontier_eq_interior
    {K : Set (ℝ × ℝ)}
    (hKconvex : Convex ℝ K)
    (hKcompact : IsCompact K)
    (hKnonempty : K.Nonempty) :
    inside (frontier K) = interior K := by
  have hKclosed : IsClosed K :=
    hKcompact.isClosed
  apply Inside.inside_eq_of_open_partition
  · calc
      (frontier K)ᶜ =
          interior K ∪ interior Kᶜ :=
        compl_frontier_eq_union_interior
      _ = interior K ∪ Kᶜ := by
        rw [hKclosed.isOpen_compl.interior_eq]
  · exact isOpen_interior
  · exact hKclosed.isOpen_compl
  · rw [Set.disjoint_left]
    intro x hxInterior hxCompl
    exact hxCompl (interior_subset hxInterior)
  · exact
      hKcompact.isBounded.subset interior_subset
  · intro x hxCompl
    obtain ⟨f, u, hKf, hfx⟩ :=
      geometric_hahn_banach_closed_point
        hKconvex hKclosed hxCompl
    obtain ⟨z, hzK⟩ :=
      hKnonempty
    have hdirection :
        0 < f (x - z) := by
      rw [map_sub]
      linarith [hKf z hzK]
    obtain
      ⟨W, hxW, hWpreconnected, hWKcompl, hWunbounded⟩ :=
        HalfspaceEscape.exists_unbounded_escape_of_strictHalfspace
          f u hfx hdirection
          (fun y hyK => (hKf y hyK).le)
    refine
      ⟨W, hxW, hWpreconnected, ?_, hWunbounded⟩
    intro y hyW hyFrontier
    apply hWKcompl hyW
    rw [← hKclosed.closure_eq]
    exact frontier_subset_closure hyFrontier

end Submission.ConvexInside
