import Mathlib
import Submission.SchauderApprox

namespace Submission

theorem schauder_fixed_point {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (hK_nonempty : K.Nonempty)
    (f : E → E)
    (hf_cont : ContinuousOn f K) (hf_maps : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  have hdist_cont : ContinuousOn (fun x => dist (f x) x) K := by
    intro x hx
    exact (hf_cont x hx).dist continuousWithinAt_id
  obtain ⟨x, hxK, hx_min⟩ :=
    hK_compact.exists_isMinOn hK_nonempty hdist_cont
  refine ⟨x, hxK, ?_⟩
  by_contra hne
  have hdist_pos : 0 < dist (f x) x := dist_pos.mpr hne
  obtain ⟨y, hyK, hy⟩ :=
    exists_approximate_fixed_point hK_compact hK_convex hK_nonempty
      f hf_cont hf_maps (half_pos hdist_pos)
  have hmin : dist (f x) x ≤ dist (f y) y := hx_min hyK
  linarith

end Submission
