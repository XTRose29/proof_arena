import Mathlib
import Submission.BrouwerReduction

open Set

namespace Submission

theorem brouwer_fixed_point {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (_hK_compact : IsCompact K) (_hK_convex : Convex ℝ K)
    (_hK_nonempty : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (_hf_cont : ContinuousOn f K) (_hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
  brouwer_fixed_point_aux _hK_compact _hK_convex _hK_nonempty f _hf_cont _hf_maps

end Submission
