import Submission.BrouwerReduction

open Set

namespace Submission

/-- Brouwer's theorem transported from a Euclidean space to an arbitrary
finite-dimensional real normed space. -/
theorem finiteDimensional_fixed_point {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (hK_nonempty : K.Nonempty)
    (f : E → E)
    (hf_cont : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let L : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := e '' K
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun y => e (f (e.symm y))
  have hL_compact : IsCompact L := hK_compact.image e.continuous
  have hL_convex : Convex ℝ L := by
    simpa [L] using hK_convex.linear_image e.toLinearEquiv.toLinearMap
  have hL_nonempty : L.Nonempty := hK_nonempty.image e
  have he_maps : MapsTo e.symm L K := by
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  have hpre_cont : ContinuousOn (fun y => f (e.symm y)) L :=
    hf_cont.comp e.symm.continuous.continuousOn he_maps
  have hg_cont : ContinuousOn g L := by
    simpa [g, Function.comp_def] using e.continuous.comp_continuousOn hpre_cont
  have hg_maps : MapsTo g L L := by
    intro y hy
    exact ⟨f (e.symm y), hf_maps (he_maps hy), by simp [g]⟩
  obtain ⟨y, hy, hgy⟩ :=
    brouwer_fixed_point_aux hL_compact hL_convex hL_nonempty g hg_cont hg_maps
  refine ⟨e.symm y, he_maps hy, ?_⟩
  have := congrArg e.symm hgy
  simpa [g] using this

end Submission
