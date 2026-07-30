import Submission.SubmoduleIntegral
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set
open scoped ContDiff Topology Manifold

noncomputable section

namespace Submission.Helpers

lemma exists_smooth_cutoff (K U : Set ℂ) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ χ : ℂ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z ∈ Metric.cthickening (δ / 3) K, χ z = 1) ∧
      tsupport χ ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let inner := Metric.cthickening (δ / 3) K
  let outer := Metric.thickening (2 * δ / 3) K
  have hinner : IsClosed inner := Metric.isClosed_cthickening
  have houter : IsOpen outer := Metric.isOpen_thickening
  have hinner_outer : inner ⊆ outer := by
    dsimp [inner, outer]
    exact Metric.cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨χ, hχsmooth, _hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, ℂ) houter hinner hinner_outer
  have houter_closure :
      closure outer ⊆ Metric.cthickening δ K := by
    refine (Metric.closure_thickening_subset_cthickening (2 * δ / 3) K).trans ?_
    exact Metric.cthickening_mono (by linarith) K
  have hχtsupport : tsupport χ ⊆ U := by
    rw [tsupport, hχsupport]
    exact houter_closure.trans hδU
  have hχcompact : HasCompactSupport χ := by
    rw [HasCompactSupport]
    exact hK.cthickening.of_isClosed_subset isClosed_closure
      (by simpa only [tsupport, hχsupport] using houter_closure)
  refine ⟨δ, hδ, χ, hχsmooth.contDiff, hχcompact, ?_, hχtsupport⟩
  intro z hz
  exact (hχone z).1 hz

end Submission.Helpers
