import Submission.CauchyIntegrandRational

open Set

noncomputable section

namespace Submission.Helpers

lemma cauchyIntegrand_hasCompactSupport (K : Set ℂ) (h : ℂ → ℂ)
    (hK0 : ∀ z ∈ K, h z = 0) (hh : HasCompactSupport h) :
    HasCompactSupport (cauchyIntegrand K h hK0) := by
  apply hh.mono'
  intro w hw
  apply subset_tsupport h
  change h w ≠ 0
  intro hw0
  apply hw
  ext z
  simp [cauchyIntegrand, hw0]

end Submission.Helpers
