import Submission.FinalSynthesis
import Submission.LinearRegularization

open scoped Polynomial

namespace Submission

theorem mergelyan (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (f : ℂ → ℂ) (hfc : ContinuousOn f K) (hfh : AnalyticOnNhd ℂ f (interior K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  exact
    Helpers.exists_mergelyan_polynomial
      K hK hKc f hfc hfh ε hε

end Submission
