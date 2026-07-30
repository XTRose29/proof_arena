import Submission.StableUniqueness

namespace Submission

theorem jordan_brouwer (d : ℕ) (_hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → EuclideanSpace ℝ (Fin d))
    (_hcont : Continuous r) (_hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d)))) =
      2 := by
  exact Helpers.jordan_brouwer_of_stable_commutation
    d _hd r _hcont _hinj

end Submission
