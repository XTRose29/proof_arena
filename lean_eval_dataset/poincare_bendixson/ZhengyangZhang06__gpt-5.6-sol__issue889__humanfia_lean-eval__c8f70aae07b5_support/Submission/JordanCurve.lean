import Submission.Transport

namespace Submission.JordanCurve

/-- The complement of a planar Jordan curve has exactly two connected
components. -/
theorem jordan_curve
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents
          ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) =
      2 := by
  exact Transport.jordan_curve_euclidean r hcont hinj

end Submission.JordanCurve
