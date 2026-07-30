import ChallengeDeps
import Submission.BezoutCount

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

variable {K : Type*} [Field K]

namespace Submission

theorem bezout_multiplicity [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (_hd : ∀ k, (f k).IsHomogeneous (d k))
    (_hdeg : ∀ k, (f k).totalDegree = d k)
    (_hd_pos : ∀ k, 1 ≤ d k)
    (_hfin : (⋂ k, vanishingSet (f k)).Finite) :
    ∑ᶠ p ∈ (⋂ k, vanishingSet (f k)), intersectionMultiplicity f p
      = (∏ k, d k : ℕ∞) := by
  obtain ⟨a, hne, hLne⟩ :=
    Helpers.exists_avoiding_nonzero_linearForm
      (⋂ k, vanishingSet (f k)) _hfin
  calc
    ∑ᶠ p ∈ (⋂ k, vanishingSet (f k)), intersectionMultiplicity f p =
        Module.length K
          (MvPolynomial (Fin (n + 1)) K ⧸
            Helpers.linearSlicePolynomialIdeal f a) :=
      (Helpers.length_linearSlicePolynomialQuotient_eq_intersectionMultiplicity_sum
        f d _hd a _hfin hne).symm
    _ = (∏ k, d k : ℕ∞) :=
      Helpers.length_linearSlicePolynomialQuotient_eq_degree_prod
        f d _hd _hd_pos a _hfin hne hLne

end Submission
