import ChallengeDeps
import Submission.Tower

open LeanEval.NumberTheory.GaussWantzel

namespace Submission

theorem gauss_wantzel_constructible_polygon (n : ℕ) (hn : 3 ≤ n) :
    IsConstructible (Real.cos (2 * Real.pi / n)) ↔ GaussWantzelNumber n := by
  constructor
  · intro hcos
    apply Helpers.gaussWantzel_of_isTwoPower_totient (by omega)
    exact Helpers.isTwoPower_totient_of_isConstructible_cos hn hcos
  · intro hgw
    apply Helpers.isConstructible_cos_of_isTwoPower_totient (by omega)
    exact Helpers.gaussWantzel_isTwoPower_totient hgw

end Submission
