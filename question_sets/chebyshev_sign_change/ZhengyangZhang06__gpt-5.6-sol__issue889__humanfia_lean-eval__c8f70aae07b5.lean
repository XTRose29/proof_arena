import Submission.BoundaryContradiction

open LeanEval.NumberTheory.ChebyshevSignChangeProblem

namespace Submission

theorem chebyshev_sign_change :
    chebyshevLead.Infinite ∧
    {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}.Infinite :=
  BoundaryContradiction.chebyshev_sign_change

end Submission
