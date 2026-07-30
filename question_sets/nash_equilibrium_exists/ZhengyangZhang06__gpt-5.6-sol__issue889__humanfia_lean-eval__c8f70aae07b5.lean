import Submission.Nash

open LeanEval.GameTheory

namespace Submission

theorem nash_equilibrium_exists {n : ℕ} {S : Fin n → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : Fin n → StrategyProfile n S → ℝ) :
    ∃ σ : ∀ i, S i → ℝ, IsNashEquilibrium u σ :=
  nash_equilibrium_exists_aux u

end Submission
