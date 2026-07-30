import Submission.Final

namespace Submission

theorem lindemann_weierstrass {n : ℕ} (x : Fin n → ℂ)
    (h_alg : ∀ i, IsAlgebraic ℚ (x i))
    (h_lin : LinearIndependent ℚ x) :
    AlgebraicIndependent ℚ (fun i => Complex.exp (x i)) :=
  Submission.Final.algebraicIndependent_exp_of_algebraic x h_alg h_lin

end Submission
