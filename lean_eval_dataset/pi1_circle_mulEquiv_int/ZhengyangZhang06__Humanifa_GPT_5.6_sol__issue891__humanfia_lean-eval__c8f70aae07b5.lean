import Mathlib
import Submission.Helpers

namespace Submission

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) := by
  rw [← Circle.exp_zero]
  exact ⟨
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Circle) (x := Circle.exp 0)).trans
      ((Circle.isAddQuotientCoveringMap_exp.fundamentalGroupMulEquiv (0 : ℝ)).trans
        (AddEquiv.toMultiplicative
          (Helpers.zMultiplesEquivInt (2 * Real.pi) (by positivity))))⟩

end Submission
