import Mathlib
import Submission.Helpers

namespace Submission

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
  ⟨Submission.Helpers.pi1CircleMulEquivIntAux⟩

end Submission
