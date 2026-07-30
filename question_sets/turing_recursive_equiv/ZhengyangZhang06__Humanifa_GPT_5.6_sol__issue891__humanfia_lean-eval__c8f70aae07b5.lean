import Mathlib
import Submission.Helpers
import Submission.Forward

open Computability Turing

namespace Submission

theorem turing_recursive_equiv (f : ℕ → ℕ) :
    Computable f ↔ Nonempty (TM2Computable encodeNat encodeNat f) := by
  constructor
  · exact Helpers.Forward.tm2_of_computable
  · rintro ⟨h⟩
    exact Helpers.Machine.computable_of_tm2 h

end Submission
