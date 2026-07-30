import Mathlib
import Submission.Pi.Chudnovsky

open scoped Real

namespace Submission

/-- **Chudnovsky's formula** for `π⁻¹`.

The proof follows Milla's complex-analytic argument (arXiv:1809.00533v6); the full
development lives in the local modules under `Submission/Pi/`. This wrapper exposes
the headline identity `Chudnovsky.chudnovskySum_eq_pi_inv`. -/
theorem chudnovsky_formula_for_pi_inv :
    chudnovskySum = π⁻¹ :=
  Chudnovsky.chudnovskySum_eq_pi_inv

end Submission
