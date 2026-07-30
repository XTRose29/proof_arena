import Submission.Helpers

open LeanEval.NumberTheory.LandsbergSchaar

namespace Submission

theorem landsberg_schaar (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    gaussS (2 * q : ℕ) p
      = Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * gaussS (-(p : ℤ)) (2 * q) :=
  Helpers.landsberg_schaar_aux p q hp hq

end Submission
