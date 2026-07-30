import Submission.OddOrder.BG.AppendixAB.PStableLift
import Submission.OddOrder.MathlibSupport.ConstrainedCentralizer

/-!
The complete p-stable form of Bender-Glauberman A.5.2.

The coprime-action argument now supplies the p-group centralizer required by
the quotient-lifting theorem, so no auxiliary group-theoretic hypothesis
remains beyond solvability and p-stability.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem abelianGeneratedConstrained_of_isPStable {p : ℕ}
    [Fact p.Prime] [IsSolvable G] (hstable : IsPStable p G) :
    AbelianGeneratedConstrained p G := by
  apply abelianGeneratedConstrained_of_isPStable_of_centralizer_isPGroup hstable
  intro P hP hPnormal hprimeCore hcent
  exact centralizer_isPGroup_of_pPrimeCore_eq_bot
    hP hPnormal hprimeCore hcent

end Submission.OddOrder.BG.AppendixAB
