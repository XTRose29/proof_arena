import Submission.OddOrder.BG.AppendixAB.PStableLift
import Submission.OddOrder.MathlibSupport.FittingPCore

/-!
The p-core specialization of the A.5.2 lifting theorem.

For a solvable group with trivial `p'`-core, the centralizer of the `p`-core
is a `p`-group.  Thus the quotient conclusion supplied by `p`-stability lifts
without an additional centralizer hypothesis when `P = O_p(G)`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem abelianGenerated_pCore_le_pCore_of_isPStable {p : ℕ}
    [Fact p.Prime] [IsSolvable G] {X : Subgroup G}
    (hstable : IsPStable p G)
    (hgen : GeneratedBy (PNormalizedAbelian p (pCore p G)) X)
    (hprimeCore : pPrimeCore p G = ⊥) :
    X ≤ pCore p G := by
  apply abelianGenerated_le_pCore_of_isPStable_of_centralizer_isPGroup
    hstable pCore_isPGroup hgen
  exact centralizer_pCore_isPGroup_of_pPrimeCore_eq_bot hprimeCore

end Submission.OddOrder.BG.AppendixAB
