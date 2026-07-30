import Submission.OddOrder.BG.Section01.AbelianConstrained
import Submission.OddOrder.BG.Section01.ConstrainedSolvable

/-!
The solvable specialization of p-stable abelian constrainedness.

After Appendix A supplies p-stability for odd-order groups, this is the exact
handoff used by `BGsection6.odd_p_abelian_constrained`.
-/

namespace Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G] [Finite G]

theorem solvable_isPAbelianConstrained_of_isPStable {p : ℕ}
    [Fact p.Prime] [IsSolvable G] (hstable : IsPStable p G) :
    IsPAbelianConstrained p G :=
  isPAbelianConstrained_of_isPConstrained_of_isPStable
    solvable_isPConstrained hstable

end Submission.OddOrder.BG.Section01
