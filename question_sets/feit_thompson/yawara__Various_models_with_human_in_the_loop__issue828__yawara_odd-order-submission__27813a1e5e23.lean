import Mathlib
import Submission.OddOrder.FeitThompson

namespace Submission

theorem feit_thompson {G : Type*} [Group G] [Finite G]
    (_h : Odd (Nat.card G)) : IsSolvable G :=
  OddOrder.feitThompson _h

end Submission
