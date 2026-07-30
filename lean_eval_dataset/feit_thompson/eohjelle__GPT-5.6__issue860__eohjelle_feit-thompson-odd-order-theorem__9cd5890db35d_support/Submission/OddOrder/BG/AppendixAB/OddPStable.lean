import Submission.OddOrder.BG.AppendixAB.OddPStableBaerSuzuki
import Submission.OddOrder.BG.AppendixAB.QuadraticPairLocalPrinciple

/-!
The odd-order p-stability theorem of Bender-Glauberman Appendix A.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The local quadratic-pair principle, discharged by strong induction on
the acted-on p-subgroup. -/
theorem oddQuadraticPairPrinciple {p : ℕ} [Fact p.Prime] :
    OddQuadraticPairPrinciple p G := by
  intro E x y hxN hyN hodd hE hx hy
  change IsPGroup p (localQuotientPair E hxN hyN)
  exact oddQuadraticLocalPrinciple G E x y hxN hyN hodd hE hx hy

/-- Every finite group of odd order is p-stable. -/
theorem odd_isPStable {p : ℕ} [Fact p.Prime]
    (hodd : Odd (Nat.card G)) : IsPStable p G :=
  isPStable_of_odd_quadraticPairPrinciple hodd oddQuadraticPairPrinciple

end Submission.OddOrder.BG.AppendixAB
