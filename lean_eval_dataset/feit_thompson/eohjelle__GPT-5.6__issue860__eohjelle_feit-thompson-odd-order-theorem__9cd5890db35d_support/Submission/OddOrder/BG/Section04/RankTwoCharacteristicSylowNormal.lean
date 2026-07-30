import Submission.OddOrder.BG.Section04.RankTwoFittingDerived
import Submission.OddOrder.MathlibSupport.FittingSylowFrattini

/-!
Bender--Glauberman Theorem 4.20(b).

A characteristic subgroup of a Sylow subgroup which lies in the Sylow
derived subgroup is normal when the Fitting subgroup has rank at most two.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection4.v: rank2_char_Sylow_normal` (Theorem 4.20(b)). -/
theorem rank2_char_Sylow_normal
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hodd : Odd (Nat.card G))
    (hsol : IsSolvable G)
    (hRank : ∀ q : ℕ, q.Prime →
      ¬ ∃ E : Subgroup (fittingCore G),
        IsElementaryAbelianOfRank q 3 E)
    (S : Sylow p G) {T : Subgroup G}
    (hTS : T ≤ (S : Subgroup G))
    (hchar : (T.subgroupOf (S : Subgroup G)).Characteristic)
    (hTder : T ≤
      (_root_.commutator S).map (S : Subgroup G).subtype) :
    T.Normal := by
  exact
    normal_of_characteristic_sylow_of_le_derived_of_derived_le_fittingCore
      S hTS hchar hTder (rank2_der1_sub_Fitting hodd hsol hRank)

end Submission.OddOrder.BG.Section04
