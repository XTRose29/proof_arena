import Submission.OddOrder.BG.Section04.RankTwoDerivedComplement
import Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment

/-!
Bender--Glauberman Theorem 4.18(d).

A `p'`-subgroup of the ambient derived subgroup is viewed inside that
derived subgroup and placed in its normal Hall `p'`-subgroup.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection4.v: rank2_sub_p'core_der1` (Bender--Glauberman
Theorem 4.18(d)). -/
theorem rank2_sub_p'core_der1
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hsol : IsSolvable G)
    (hodd : Odd (Nat.card G))
    (hRank : ¬ ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E)
    {A : Subgroup G}
    (hAder : A ≤ _root_.commutator G)
    (hAp' : IsPPrimeSubgroup p A) :
    A ≤ (pPrimeCore p (_root_.commutator G)).map
      (_root_.commutator G).subtype := by
  let D : Subgroup G := _root_.commutator G
  let AD : Subgroup D := A.subgroupOf D
  have hADprime : IsPPrimeSubgroup p AD := by
    rw [IsPPrimeSubgroup]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAder).toEquiv]
    exact hAp'
  have hHall : IsPrimeComplement p (pPrimeCore p D) := by
    exact (rank2_der1_complement hsol hodd hRank).1
  have hADcore : AD ≤ pPrimeCore p D :=
    isPPrimeSubgroup_le_normal_primeComplement
      (hHnormal := by infer_instance) hHall hADprime
  rw [← Subgroup.map_subgroupOf_eq_of_le hAder]
  exact Subgroup.map_mono hADcore

end Submission.OddOrder.BG.Section04
